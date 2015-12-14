#include <stdio.h>
#include <iostream>
#include <stdlib.h>
#include <string.h>

using namespace std;

bool ltableInit = false;
typedef unsigned char UBYTE;
typedef unsigned int UWORD;

#define MAX_ROW 4
#define MAX_COL 4
#define ROUND_CNT 10
#define NROUND ROUND_CNT
#define KEY_CHAIN_CNT (MAX_COL*(ROUND_CNT+1))
#define NBYTE MAX_COL
#define NKEY 4
#define BLOCK_SIZE 16 // 128 bits

UBYTE *ltable=NULL;
UBYTE *atable=NULL; 

UBYTE PTable[256][256] = { 0 };
UBYTE SBox[256] = { 0x0 };
UBYTE InvSBox[256] = { 0x0 };

UBYTE State[MAX_ROW][MAX_COL] = 
{ 
    { 0x32, 0x88, 0x31, 0xe0 },  
    { 0x43, 0x5a, 0x31, 0x37 },  
    { 0xf6, 0x30, 0x98, 0x07 },  
    { 0xa8, 0x8d, 0xa2, 0x34 }
};

UBYTE IV[MAX_ROW][MAX_COL] = { 0 };

UBYTE ResState[MAX_ROW][MAX_COL];
UBYTE key[4*NKEY] = { 0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c };

UWORD KeyChain[KEY_CHAIN_CNT];
UWORD Rcon[NROUND+2]; // starts from 1
UBYTE Text[BLOCK_SIZE*1024*128] = { 0 }; // plain text or cipher text 
int TextSize;
UBYTE OutText[BLOCK_SIZE*1024*128] = { 0 }; // plain text or cipher text 
int PlainTextSize;


enum {
    MODE_AES_CBC_ENC=1,
    MODE_AES_CBC_DEC,
    MODE_AES_CTR_ENC,
    MODE_AES_CTR_DEC,
} CIPHER_MODE;

void show_sbox()
{
    int i;
    printf("s-box>>=======\n");
    for (i=0; i< 256; i++)
    {
        if ((i%16)==0)
            cout << endl;
        printf("%02x ", SBox[i]);
    }
    printf("s-box<<=======\n");
}

void show_ltable()
{
    int i;
    printf("atable>>=======");
    for (i=0; i< 256; i++)
    {
        if ((i%8)==0)
            cout << endl;
        printf("%02x ", atable[i]);
    }
    cout << endl;
    printf("ltable>>=======");
    for (i=0; i< 256; i++)
    {
        if ((i%8)==0)
            cout << endl;
        printf("%02x ", ltable[i]);
    }
    cout << endl;
}

UBYTE byte_prod2(UBYTE in)
{
    UBYTE val = in, msb;
    msb = in & 0x80;
    val<<=1;
    if (msb)
    {
        val^=0x1b;
    }
    return val;
}

UBYTE byte_prod3(UBYTE in)
{
    UBYTE val = byte_prod2(in);
    return val^in;
}

UBYTE get_ms1bmask(UBYTE byte)
{
    UBYTE bmask;
    
    for (bmask = 0x80; bmask > 0 ; bmask>>=1)
    {
        if (byte & bmask)
            break;
    }
    return bmask;
}

void show_ptable()
{
    int ml, n;
    cout << "PTable >>----------------------" << endl;
    for (ml = 1 ; ml ; ml++)
    {
        for (n = ml ; n ; n++)
        {
           printf("PTable[%d][%d]= %02x ", ml, n, PTable[n][ml]);     
        }
        cout <<endl;
    }
    cout << "PTable <<----------------------" << endl;

}


void create_ptable()
{
    static bool ptable_init = false;
    if (ptable_init)
        return;
    UBYTE ml, n, mlLeft, mlRight;
  
    for (ml = 1 ; ml ; ml++)
    {
        
        if (ml==1)
        {
            for (n = ml ; n ; n++)
            {
                PTable[n][ml] = PTable[ml][n] = n;
                printf("PTable[%d][%d]= %02x ", n, ml, PTable[n][ml]);     
            }
            continue;
        }
        else
        {
            for (n = ml ; n  ; n++)
            {
                mlLeft = get_ms1bmask(ml);
                mlRight = ml & (~mlLeft);
                if (mlRight)
                {
                   PTable[n][ml] = PTable[ml][n] = PTable[n][mlLeft] ^ PTable[n][mlRight];
                   printf("c1 PTable[%d][%d]= %02x ", n, ml, PTable[n][ml]);     
                }
                else
                {
                    PTable[n][ml] = PTable[ml][n] = byte_prod2(PTable[n][mlLeft>>1]);
                    printf("c2 PTable[%d][%d]= %02x ", n, ml, PTable[n][ml]);     
                }
            }
        }
    }
    ptable_init = true;   
 //   show_ptable();
}


UBYTE byte_prod(UBYTE in1, UBYTE in2)
{
    create_ptable();
    
//    printf("byte_prod -> %02x\n", PTable[in1][in2]);
    return PTable[in1][in2];
}

void gen_ltable()
{
    if (ltableInit)
    {
        return;
    }
    ltable = (UBYTE*)calloc(256, 1);
    atable = (UBYTE*)calloc(256, 1);
    // use 3 as generator for GF(2^8)     
    int i;
    atable[0] = 1;
    ltable[1] = 0;
    for (i=1; i< 256; i++)
    {
        UBYTE d, hi;
        d = atable[i-1];
        hi = d & 0x80;
        d<<=1;
        if (hi)
        {
            d^=0x1b;
        }
        d^=atable[i-1];
        atable[i] = d;
        ltable[d] = i;
    }
    ltableInit = true;
 //   show_ltable();
}

// multiplically inversion of input x
// http://www.samiam.org/galois.html#inverse
// 
int mult_inv(unsigned char in)
{
    gen_ltable();
    if (!in)
        return 0;
    return atable[255-ltable[in]];
}


void release_ltable()
{
    if (ltableInit)
    {
        free(ltable);
        free(atable);
    }
}

void copy_state(UBYTE in[MAX_ROW][MAX_COL],  UBYTE out[MAX_ROW][MAX_COL])
{
    int r, c;
    
    for (r =0 ; r< MAX_ROW ; r++)
        for (c =0 ; c< MAX_COL ; c++)
        {
            out[r][c] = in[r][c];
        }
}

void create_sbox()
{
    static bool SBoxCreated = false;
    if (SBoxCreated==true)
        return ;
    int d, ind;    
       // create S-Box 
    for (d=0; d <= 0xff ; d++)
    {
        UBYTE mi = mult_inv(d);
        printf("%02x - MI -> %02x\n", d, mi);
        
        UBYTE matrixRow = 0xf1;
        UBYTE c = 0x63;
        int i, bi;
        UBYTE bit0 = 0x1;
        UBYTE subByte=0;
            
        for (i =0 ; i< 8; i++, bit0<<=1)
        {
            UBYTE val = 0;
            UBYTE val1 =  matrixRow & mi;
            UBYTE bit1 = 0x1;
            for (bi= 0; bi < 8 ; bi++, bit1<<=1)
            {
                if (val1 & bit1)
                    val ^= 1;
            }
            if (val) 
                subByte |= bit0;
            UBYTE lsb = (matrixRow & 0x80)? 0x1 : 0;
            matrixRow <<=1 ;
            matrixRow |= lsb;
        }
        subByte ^= c;

            
        SBox[d] = subByte;
#if  0
        if (InvSBox[subByte])
        {
            printf("Error! InvSBox[%d]= %02x duplicate\n", subByte, d);
            exit(-1);
        }
#endif        
        InvSBox[subByte] = d;
    }
    show_sbox();
    release_ltable();
    SBoxCreated = true;
    
}

void SubBytes(UBYTE in[MAX_ROW][MAX_COL])
{
    create_sbox();
    int r, c;
    
    for (r =0 ; r< MAX_ROW ; r++)
        for (c =0 ; c< MAX_COL ; c++)
        {
            in[r][c] = SBox[in[r][c]];
        }
}

void ShiftRows(UBYTE in[MAX_ROW][MAX_COL])
{
    UBYTE val;
    int r, shiftByte ;
    for (r = 0, shiftByte = 0 ; r < MAX_ROW ; r++, shiftByte ++ )
    {
        UWORD val = (in[r][0]<<24) | (in[r][1]<<16) | (in[r][2]<<8) | in[r][3];
        val = (val << (shiftByte << 3)) |  (val >> ((4-shiftByte) << 3));
        int c, shitfBit;
        for (c=0, shitfBit = 24; c< 4; c++, shitfBit-=8)
        {
            in[r][c] = (UBYTE) ((val >> shitfBit) & 0xff);
        }
    }
}

void copy_to_col_list(UBYTE in[MAX_ROW][MAX_COL], int c, UBYTE clist[MAX_COL])
{
    int r;
    for (r=0; r < MAX_ROW; r++)
    {
        clist[r] = in[r][c];
    }
}

void copy_from_col_list(UBYTE out[MAX_ROW][MAX_COL], int c, UBYTE clist[MAX_COL])
{
    int r;
    for (r=0; r < MAX_ROW; r++)
    {
        out[r][c] = clist[r];
    }
}

void copy_array(UBYTE inArray[BLOCK_SIZE],  UBYTE outArray[BLOCK_SIZE])
{
    memcpy(outArray, inArray, BLOCK_SIZE);
}


void multi_matrix(UBYTE matrix[MAX_ROW][MAX_COL], UBYTE in[MAX_ROW], UBYTE out[MAX_ROW])
{
    int r, c;
    for (r=0; r<MAX_ROW ; r++)
    {
        UBYTE val = 0;
    
        for (c=0; c< MAX_COL; c++)
        {
            val ^= byte_prod(matrix[r][c], in[c]);
        }
        out[r] = val;
    }
}

void gen_matrix_from_row(UBYTE matrix[MAX_ROW][MAX_COL], UBYTE r0[MAX_COL])
{
    int r,c ;
    int r0Start = 3;
    int r0Pos;
    for (r=0; r< MAX_ROW ; r++, r0Start--)
    {
        for (c=0, r0Pos = r0Start; c< MAX_COL ; c++)
        {
            matrix[r][c] = r0[r0Pos];
            r0Pos ++;
            r0Pos %= MAX_COL;
        }
    }
}

void _MixColumns(UBYTE in[MAX_ROW][MAX_COL],  UBYTE r0[MAX_COL] )
{
    int c;

    UBYTE matrix[MAX_ROW][MAX_COL];
    gen_matrix_from_row(matrix, r0);

    UBYTE outCol[MAX_ROW];
    for (c=0; c< MAX_COL; c++)
    {
        UBYTE clist[MAX_COL];
        copy_to_col_list(in, c, clist);
        multi_matrix(matrix, clist, outCol);
        copy_from_col_list(in, c, outCol);
    }
}
void InvMixColumns(UBYTE in[MAX_ROW][MAX_COL])
{
    UBYTE r0[MAX_COL] = { 0xb, 0xd, 0x9, 0xe}; 
    _MixColumns(in, r0);
 }

void MixColumns(UBYTE in[MAX_ROW][MAX_COL])
{

    UBYTE r0[MAX_COL] = { 0x3, 0x1, 0x1, 0x2}; 
    _MixColumns(in, r0);
}

// w is treated as Big-Endian  
void AddRoundKey(UBYTE in[MAX_ROW][MAX_COL], UWORD w[MAX_COL])
{
    int r, c;
    for (c=0; c< MAX_COL; c++)
    {
        int shiftByte=3;
        UWORD mask = 0xff000000; 
    
        for (r=0 ; r< MAX_ROW ; r++, shiftByte--, mask>>=8)
        {
            in[r][c] = in[r][c] ^ ((UBYTE)((w[c]&mask) >> (shiftByte*8)));
        }
    }
}



UWORD SubWord(UWORD in)
{
    create_sbox();
    UWORD out = 0x00;
    UWORD mask = 0x000000ff; 
    int byte;
    
    for (byte =0 ; byte < MAX_COL ; byte++, mask<<=8)
    {
        out |= ((SBox[(UBYTE)((in & mask)>>(byte*8))] << (byte*8)));
    }
    return out;
}

UWORD RotWord(UWORD in)
{
    UWORD out;
    out = ((in & 0xff000000) >> 24) | (in << 8);
    return out;
}

void show_Rcon(UWORD Rcon[NROUND+2])
{
    int i;
    cout << "Rcon >>=============" << endl;
    for (i=1; i < (NROUND+2) ; i++)
    {
        if (i % 8 == 0)
            cout << endl;
        printf("%08x ", Rcon[i]);
    }
}

void gen_Rcon(UWORD Rcon[NROUND+2])
{
    static bool RconReady = false;
    
    if (RconReady)
        return;
        
    int i;
    UBYTE byte0 = 1;
    Rcon[1] = ((UWORD)byte0 << 24);
    for (i=2; i < (NROUND+2) ; i++)
    {
        byte0 = byte_prod2(byte0);
        Rcon[i] = ((UWORD)byte0 << 24);
    }
    RconReady = true;
    show_Rcon(Rcon);
}


void KeyExpansion(UBYTE key[4*NKEY], UWORD w[NBYTE*(NROUND+1)], int Nk)
{
    UWORD temp;
    int i = 0;
    for (i=0; i < Nk; i++)
    {
        w[i] = ((UWORD)key[4*i] << 24) | ((UWORD)key[4*i+1] << 16) 
                    | ((UWORD)key[4*i+2] << 8) |  (UWORD)key[4*i+3] ;
    }
    i = Nk;
    
    for (i=Nk; i< NBYTE*(NROUND+1) ; i++)
    {
        temp = w[i-1];
        printf("temp = %08x\n", temp);
        if ((i % Nk) == 0)
        {
            printf("RotWord -> %08x\n", RotWord(temp));
            printf("SubWord -> %08x\n", SubWord(RotWord(temp)));
            printf("Rcon[%d] = %08x\n", i/Nk, Rcon[i/Nk]); 
            temp = SubWord(RotWord(temp)) ^ Rcon[i/Nk];
        }
        else
        if ((Nk > 6) && (i % Nk ==4))
        {
            temp = SubWord(temp);
        }
        
        w[i] = w[i-Nk] ^ temp;
        printf("temp %08x XOR w[%d] %08x ==> w[%d] %08x\n", temp, i-Nk, w[i-Nk], i, w[i]);
    }
        
}


void show_state(char *name, UBYTE state[MAX_ROW][MAX_COL])
{
    int r, c;
    printf("[ %s ] >>=============\n", name );
    
    for (r=0; r< MAX_ROW ; r++)
    {
        for (c=0; c < MAX_COL ; c++)
        {
            printf("%02x ", state[r][c]);
        }
        cout << endl;
    }
    printf("[ %s ] <<=============\n", name );
    
}

void show_text(char *name, UBYTE text[], int textSize, bool isString=false)
{
    int pos;
    printf("[ %s ] >>=============\n", name );
    
    for (pos=0; pos< textSize ; pos++)
    {
        if (!isString)
        {
            printf("%02x", text[pos]);       

            if (pos%16==15)
                cout <<endl;
            else
            if (pos%8==7)
                cout << " " ;
        }
        else
            printf("%c", text[pos]);       
    }
    printf("[ %s ] <<=============\n", name );
}


void show_RoundKey(char *name, UWORD w[NBYTE])
{
    int r, c;
    printf("[ %s ] >>=============\n", name );
    UWORD mask = 0xff000000;
    for (r=0; r< MAX_ROW ; r++, mask>>=8)
    {
        for (c=0; c < MAX_COL ; c++)
        {
            printf("%02x ", (UBYTE)((w[c]&mask)>>((3-r)*8)));
        }
        cout << endl;
    }
    printf("[ %s ] <<=============\n", name );
    
}

void Cipher(UBYTE in[MAX_ROW][MAX_COL],  UBYTE out[MAX_ROW][MAX_COL], UWORD w[KEY_CHAIN_CNT])
{
    UBYTE state[MAX_ROW][MAX_COL];
    copy_state(in, state);
    
    printf("round %d >>------------\n", 0);
    show_state("State", state);
    show_RoundKey("RoundKey", &w[0]); 
    AddRoundKey(state, &w[0]);
    
    int round;
    for (round=1; round <=ROUND_CNT-1; round++)
    {
        printf("round %d >>------------\n", round);
        show_state("State", state);
        
        SubBytes(state);
        
        show_state("State", state);
        
        ShiftRows(state);
        
        show_state("State", state);
        
        MixColumns(state);
        
        show_state("State", state);

        show_RoundKey("RoundKey", &w[round*MAX_COL]); 
        AddRoundKey(state, &w[round*MAX_COL]);
        
    }
    printf("round %d >>------------\n", round);
    show_state("State", state);
    
    SubBytes(state); 
    show_state("State", state);
    
    ShiftRows(state);
    show_state("State", state);
    
    show_RoundKey("RoundKey", &w[round*MAX_COL]);  
    AddRoundKey(state, &w[round*MAX_COL]);
   
    copy_state(state, out);
    show_state("Out", out);
}

void InvShiftRows(UBYTE in[MAX_ROW][MAX_COL])
{
    UBYTE val;
    int r, shiftByte ;
    for (r = 0, shiftByte = 0 ; r < MAX_ROW ; r++, shiftByte ++ )
    {
        UWORD val = (in[r][0]<<24) | (in[r][1]<<16) | (in[r][2]<<8) | in[r][3];
        val = (val >> (shiftByte << 3)) |  (val << ((4-shiftByte) << 3));
        int c, shitfBit;
        for (c=0, shitfBit = 24; c< 4; c++, shitfBit-=8)
        {
            in[r][c] = (UBYTE) ((val >> shitfBit) & 0xff);
        }
    }
}

void InvSubBytes(UBYTE in[MAX_ROW][MAX_COL])
{
    create_sbox();
    int r, c;
    
    for (r =0 ; r< MAX_ROW ; r++)
        for (c =0 ; c< MAX_COL ; c++)
        {
            in[r][c] = InvSBox[in[r][c]];
        }
}

void InvCipher(UBYTE in[MAX_ROW][MAX_COL],  UBYTE out[MAX_ROW][MAX_COL], UWORD w[KEY_CHAIN_CNT])
{
    UBYTE state[MAX_ROW][MAX_COL];
    copy_state(in, state);
    
    printf("round %d >>------------\n", 0);
    show_RoundKey("RoundKey", &w[ROUND_CNT*MAX_COL]);  
    AddRoundKey(state, &w[ROUND_CNT*MAX_COL]);
    
    int round;
    for (round=ROUND_CNT-1; round >= 1; round--)
    {
        printf("round %d >>------------\n", round);
        InvShiftRows(state);
        show_state("State", state);
    
        InvSubBytes(state); 
        show_state("State", state);
        
        show_RoundKey("RoundKey", &w[round*MAX_COL]); 
        AddRoundKey(state, &w[round*MAX_COL]);
        
        InvMixColumns(state);
        show_state("State", state);
        

    }

    printf("round %d >>------------\n", 0);
    InvShiftRows(state);
    show_state("State", state);
        
    InvSubBytes(state);
    show_state("State", state);
    
    show_RoundKey("RoundKey", &w[0]); 
    AddRoundKey(state, &w[0]);
    
    copy_state(state, out);
    show_state("Out", out);
}

int parse_HexaDigits(char input[], UBYTE value[])
{
    int i;
    for (i=0; input[i]; i++)
    {
        if (i % 2)
            value[i/2]<<=4;
        else
            value[i/2]=0;
            
        if (input[i]>='a' && input[i]<='f')
        {
            value[i/2] |= input[i]-'a' + 10;
        }
        else
        if (input[i]>='0' && input[i]<='9')
        {
            value[i/2] |= input[i]-'0';
        }
    }
    return (i/2);
}


void get_key()
{ 
    char inputKey[33] = { 0 };
    cout << "AES Key --> " ;
    cin >> inputKey;
    parse_HexaDigits(inputKey, key);
}

int get_input(char *prompt, UBYTE out[])
{ 
    char input[1025] = { 0 }; // plain text or cipher text 
 
    cout << prompt ;
    cin >> input;
    return parse_HexaDigits(input, out);
}

int get_inputInt(char *prompt)
{ 
    int input;
    cout << prompt ;
    cin >> input;
    return input;
}

void get_inputs()
{
    char inputKey[33] = { 0 };
    char inputText[1025] = { 0 }; // plain text or cipher text 
 
    
    cout << "AES Key --> " ;
    cin >> inputKey;
    parse_HexaDigits(inputKey, key);
    
    cout << "Plain Text --> " ;
    cin >> inputText;
    TextSize= parse_HexaDigits(inputText, Text);
   
        
}

void matrix_to_array(UBYTE matrix[MAX_ROW][MAX_COL], UBYTE array[])
{
    int c;
    for (c=0 ;  c < NKEY ; c++)
    {
        copy_to_col_list(matrix, c, &array[4*c]);
    }
}

void matrix_from_array(UBYTE matrix[MAX_ROW][MAX_COL], UBYTE array[], int arrayLen=BLOCK_SIZE)
{
    int r, c, pos=0;

    for (c=0 ;  c < NKEY ; c++)
        for (r=0 ;  r < 4 ; r++)
        {
            if (pos< arrayLen)
                matrix[r][c] = array[pos++];
            else
                matrix[r][c] = 0x0;
        }
}

void get_IV()
{
    UBYTE iv[4*NKEY] = { 0 };
    get_input("CBC IV --> ", iv);
    
    matrix_from_array(IV, iv);
}

void matrix_add(UBYTE in1[MAX_ROW][MAX_COL], UBYTE in2[MAX_ROW][MAX_COL],  UBYTE out[MAX_ROW][MAX_COL])
{
    int r, c;
    for (r=0; r<MAX_ROW ; r++)
        for (c=0;  c< MAX_COL ; c++)
        {
            out[r][c] = in1[r][c] ^ in2[r][c];
        }
}

// PKCS#7 padding using BLOCK SIZE(=16 bytes)
int append_padding(UBYTE text[], int textLen)
{
    int padLen, pos;
    
    padLen = BLOCK_SIZE - textLen % BLOCK_SIZE;
    
    for (pos=0; pos<padLen; pos++)
    {
        text[textLen+pos] = (UBYTE)padLen;
    }
    return padLen;
}


void array_inc(UBYTE array[BLOCK_SIZE], UBYTE val)
{
    int pos;
    for (pos=BLOCK_SIZE-1 ; pos >=0 ; pos--)
    {
        UBYTE org = array[pos];
        array[pos] += val;
        if (array[pos] >= org)
            break;
        val = 1;    
    }
}

int main(int argc, char **argv)
{
    int mode;
    
    mode = get_inputInt("Choose Mode -> 1) AES-CBC-ENC 2) AES-CBC-DEC 3) AES-CTR-ENC 4) AES-CTR-DEC : ");
 
    if (mode == MODE_AES_CBC_ENC )
    {
        UBYTE textState[MAX_ROW][MAX_COL];
        int textLenToEnc;
        
        get_input("AES Key --> ", key);
       
        gen_Rcon(Rcon);
        KeyExpansion(key, KeyChain, NKEY);

        get_IV();
        
      
        TextSize = get_input("Plain Text --> ", Text);
        TextSize += append_padding(Text, TextSize);
        
        matrix_to_array(IV, OutText); // IV is prepended. 
        
        // CBC Encryption 
        int msgPos, c;
        int outPos = BLOCK_SIZE;  // IV size = BLOCK_SIZE
     
        for (msgPos=0, textLenToEnc = TextSize ; textLenToEnc > 0 ;  textLenToEnc -= BLOCK_SIZE, msgPos+=BLOCK_SIZE)
        {
            UBYTE textState[MAX_ROW][MAX_COL];
            UBYTE addVal[MAX_ROW][MAX_COL]; 
            UBYTE added[MAX_ROW][MAX_COL];
                     
            matrix_from_array(textState, &Text[msgPos]);        
            matrix_from_array(addVal, &OutText[outPos-BLOCK_SIZE]);
  
            matrix_add(textState, addVal, added);
            Cipher(added, ResState, KeyChain);
            matrix_to_array(ResState, &OutText[outPos]);
            outPos += BLOCK_SIZE;
        }

        show_text("input", Text, TextSize);
        show_text("output", OutText, outPos);
        return 0;
    }
    if (mode == MODE_AES_CBC_DEC )
    {
     // CBC Decryption 
        UBYTE textState[MAX_ROW][MAX_COL];
        UBYTE *CipherText = Text;
        UBYTE *PlainText = OutText;
        int cipherTextSize;
        int textLenToDec;
        int msgPos, c;
        int outPos = BLOCK_SIZE;  // IV size = BLOCK_SIZE
        
        get_input("AES Key --> ", key);
       
        gen_Rcon(Rcon);
        KeyExpansion(key, KeyChain, NKEY);

        cipherTextSize = get_input("Cipher Text --> ", CipherText);
         
        outPos=0; 
        
        for (msgPos=BLOCK_SIZE, textLenToDec = cipherTextSize-BLOCK_SIZE ; textLenToDec > 0 ;  textLenToDec -= BLOCK_SIZE, msgPos+=BLOCK_SIZE)
        {
            UBYTE addVal[MAX_ROW][MAX_COL]; 
            UBYTE added[MAX_ROW][MAX_COL];
                
            matrix_from_array(textState, &CipherText[msgPos]);  
            InvCipher(textState, ResState, KeyChain);
            matrix_from_array(addVal, &CipherText[msgPos-BLOCK_SIZE]);
                
            matrix_add(ResState, addVal, added);
               
            matrix_to_array(added, &PlainText[outPos]);
            outPos += BLOCK_SIZE;  
        }  
                

        PlainTextSize = outPos - PlainText[outPos-1];
        show_text("CipherText", CipherText, cipherTextSize);
        show_text("PlainText", PlainText, PlainTextSize);
        show_text("PlainText", PlainText, PlainTextSize, true);
        return 0;
    }
    
    if (mode == MODE_AES_CTR_ENC )
    {
        UBYTE textState[MAX_ROW][MAX_COL];
        UBYTE ctrArray[BLOCK_SIZE] = { 0 };
        int textLenToEnc;
        int msgPos;
        int outPos ;
        
        get_input("AES Key --> ", key);
       
        gen_Rcon(Rcon);
        KeyExpansion(key, KeyChain, NKEY);

 
        get_IV(); // init CTR 
        matrix_to_array(IV, ctrArray);  
        
        TextSize = get_input("Plain Text --> ", Text);
        
        
        matrix_to_array(IV, OutText); // IV is prepended. 
        
        // CTR Encryption 
        outPos = BLOCK_SIZE;  // IV size = BLOCK_SIZE
        
        for (msgPos=0, textLenToEnc = TextSize ; textLenToEnc > 0 ;  textLenToEnc -= BLOCK_SIZE, msgPos+=BLOCK_SIZE)
        {
            UBYTE ctrState[MAX_ROW][MAX_COL];
            UBYTE added[MAX_ROW][MAX_COL];
                     
            if (textLenToEnc < BLOCK_SIZE)
            {
                matrix_from_array(textState, &Text[msgPos], textLenToEnc);
            }
            else
                matrix_from_array(textState, &Text[msgPos]);        

            matrix_from_array(ctrState, ctrArray);

            Cipher(ctrState, ResState, KeyChain);
            matrix_add(textState, ResState, added);
            matrix_to_array(added, &OutText[outPos]);
         
            if (textLenToEnc >= BLOCK_SIZE)
            {
                array_inc(ctrArray, 1);
                outPos += BLOCK_SIZE;
            }
            else
            {
                outPos += textLenToEnc;
                textLenToEnc = 0;
                break;
            }
           
        }

        show_text("input", Text, TextSize);
        show_text("output", OutText, outPos);
        return 0;
    }
    if (mode == MODE_AES_CTR_DEC )
    {
        UBYTE *CipherText = Text;
        UBYTE *PlainText = OutText;
        UBYTE textState[MAX_ROW][MAX_COL];
        UBYTE ctrArray[BLOCK_SIZE] = { 0 };
        int cipherTextSize;
        int textLenToDec;
        int msgPos;
        int outPos;         
        
        get_input("AES Key --> ", key);
       
        gen_Rcon(Rcon);
        KeyExpansion(key, KeyChain, NKEY);

        cipherTextSize = get_input("Cipher Text --> ", CipherText);
        copy_array(CipherText, ctrArray); // IV(=CTR0) is prepended in ciphertext.  

        // CTR Decryption 

        outPos=0; 
        
        for (msgPos=BLOCK_SIZE, textLenToDec = cipherTextSize-BLOCK_SIZE ; textLenToDec > 0 ;  textLenToDec -= BLOCK_SIZE, msgPos+=BLOCK_SIZE)
        {
            UBYTE ctrState[MAX_ROW][MAX_COL];
            UBYTE added[MAX_ROW][MAX_COL];
            
            if (textLenToDec < BLOCK_SIZE)
            {
                matrix_from_array(textState, &CipherText[msgPos], textLenToDec);
            }
            else
                matrix_from_array(textState, &CipherText[msgPos]);        
    
            matrix_from_array(ctrState, ctrArray);

            Cipher(ctrState, ResState, KeyChain);
            matrix_add(textState, ResState, added);
            matrix_to_array(added, &PlainText[outPos]);
            
            if (textLenToDec >= BLOCK_SIZE)
            {
                array_inc(ctrArray, 1);
                outPos += BLOCK_SIZE;
            }
            else
            {
                outPos += textLenToDec;
                textLenToDec = 0;
                break;
            }
        }
  
        PlainTextSize = outPos;
        show_text("CipherText", CipherText, cipherTextSize);
        show_text("PlainText", PlainText, PlainTextSize);
        show_text("PlainText", PlainText, PlainTextSize, true);
     
    }
	return 0;
}
