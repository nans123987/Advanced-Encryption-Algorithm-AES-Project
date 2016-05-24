#!/usr/bin/python2.5
# Copyright (c) 2007 Brandon Sterne
# Licensed under the MIT license.
# http://brandon.sternefamily.net/files/mit-license.txt
# Python AES implementation

#THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
#OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
#THE SOFTWARE.

# Modified by 
# author: Nandan Thareja
#         James Lunsford
#

import sys, hashlib, string, getpass
from copy import copy
from random import randint

# The actual Rijndael specification includes variable block size, but
# AES uses a fixed block size of 16 bytes (128 bits)

# Additionally, AES allows for a variable key size, though this implementation
# of AES uses only 256-bit cipher keys (AES-256)

sbox = [
        0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
        0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
        0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
        0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
        0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
        0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
        0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
        0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
        0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
        0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
        0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
        0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
        0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
        0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
        0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
        0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
        ]

sboxInv = [
        0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
        0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
        0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
        0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
        0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
        0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
        0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
        0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
        0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
        0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
        0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
        0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
        0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
        0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
        0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
        0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d
        ]

rcon = [
        0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a,
        0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39,
        0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a,
        0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8,
        0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef,
        0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc,
        0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b,
        0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3,
        0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94,
        0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20,
        0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35,
        0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f,
        0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04,
        0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63,
        0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd,
        0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb
        ]




#Determining Subbytes using S-Box Substitution Method
def StateSubBytes(RoundState):
    temp = 0
    while temp < len(RoundState):
        RoundState[temp] = sbox[RoundState[temp]]
        temp = temp + 1
          

#perform Shiftrows operation on the ROUndState
def ShiftRowsOperation(RoundState):
    for temp in range(4):
        RoundState[temp*4:temp*4+4] = RotWordOperation(RoundState[temp*4:temp*4+4],temp)
    
    
#Peforms MixCOlumn operation on a state
def StateMixColumnOperartion(RoundState):
    for colElement in range(4):
        column = []
        for i in range(4):
            column.append(RoundState[i*4+colElement])
        temp = copy(column)
        column[0] = gmul(temp[0],2) ^ gmul(temp[3],1) ^ \
                    gmul(temp[2],1) ^ gmul(temp[1],3)
        column[1] = gmul(temp[1],2) ^ gmul(temp[0],1) ^ \
                    gmul(temp[3],1) ^ gmul(temp[2],3)
        column[2] = gmul(temp[2],2) ^ gmul(temp[1],1) ^ \
                    gmul(temp[0],1) ^ gmul(temp[3],3)
        column[3] = gmul(temp[3],2) ^ gmul(temp[2],1) ^ \
                    gmul(temp[1],1) ^ gmul(temp[0],3)

        for i in range(4):
            RoundState[i*4+colElement] = column[i]
    
#Individual AES Round which performs Subbytes, Shiftrows, and Mixcolumns
def Round(RoundState, RoundKey):
    #perform Sub-bytes operation in a round
    StateSubBytes(RoundState)
    #performs shiftRows Operation in a ROund
    ShiftRowsOperation(RoundState)
    #performs MixCOlum operation
    StateMixColumnOperartion(RoundState)
    #add round key before next round
    AddingRoundKeyToState(RoundState, RoundKey)

# performs galois multiplication
def gmul(a, b):
    p = 0
    counter = 0
    hi_bit_set = 0;
    temp = 0
    while temp < 8:
        if b & 1 == 1:
            p ^= a
        hi_bit_set = a & 0x80
        a <<= 1
        if hi_bit_set == 0x80:
            a ^= 0x1b
        b >>= 1
        temp  = temp + 1
    
    return p % 256
#Adding round key to the round state by XOR of round state with key 
def AddingRoundKeyToState(RoundState, RoundKey):
    for temp in range(len(RoundState)):
        RoundState[temp] = RoundState[temp] ^ RoundKey[temp] 
        
# extracts 16 bytes from the 240 byte expanded key consecutively for every round
def produceIndividualRoundKey(KeyExpandedIn240Bytes, RoundNumber): 
    return KeyExpandedIn240Bytes[(RoundNumber*16):(RoundNumber*16+16)]

#Rijndael's key schedule

#key expansion - expanding 32byte key to 240 byte key.

def keyExpansion(aesPasswordToKey):
    keySize = len(aesPasswordToKey)
    rconIterationVal = 1
    
    expandedKeyLength = 0
    
    KeyExpandedIn240Bytes = []
    #The first 32 bytes of the expanded key are simply the encryption key.
    #copy the first 32 bytes of the AES key in KeyExpandedIn240Bytes
    for temp in range(keySize):
        KeyExpandedIn240Bytes.append(aesPasswordToKey[temp])
    expandedKeyLength = expandedKeyLength + keySize
         
    #create a 4-byte temporary variable, t
    t = [0,0,0,0]
    j = 0
    
    assert keySize == 32        
    while expandedKeyLength < 240:
        
        #copy the last 4 bytes in AES password to key converted in t temporary variable.
        for temp in range(4):
            t[temp] = KeyExpandedIn240Bytes[(expandedKeyLength - 4)+temp]
         
        #perform schedule_core (see above) on t, with i as the rcon iteration value.
        if expandedKeyLength % keySize == 0:
            #Rijndael's key schedule
            outputWord = []
             #copy input word to the output word
            tempOutputWord = t
            # rotate the output eight bits to the left
            tempOutputWord = tempOutputWord[1:] + tempOutputWord[0:1]
            #Apply Rijndael's S-box on all four individual bytes in the output word.
            for tempBytes in tempOutputWord:
                outputWord.append(sbox[tempBytes])
            outputWord[0] = outputWord[0]^rcon[rconIterationVal]
            t= outputWord
            rconIterationVal = rconIterationVal + 1
            
        if expandedKeyLength % keySize == 16:
            for i in range(4):
                t[i] = sbox[t[i]]
                
        for i in range(4):
            KeyExpandedIn240Bytes.append(((KeyExpandedIn240Bytes[expandedKeyLength - keySize]) ^ (t[i])))
            expandedKeyLength += 1      
    
        
    return KeyExpandedIn240Bytes    
     
# performs left shift operation by shiftCount in a 4 byte word tWord
def RotWordOperation(tWord, shiftCount):
    return tWord[shiftCount:]+tWord[0:shiftCount]
        
#Executes 14 rounds for encryption using 256 bit Key
def AES(RoundState, KeyExpandedIn240Bytes):  
    numberOfRounds = 14  
    RoundKey = produceIndividualRoundKey(KeyExpandedIn240Bytes, 0)
    AddingRoundKeyToState(RoundState,RoundKey)
    #executing operations of subBytes, ShiftRows and MixColumns for n-1 rounds
    J = 1;
    while J < numberOfRounds:
        RoundKey = produceIndividualRoundKey(KeyExpandedIn240Bytes,J)
        Round(RoundState,RoundKey)
        J = J + 1    
    RoundKey = produceIndividualRoundKey(KeyExpandedIn240Bytes, numberOfRounds)
    StateSubBytes(RoundState)
    ShiftRowsOperation(RoundState)
    AddingRoundKeyToState(RoundState, RoundKey)
    
# create a key from a user-supplied password using SHA-256
def passwordToKey(password):
    sha256 = hashlib.sha256()
    sha256.update(password)
    key = []
    for c in list(sha256.digest()):
        key.append(ord(c))
    return key
   
# aesEncrypt - encrypt a single block of plaintext
def aesEncrypt(plaintext, key):
    block = copy(plaintext)
    KeyExpandedIn240Bytes = keyExpansion(key)
    AES(block, KeyExpandedIn240Bytes)
    return block

# aesDecrypt - decrypt a single block of ciphertext
def aesDecrypt(ciphertext, key):
    block = copy(ciphertext)
    return block

# return 16-byte block from an open file
# pad to 16 bytes with null chars if needed
def getBlock(fp):
    raw = fp.read(16)
    # reached end of file
    if len(raw) == 0:
        return ""
    # container for list of bytes
    block = []
    for c in list(raw):
        block.append(ord(c))
    # if the block is less than 16 bytes, pad the block
    # with the string representing the number of missing bytes
    if len(block) < 16:
        padChar = 16-len(block)
        while len(block) < 16:
            block.append(padChar)
    return block

# encrypt - wrapper function to allow encryption of arbitray length
# plaintext using Output Feedback (OFB) mode
def encrypt(myInput, password, outputfile=None):
    block = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] # plaintext
    ciphertext = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] # ciphertext
    # Initialization Vector
    IV = []
    for i in range(16):
        IV.append(randint(0, 255))

    # convert password to AES 256-bit key
    aesKey = passwordToKey(password)

    # create handle for file to be encrypted
    try:
        fp = open(myInput, "rb")
    except:
        print "pyAES: unable to open input file -", myInput
        sys.exit()

    # create handle for encrypted output file
    if outputfile is not None:
        try:
            outfile = open(outputfile,"w")
        except:
            print "pyAES: unable to open output file -", outputfile
            sys.exit()
    else:
        filename = myInput+".aes"
        try:
            outfile = open(filename,"w")
        except:
            print "pyAES: unable to open output file -", filename
            sys.exit()

    # write IV to outfile
    for byte in IV:
        outfile.write(chr(byte))

    # get the file size (bytes) 
    # if the file size is a multiple of the block size, we'll need 
    # to add a block of padding at the end of the message
    fp.seek(0,2)
    filesize = fp.tell()
    # put the file pointer back at the beginning of the file
    fp.seek(0)

    # begin reading in blocks of input to encrypt
    firstRound = True
    block = getBlock(fp)
    while block != "":
        if firstRound:
            blockKey = aesEncrypt(IV, aesKey)
            firstRound = False
        else:
            blockKey = aesEncrypt(blockKey, aesKey)

        for i in range(16):
            ciphertext[i] = block[i] ^ blockKey[i]

        # write ciphertext to outfile
        for c in ciphertext:
            outfile.write(chr(c))

        # grab next block from input file
        block = getBlock(fp)
    # if the message ends on a block boundary, we need to add an
    # extra block of padding
    if filesize % 16 == 0:
        outfile.write(16*chr(16))
    # close file pointers
    fp.close()
    outfile.close()

# decrypt - wrapper function to allow decryption of arbitray length
# ciphertext using Output Feedback (OFB) mode
def decrypt(myInput, password, outputfile=None):
    block = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] # ciphertext
    plaintext = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] # plaintext container

    # convert password to AES 256-bit key
    aesKey = passwordToKey(password)

    # create handle for file to be encrypted
    try:
        fp = open(myInput, "rb")
    except:
        print "pyAES: unable to open input file -", myInput
        sys.exit()

    # create handle for file to be decrypted
    try:
        fp = open(myInput, "rb")
    except:
        print "pyAES: unable to open input file -", myInput
        sys.exit()

    # create handle for decrypted output file
    if outputfile is not None:
        try:
            outfile = open(outputfile,"w")
        except:
            print "pyAES: unable to open output file -", filename
            sys.exit()
    else:
        if myInput[-4:] == ".aes":
            filename = myInput[:-4]
            print "Using", filename, "for output file name."
        else:
            filename = raw_input("output file name: ")
        try:
            outfile = open(filename,"w")
        except:
            print "pyAES: unable to open output file -", filename
            sys.exit()

    # recover Initialization Vector, the first block in file
    IV = getBlock(fp)

    # get the file size (bytes) in order to handle the
    # padding at the end of the file
    fp.seek(0,2)
    filesize = fp.tell()
    # put the file pointer back at the first block of ciphertext
    fp.seek(16)

    # begin reading in blocks of input to decrypt
    firstRound = True
    block = getBlock(fp)
    while block != "":
        if firstRound:
            blockKey = aesEncrypt(IV, aesKey)
            firstRound = False
        else:
            blockKey = aesEncrypt(blockKey, aesKey)

        for i in range(16):
            plaintext[i] = block[i] ^ blockKey[i]

        # if we're in the last block of text -> throw out the
        # number of bytes represented by the last byte in the block
        if fp.tell() == filesize:
            plaintext = plaintext[0:-(plaintext[-1])]

        # write ciphertext to outfile
        for c in plaintext:
            outfile.write(chr(c))

        # grab next block from input file
        block = getBlock(fp)
    # close file pointers
    fp.close()
    outfile.close()

def printUsage():
    print "./pyAES.py [-e <input file> | -d <input file>] [(optional) -o <output file>]"
    print "You will be prompted for a password after you specify the encryption/decryption args.\n"
    sys.exit()

# gather command line arguments and validate input
def main():
    # containers for command line arguments
    inputfile = None
    outputfile = None

    for a in range(len(sys.argv)):
        if sys.argv[a] == "-e":
            try:
                inputfile = sys.argv[a+1]
            except:
                inputfile = raw_input("File to encrypt: ")
        elif sys.argv[a] == "-d":
            try:
                inputfile = sys.argv[a+1]
            except:
                inputfile = raw_input("File to decrypt: ")
        if sys.argv[a] == "-o":
            try:
                outputfile = sys.argv[a+1]
            except:
                pass
    # print help message
    if ("-h" in sys.argv) or ("--help" in sys.argv):
        printUsage()
    if inputfile is None:
        print "Error: please specify options for encryption or decryption."
        printUsage()
    # encrypt file per user instructions
    if "-e" in sys.argv:
        password = getpass.getpass("Password: ")
        print "Encrypting file:", inputfile
        if outputfile is not None:
            encrypt(inputfile, password, outputfile)
        else:
            encrypt(inputfile, password)
        print "Encryption complete."
    # decrypt file per user instructions
    elif "-d" in sys.argv:
        password = getpass.getpass("Password: ")
        print "Decrypting file:", inputfile
        if outputfile is not None:
            decrypt(inputfile, password, outputfile)
        else:
            decrypt(inputfile, password)
        print "Decryption complete."

if __name__ == "__main__":
    main()
