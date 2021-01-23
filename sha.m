/*
* DESCRIPTION: Magma implementation of SHA256 algorithm.
* AUTHOR: Emanuele Bellini 04052017
* REF: FIPS PUB 180-4
* LINKS: http://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
*/

// ---------------------------------------------------------------------------

h2b := function(h)
  // hex string to binary sequence
  // h must be a string of hex characters
  local b;
  
  b := [];
  for i in [1..#h] do
    if not h[i] in "0123456789abcdefABCDEF" then
      h[i];
      print "Error! Input string contains non-hexadecimal chatacters!";
      return [];
    else
      case h[i]:
        when "0": b := b cat [0,0,0,0];
        when "1": b := b cat [0,0,0,1];
        when "2": b := b cat [0,0,1,0];
        when "3": b := b cat [0,0,1,1];
        when "4": b := b cat [0,1,0,0];
        when "5": b := b cat [0,1,0,1];
        when "6": b := b cat [0,1,1,0];
        when "7": b := b cat [0,1,1,1];
        when "8": b := b cat [1,0,0,0];
        when "9": b := b cat [1,0,0,1];
        when "a": b := b cat [1,0,1,0];
        when "b": b := b cat [1,0,1,1];
        when "c": b := b cat [1,1,0,0];
        when "d": b := b cat [1,1,0,1];
        when "e": b := b cat [1,1,1,0];
        when "f": b := b cat [1,1,1,1];
        when "A": b := b cat [1,0,1,0];
        when "B": b := b cat [1,0,1,1];
        when "C": b := b cat [1,1,0,0];
        when "D": b := b cat [1,1,0,1];
        when "E": b := b cat [1,1,1,0];
        when "F": b := b cat [1,1,1,1];
      end case;
    end if; 
  end for;

  return b;
end function;

// ---------------------------------------------------------------------------

b2h := function(b);
  h := IntegerToString(SequenceToInteger(Reverse(b),2),16);
  tmp := #b/4-#h;
  for i in [1..tmp] do
    h := "0" cat h ;
  end for;

  return h;
end function;

// ---------------------------------------------------------------------------

i2b := function(i, l)
// integer to binary function
// must specify binary sequence length
  if i eq 0 then
    b := [0 : j in [1..l]];
  else
    b := [0 : j in [1..l-(Floor(Log(2,i))+1)]] cat 
         Reverse(IntegerToSequence(i,2));
  end if;

  return b;
end function;

// ---------------------------------------------------------------------------

b2i := function(b)
// from binary sequence to integer
  i := SequenceToInteger(Reverse(b),2); 

  return i;
end function;

// ---------------------------------------------------------------------------

K1 := function(t)
  local K;

  if t ge 0 and t le 19 then
    return 0x5a827999;
  elif t ge 20 and t le 39 then
    return 0x6ed9eba1;
  elif t ge 40 and t le 59 then
    return 0x8f1bbcdc;
  elif t ge 60 and t le 79 then
    return 0xca62c1d6;
  else 
    print "Error! Invalid parameter t, must be such that 0 <= t <= 79!";
    return [];
  end if;
end function;

// ---------------------------------------------------------------------------

K256 := function(i)
  local K;
  K := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2

//   "428a2f98","71374491","b5c0fbcf","e9b5dba5","3956c25b","59f111f1","923f82a4","ab1c5ed5",
//   "d807aa98","12835b01","243185be","550c7dc3","72be5d74","80deb1fe","9bdc06a7","c19bf174",
//   "e49b69c1","efbe4786","0fc19dc6","240ca1cc","2de92c6f","4a7484aa","5cb0a9dc","76f988da",
//   "983e5152","a831c66d","b00327c8","bf597fc7","c6e00bf3","d5a79147","06ca6351","14292967",
//   "27b70a85","2e1b2138","4d2c6dfc","53380d13","650a7354","766a0abb","81c2c92e","92722c85",
//   "a2bfe8a1","a81a664b","c24b8b70","c76c51a3","d192e819","d6990624","f40e3585","106aa070",
//   "19a4c116","1e376c08","2748774c","34b0bcb5","391c0cb3","4ed8aa4a","5b9cca4f","682e6ff3",
//   "748f82ee","78a5636f","84c87814","8cc70208","90befffa","a4506ceb","bef9a3f7","c67178f2"
  ];
  return K[i+1];
end function;

// ---------------------------------------------------------------------------

K512 := function(i)
  local K;
  K := [
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817

//  "428a2f98d728ae22","7137449123ef65cd","b5c0fbcfec4d3b2f","e9b5dba58189dbbc",
//  "3956c25bf348b538","59f111f1b605d019","923f82a4af194f9b","ab1c5ed5da6d8118",
//  "d807aa98a3030242","12835b0145706fbe","243185be4ee4b28c","550c7dc3d5ffb4e2",
//  "72be5d74f27b896f","80deb1fe3b1696b1","9bdc06a725c71235","c19bf174cf692694",
//  "e49b69c19ef14ad2","efbe4786384f25e3","0fc19dc68b8cd5b5","240ca1cc77ac9c65",
//  "2de92c6f592b0275","4a7484aa6ea6e483","5cb0a9dcbd41fbd4","76f988da831153b5",
//  "983e5152ee66dfab","a831c66d2db43210","b00327c898fb213f","bf597fc7beef0ee4",
//  "c6e00bf33da88fc2","d5a79147930aa725","06ca6351e003826f","142929670a0e6e70",
//  "27b70a8546d22ffc","2e1b21385c26c926","4d2c6dfc5ac42aed","53380d139d95b3df",
//  "650a73548baf63de","766a0abb3c77b2a8","81c2c92e47edaee6","92722c851482353b",
//  "a2bfe8a14cf10364","a81a664bbc423001","c24b8b70d0f89791","c76c51a30654be30",
//  "d192e819d6ef5218","d69906245565a910","f40e35855771202a","106aa07032bbd1b8",
//  "19a4c116b8d2d0c8","1e376c085141ab53","2748774cdf8eeb99","34b0bcb5e19b48a8",
//  "391c0cb3c5c95a63","4ed8aa4ae3418acb","5b9cca4f7763e373","682e6ff3d6b2b8a3",
//  "748f82ee5defb2fc","78a5636f43172f60","84c87814a1f0ab72","8cc702081a6439ec",
//  "90befffa23631e28","a4506cebde82bde9","bef9a3f7b2c67915","c67178f2e372532b",
//  "ca273eceea26619c","d186b8c721c0c207","eada7dd6cde0eb1e","f57d4f7fee6ed178",
//  "06f067aa72176fba","0a637dc5a2c898a6","113f9804bef90dae","1b710b35131c471b",
//  "28db77f523047d84","32caab7b40c72493","3c9ebe0a15c9bebc","431d67c49c100d4c",
//  "4cc5d4becb3e42b6","597f299cfc657e2a","5fcb6fab3ad6faec","6c44198c4a475817"
  ];
  return K[i+1];
end function;

// ---------------------------------------------------------------------------

SHR := function(x,n)
// right shift
  tmp := Rotate(x,n);
  for i in [1..Min(#x,n)] do
    tmp[i] := 0;
  end for;

  return tmp;
end function;

// ---------------------------------------------------------------------------

ROTL := function(x,n)
  return Rotate(x,#x-n);
end function;

// ---------------------------------------------------------------------------

ROTR := function(x,n)
  return Rotate(x,n);
end function;

// ---------------------------------------------------------------------------

NOT := function(x)
  r := [];

  for i in x do
    if i eq 1 then
      Append(~r,0);
    elif i eq 0 then
      Append(~r,1);
    else
      print "Error! Input must be a binary string!";
      return [];
    end if;
  end for;

  return r;
end function;

// ---------------------------------------------------------------------------

XOR := function(x,y)
  z := [];
  for i in [1..#x] do
    Append(~z, x[i]+y[i] - 2*x[i]*y[i] );
  end for;

  return z;
end function;

// ---------------------------------------------------------------------------

AND := function(x,y)
  z := [];
  for i in [1..#x] do
    Append(~z, x[i]*y[i] );
  end for;

  return z;
end function;

// ---------------------------------------------------------------------------

Ch := function(x,y,z)
  return XOR(AND(x,y),AND(NOT(x),z));
end function;

// ---------------------------------------------------------------------------

Maj := function(x,y,z);
  return XOR(XOR(AND(x,y),AND(x,z)),AND(y,z));
end function;

// ---------------------------------------------------------------------------

Parity := function(x,y,z);
  return XOR(XOR(x,y),z);
end function;

// ---------------------------------------------------------------------------

ff := function(t, x, y, z)
  if t ge 0 and t le 19 then
    return Ch(x,y,z);
  elif t ge 20 and t le 39 then
    return Parity(x,y,z);
  elif t ge 40 and t le 59 then
    return Maj(x,y,z);
  elif t ge 60 and t le 79 then
    return Parity(x,y,z);
  else 
    print "Error! Invalid parameter t, must be such that 0 <= t <= 79!";
    return [];
  end if;
end function;

// ---------------------------------------------------------------------------

SIGMA_0_256 := function(x)
  return XOR(XOR(ROTR(x,2),ROTR(x,13)),ROTR(x,22));
end function;

// ---------------------------------------------------------------------------

SIGMA_1_256 := function(x)
    return XOR(XOR(ROTR(x,6),ROTR(x,11)),ROTR(x,25));
end function;


// ---------------------------------------------------------------------------

SIGMA_0_512 := function(x)
    return XOR(XOR(ROTR(x,28),ROTR(x,34)),ROTR(x,39));
end function;

// ---------------------------------------------------------------------------

SIGMA_1_512 := function(x)
    return XOR(XOR(ROTR(x,14),ROTR(x,18)),ROTR(x,41));
end function;

// ---------------------------------------------------------------------------

sigma_0_256 := function(x)
    return XOR(XOR(ROTR(x,7),ROTR(x,18)),SHR(x,3));
end function;

// ---------------------------------------------------------------------------

sigma_1_256 := function(x)
    return XOR(XOR(ROTR(x,17),ROTR(x,19)),SHR(x,10));
end function;


// ---------------------------------------------------------------------------

sigma_0_512 := function(x)
    return XOR(XOR(ROTR(x,1),ROTR(x,8)),SHR(x,7));
end function;

// ---------------------------------------------------------------------------

sigma_1_512 := function(x)
    return XOR(XOR(ROTR(x,19),ROTR(x,61)),SHR(x,6));
end function;

// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------

Sha := function(msg, type : MsgType:="ascii")
// Computes SHA-1, SHA-224, SHA-256, SHA-384, SHA-512
// of either an ASCII string or an HEX string (varible msg).
// The variable type can be 1, 224, 256, 384, 512. 
// Implementation of 256/t and 512/t is missing... 
// MsgType can be "ascii" or "hex", and msg must be a string.
//
// Example:
// > SHA("ciao",1:MsgType:="ascii");  
// 1E4E888AC66F8DD41E00C5A7AC36A32A9950D271
// > SHA("ae1234",224:MsgType:="hex");
// 4D45098880E700BCD5633D3EA3D08E4FD50CBE92A4659AE3E120889F
// > SHA("abc",256:MsgType:="ascii"); 
// BA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD


  local digest, H, Mbit, l, k, fp, bs, ws, M, W, temp;
  local a,b,c,d,e,f,g,h,T,T1,T2;

  // PRE-PROCESSING

  // STEP 1 - padding message
  if MsgType eq "ascii" then
    // make the string a bit sequence 
    Mbit := [] ;
    for i in [1..#msg] do
      Mbit := Mbit cat [0] cat Reverse(IntegerToSequence(StringToCode(msg[i]),2));
    end for;
  elif MsgType eq "hex" then
    Mbit := h2b(msg);
  else
    print "Error! Message type is not valid!";
    return 0;
  end if;

  l := #Mbit;
  fp :=  Reverse(IntegerToSequence(l,2)); // final pad
  k := -1;

  if type in {1, 224, 256} then
    repeat
      k := k + 1;
    until ((l+1+k) mod 512) eq 448;
    fp := [0 : i in [1..64-#fp]] cat fp;
    bs := 512 ; // block size in bits
    ws := 32;  // word size in bits
  elif type in {384,512} then
    repeat
      k := k + 1;
//      print "**";
    until ((l+1+k) mod 1024) eq 896;
    fp := [0 : i in [1..128-#fp]] cat fp;
    bs := 1024 ; // block size in bits
    ws := 64;  // word size in bits
  else
    print "Error! Unknown SHA type!";
    return "";
  end if;

  Mbit := Mbit cat [1] cat [0 : i in [1..k]] cat fp;

  // STEP 1 - parse message into message blocks
  N := #Mbit div bs;
  M := [];
  for i in [1..N] do
    M[i] := Mbit[1+bs*(i-1)..bs+bs*(i-1)];
  end for;  

  // STEP 3 - set initial hash value
  H := [];
  case type:
    when 1:
      H[1] := 0x67452301;
      H[2] := 0xefcdab89;
      H[3] := 0x98badcfe;
      H[4] := 0x10325476;
      H[5] := 0xc3d2e1f0;
    when 224:
      H[1] := 0xc1059ed8;
      H[2] := 0x367cd507;
      H[3] := 0x3070dd17;
      H[4] := 0xf70e5939;
      H[5] := 0xffc00b31;
      H[6] := 0x68581511;
      H[7] := 0x64f98fa7;
      H[8] := 0xbefa4fa4;
    when 256:
      H[1] := 0x6a09e667;
      H[2] := 0xbb67ae85;
      H[3] := 0x3c6ef372;
      H[4] := 0xa54ff53a;
      H[5] := 0x510e527f;
      H[6] := 0x9b05688c;
      H[7] := 0x1f83d9ab;
      H[8] := 0x5be0cd19;
    when 384:
      H[1] := 0xcbbb9d5dc1059ed8;
      H[2] := 0x629a292a367cd507;
      H[3] := 0x9159015a3070dd17;
      H[4] := 0x152fecd8f70e5939;
      H[5] := 0x67332667ffc00b31;
      H[6] := 0x8eb44a8768581511;
      H[7] := 0xdb0c2e0d64f98fa7;
      H[8] := 0x47b5481dbefa4fa4;
    when 512:
      H[1] := 0x6a09e667f3bcc908;
      H[2] := 0xbb67ae8584caa73b;
      H[3] := 0x3c6ef372fe94f82b;
      H[4] := 0xa54ff53a5f1d36f1;
      H[5] := 0x510e527fade682d1;
      H[6] := 0x9b05688c2b3e6c1f;
      H[7] := 0x1f83d9abfb41bd6b;
      H[8] := 0x5be0cd19137e2179;
  end case;

  // HASH COMPUTATION
  for i in [1..N] do
    if type eq 1 then
    // ---------------------------------------------------------------------//
    // ---------------------------- SHA 1 COMPUTATION ----------------------//
    // ---------------------------------------------------------------------//
      // step 1 - prepare message schedule
      W := [];
      for t in [0..15] do
        Append(~W,M[i][1+t*ws..ws+t*ws]);
      end for;
      for t in [16..79] do
        temp := b2i(
                  ROTL(
                    XOR(W[t -3+1],XOR(W[t -8+1],XOR(W[t-14+1],W[t-16+1])))
                  ,1));
        Append(~W, i2b(temp,ws));
      end for;
      
      // step 2 - initialize a,b,c,d,e,f,g,h
      a := H[1]; 
      b := H[2];
      c := H[3];
      d := H[4];
      e := H[5];

      // step 3
      for t in [0..79] do
        T := (  b2i(ROTL(i2b(a,ws),5)) + 
                b2i( ff(t,i2b(b,ws), i2b(c,ws), i2b(d,ws)) )+ 
                e +
                K1(t) + 
                b2i( W[t+1] ) 
              ) mod 2^ws;
        e := d;
        d := c;
        c := b2i(ROTL(i2b(b,ws),30));
        b := a;
        a := T;
      end for;

      // compute the ith intermediate hash value
      H[1] := (a + H[1]) mod 2^ws;
      H[2] := (b + H[2]) mod 2^ws;
      H[3] := (c + H[3]) mod 2^ws;
      H[4] := (d + H[4]) mod 2^ws;
      H[5] := (e + H[5]) mod 2^ws;

    elif type eq 224 or type eq 256 then
    // ---------------------------------------------------------------------//
    // ---------------------- SHA 224 - SHA 256 COMPUTATION ----------------//
    // ---------------------------------------------------------------------//
      // step 1 - prepare message schedule
      W := [];
      for t in [0..15] do
        Append(~W,M[i][1+t*ws..ws+t*ws]);
      end for;
      for t in [16..79] do
        //temp := sigma_1_512(W[t-2+1]) + W[t-7+1] + sigma_0_512(W[t-15+1]) + W[t-16+1];
        temp := ( b2i(sigma_1_256(W[t-2+1]))  + 
                  b2i(W[t-7+1])               + 
                  b2i(sigma_0_256(W[t-15+1])) + 
                  b2i(W[t-16+1])
                ) mod 2^ws;
        Append(~W, i2b(temp,ws));
      end for;
      
      // step 2 - initialize a,b,c,d,e,f,g,h
      a := H[1]; 
      b := H[2];
      c := H[3];
      d := H[4];
      e := H[5];
      f := H[6];
      g := H[7];
      h := H[8];

      // step 3
      for t in [0..63] do
        T1 := ( h + 
                b2i( SIGMA_1_256(i2b(e,ws)) ) + 
                b2i( Ch(i2b(e,ws), i2b(f,ws), i2b(g,ws)) )+ 
                K256(t) + 
                b2i( W[t+1] ) 
              ) mod 2^ws;
        T2 := ( b2i(SIGMA_0_256(i2b(a,ws))) + 
                b2i(Maj(i2b(a,ws),i2b(b,ws),i2b(c,ws)))
              ) mod 2^ws;
        h := g;
        g := f;
        f := e;
        e := (d + T1) mod 2^ws;
        d := c;
        c := b;
        b := a;
        a := (T1 + T2) mod 2^ws;

      end for;

      // compute the ith intermediate hash value
      H[1] := (a + H[1]) mod 2^ws;
      H[2] := (b + H[2]) mod 2^ws;
      H[3] := (c + H[3]) mod 2^ws;
      H[4] := (d + H[4]) mod 2^ws;
      H[5] := (e + H[5]) mod 2^ws;
      H[6] := (f + H[6]) mod 2^ws;
      H[7] := (g + H[7]) mod 2^ws;
      H[8] := (h + H[8]) mod 2^ws;

    elif type eq 384 or type eq 512 then
    // ---------------------------------------------------------------------//
    // ---------------------- SHA 384 - SHA 512 COMPUTATION ----------------//
    // ---------------------------------------------------------------------//
      // step 1 - prepare message schedule
      W := [];
      for t in [0..15] do
        Append(~W,M[i][1+t*ws..ws+t*ws]);
      end for;
      for t in [16..79] do
        //temp := sigma_1_512(W[t-2+1]) + W[t-7+1] + sigma_0_512(W[t-15+1]) + W[t-16+1];
        temp := ( b2i(sigma_1_512(W[t-2+1]))  + 
                  b2i(W[t-7+1])               + 
                  b2i(sigma_0_512(W[t-15+1])) + 
                  b2i(W[t-16+1])
                ) mod 2^ws;
        Append(~W, i2b(temp,ws));
      end for;
      
      // step 2 - initialize a,b,c,d,e,f,g,h
      a := H[1]; 
      b := H[2];
      c := H[3];
      d := H[4];
      e := H[5];
      f := H[6];
      g := H[7];
      h := H[8];

      // step 3
      for t in [0..79] do
        T1 := ( h + 
                b2i( SIGMA_1_512(i2b(e,ws)) ) + 
                b2i( Ch(i2b(e,ws), i2b(f,ws), i2b(g,ws)) )+ 
                K512(t) + 
                b2i( W[t+1] ) 
              ) mod 2^ws;
        T2 := ( b2i(SIGMA_0_512(i2b(a,ws))) + 
                b2i(Maj(i2b(a,ws),i2b(b,ws),i2b(c,ws)))
              ) mod 2^ws;
        h := g;
        g := f;
        f := e;
        e := (d + T1) mod 2^ws;
        d := c;
        c := b;
        b := a;
        a := (T1 + T2) mod 2^ws;

      end for;

      // compute the ith intermediate hash value
      H[1] := (a + H[1]) mod 2^ws;
      H[2] := (b + H[2]) mod 2^ws;
      H[3] := (c + H[3]) mod 2^ws;
      H[4] := (d + H[4]) mod 2^ws;
      H[5] := (e + H[5]) mod 2^ws;
      H[6] := (f + H[6]) mod 2^ws;
      H[7] := (g + H[7]) mod 2^ws;
      H[8] := (h + H[8]) mod 2^ws;
    else
      print "Error! Unknown SHA type!";
      return "";
    end if;
  end for;

  case type:
    when 1:
      digest := b2h(i2b(H[1],ws) cat i2b(H[2],ws) cat 
                    i2b(H[3],ws) cat i2b(H[4],ws) cat
                    i2b(H[5],ws) ) ;
    when 224:
      digest := b2h(i2b(H[1],ws) cat i2b(H[2],ws) cat 
                    i2b(H[3],ws) cat i2b(H[4],ws) cat
                    i2b(H[5],ws) cat i2b(H[6],ws) cat 
                    i2b(H[7],ws) ) ;
    when 256:
      digest := b2h(i2b(H[1],ws) cat i2b(H[2],ws) cat 
                    i2b(H[3],ws) cat i2b(H[4],ws) cat
                    i2b(H[5],ws) cat i2b(H[6],ws) cat 
                    i2b(H[7],ws) cat i2b(H[8],ws) ) ;
    when 384:
      digest := b2h(i2b(H[1],ws) cat i2b(H[2],ws) cat 
                    i2b(H[3],ws) cat i2b(H[4],ws) cat
                    i2b(H[5],ws) cat i2b(H[6],ws) ) ;
    when 512:
      digest := b2h(i2b(H[1],ws) cat i2b(H[2],ws) cat 
                    i2b(H[3],ws) cat i2b(H[4],ws) cat
                    i2b(H[5],ws) cat i2b(H[6],ws) cat 
                    i2b(H[7],ws) cat i2b(H[8],ws) ) ;
  end case;

  return digest;
end function;



