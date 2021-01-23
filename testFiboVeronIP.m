clear;

load "sha.m";

// Global Paramters

// r := 2; p := 11; n := p+2; //l := 6;
// r := 2; p := 3; n := p+2; 
// r := 2; p := 20; n := p+2; // 130 sec lev
// r := 2; p := 16; n := p+2; //  96 sec lev
r := 2; p := 14; n := p+2; //  80 sec lev

// compute all possible determinants and their frequency (doable only for p=2,3)
/*
Determinants := [];
Frequencies := [];
for x in CartesianPower([1,2,3], (p+1)^2) do
    d := Determinant(Matrix(Integers(), p+1, p+1, [x[i] : i in [1..#x]]));
    if not d in Determinants then
        Append(~Determinants,d);
        Append(~Frequencies,1);
    else
        ind := Index(Determinants,d);
        Frequencies[ind] := Frequencies[ind] + 1;
    end if;
    if d le 10 or d ge -10 then
        printf "Matrix(Integers(), p+1, p+1, %o);\n", [x[i] : i in [1..#x]];
    end if;
end for;
*/

// r := 2; p := 20; n := p+2; 
// Log(2,alpha), alpha solution of x^(p+1) -x^p - 1
// l := r + Ceiling(Log(2,p+1) + (n-1)*Log(2,alpha));
R<x> := PolynomialRing(RealField());
roots := Roots(x^(p+1) -x^p -1);
max_root := Max([AbsoluteValue(roots[i][1]) : i in [1..#roots]]);
l := r + Ceiling(Log(2,p+1) + (n-1)*Log(2,max_root));

// ---------------------------------------------------------------------------

pFibonacci := function(p, n)
    if n eq 0 then // n = 0
        return 0;
    elif n ge 1 and n le p+1 then // 1 <= n <= p+1
        return 1;
    elif n gt p+1 then // n > p+1
        return $$(p, n-1) + $$(p, n-p-1);
    else // n < 0
        return $$(p, n+p+1) - $$(p, n+p);
    end if;
end function;

// ---------------------------------------------------------------------------

Qp_matrix_power := function(p,n)
    Q := ZeroMatrix(Integers(), p+1, p+1);
    for j in [0..p] do
        //0,j,pFibonacci(p,n-p-j);
        Q[1,j+1] := pFibonacci(p,n+1-j);
    end for;

    for i in [1..p] do
        for j in [0..p] do
            //i,j,pFibonacci(p,n-p+i-j);
            Q[i+1,j+1] := pFibonacci(p,n-p+i-j);
        end for;
    end for;

    return Q;
end function;

// ---------------------------------------------------------------------------

FibonacciWeight := function(A)
    w := 0;
    for i in [1..Nrows(A)] do
        for j in [1..Ncols(A)] do
            if A[i,j] ne 0 then
                w := w + 1;
            end if;
        end for;
    end for;

    return w;
end function;

// ---------------------------------------------------------------------------
 
RandomMessage := function(size, max)
  return Matrix(size,size,[Random(1,max) : i in [1..size^2]]);
end function;

// ---------------------------------------------------------------------------

RandomPermutation := function(n)
    L := [i : i in [1..n]];
    P := [];
    while L ne [] do
        ind := Random(1,#L);
        Append(~P, L[ind]);
        Remove(~L,ind);
    end while;

    return P;
end function;

// ---------------------------------------------------------------------------

GenerateRandomGamma := function(p,l)
    Gamma1 := RandomPermutation(p+1);
    Gamma2 := RandomPermutation(p+1);

    return [*Gamma1,Gamma2*];
end function;

// ---------------------------------------------------------------------------

Permutation2Hex := function(P)
// NOTE: 
// DECIDE IF ALL ELEMENT IN P MUST BE TRANSLATED 
// IN A STRING WITH FIXED NUMBER OF DIGITS
// LIKE 16 -> 10_hex then e.g. 10 -> 0A_hex instead in 10 -> A_hex
//
    s := "";
    for i in [1..#P] do
        s := s cat IntegerToString(P[i],16);
    end for;

    return s;
end function;

// ---------------------------------------------------------------------------

RationalMatriz2Hex := function(A)
    s := "";
    for i in [1..Nrows(A)] do
        for j in [1..Ncols(A)] do
            s := s cat IntegerToString(Numerator(A[i,j])) cat IntegerToString(Denominator(A[i,j]));
        end for;
    end for;

    return s;
end function;

// ---------------------------------------------------------------------------

ApplyGammaToMatrix := function(Gamma, A)

    Gamma1 := Gamma[1];
    Gamma2 := Gamma[2];

    A_out := ZeroMatrix(Rationals(),Nrows(A),Ncols(A));
    for i in [1..Nrows(A)] do
        for j in [1..Ncols(A)] do
            A_out[i,j] := A[Gamma1[i],Gamma2[j]];
        end for;
    end for;

    return A_out;
end function;

// ---------------------------------------------------------------------------

GenerateRandomErrorWithOneZeroEnntry := function(p,l)

    E := Matrix(p+1,p+1,[Random(1,2^l-1) : i in [1..(p+1)^2]]);
    i := Random(1,p+1);
    j := Random(1,p+1);
    E[i,j] := 0;

    return E;
end function;


XOR := function(A, B, l)
    A_bits := IntegerToSequence(Integers()!A,2);
    B_bits := IntegerToSequence(Integers()!B,2);
    AxorB := Vector(GF(2), B_bits cat [0 : i in [1..l - #B_bits]]) + Vector(GF(2), A_bits cat [0 : i in [1..l - #A_bits]]); 

    return SequenceToInteger([Integers()!AxorB[i] : i in [1..Ncols(AxorB)]],2);
end function;

AddError := function(C, E, p, l)
    R := ZeroMatrix(Integers(),p+1,p+1);
    for i in [1..Nrows(R)] do
        for j in [1..Ncols(R)] do
            // R[i,j] := (C[i,j] + E[i,j]) mod 2^l; // could also be xor
            R[i,j] := XOR(C[i,j], E[i,j], l);
        end for;
    end for;

    return R;
end function;

GenerateRandomError := function(M, Q, p, l)
    E_prime := GenerateRandomErrorWithOneZeroEnntry(p,l);

    // generate PUBLIC KEY
    // R := M*Q + E;
    R_tmp := M*Q;

    // R := ZeroMatrix(Integers(),p+1,p+1);
    // for i in [1..Nrows(R)] do
    //  for j in [1..Ncols(R)] do
    //      R[i,j] := (R_tmp[i,j] + E_prime[i,j]) mod 2^l; // could also be xor
    //  end for;
    // end for;
    R := AddError(R_tmp, E_prime, p, l);
    E := R-R_tmp;

    return E;
end function;

FibonacciKeyGen := function(PARAM)
    r := PARAM["r"];
    p := PARAM["p"];    
    n := PARAM["n"];
    l := PARAM["l"];    

    Q := Qp_matrix_power(p,n);

    // generate PRIVATE KEY
    // random message
    M := RandomMessage(p+1,2^r-1);
    // M := Matrix(Integers(), p+1, p+1, [ 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 2]);
    // random error of weight p+1
    // E_prime :=  Matrix(p+1,p+1,[Random(1,2^l-1) : i in [1..(p+1)^2]]);
    // i := Random(1,p+1);
    // j := Random(1,p+1);
    // E_prime[i,j] := 0;

    /*
    E_prime := GenerateRandomError(p,l);

    // generate PUBLIC KEY
    // R := M*Q + E;
    R_tmp := M*Q;

    // R := ZeroMatrix(Integers(),p+1,p+1);
    // for i in [1..Nrows(R)] do
    //  for j in [1..Ncols(R)] do
    //      R[i,j] := (R_tmp[i,j] + E_prime[i,j]) mod 2^l; // could also be xor
    //  end for;
    // end for;
    R := AddError(R_tmp, E_prime);
    E := R-R_tmp;
    */
    E := GenerateRandomError(M, Q, p, l);

    // R := AddError(M*Q, E, p, l);
    R := M*Q + E;

    PRIV_KEY := AssociativeArray();
    PRIV_KEY["M"] := M; 
    PRIV_KEY["E"] := E;

    PUB_KEY := AssociativeArray();
    PUB_KEY["R"] := R;
    PUB_KEY["Q"] := Q;

    return PRIV_KEY, PUB_KEY;
end function;

// ---------------------------------------------------------------------------

ComputeC1 := function(gamma)
    gamma1 := gamma[1];
    gamma2 := gamma[2];
    gamma1_hex := Permutation2Hex(gamma1);
    gamma2_hex := Permutation2Hex(gamma2);
    c1 := Sha(gamma1_hex cat gamma2_hex ,256:MsgType:="hex");

    return c1;
end function;

// ---------------------------------------------------------------------------

ComputeC2 := function(gamma,U,Q)
    T := ApplyGammaToMatrix(gamma, U*Q );
    T_hex := RationalMatriz2Hex(T);
    c2 := Sha(T_hex,256:MsgType:="hex");

    return c2;
end function;

// ---------------------------------------------------------------------------

ComputeC3 := function(gamma,V1,Q,V2)
    T := ApplyGammaToMatrix(gamma, V1*Q + V2) ;
    T_hex := RationalMatriz2Hex(T);
    c3 := Sha(T_hex,256:MsgType:="hex");

    return c3;
end function;

// ---------------------------------------------------------------------------

//t := Floor((n-k)/(2*lambda)); 
PARAM := AssociativeArray();
PARAM["r"] := r;
PARAM["p"] := p;
PARAM["n"] := n;
PARAM["l"] := l;


// Veron Identification Protocol
// -----------------------------

// KEY GENERATION

"\nPublic parameter:";
"r = ", r;
"p = ", p;
"n = ", n;
"l = ", l;


PRIV_KEY, PUB_KEY := FibonacciKeyGen(PARAM);

R := PUB_KEY["R"];
Q := PUB_KEY["Q"];

"Q_p^n = ", Q;

M := PRIV_KEY["M"];
E := PRIV_KEY["E"];

"\nPrivate key:";
"M = ", M;
"E = ", E;

"\nPublic key:";
"R = ", R;

// try to find M',F such that 
// - w_F(F) = w_F(E)
// - R = M * Q_p^n + E = M' * Q_p^n + F
// - det(M') = det(M)
/*
counter := 0;
repeat
    F := GenerateRandomError(p,l);
    M_prime := (AddError(R,F,p,l) * Qp_matrix_power(p,-n));
    counter := counter + 1;
    a,b := IsPowerOf(counter,2);
    if a then
        printf "2^%o\n", b;
    end if;
until (SequenceToSet(ElementToSequence(M_prime)) eq {1,2,3}) and 
    (Determinant(M_prime) eq Determinant(M) or Determinant(M_prime) eq -Determinant(M));

printf "counter = %o\n", counter;
*/

// IDENTIFICATION PROTOCOL

// 1. COMMITMENT

U := RandomMessage(p+1,2^r-1);

Gamma := GenerateRandomGamma(p,l);

c1 := ComputeC1(Gamma);

c2 := ComputeC2(Gamma,U+M,Q);

c3 := ComputeC3(Gamma,U,Q,R);

"\nCommitment:";
c1,c2,c3;

// 2. CHALLENGE
b := Random({0,1,2});

// b := 1;

"\nChallenge:";
b;

// 3. RESPONSE
case b:
    when 0:
        response := [* Gamma, U+M *];
    when 1:
        tmp1 := ApplyGammaToMatrix(Gamma, (U+M)*Q);
        tmp2 := ApplyGammaToMatrix(Gamma, E);
        response := [* tmp1, tmp2 *];
    when 2:
        response := [* Gamma, U *];
end case;

// "\n*******\n";
// "c3: ";
// "U = ", U;
// "U*Q = ", U*Q;
// "R = ", R;
// // "U*Q XOR R = ", AddError(U*Q,R,p,l);
// "U*Q + R = ", U*Q + R;
// // T := ApplyGammaToMatrix(Gamma, AddError(U*Q,R,p,l)) ;
// T := ApplyGammaToMatrix(Gamma, U*Q+R) ;
// "Gamma(U*Q + R) = ", T;
// T_hex := RationalMatriz2Hex(T);
// "Hex(Gamma(U*Q + R)) = ", T_hex;
// c3 := Sha(T_hex,256:MsgType:="hex");

// "\n";

// tmp1 := ApplyGammaToMatrix(Gamma, (U+M)*Q);
// tmp2 := ApplyGammaToMatrix(Gamma, E);
// "Gamma((U+M)*Q) = ", tmp1;
// "Gamma(E) = ", tmp2;
// // "Gamma((U+M)*Q) XOR Gamma(E) = ", AddError(tmp1, tmp2, p, l);
// "Gamma((U+M)*Q) + Gamma(E) = ", tmp1 + tmp2;
// "\n*******\n";

"\nResponse:";
response;

// 4. CHECK
R := PUB_KEY["R"];
Q := PUB_KEY["Q"];


"\n";
case b:
    when 0:
        // check c1,c2
        if c1 eq ComputeC1(response[1])                and 
           c2 eq ComputeC2(response[1],response[2],Q)  then
            "IDENTIFICATION SUCCESS!";
        else
            "IDENTIFICATION FAILURE...";
        end if;
    when 1:
        // check c2,c3 and Weight((E))) == (p+1)^2-1

        // c2 ?= Hash(rsp1)
        T_hex := RationalMatriz2Hex(response[1]);
        h1 := Sha(T_hex,256:MsgType:="hex"); 

        // c3 ?= Hash(rsp1+rsp2)
        // T_hex := RationalMatriz2Hex(AddError(response[1], response[2], p, l));
        T_hex := RationalMatriz2Hex(response[1] + response[2]);
        h2 := Sha(T_hex,256:MsgType:="hex");

        if c2 eq h1                      and 
           c3 eq h2                      and
           FibonacciWeight(response[2]) eq (p+1)^2-1  then
            "IDENTIFICATION SUCCESS!";
        else
            if c2 ne h1 then
                "c2 ne h1";
            end if;
            if c3 ne h2 then
                "c3 ne h2"; // *****
            end if;
            if FibonacciWeight(response[2]) ne (p+1)^2-1  then
                "FibonacciWeight(response[2]) ne (p+1)^2-1";
            end if;
            "IDENTIFICATION FAILURE...";
        end if;
    when 2:
        // check c1,c3
        if c1 eq ComputeC1(response[1])                                  and 
           c3 eq ComputeC3(response[1],response[2],Q,R)  then
            "IDENTIFICATION SUCCESS!";
        else
            "IDENTIFICATION FAILURE...";
        end if;
end case;


"\nFIBONACCI CODE INFORMATION\n";

"\nPublic parameter:";
"r = ", r;
"p = ", p;
"n = ", n;
"l = ", l;

RR<x> := PolynomialRing(RealField());
poly := x^(p+1) - x^p - 1; 
alpha := Max(Roots(poly))[1];
ll := r + Ceiling(Log(2,p+1) + (n-1)*Log(2,alpha));

"\nl <= r + Ceiling(Log(2,p+1) + (n-1)*Log(2,alpha)) = ", r + Ceiling(Log(2,p+1) + (n-1)*Log(2,alpha)); 

"\ncode dimension = r*(p+1)^2 = ", r*(p+1)^2 ;
"\ncode length    = l*(p+1)^2 = ", l*(p+1)^2 ;
R_length := 0;
for i in [1..Nrows(R)] do
    for j in [1..Ncols(R)] do
        R_length := R_length + #IntegerToSequence(R[i,j],2);
    end for;
end for;
R_max_entry_length := 0;
for i in [1..Nrows(R)] do
    for j in [1..Ncols(R)] do
        if #IntegerToSequence(R[i,j],2) gt R_max_entry_length then
            R_max_entry_length := #IntegerToSequence(R[i,j],2);
        end if;
    end for;
end for;
R_max_length := R_max_entry_length*(p+1)^2;
"\nactual |R| = ", R_length;
"\nmax    |R| = ", R_max_length;



"\n|Public parameters size| = ", Log(2,r) + Log(2,p) + Log(2,n);
"\n|PK| = ", l * (p+1)^2;
"\n|SK| = ", r*(p+1)^2 + l*(p+1)^2;
"\nResponse step cost (b=0,2) = ", 2*(p+1)*Log(2,p+1) + r*(p+1)^2;
"\nResponse step cost (b=1)   = ", 2*l*(p+1)^2;

"\nSecurity:";
"\nLog(2,2^((p+1)^2)) = ", Log(2,2^((p+1)^2));
"\nLog(2,Factorial(p+1)^2) = ", Log(2,Factorial(p+1)^2);
// "\n------------------- LATEX TABLE -------------------\n";

// Code parameters & $(r,p,n)$ & $(q,n,k,w)$ & $(q,n,w)$ & $(q,m,n,k,r)$ & $(q,m,n,r)$ \\
// Public param. size & $\log_2 r + \log_2 p + \log_2 n$ & $k(n-k)+\log_r$ & $n+\log_2 r$& $mk(n-k)+\log_2 r$ & $mn+\log_2 r$ \\
// $|\sk|$ & $r(p+1)^2 + l(p+1)^2$ & $k+n$ & $k+n$ & $m(k+n)$ & $m(k+n)$ \\
// $|\pk|$ & $l(p+1)^2$ & $n$ & $n$ & $mn$ & $mn$ \\
// Rsp. step cost $b=0,2$ & $2(p+1)\log_2(p+1) + 3r(p+1)^2$ & $n \log n + k$ & $n \log n + k$  & $m^2+n^2+mk$ & $m^2+n^2+mk$ \\
// Response step cost $b=1$ & $4l(p+1)^2$ & $2n$  & $2n$ & $2mn$ & $2mn$ \\
 
