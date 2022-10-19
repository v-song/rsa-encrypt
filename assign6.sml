(*
 *
 * Vivien Song
 *
 * CS 54, Fall 2022
 * Assignment 6
 *
 *)



(*** Starter code   $-* $+ ***)
(*
 * Starter code, part 1 of 6
 *
 * We want to be able to see long integers in their entirety,
 * so we set a parameter to a large value.
 *)
Control.Print.intinfDepth := 1000;

(*
 * Starter code, part 2 of 6
 *
 * We prefer the operations quot and rem because they are a little faster
 * than div and mod. The difference is that quot rounds toward minus infinity
 * while div rounds toward zero. Here we make quot and rem infix operators.
 *)
infix 7 quot rem;

(*
 * Starter code, part 3 of 6
 *
 * We redeclare the usual arithmetic operators to work with IntInf.int. The
 * change is convenient in most situations, but it has the side effect of 
 * hiding the operators on ordinary int values. In the few cases when we 
 * want to work with ordinary int values, we must use awkward expressions
 * like Int.-(x,y).
 *
 * Notice the function quotRem. The call quotRem(x,y) returns an ordered pair
 * with both the quotient and remainder and is more efficient than calling
 * quot and rem separately.
 *)
val op +    = IntInf.+;
val op -    = IntInf.-;
val op *    = IntInf.*;
val op quot = IntInf.quot;
val op rem  = IntInf.rem;
val op <    = IntInf.<;
val op <=   = IntInf.<=;
val quotRem = IntInf.quotRem;
val fromInt = IntInf.fromInt;
val toInt   = IntInf.toInt;

(*
 * Starter code, part 4 of 6
 *
 * Here are a few useful constants. Using zero in in place of 0 helps the
 * SML type inference system and helps to give you functions with the proper
 * type signatures.
 *)
val zero    = fromInt 0;
val one     = fromInt 1;
val two     = fromInt 2;
val three   = fromInt 3;

(*
 * Starter code, part 5 of 6
 *
 * Here is a function to generate random IntInf.int values. It pieces them
 * together 8 bits at a time using a random number generator. To make the
 * computation efficient, we define two auxiliary functions--one to compute
 * 2^b-1, the largest number expressible in b bits, for small values of b;
 * and another to multiply by 256 quickly using a shift.
 *
 * See the assignment for more information about random number generators.
 *
 * randomIntInf : Random.rand -> int -> IntInf.int
 *)
fun randomIntInf gen bits =
        let
            fun randomBits gen b =
                    let
                        val top = case b of
                                      1 =>   1
                                    | 2 =>   3
                                    | 3 =>   7
                                    | 4 =>  15
                                    | 5 =>  31
                                    | 6 =>  63
                                    | 7 => 127
                                    | 8 => 255
                                    | _ =>   0;
                    in
                        fromInt(Random.randRange(0,top) gen)
                    end;
            fun mult256 x = IntInf.<<(x, Word.fromInt 8);
        in
            if Int.<=(bits,8)
               then randomBits gen bits
               else randomBits gen 8 +
                    mult256(randomIntInf gen (Int.-(bits,8)))
        end;

(*
 * Starter code, part 6 of 6
 *
 * Here is a function for finding the mod-m multiplicative inverse of u. 
 * It will return SOME a, with 0 <= a < m, if ua mod m = 1. It will return
 * NONE if there is no such a. 
 *
 * The implementations uses a variant of Euclid's algorithm for finding
 * greatest common divisors. See the assignment for a discussion of the
 * theory behind the function.
 *
 * inverseMod : IntInf.int * IntInf.int -> IntInf.int option
 *)
fun inverseMod (u,m) =
        let
            (*
             * Invariant: There are constants b and d
             * satisfying
             *     x = au+bm  and  y = cu+dm.
             * If ever x=1, then 1 = au+bm, and a
             * is the inverse of u, mod m.
             *)
            fun extendedEuclid(x,y,a,c) =
                if x = zero
                   then NONE
                else if x = one
                   then SOME (if a < zero
                                 then a + m
                                 else a)
                else let
                         val (q,r) = quotRem(y,x);
                     in
                         extendedEuclid(r,x,c - a * q,a)
                     end;
        in
            extendedEuclid(u,m,one,zero)
        end;


(*** Problem 1   $- $+06_01 ***)
(* powerMod : IntInf.int * IntInf.int * IntInf.int -> IntInf.int *)
(* This function computes b^e mod n recursively *)

    fun powerMod (b, e, n) = 
        if e = zero then one 
        else if e rem two = zero then
            ((powerMod(b, (e quot two), n)) * (powerMod(b, (e quot two), n))) rem n
        else 
            b * ((powerMod(b, (e quot two), n)) * (powerMod(b, (e quot two), n))) rem n;
        

(*** Problem 2   $-06_01 $+06_s02 ***)
(* block : IntInf.int * IntInf.int -> IntInf.int list   *)
(* This function turns an integer into its base-n representation in a list*)

(* unblock : IntInf.int * IntInf.int list -> IntInf.int *)
(* This function turns a base-n representation in a list into an integer *)

fun block (x, y) = 
        if y = zero then []
        else 
            (y rem x)::(block (x, (y quot x)))


fun unblock (x, []) = zero
    | unblock (x, lst) =
    let
        val len = Int.toLarge(length lst) - one; 

        fun power n 0 = 1
          | power 0 k = 0
          | power n k = if k < 0 then
                             0
                         else
                             n * (power n (k-1));

        fun add _ [] _ = 0
            | add base (x::xs) len = 
                x*(power base len) + (add base xs (len-1)); 


    in
        add x (rev(lst)) len
    end;



(*** Problem 3   $-06_02 $+06_03 ***)
(* messageToIntInf : string -> IntInf.int *)
(* Converts a string of letters into a number represented in base 256 *)

(* intInfToMessage : IntInf.int -> string *)
(* Converts a number in base 256 back to a string of letters *)

fun messageToIntInf str =
    let 
        val exploded = explode(str);
        val len = Int.toLarge(length exploded) - one;

        fun power n 0 = 1
          | power 0 k = 0
          | power n k = if k < 0 then
                             0
                         else
                             n * (power n (k-1));

        fun add [] _ = 0
            | add (x::xs) len = 
                (Int.toLarge(ord(x)))*(power 256 len) + (add xs (len-1)); 
    in 
        if str = "" then zero
        else 
            add (rev(exploded)) len
    end;

fun intInfToMessage x = 
    let
        fun toStringList (x, y) =
            if y = zero then []
            else 
                toStringList(x, (y quot x))@[chr(toInt(y rem x))]

    in
        implode(rev(toStringList (fromInt(256), x)))
    end;



(*** Problem 4   $-06_03 $+06_04 ***)
(* rsaEncode : IntInf.int * IntInf.int -> IntInf.int -> IntInf.int *)
(* Calculates m^e mod n *)

fun rsaEncode (e, n) m = powerMod (m, e, n);



(*** Problem 5a   $-06_04 $+06_05a ***)
(* encodeString : IntInf.int * IntInf.int -> string -> IntInf.int *)
(* Takes a string and a key and encrypts the message in the string *)

fun encodeString (e, n) str = 
    let
        val newList = block(n, messageToIntInf str);
        val encrypted = map (rsaEncode (e,n)) newList;
    in
         unblock (n, encrypted)
    end;


(*** Problem 5b   $-06_05a $+06_05b ***)
(* decodeString : IntInf.int * IntInf.int -> IntInf.int -> string *)
(* Takes a number and a key and decrypts a message from the given number *)

fun decodeString (e, n) num = 
    let 
        val newList = block(n, num);
        val decrypted = map (rsaEncode (e,n)) newList;
        val unblocked = unblock (n, decrypted)
    in  
        intInfToMessage unblocked
    end;


(*** Problem 6   $-06_05b $+06_06 ***)
(* industrialStrengthPrime : Random.rand -> int -> IntInf.int *)
(* Takes a random number generator and a number of bits to generate a random prime *)

val gen = Random.rand(752,653);
fun industrialStrengthPrime gen k = 
    let 
        val newPrime = randomIntInf gen k
        fun checkPrime gen k p 0 = p 
            | checkPrime gen k p count = 
                let 
                    val newNum = randomIntInf gen k
                in
                    if (newNum < p) andalso (powerMod (newNum, p, p) = newNum) then 
                        checkPrime gen k p (count -1 )
                    else
                        if (newNum < p) then
                            industrialStrengthPrime gen k 
                        else
                            checkPrime gen k p count
                end

    in 
        checkPrime gen k newPrime 20
    end;



    


(*** Problem 7   $-06_06 $+06_07 ***)
(* newRSAKeys : int -> (IntInf.int * IntInf.int) * (IntInf.int * IntInf.int) *)
(* Generates a pair of public and private keys by calling industrialStrengthPrime *)

fun newRSAKeys gen k =
        let
            val p = industrialStrengthPrime gen k;
            val q = industrialStrengthPrime gen k;
            val n = p * q;
            val phin = (p-1) * (q-1);
            val twoK = Int.+(k,k);
            fun getDE () =
                let
                    val d = randomIntInf gen twoK;
                in
                    case if one < d andalso d < n
                            then inverseMod(d,phin)
                            else NONE                of
                         NONE     => getDE()
                       | (SOME e) => ((e,n),(d,n))
                end;
        in
            getDE()
        end;

(*** Problem 8a   $-06_07 $+06_08a ***)
(* Takes a public key and finds the corresponding private key. plus variable with cracked key *)

fun privateKey (e, n) = 
    let 
        fun factor n count = 
            if (n rem (count-1) = 0) then count-1
                else factor n (count-1)

        val p = factor n n;
        val q = n quot p; 
        val modulus = (p-1) * (q-1);
       
    in
        inverseMod(e, modulus)
    end;

val crackedPrivateKey = (one * 701, one * 52753);



(*** Problem 8b   $-06_08a $+06_08b ***)

(* ANSWER: (2^80)/(2^8)t *)



(*** $-06_08 ***)


