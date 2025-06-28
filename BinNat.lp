require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Bool Stdlib.Nat Stdlib.Pos Stdlib.Comp;

inductive BinNat: TYPE ≔
| N0 : BinNat
| Npos: ℙ → BinNat;

symbol BNat: Set;
rule τ BNat ↪ BinNat;

symbol Nsucc_double: BinNat → BinNat;
rule Nsucc_double N0 ↪ Npos H
with Nsucc_double (Npos $p) ↪ Npos (I $p);

symbol Ndouble: BinNat → BinNat;
rule Ndouble N0 ↪ N0
with Ndouble (Npos $p) ↪ Npos (O $p);

symbol from_pos: ℙ → BinNat ≔ λ x, Npos x;

coerce_rule coerce ℙ BinNat $x ↪ from_pos $x;

symbol to_nat: BinNat → ℕ;
rule to_nat N0 ↪ 0
with to_nat (Npos $x) ↪ val $x;

symbol from_nat: ℕ → BinNat;
rule from_nat 0 ↪ N0
with from_nat ($x +1) ↪ Npos (of_succ_nat $x);

symbol compare: BinNat → BinNat → Comp;
rule compare N0 N0 ↪ Eq
with compare N0 (Npos _) ↪ Lt
with compare (Npos _) N0 ↪ Gt
with compare (Npos $x) (Npos $y) ↪ compare $x $y;

// Operation over bits

symbol ⎪⎪ : BinNat → BinNat → BinNat; notation ⎪⎪ infix 22;
rule N0 ⎪⎪ $x ↪ $x
with $x ⎪⎪ N0 ↪ $x
with (Npos $x) ⎪⎪ (Npos $y) ↪ $x ⎪ $y; 

symbol && : BinNat → BinNat → BinNat; notation && infix 20;
rule N0 && _ ↪ N0
with _ && N0 ↪ N0
with (Npos $x) && (Npos $y) ↪ $x & $y; 

symbol xor: BinNat → BinNat → BinNat; notation xor infix 20;
rule N0 xor N0 ↪ N0
with N0 xor (Npos $x) ↪ Npos $x
with (Npos $x) xor N0 ↪ Npos $x
with (Npos H) xor (Npos H) ↪ N0
with (Npos H) xor (Npos (O $x)) ↪ Npos (I $x)
with (Npos H) xor (Npos (I $x)) ↪ Npos (O $x)
with (Npos (O $x)) xor H ↪ Npos (I $x)
with (Npos (O $x)) xor (Npos (O $y)) ↪ Ndouble ($x xor $y)
with (Npos (O $x)) xor (Npos (I $y)) ↪ Nsucc_double ($x xor $y)
with (Npos (I $x)) xor (Npos H) ↪ Npos (O $x)
with (Npos (I $x)) xor (Npos (O $y)) ↪ Nsucc_double ($x xor $y)
with (Npos (I $x)) xor (Npos (I $y)) ↪ Ndouble ($x xor $y);

// The predecessor of a positive number can be seen as a BinNat
symbol pred_N: ℙ → BinNat;
rule pred_N (O $p) ↪ Npos (pos_pred_double $p) 
with pred_N (I $p) ↪ Npos (O $p)
with pred_N H ↪ N0;

symbol testbit: ℙ → BinNat → 𝔹;
rule testbit (O $p) N0 ↪ false
with testbit _ N0 ↪ true
with testbit H _ ↪ false
with testbit (O $p) (Npos $n) ↪ testbit $p (pred_N $n)
with testbit (I $p) (Npos $n) ↪ testbit $p (pred_N $n);