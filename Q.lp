require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Eq;
require open Stdlib.Set;
require open Stdlib.Z;
require open Stdlib.Pos;
require open Stdlib.Bool;
require open Stdlib.Prod;
require open Stdlib.Comp;
require open Stdlib.Classic;
require open Stdlib.PropExt;
require open Stdlib.Impred;

inductive ℚ : TYPE ≔
| Qmake : ℤ → ℙ → ℚ;

constant symbol rational : Set;
rule τ rational ↪ ℚ;

symbol inject_Z (x: ℤ) ≔  Qmake x H;
symbol inject_P_in_Z (x: ℙ) ≔  Zpos x;

coerce_rule coerce ℤ ℚ $x ↪ inject_Z $x;
coerce_rule coerce ℙ ℤ $x ↪ inject_P_in_Z $x;

symbol / : ℤ → ℙ → ℚ;

rule / 0 (I _) ↪ Qmake 0 H
with / 0 (O _) ↪ Qmake 0 H; 

//rule / $z $p ↪ Qmake $z $p;



symbol Qnum (q: ℚ): ℤ;
rule Qnum (Qmake $z $p) ↪ $z;

symbol Qden (q: ℚ): ℙ;
rule Qden (Qmake $z $p) ↪ $p;

symbol QDen (q: ℚ): ℤ ≔ Zpos (Qden q);

symbol q≐ : ℚ → ℚ → Comp;  notation q≐  infix 10; //≔ (Qnum p) * (QDen q) ≐ (Qnum q) * (QDen p); notation q≐ infix 10;
rule  (Qmake $n1 $d1) q≐ (Qmake $n2 $d2) ↪ ($n1 * $d2) ≐ ($n2 *  $d1);

symbol q= : ℚ → ℚ → Prop; notation q= infix 10;  //≔ (Qnum p) * (QDen q) = (Qnum q) * (QDen p); notation q= infix 10;
rule (Qmake $n1 $d1) q= (Qmake $n2 $d2) ↪ ($n1 * $d2) = ($n2 * $d1);

symbol q≤ : ℚ → ℚ → Prop;  notation q≤  infix 15; //≔ ((Qnum p) * (QDen q)) ≤ ((Qnum q) * (QDen p)); notation q≤ infix 10;
rule  (Qmake $n1 $d1) q≤ (Qmake $n2 $d2) ↪ ($n1 * $d2) ≤ ($n2 *  $d1); 

symbol q< : ℚ → ℚ → Prop; notation q< infix 15;  //≔ ((Qnum p) * (QDen q)) < ((Qnum q) * (QDen p)); notation q< infix 10;
rule (Qmake $n1 $d1)  q<(Qmake $n2 $d2) ↪ ($n1 * $d2) < ($n2 *  $d1);

symbol q≥ : ℚ → ℚ → Prop;  notation q≥  infix 15; //≔  ((Qnum p) * (QDen q)) ≥ ((Qnum q) * (QDen p)); notation q≥ infix 10;
rule  (Qmake $n1 $d1) q≥ (Qmake $n2 $d2) ↪ ($n1 * $d2) ≥ ($n2 *  $d1); 

symbol q> : ℚ → ℚ → Prop; notation q> infix 15;  //≔ ((Qnum p) * (QDen q)) > ((Qnum q) * (QDen p)); notation q> infix 10;
rule (Qmake $n1 $d1)  q>(Qmake $n2 $d2) ↪ ($n1 * $d2) > ($n2 *  $d1); 

symbol q+: ℚ → ℚ → ℚ; notation q+ infix left 20 ; // λ x, λ y, ((Qnum x * QDen y) + (Qnum y * QDen x)) # (mul (Qden x) (Qden y));
rule (Qmake $n1 $d1)  q+ (Qmake $n2 $d2) ↪ Qmake (($n1 * $d2) + ($n2 *  $d1)) (mul $d1 $d2);

symbol q+_com x y: π (x q+ y = y q+ x) ≔
begin
    induction;
    assume u1 d1;
    induction;
    assume u2 d2;
    simplify q+;
    rewrite +_com;
    rewrite mul_com;
    reflexivity
end;

symbol q+_assoc x y z : π (x q+ y q+ z = x q+ (y q+ z)) ≔
begin
admitted;

symbol q*: ℚ → ℚ → ℚ; notation q* infix left 22; //≔ λ x, λ y, (Qnum x * Qnum y) # (mul(Qden x) (Qden y));
rule (Qmake $n1 $d1)  q* (Qmake $n2 $d2) ↪ Qmake ($n1 * $n2) (mul $d1 $d2);

symbol q*_com x y: π (x q* y = y q* x) ≔
begin
    induction;
    assume u1 d1;
    induction;
    assume u2 d2;
    simplify q*;
    rewrite *_com;
    rewrite mul_com;
    reflexivity
end;

symbol q~: ℚ → ℚ; notation q~ prefix 24; // ≔ λ x, (— (Qnum x)) # (Qden x);
rule q~ (Qmake $n $d) ↪ Qmake (— $n) $d;

symbol q~~_eq_q x : π (q~ q~ x  = x) ≔ begin
    induction; assume x y;
    simplify;
    rewrite —_idem;
    reflexivity
end;

symbol q-: ℚ → ℚ → ℚ; notation q- infix left 21; //≔ λ x, λ y, x q+ (q~ y); 
rule $x q- $y ↪  $x q+ (q~ $y);

symbol Qinv: ℚ → ℚ;
rule Qinv (Qmake Z0 $y) ↪ Qmake Z0 H
with Qinv (Qmake (Zpos $x) $y) ↪ Qmake (Zpos $y) $x
with Qinv (Qmake (Zneg $x) $y) ↪ Qmake (Zneg $y) $x;

symbol Qdiv: ℚ → ℚ → ℚ;
rule Qdiv $x $y ↪ $x q* (Qinv $y);

symbol 1#1 : ℚ ≔ Qmake 1 H;


symbol Qeq_imp_refl [x y] : π (x q= y) → π (x = y) ≔
begin
admitted;

symbol Qeq_refl [x] : π (x q= x) ≔
begin induction; reflexivity end;

symbol Qeq_sym [x y] : π (x q= y) → π (y q= x) ≔
begin
  induction; assume u1 d1;
  induction; assume u2 d2;
  simplify;
  assume h;
  symmetry;
  refine h
end;

symbol Qeq_trans [x y z] : π (x q= y) → π (y q= z) → π (x q= z) ≔
begin
  induction; assume u1 d1;
  induction; assume u2 d2;
  induction; assume u3 d3;
  simplify q=;
  assume h1 h2;
  admit
end;

symbol Qden_cancel a b p : π (((Qmake a p) q= (Qmake b p)) ⇒ (a = b)) ≔
begin
admitted;

symbol Qnum_cancel (z : τ int) (a b : τ pos) : π (z ≠ 0) → π (((Qmake z a) q= (Qmake z b)) ⇒ (a = b));

require open Stdlib.Nat;

constant symbol tup : Set → Set → Set;
symbol tupe [a b] : τ a → τ b → τ (tup a b);
symbol π2 [a b] : τ(tup a b) → τ b;
rule π2 (tupe _ $b) ↪ $b;
symbol π1 [a b] : τ(tup a b) → τ a;

require open Stdlib.Zgcd;

// Definition Qred (q:Q) :=
//   let (q1,q2) := q in
//   let (r1,r2) := snd (Z.ggcd q1 (Zpos q2))
//   in r1#(Z.to_pos r2).
protected symbol Qred (q: ℚ) ≔ 
  let q1 ≔ (Qnum q) in 
  let q2 ≔ (Qden q) in
  let r ≔ (Zggcd q1 (Zpos q2)) ₂ in
   Qmake (r ₁) (to_pos (r ₂));

symbol # (z: ℤ) (p: ℙ): ℚ; notation # infix 5;
rule $x # $y ↪ Qred (Qmake $x $y);

symbol divide ≔ λ n, λ m, (`∃ p,  m = p Stdlib.Z.* n);

symbol zggcd ≔ λ n, λ m, ((Zggcd n m) ₂ ₂);

opaque symbol gcd_divide_l: Π (n: τ int) , Π (m: τ int), π (divide (zggcd n m) n) ≔
begin admit end;

opaque symbol gcd_divide_r: Π (n: τ int) , Π (m: τ int), π (divide (zggcd n m) m) ≔
begin admit end;

opaque symbol gcd_greatest: Π (n: τ int) , Π (m: τ int), Π (p: τ int), π (divide p n) → π (divide p m) → π (divide p (zggcd n m)) ≔
begin admit end;

opaque symbol gcd_nonneg: Π (n: τ int) , Π (m: τ int), π (Z0 Stdlib.Z.≤ (zggcd n m)) ≔
begin admit end;

symbol q+' : ℚ → ℚ → ℚ ≔ λ p, λ q, Qred (p q+ q);
notation q+' infix left 20;

symbol q-' : ℚ → ℚ → ℚ ≔ λ p, λ q, Qred (p q- q);
notation q-' infix left 20;

symbol q*' : ℚ → ℚ → ℚ ≔ λ p, λ q, Qred (p q* q);
notation q*' infix left 22;
