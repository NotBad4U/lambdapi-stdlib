require open Stdlib.Prop Stdlib.FOL Stdlib.Eq;
require open Stdlib.Set;
require open Stdlib.Z;
require open Stdlib.Pos;

inductive ℚ : TYPE ≔
|  Qmake : ℤ → ℙ → ℚ;

constant symbol rat : Set;

rule τ rat ↪ ℚ;

injective symbol inject_Z (x: ℤ) ≔  Qmake x H;

symbol # : ℤ → ℙ → ℚ; notation # infix 1;
rule  $z # $p ↪ Qmake $z $p;

symbol Qnum (q: ℚ): ℤ;
rule Qnum (Qmake $z $p) ↪ $z;

symbol Qden (q: ℚ): ℙ;
rule Qden (Qmake $z $p) ↪ $p;

symbol QDen (q: ℚ): ℤ ≔ Zpos (Qden q);

symbol Qeq (p q : ℚ) ≔ (Qnum p) × (QDen q) = (Qnum q) × (QDen p);

symbol == : ℚ → ℚ → Prop; notation == infix 10;
rule $x == $y ↪ Qeq $x $y;

symbol Qle (p q : ℚ) ≔ ((Qnum p) × (QDen q)) ≤ ((Qnum q) × (QDen p));

symbol Qlt (p q : ℚ) ≔ ((Qnum p) × (QDen q)) < ((Qnum q) × (QDen p));

commutative associative symbol Qplus: ℚ → ℚ → ℚ;
rule Qplus $x $y ↪ (Qnum $x × QDen $y + Qnum $y × QDen $x) # (mul (Qden $x) (Qden $y));

commutative associative symbol Qmult: ℚ → ℚ → ℚ;
rule Qmult $x $y ↪ (Qnum $x × Qnum $y) # (mul(Qden $x) (Qden $y));

symbol Qopp: ℚ → ℚ;
rule Qopp $x ↪ (~ (Qnum $x)) # (Qden $x);

symbol Qminus: ℚ → ℚ → ℚ;
rule Qminus $x $y ↪  Qplus $x (Qopp $y);

symbol Qinv: ℚ → ℚ;
rule Qinv (Z0  # $y) ↪ Z0 # H
with Qinv ((Zpos $x) # $y) ↪ (Zpos $y) # $x
with Qinv ((Zneg $x) # $y) ↪ (Zneg $y) # $x;

symbol Qdiv: ℚ → ℚ → ℚ;
rule Qdiv $x $y ↪   Qmult $x (Qinv $y);

opaque symbol Qden_cancel a b p : π (((a # p) == (b # p)) ⇒ (a = b)) ≔
begin
    assume a b p;
    refine mul_reg_r (Zpos p) (Zpos≠Z0 p)
end;

opaque symbol Qnum_cancel (z : τ int) (a b : τ pos) : π (z ≠ 0) → π (((z # a) == (z # b)) ⇒ (a = b)) ≔
begin
    assume z a b Hz_ne_0;
    simplify;
    assume H;
    symmetry;
    have H2 : π ((Zpos b) = (Zpos a)) {
        refine mul_reg_l z Hz_ne_0 H;
    };
    apply (∧ₑ₁ (Zpos_inj b a)) H2 
end;

opaque symbol Qeq_refl [x] : π (x == x) ≔
begin
    assume x; reflexivity;
end;

opaque symbol Qeq_sym [x y] : π (x == y) → π (y == x) ≔
begin
    simplify;
    assume x y H;
    symmetry;
    apply H;
end;

opaque symbol Qeq_trans [x y z] : π (x == y) → π (y == z) → π (x == z) ≔
begin
    simplify;
    assume x y z Hxy Hyz;
    apply mul_reg_r (QDen y)  (Zpos≠Z0 (Qden y));
    admit
    //apply mul_shuffle
end;


opaque symbol Qle_refl [x] : π (Qle x x) ≔
begin
    assume x;
    simplify;
    admit 
end;
