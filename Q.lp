require open Stdlib.Prop Stdlib.FOL Stdlib.Eq;
require open Stdlib.Set;
require open Stdlib.Z;
require open Stdlib.Pos;

inductive ℚ : TYPE ≔
|  Qmake : ℤ → ℙ → ℚ;

constant symbol rat : Set;

rule τ rat ↪ ℚ;

symbol inject_Z (x: ℤ) ≔  Qmake x H;

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

symbol Qle (p q : ℚ) ≔ (Qnum p) × (QDen q) ≤ (Qnum q) × (QDen p);

symbol Qlt (p q : ℚ) ≔ (Qnum p) × (QDen q) < (Qnum q) × (QDen p);

symbol Qplus: ℚ → ℚ → ℚ;
rule Qplus $x $y ↪ (Qnum $x × QDen $y + Qnum $y × QDen $x) # (mul (Qden $x) (Qden $y));

symbol Qmult: ℚ → ℚ → ℚ;
rule Qplus $x $y ↪ (Qnum $x × Qnum $y) # (mul(Qden $x) (Qden $y));

symbol Qopp: ℚ → ℚ;
rule Qopp $x ↪ (~ (Qnum $x)) # (Qden $x);

symbol Qminus: ℚ → ℚ → ℚ;
rule Qplus $x $y ↪  Qplus $x (Qopp $y);

symbol Qinv: ℚ → ℚ;
rule Qinv (Z0  # $y) ↪ Z0 # H
with Qinv ((Zpos $x) # $y) ↪ (Zpos $y) # $x
with Qinv ((Zneg $x) # $y) ↪ (Zneg $y) # $x;

symbol Qdiv: ℚ → ℚ → ℚ;
rule Qdiv $x $y ↪   Qmult $x (Qinv $y);

opaque symbol Qden_cancel [a b p] : π (((a # p) == (b # p)) ⇒ (a = b)) ≔
begin
    admit
end;
