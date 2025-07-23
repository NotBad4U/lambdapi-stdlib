require Stdlib.Nat as Nat;
open Stdlib.Nat;
require open Stdlib.Eq  Stdlib.Set Stdlib.Prop Stdlib.Prod Stdlib.Bool;

injective symbol Fin (n: ℕ) ≔ Σ (λ x, istrue (x < n));
injective symbol FinMk (n: ℕ) (m: ℕ) (isLT : π (m < n)): Fin n ≔ @exist nat (λ x, istrue (x < n)) m isLT;

symbol fin: ℕ →  Set;
rule τ (fin $n) ↪ Fin $n;

// Projector renamed

compute (FinMk (2 ^ 4) 4 ⊤ᵢ);

symbol val [n]: Fin n → ℕ ≔ λ e, e s₁;

assert ⊢ val (FinMk 5 1 ⊤ᵢ) ≡ 1;

symbol isLt [n] (f: Fin n): π (f s₁ < n) ≔ f s₂;

assert ⊢ isLt (FinMk 5 1 ⊤ᵢ) ≡ ⊤ᵢ;

//coerce_rule coerce (Fin $n) ℕ $e ↪ val $n $e;

//FIXME: coerce above does not work
//compute (1 + ((FinMk 5 1 ⊤ᵢ)));

symbol last n: Fin (n + 1) ≔ (FinMk (n + 1) n (≤_refl n));

symbol succ n: Fin n → Fin (n + 1) ≔ (λ e, FinMk (n + 1) n (≤_refl n));

// Addition modulo n
symbol add [n] : Fin n → Fin n → Fin n;
rule @add $n (exist $x $px) (exist $y $py) ↪ FinMk $n (($x + $y) % $n) (@modulo_lt ($x + $y) $x $n $px);

symbol t1 ≔ (FinMk 5 2 ⊤ᵢ);
symbol t2 ≔ (FinMk 5 1 ⊤ᵢ);

compute add t1 t2;

compute (add (FinMk 8 2 ⊤ᵢ) (FinMk 8 2 ⊤ᵢ));

assert ⊢ val (add (FinMk 8 2 ⊤ᵢ) (FinMk 8 2 ⊤ᵢ)) ≡ 4;
assert ⊢ val (add (FinMk 3 2 ⊤ᵢ) (FinMk 3 2 ⊤ᵢ)) ≡ 1; // outof bound

// Multiplication modulo n
symbol mul n: Fin n → Fin n → Fin n;
rule mul $n (exist $x $px) (exist $y $py) ↪ FinMk $n (($x * $y) % $n) (@modulo_lt ($x * $y) $x $n $px);

// Subtraction modulo n
symbol sub n: Fin n → Fin n → Fin n;
rule sub $n (exist $x $px) (exist $y $py) ↪ FinMk $n (($x - $y) % $n) (@modulo_lt ($x - $y) $x $n $px);

symbol shiftl n: Fin n → Fin n → Fin n;
rule shiftl $n (exist $x $px) (exist $y $py) ↪ FinMk $n (($x <<< $y) % $n) (@modulo_lt ($x <<< $y) $x  $n $px);

symbol shiftr n: Fin n → Fin n → Fin n;
rule shiftr $n (exist $x $px) (exist $y $py) ↪ FinMk $n (($x >>> $y) % $n) (@modulo_lt ($x >>> $y) $x $n $px);

symbol natAdd [n m: ℕ]: Fin n → Fin m → Fin (n + m) ≔
begin
  assume n m finN finM;
  apply (FinMk (n + m) (val finN));
  have g: π (istrue ((val finN) < (n + m))) → π (istrue ((val finN +1) ≤ (n + m))) {
      refine λ x, x;
  };
  refine g _;
  rewrite addnC;
  refine ltn_addl (val finN) n m (isLt finN);
end;

// Binary logic operators

symbol and n: Fin n → Fin n → Fin n;
rule @and $n (exist $x $px) (exist $y $py) ↪ FinMk $n (($x && $y) % $n) (@modulo_lt ($x && $y) $x $n $px);

symbol or n: Fin n → Fin n → Fin n;
rule @or $n (exist $x $px) (exist $y $py) ↪ FinMk $n (($x ⎪⎪ $y) % $n) (@modulo_lt ($x ⎪⎪ $y) $x $n $px);

symbol diff n: Fin n → Fin n → Fin n;
rule @diff $n (exist $x $px) (exist $y $py) ↪ FinMk $n ((Nat.diff $x $y) % $n) (@modulo_lt (Nat.diff $x $y) $x $n $px);

symbol xor n: Fin n → Fin n → Fin n;
rule @xor $n (exist $x $px) (exist $y $py) ↪ FinMk $n (($x Nat.xor $y) % $n) (@modulo_lt ($x Nat.xor $y) $x $n $px);

require Stdlib.BinNat as BinNat;
open Stdlib.BinNat;

//coerce_rule coerce (Fin $n) BinNat $e ↪ val $n $e;

symbol from_nat (n: ℕ) (v: ℕ) (p: π (0 < n)) : Fin n ≔ begin
  assume n v NeZero_n;
  refine FinMk n (v % n) _;
  refine (@modulo_lt v 0 n NeZero_n);
end;
