require open Stdlib.Set Stdlib.Nat Stdlib.Prop;

(a : Set) inductive Vector : ℕ → TYPE ≔
| Vnil  : Vector a 0
| Vcons : Π (n : ℕ), τ a → Vector a n → Vector a (n +1);

