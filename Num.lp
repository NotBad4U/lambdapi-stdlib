require open Stdlib.Set Stdlib.Prod Stdlib.Nat Stdlib.Z Stdlib.Bool Stdlib.HOL;

symbol + [a: Set] : τ a → τ a → τ a;
rule (@+ nat) ↪ (Stdlib.Nat.+)
with (@+ int) ↪ (Stdlib.Z.+);

notation + infix right 20;

assert ⊢ (Stdlib.Nat._10 + Stdlib.Nat._10): ℕ;
assert ⊢ (12 + 10): ℤ;

