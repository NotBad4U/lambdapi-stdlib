require open Stdlib.Set;

symbol ⤳ : Set → Set → Set; // \leadsto

notation ⤳ infix right 20;

rule τ ($x ⤳ $y) ↪ τ $x → τ $y;

symbol ∘ [a b c] : τ (b ⤳ c) → τ (a ⤳ b) → τ a → τ c ≔ λ g f x, g (f x);
notation ∘ infix 20;
