// Cartesian product

require open Stdlib.Set Stdlib.Prop;

constant symbol × : Set → Set → Set; notation × infix right 10; // \times

assert a b c ⊢ a × b × c ≡ a × (b × c);

symbol ‚ [a b] : τ a → τ b → τ (a × b); notation ‚ infix right 30;

assert a (x:τ a) b (y:τ b) c (z:τ c) ⊢ x ‚ y ‚ z : τ(a × b × c);
assert x y z ⊢ x ‚ y ‚ z ≡ x ‚ (y ‚ z);

symbol ₁ [a b] : τ(a × b) → τ a; notation ₁ postfix 10;

rule ($x ‚ _)₁ ↪ $x;

symbol ₂ [a b] : τ(a × b) → τ b; notation ₂ postfix 10;

rule (_ ‚ $x)₂ ↪ $x;

[a: Set] (p: τ a → Set) inductive ∫ : TYPE ≔
    existS (x: τ a) : τ (p x) → ∫ p;

[a: Set] (p: τ a → Prop) inductive Σ : TYPE ≔
    exist (x: τ a) : π (p x) → Σ p;

symbol Sigma [a: Set]: (τ a → Prop) → Set;
rule τ (Sigma $p)  ↪ Σ $p;

symbol s₁ [a] [p] (e: @Σ a p): τ a; notation s₁ postfix 10;
rule (exist $x _) s₁ ↪ $x;

symbol s₂ [a] [p] (e: @Σ a p): π (p (e s₁)); notation s₂ postfix 10;
rule (exist $x $prf) s₂ ↪ $prf;

[a: Set] (p: τ a → Set) inductive sigT : TYPE ≔
    exisT (x: τ a) : τ (p x) → sigT p;

symbol st₁ [a] [p] (e: @sigT a p): τ a; notation st₁ postfix 10;
rule (exisT $x _) st₁ ↪ $x;

symbol st₂ [a] [p] (e: @sigT a p): τ (p (e st₁)); notation st₂ postfix 10;
rule (exisT $x $prf) st₂ ↪ $prf;

(a b: Set) inductive ⨥: TYPE ≔
| inl: τ a → ⨥ a b
| inr: τ b → ⨥ a b
;

notation ⨥ infix 10;

symbol Sum: Set → Set → Set;
rule τ (Sum $a $b) ↪ $a ⨥ $b;