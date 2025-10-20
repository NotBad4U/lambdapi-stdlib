// Cartesian product

require open Stdlib.Set Stdlib.Prop Stdlib.Eq;

constant symbol × : Set → Set → Set; notation × infix right 10; // \times

assert a b c ⊢ a × b × c ≡ a × (b × c);

symbol ‚ [a b] : τ a → τ b → τ (a × b); notation ‚ infix right 40;

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
rule τ (@Sigma $a $p)  ↪ @Σ $a $p;

symbol s₁ [a] [p] (e: @Σ a p): τ a; notation s₁ postfix 12;
rule (exist $x _) s₁ ↪ $x;

symbol s₂ [a] [p] (e: @Σ a p): π (p (e s₁)); notation s₂ postfix 12;
rule (exist $x $prf) s₂ ↪ $prf;

//symbol eq_Σ [a: Set] (p: τ a → Prop) (x y: @Σ a p) (h1: π (x s₁ = y s₁)) (q: ind_eq h1 p (x s₂) = y s₂) : π (x = y);

symbol eq_Σ [a: Set] (p: τ a → Prop) (x y: Σ p) (h1: π (x s₁ = y s₁)) : π (x = y);

// Lemma eq_exist_curried {A : Type} {P : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
//              (p : u1 = v1) (q : rew p in u2 = v2) : exist P u1 u2 = exist P v1 v2.

require Stdlib.Impred;

// symbol ⇒d : Π (x: Prop), (π x → Prop) → Prop; notation ⇒d infix 10;
// rule π ($x ⇒d $y) ↪ Π (z: π $x), π ($y z);

// symbol o : Set;

// rule τ o ↪ Prop;

// symbol eq_Σ_curried [a: Set] (p: τ a → Prop) (u1 v1: τ a) (u2: π (p u1)) (v2: π (p v1))
//     (h: π (u1 = v1)) (h2: π (ind_eq h (λ u, (p u = p v1)) (eq_refl (p v1)))) : π ((@exist a p u1 u2) = (@exist a p v1 v2)) ≔
// begin

// end;






// symbol eq_Σ_curried [a: Set] (p: τ a → Prop) (u1 v1: τ a) (u2: π (p u1)) (v2: π (p v1))
//     (h: π (u1 = v1)) (h2: @ind_eq a u1 v1 h (λ u, (p u) = (p v1)) (eq_refl (p v1))) : π ((@exist a p u1 u2) = (@exist a p v1 v2)) ≔
// begin

// end;

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