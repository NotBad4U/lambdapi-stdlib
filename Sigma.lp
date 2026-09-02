// Cartesian product

//require open Stdlib.Eq Stdlib.Impred;
constant symbol Set : TYPE;

builtin "Set" ≔ Set;

// Interpretation of set codes in TYPE

injective symbol τ : Set → TYPE; // `t or \tau

constant symbol Prop : TYPE;

builtin "Prop" ≔ Prop;

builtin "El" ≔ τ;

// interpretation of propositions in TYPE

injective symbol π : Prop → TYPE; // `p

builtin "Prf" ≔ π;

symbol o : Set;

rule τ o ↪ Prop;


constant symbol = [a] : τ a → τ a → Prop;

notation = infix 10;

constant symbol eq_refl [a] (x:τ a) : π (x = x);
constant symbol ind_eq [a] [x y:τ a] : π (x = y) → Π p, π (p y) → π (p x);

builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

// Sigma type with predicate in Prop (equivalent to `sig` in Coq).
[a: Set] (p: τ a → Prop) inductive Σ : TYPE ≔
    exist (x: τ a) : π (p x) → Σ p;

// code name
symbol Sigma [a: Set]: (τ a → Prop) → Set;
rule τ (Sigma $p)  ↪ Σ $p;

// first projection
symbol s₁ [a] [p] (e: @Σ a p): τ a; notation s₁ postfix 12;
rule (exist $x _) s₁ ↪ $x;

// second projection
symbol s₂ [a] [p] (e: @Σ a p): π (p (e s₁)); notation s₂ postfix 12;
rule (exist $x $prf) s₂ ↪ $prf;

symbol prf: Prop → Set;

rule τ (prf $p) ↪ π $p;


// Maybe necessary ?
// symbol ⇒d : Π (x: Prop), (π x → Prop) → Prop; notation ⇒d infix 10;
// rule π ($x ⇒d $y) ↪ Π (z: π $x), π ($y z);

// How to replicate this theorem ?
// Lemma eq_exist_curried {A : Type} {P : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
//              (p : u1 = v1) (q : rew p in u2 = v2) : exist P u1 u2 = exist P v1 v2.

// symbol eq_Σ_curried [a: Set] (p: τ a → Prop) (u1 v1: τ a) (u2: τ (prf (p u1))) (v2: τ (prf (p v1)))
//     (h: π (u1 = v1)) (h2: π (ind_eq h p v2 = u2)) : π (@exist a p u1 u2 = @exist a p v1 v2) ≔
// begin
//     assume a P u1 v1 u2 v2 heq_u1v1 heq_u2v2;
    
// end;

