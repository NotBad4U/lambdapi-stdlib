require open Stdlib.Prop Stdlib.FOL Stdlib.Eq;
require open Stdlib.Set;
require open Stdlib.Nat;
require open Stdlib.Bool; 

// (a :Set) (b :Prop) inductive toto : TYPE ≔
// | □ : toto a b // \Box
// | ⸬ : τ a → π b → toto a b;

symbol ite: Prop → Prop → Prop → Prop;
constant symbol ite_ind : Π c t e p,
                           (π c → π (p t))
                         → ((π c → π ⊥) → π (p e))
                         → π (p (ite c t e));

symbol ⟇: Prop → Prop → Prop;
notation ⟇ infix left 6;
rule $x ⟇ $y ↪ ($x) ∨ ($y);

// Rule 3: ⊤ true
// Is equivalent to "top : π ⊤".

// Rule 13 la_disequality
constant symbol la_disequality t1 t2: π ( t1 = t2 ∨ ¬ ( istrue(t1 ≤ t2) ) ∨ ¬ (istrue(t1 ≤ t2)) );

// Rule 14 la_totality
constant symbol la_totality t1 t2: π ( istrue(t1 ≤ t2) ∨ istrue(t2 ≤ t1) );

constant symbol bind p q: (Π x, π (p x ⇔ q x)) → π ((∀ p) ⇔ (∀ q));

constant symbol bind2 p q: (Π x y , π (p x y ⇔ q x y)) → π ((`∀ a, `∀ b, p a b) ⇔ (`∀ x, `∀ y, q x y));

//TODO: review
constant symbol sko_ex p q: (Π x , π (p x ⇔ q)) → π ((`∃ x, p x) ⇔ q);
constant symbol sko_forall p q: (Π x , π (p x ⇔ q)) → π ((`∀ x, p x) ⇔ q);


constant symbol notnot x : π ( (¬ (¬ (¬ x))) ⟇ x);

// Rule 22 cong version for ⇔
opaque symbol cong_⇔ x y f : π (x = y) → π (f x ⇔ f y) ≔
begin
    assume x y f Hx;
    rewrite Hx;
    apply ⇔_refl;
end;

// Rule 22 cong version for =
opaque symbol cong_= [a] (x y : τ a) (f: τ a → τ a) : π (x = y) → π (f x = f y) ≔
begin
    assume x y f Hf Hx_eq_y;
    rewrite Hx_eq_y;
    reflexivity
end;

opaque symbol =_to_⇔ (x y : τ bool) : π (x = y) → π ((istrue x) ⇔ (istrue y)) ≔
begin
    assume x y Hx_eq_y;
    rewrite Hx_eq_y;
    apply ⇔_refl
end;

// Rule 24 eq_transitive
constant symbol eq_transitive t1 t2 t3 : π ( t1 ⇔ t2 ⟇ t2 ⇔ t3 ⟇ t1 ⇔ t3 );

// Rule 25 eq_congruent
constant symbol eq_congruence t1 t2 u1 u2 f : π ( ¬ (t1 ⇔ u1) ⟇ ¬ (t2 ⇔ u2) ⟇ ( f t1 t2 ⇔ f u1 u2));

// Rule 26 eq_congruent_pred
// where 𝑃 is a function symbol with co-domain sort Bool.
//constant symbol eq_congruence_pred t1 t2 u1 u2 (p: Set → Set → 𝔹) : π ( ¬ (istrue t1 ⇔  istrue u1) ⟇ ¬ (istrue t2 ⇔  istrue u2) ⟇ (istrue(p t1 t2) ⇔ istrue(p u1 u2)));


//Rule 28: and i
// Similar to and ∧ₑ but for i elements

constant symbol equiv_pos1 φ₁ φ₂ : π (¬ (φ₁ ⇔ ¬ φ₂) ⟇ φ₁ ⟇ ¬ φ₂);

constant symbol equiv_pos2 φ₁ φ₂ : π (¬ (φ₁ ⇔ ¬ φ₂) ⟇ ¬ φ₁ ⟇ φ₂);

opaque symbol or_simplify₁ x : π ( x ∨ ⊥ ) → π ( x ) ≔
begin
    assume x HorX;
    apply ∨ₑ HorX 
    { assume Hx; apply Hx; }
    { assume HFalse; apply ⊥ₑ HFalse }
end;

// Rule 56 equiv_neg1
constant symbol equiv_neg1 φ₁ φ₂ : π ((φ₁ ⇔ φ₂) ⟇ ¬ φ₁ ⟇ ¬ φ₂);

// Rule 57
constant symbol equiv_neg2 φ₁ φ₂ : π ((φ₁ ⇔ φ₂) ⟇ φ₁ ⟇ φ₂);

// FIXME: ite1 order of φ₁, φ₃ should be inverse
// Rule 58
constant symbol ite1 φ₁ φ₂ φ₃: π (ite φ₁ φ₂ φ₃) → π (φ₁ ⟇ φ₂);

// Rule 59
constant symbol ite2 φ₁ φ₂ φ₃: π (ite φ₁ φ₂ φ₃) → π (¬ φ₁ ⟇ φ₃);

// Rule 60
constant symbol ite_pos1 φ₁ φ₂ φ₃: π (¬ (ite φ₁ φ₂ φ₃) ⟇ ¬ φ₁ ⟇ φ₃);

// Rule 61
constant symbol ite_pos2 φ₁ φ₂ φ₃: π (¬ (ite φ₁ φ₂ φ₃) ⟇ ¬ φ₁ ⟇ φ₂);

// Rule 62
constant symbol ite_neg1 φ₁ φ₂ φ₃: π (ite φ₁ φ₂ φ₃ ⟇ ¬ φ₁ ⟇ φ₃);

// Rule 63
constant symbol ite_neg2 φ₁ φ₂ φ₃: π (ite φ₁ φ₂ φ₃ ⟇ ¬ φ₁ ⟇ ¬ φ₂);

// Rule 64
constant symbol not_ite1 φ₁ φ₂ φ₃: π (¬ (ite φ₁ φ₂ φ₃)) → π ( φ₁ ⟇ ¬ φ₃);

// Rule 65
constant symbol not_ite2 φ₁ φ₂ φ₃: π (¬ (ite φ₁ φ₂ φ₃)) → π ( ¬ φ₁ ⟇ ¬ φ₂);

// Rule cannot be given on defined symbol
// QUESTION: Should we unroll the definition and do the rewrite rule on it ?
//rule ¬ (¬ $x) ↪ $x;

// rule 72 bool_simplify
//rule ($x ⇒ $y) ⇒ ⊥ ↪ ($x ∧ ¬ $y);


// QUESTION: ask if we can remove the `constant` for disjunction, or
// we can not implement or_simplify with rewriting rules.
// Rule 68:  or_simplify
//  ⊥ ∨ ⋯ ∨ ⊥ ⇒ ⊥
// rule ⊥ ∨ ⊥ ↪ ⊥;

// compute ⊥ ∨ ⊥ ∨ ⊥ ∨ ⊥;


// // 𝜑1 ∨ ⋯ ∨ 𝜑𝑛 ⇒ 𝜑1 ∨ ⋯ ∨ 𝜑𝑛′ where the right-hand side has all ⊥ literals removed.
// rule $x ∨ ⊥ ↪ $x;

// compute  ⊤ ∨ ⊥ ∨ ⊥ ∨ ⊥ ∨ ⊥;

// // 𝜑1 ∨ ⋯ ∨ 𝜑𝑛 ⇒ 𝜑1 ∨ ⋯ ∨ 𝜑𝑛′ where the right-hand side has all repeated literals removed.
// rule $x ∨ $x ↪ $x;
// rule $x ∨ $y ∨ $x ↪ $x ∨ $y;
// rule $x ∨ $y ∨ $z ∨ $x ↪ $x ∨ $y ∨ $z;

// // 𝜑1 ∨ ⋯ ∨ ⊤ ∨ ⋯ ∨ 𝜑𝑛 ⇒ ⊤
// rule $x ∨ ⊤ ↪ ⊤;

// compute  ⊥ ∨ ⊥ ∨ ⊥ ∨ ⊥ ∨ ⊤ ;

// Rule 69: not_simplify


// Rul 74: ite_simplify 
rule ite ⊤ $t1 $t2 ↪ $t1
with ite ⊥ $t1 $t2 ↪ $t2
with ite $c $t $t ↪ $t
with ite (¬ $c) $t1 $t2  ↪ ite $c $t2 $t1
with ite $c (ite $c $t1 $t2) $t3 ↪ ite $c $t1 $t3
with ite $c $t1 (ite $c $t2 $t3) ↪ ite $c $t1 $t3
with ite $c ⊤ ⊥ ↪ $c
with ite $c ⊥ ⊤  ↪ ¬ $c
with ite $x ⊤ $y ↪ $x ∨ $y
with ite $x $y ⊥ ↪ $x ∧ $y
with ite $x ⊥ $y ↪ (¬ $x) ∧ $y
with ite $x $y ⊤  ↪ (¬ $x) ∨ $y;



opaque symbol resolutionₗ x a b: π (x ∨ a) → π ((¬ x) ∨ b) → π (a ∨ b) ≔
begin
    assume x a b ClauseXA ClauseNotXB;
    apply ∨ₑ ClauseXA
    {
        assume Hx;
        apply ∨ₑ ClauseNotXB
        { assume Hnotx; apply ¬ₑ Hnotx Hx }
        { assume Hb; apply ∨ᵢ₂ Hb }
    }
    { assume Ha; apply ∨ᵢ₁ Ha };
end;

opaque symbol resolutionᵣ x a b: π (a ∨ x) → π (b ∨ (¬ x)) → π (a ∨ b) ≔
begin
    assume x a b ClauseAX ClauseBNotX;
    apply resolutionₗ x a b (∨_com ClauseAX) (∨_com ClauseBNotX)
end;
