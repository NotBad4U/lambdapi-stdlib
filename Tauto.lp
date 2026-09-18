/*
    This file provides the tactic #tauto, a proof search for intuitionistic
    propositional calculus following Dyckhoff's contraction-free sequent
    calculus LJT.

      R. Dyckhoff, "Contraction-free sequent calculi for intuitionistic logic",
      Journal of Symbolic Logic 57(3), 1992.

    The search is reflective: the goal is reified into the datatype `prop`,
    a boolean `prove` decides provability by rewriting, and `prove_sound`
    turns a successful search into a proof term.

    `prove` is *not* structurally recursive (the left rules rebuild the
    context), and LJT's termination argument uses a multiset ordering that is
    not formalised here. We therefore bound the search depth by a fuel
    argument: the procedure is sound, and complete for LJT-derivable sequents
    provided the fuel suffices.
*/
require open Stdlib.Impred;
require open Stdlib.FOL;
require open Stdlib.Nat;
require open Stdlib.List;
require open Stdlib.Prod;
require open Stdlib.Tactic;

inductive prop: TYPE ≔
| pTrue: prop
| pFalse: prop
| pAnd: prop → prop → prop
| pOr: prop → prop → prop
| pImpl: prop → prop → prop
| pOther: ℕ → prop
;

symbol pNot p ≔ pImpl p pFalse;

symbol pIff p q ≔ pAnd (pImpl p q) (pImpl q p);

symbol propS: Set;

rule τ propS ↪ prop;


symbol not_found: Prop; // Just a simple opaque definition to represent an error message.

// A denotation function converts our syntax into a semantic value
// The σ is the context which contains the mapping from variables to Props.
symbol propD (σ: 𝕃 o) (p: prop): Prop;
rule propD _ pTrue ↪ ⊤
with propD _ pFalse ↪ ⊥
with propD $ctx (pAnd $x $y) ↪  (propD $ctx $x) ∧ (propD $ctx $y)
with propD $ctx (pOr $x $y) ↪  (propD $ctx $x) ∨ (propD $ctx $y)
with propD $ctx (pImpl $x $y) ↪  (propD $ctx $x) ⇒ (propD $ctx $y)
with propD $ctx (pOther $i) ↪ nth not_found $ctx $i;

private symbol a: Prop;
private symbol b: Prop;
private symbol f: Prop → Prop;

type (a ⸬ f b ⸬ b ⸬ □);

private symbol ctx ≔ (a ⸬ f b ⸬ b ⸬ □);

assert ⊢ propD ctx (pOther 0) ≡ a;
assert ⊢ propD ctx (pOther 1) ≡ f b;
assert ⊢ propD ctx (pOther 2) ≡ b;
assert ⊢ propD ctx (pOther 3) ≡ not_found;

// The prover only ever looks up ⊥ and atoms in the context.

symbol is_false : prop → 𝔹;
rule is_false pFalse ↪ true
with is_false pTrue ↪ false
with is_false (pAnd _ _) ↪ false
with is_false (pOr _ _) ↪ false
with is_false (pImpl _ _) ↪ false
with is_false (pOther _) ↪ false;

symbol is_var : ℕ → prop → 𝔹;
rule is_var $i (pOther $j) ↪ eqn $i $j
with is_var _ pTrue ↪ false
with is_var _ pFalse ↪ false
with is_var _ (pAnd _ _) ↪ false
with is_var _ (pOr _ _) ↪ false
with is_var _ (pImpl _ _) ↪ false;

symbol knows_false : 𝕃 propS → 𝔹 ≔ has is_false;

symbol knows_var (i: ℕ) : 𝕃 propS → 𝔹 ≔ has (is_var i);

symbol All: 𝕃 propS → prop ≔ foldr (pAnd) pTrue;

///////////////////////////////////////////////////////////////////////////////
// Proof search (LJT)
///////////////////////////////////////////////////////////////////////////////

/* `prove n Γ g` decides the sequent Γ ⊢ g with at most `n` non-trivial steps.

   The search alternates two phases:

   - `prove` applies the *right* rules. ⊤R, ∧R and ⇒R are invertible, so they
     commit. ∨R, the axioms and ⊥L are not enough on their own, so an atomic,
     absurd or disjunctive goal falls through to the left phase.

   - `scan n done todo g` walks the context looking for a left rule to apply.
     `done` holds the hypotheses already visited, `todo` those still to visit;
     the context of the sequent is `done ++ todo`. The invertible left rules
     (⊥L, ⊤L, ∧L, ∨L, and the ⇒-left rules whose antecedent is ⊤, ⊥, ∧ or ∨)
     commit as soon as they are found. The two non-invertible ones —
     ⇒L on an atomic antecedent, and Dyckhoff's ⇒L on an implicative
     antecedent — are tried and, on failure, the scan resumes with the
     hypothesis parked in `done`.

   The principal formula is always *removed* from the context, which is what
   makes the calculus contraction-free: no hypothesis is ever duplicated. */

symbol prove (fuel: ℕ):  𝕃 propS → prop → 𝔹;

symbol scan (fuel: ℕ): 𝕃 propS → 𝕃 propS → prop → 𝔹;

rule prove _0 _ _ ↪ false
// ⊤R
with prove (_ +1) _ pTrue ↪ true
// ∧R and ⇒R are invertible
with prove ($n +1) $Γ (pAnd $x $y) ↪
  let l ≔ prove $n $Γ $x in
  let r ≔ prove $n $Γ $y in
  l and r
with prove ($n +1) $Γ (pImpl $x $y) ↪ prove $n ($x ⸬ $Γ) $y
// axiom, then the left rules
with prove ($n +1) $Γ (pOther $i) ↪
  let in_context ≔ knows_var $i $Γ in
  let by_left_rules ≔ scan $n □ $Γ (pOther $i) in
  in_context or by_left_rules
// ⊥L, then the left rules
with prove ($n +1) $Γ pFalse ↪
  let in_context ≔ knows_false $Γ in
  let by_left_rules ≔ scan $n □ $Γ pFalse in
  in_context or by_left_rules
// ∨R is not invertible: try both disjuncts, then the left rules
with prove ($n +1) $Γ (pOr $x $y) ↪
  let l ≔ prove $n $Γ $x in
  let r ≔ prove $n $Γ $y in
  let by_left_rules ≔ scan $n □ $Γ (pOr $x $y) in
  l or (r or by_left_rules);

rule scan _ _ □ _ ↪ false
// ⊥L
with scan _ _ (pFalse ⸬ _) _ ↪ true
// ⊤L : a trivial hypothesis is dropped
with scan $n $done (pTrue ⸬ $t) $g ↪ prove $n ($done ++ $t) $g
// ∧L
with scan $n $done (pAnd $x $y ⸬ $t) $g ↪
  prove $n ($x ⸬ $y ⸬ ($done ++ $t)) $g
// ∨L : invertible, but branching
with scan $n $done (pOr $x $y ⸬ $t) $g ↪
  let Γ ≔ $done ++ $t in
  let l ≔ prove $n ($x ⸬ Γ) $g in
  let r ≔ prove $n ($y ⸬ Γ) $g in
  l and r
// ⊤⇒ : ⊤ ⇒ C gives C
with scan $n $done (pImpl pTrue $c ⸬ $t) $g ↪ prove $n ($c ⸬ ($done ++ $t)) $g
// ⊥⇒ : ⊥ ⇒ C is useless
with scan $n $done (pImpl pFalse _ ⸬ $t) $g ↪ prove $n ($done ++ $t) $g
// ∧⇒ : currying
with scan $n $done (pImpl (pAnd $x $y) $c ⸬ $t) $g ↪
  prove $n (pImpl $x (pImpl $y $c) ⸬ ($done ++ $t)) $g
// ∨⇒ : splitting
with scan $n $done (pImpl (pOr $x $y) $c ⸬ $t) $g ↪
  prove $n (pImpl $x $c ⸬ pImpl $y $c ⸬ ($done ++ $t)) $g
// atom⇒ : fires only when the antecedent is already known
with scan $n $done (pImpl (pOther $i) $c ⸬ $t) $g ↪
  let Γ ≔ $done ++ $t in
  let antecedent ≔ knows_var $i Γ in
  let consequent ≔ prove $n ($c ⸬ Γ) $g in
  let resume ≔ scan $n (pImpl (pOther $i) $c ⸬ $done) $t $g in
  (antecedent and consequent) or resume
// ⇒⇒ : Dyckhoff's rule, the replacement for contraction on (X ⇒ Y) ⇒ C
with scan $n $done (pImpl (pImpl $x $y) $c ⸬ $t) $g ↪
  let Γ ≔ $done ++ $t in
  let antecedent ≔ prove $n (pImpl $y $c ⸬ Γ) (pImpl $x $y) in
  let consequent ≔ prove $n ($c ⸬ Γ) $g in
  let resume ≔ scan $n (pImpl (pImpl $x $y) $c ⸬ $done) $t $g in
  (antecedent and consequent) or resume
// an atomic hypothesis carries no left rule: park it
with scan $n $done (pOther $i ⸬ $t) $g ↪ scan $n (pOther $i ⸬ $done) $t $g;

// Search depth granted to `prove`. Every rule application removes a connective
// from the sequent except ⇒⇒, which duplicates the antecedent of the principal
// implication, so the number of connectives is not a bound: we take its square.
symbol weight : prop → ℕ;
rule weight pTrue ↪ _0 +1
with weight pFalse ↪ _0 +1
with weight (pOther _) ↪ _0 +1
with weight (pAnd $x $y) ↪ (weight $x + weight $y) +1
with weight (pOr $x $y) ↪ (weight $x + weight $y) +1
with weight (pImpl $x $y) ↪ (weight $x + weight $y) +1;

symbol fuel (g : prop) : ℕ ≔ weight g * weight g;

assert ⊢ prove 20 ((pOther 0) ⸬ □) (pAnd (pOther 0) pTrue) ≡ true;
assertnot ⊢ prove 20 ((pOther 0) ⸬ □) (pAnd (pOther 0) pFalse) ≡ true;
// the left rules LJT adds, on the sequents the previous version could not do
assert ⊢ prove 20 (pOr (pOther 0) (pOther 1) ⸬ □) (pOr (pOther 1) (pOther 0)) ≡ true;
assert ⊢ prove 20 (pImpl (pOther 0) (pOther 1) ⸬ pOther 0 ⸬ □) (pOther 1) ≡ true;
// Peirce's law is classical: it must *not* be found
assertnot ⊢ prove 40 □
  (pImpl (pImpl (pImpl (pOther 0) (pOther 1)) (pOther 0)) (pOther 0)) ≡ true;

///////////////////////////////////////////////////////////////////////////////
// Soundness
///////////////////////////////////////////////////////////////////////////////

opaque symbol is_false_sound (σ: 𝕃 o) (p: prop) : π (is_false p) → π (propD σ p) → π ⊥ ≔
begin
    assume σ;
    induction
    { assume h d; apply ⊥ₑ h }
    { assume h d; apply d }
    { assume x ihx y ihy h d; apply ⊥ₑ h }
    { assume x ihx y ihy h d; apply ⊥ₑ h }
    { assume x ihx y ihy h d; apply ⊥ₑ h }
    { assume j h d; apply ⊥ₑ h }
end;

opaque symbol is_var_sound (σ: 𝕃 o) (i: ℕ) (p: prop) : π (is_var i p) → π (propD σ p) → π (nth not_found σ i) ≔
begin
    assume σ i;
    induction
    { assume h d; apply ⊥ₑ h }
    { assume h d; apply ⊥ₑ h }
    { assume x ihx y ihy h d; apply ⊥ₑ h }
    { assume x ihx y ihy h d; apply ⊥ₑ h }
    { assume x ihx y ihy h d; apply ⊥ₑ h }
    { assume j h d; rewrite eqn_correct i j h; apply d }
end;

opaque symbol knows_false_sound (σ: 𝕃 o) (c: 𝕃 propS) : π (knows_false c) → π (propD σ (All c)) → π ⊥ ≔
begin
    assume σ;
    induction
    { assume h d; apply h }
    { assume p c ih h d;
      have e: π (is_false p ∨ knows_false c) { refine ∨_has is_false p c h };
      apply ∨ₑ e
      { assume hp; apply is_false_sound σ p hp (∧ₑ₁ d) }
      { assume hc; apply ih hc (∧ₑ₂ d) }
    }
end;

opaque symbol knows_var_sound (σ: 𝕃 o) (i: ℕ) (c: 𝕃 propS) : π (knows_var i c) → π (propD σ (All c)) → π (nth not_found σ i) ≔
begin
    assume σ i;
    induction
    { assume h d; apply ⊥ₑ h }
    { assume p c ih h d;
      have e: π (is_var i p ∨ knows_var i c) { refine ∨_has (is_var i) p c h };
      apply ∨ₑ e
      { assume hp; apply is_var_sound σ i p hp (∧ₑ₁ d) }
      { assume hc; apply ih hc (∧ₑ₂ d) }
    }
end;

// The context of a sequent being scanned is `done ++ (p ⸬ todo)`: singling out
// the hypothesis under focus is the only context surgery the proofs need.
opaque symbol All_split (σ: 𝕃 o) (p: prop) (t: 𝕃 propS) :
  Π (done: 𝕃 propS),
    π (propD σ (All (done ++ (p ⸬ t)))) →
    π (propD σ p ∧ propD σ (All (done ++ t))) ≔
begin
  assume σ p t;
  induction
  { assume d; refine ∧ᵢ (∧ₑ₁ d) (∧ₑ₂ d) }
  { assume q done ih d;
    have e: π (propD σ p ∧ propD σ (All (done ++ t))) { refine ih (∧ₑ₂ d) };
    refine ∧ᵢ (∧ₑ₁ e) (∧ᵢ (∧ₑ₁ d) (∧ₑ₂ e))
  }
end;

/* The soundness of the two phases is mutual, and the recursion that ties them
   is the one on the fuel. We break the knot by making the induction hypothesis
   on `prove` an explicit argument of the `scan` lemmas. */

// The ⇒-left rules, one lemma per shape of the antecedent. Only the last one
// is not immediate: it is the semantic content of Dyckhoff's ⇒⇒ rule.
opaque symbol and_imp [X Y C : Prop] : π ((X ∧ Y) ⇒ C) → π (X ⇒ Y ⇒ C) ≔
begin
  assume X Y C h x y; refine h (∧ᵢ x y)
end;

opaque symbol or_imp₁ [X Y C : Prop] : π ((X ∨ Y) ⇒ C) → π (X ⇒ C) ≔
begin
  assume X Y C h x; refine h (∨ᵢ₁ x)
end;

opaque symbol or_imp₂ [X Y C : Prop] : π ((X ∨ Y) ⇒ C) → π (Y ⇒ C) ≔
begin
  assume X Y C h y; refine h (∨ᵢ₂ y)
end;

opaque symbol imp_imp_left [X Y C : Prop] :
  π ((X ⇒ Y) ⇒ C) → π ((Y ⇒ C) ⇒ (X ⇒ Y)) → π C ≔
begin
  assume X Y C h k; refine h (k (λ y, h (λ _, y)))
end;

// `scan` on a hypothesis of the form `pImpl x c`, by cases on `x`.
opaque symbol scan_imp_sound (σ: 𝕃 o) (n: ℕ)
  (IH: Π (g: prop) (Γ: 𝕃 propS),
         π (prove n Γ g) → π (propD σ (All Γ)) → π (propD σ g))
  (g: prop) (t: 𝕃 propS)
  (IHt: Π (done: 𝕃 propS),
          π (scan n done t g) → π (propD σ (All (done ++ t))) → π (propD σ g))
  (c: prop) :
  Π (x: prop) (done: 𝕃 propS),
    π (scan n done (pImpl x c ⸬ t) g) →
    π (propD σ (All (done ++ (pImpl x c ⸬ t)))) →
    π (propD σ g) ≔
begin
  assume σ n IH g t IHt c;
  induction
  // x = pTrue : ⊤ ⇒ C gives C
  { assume done h d;
    have e: π (propD σ (pImpl pTrue c) ∧ propD σ (All (done ++ t)))
      { refine All_split σ (pImpl pTrue c) t done d };
    refine IH g (c ⸬ (done ++ t)) h (∧ᵢ (∧ₑ₁ e ⊤ᵢ) (∧ₑ₂ e))
  }
  // x = pFalse : the hypothesis is useless
  { assume done h d;
    have e: π (propD σ (pImpl pFalse c) ∧ propD σ (All (done ++ t)))
      { refine All_split σ (pImpl pFalse c) t done d };
    refine IH g (done ++ t) h (∧ₑ₂ e)
  }
  // x = pAnd u v : currying
  { assume u ihu v ihv done h d;
    have e: π (propD σ (pImpl (pAnd u v) c) ∧ propD σ (All (done ++ t)))
      { refine All_split σ (pImpl (pAnd u v) c) t done d };
    refine IH g (pImpl u (pImpl v c) ⸬ (done ++ t)) h
      (∧ᵢ (and_imp (∧ₑ₁ e)) (∧ₑ₂ e))
  }
  // x = pOr u v : splitting
  { assume u ihu v ihv done h d;
    have e: π (propD σ (pImpl (pOr u v) c) ∧ propD σ (All (done ++ t)))
      { refine All_split σ (pImpl (pOr u v) c) t done d };
    refine IH g (pImpl u c ⸬ pImpl v c ⸬ (done ++ t)) h
      (∧ᵢ (or_imp₁ (∧ₑ₁ e)) (∧ᵢ (or_imp₂ (∧ₑ₁ e)) (∧ₑ₂ e)))
  }
  // x = pImpl u v : Dyckhoff's rule
  { assume u ihu v ihv done h d;
    have e: π (propD σ (pImpl (pImpl u v) c) ∧ propD σ (All (done ++ t)))
      { refine All_split σ (pImpl (pImpl u v) c) t done d };
    have s: π ((prove n (pImpl v c ⸬ (done ++ t)) (pImpl u v)
                and prove n (c ⸬ (done ++ t)) g)
               ∨ scan n (pImpl (pImpl u v) c ⸬ done) t g)
      { refine ∨_istrue h };
    apply ∨ₑ s
    { assume hl;
      have p: π (prove n (pImpl v c ⸬ (done ++ t)) (pImpl u v)
                 ∧ prove n (c ⸬ (done ++ t)) g)
        { refine ∧_istrue hl };
      have k: π ((propD σ v ⇒ propD σ c) ⇒ (propD σ u ⇒ propD σ v))
        { assume hv;
          refine IH (pImpl u v) (pImpl v c ⸬ (done ++ t)) (∧ₑ₁ p)
            (∧ᵢ hv (∧ₑ₂ e)) };
      refine IH g (c ⸬ (done ++ t)) (∧ₑ₂ p)
        (∧ᵢ (imp_imp_left (∧ₑ₁ e) k) (∧ₑ₂ e))
    }
    { assume hr;
      refine IHt (pImpl (pImpl u v) c ⸬ done) hr (∧ᵢ (∧ₑ₁ e) (∧ₑ₂ e))
    }
  }
  // x = pOther i : the rule fires only if the atom is known
  { assume i done h d;
    have e: π (propD σ (pImpl (pOther i) c) ∧ propD σ (All (done ++ t)))
      { refine All_split σ (pImpl (pOther i) c) t done d };
    have s: π ((knows_var i (done ++ t) and prove n (c ⸬ (done ++ t)) g)
               ∨ scan n (pImpl (pOther i) c ⸬ done) t g)
      { refine ∨_istrue h };
    apply ∨ₑ s
    { assume hl;
      have p: π (knows_var i (done ++ t) ∧ prove n (c ⸬ (done ++ t)) g)
        { refine ∧_istrue hl };
      have ha: π (nth not_found σ i)
        { refine knows_var_sound σ i (done ++ t) (∧ₑ₁ p) (∧ₑ₂ e) };
      refine IH g (c ⸬ (done ++ t)) (∧ₑ₂ p) (∧ᵢ (∧ₑ₁ e ha) (∧ₑ₂ e))
    }
    { assume hr;
      refine IHt (pImpl (pOther i) c ⸬ done) hr (∧ᵢ (∧ₑ₁ e) (∧ₑ₂ e))
    }
  }
end;

// `scan` on the first hypothesis of `todo`, by cases on it.
opaque symbol scan_cons_sound (σ: 𝕃 o) (n: ℕ)
  (IH: Π (g: prop) (Γ: 𝕃 propS),
         π (prove n Γ g) → π (propD σ (All Γ)) → π (propD σ g))
  (g: prop) (t: 𝕃 propS)
  (IHt: Π (done: 𝕃 propS),
          π (scan n done t g) → π (propD σ (All (done ++ t))) → π (propD σ g)) :
  Π (p: prop) (done: 𝕃 propS),
    π (scan n done (p ⸬ t) g) →
    π (propD σ (All (done ++ (p ⸬ t)))) →
    π (propD σ g) ≔
begin
  assume σ n IH g t IHt;
  induction
  // p = pTrue : dropped
  { assume done h d;
    have e: π (propD σ pTrue ∧ propD σ (All (done ++ t)))
      { refine All_split σ pTrue t done d };
    refine IH g (done ++ t) h (∧ₑ₂ e)
  }
  // p = pFalse : ⊥L closes the branch
  { assume done h d;
    have e: π (propD σ pFalse ∧ propD σ (All (done ++ t)))
      { refine All_split σ pFalse t done d };
    apply ⊥ₑ (∧ₑ₁ e)
  }
  // p = pAnd u v
  { assume u ihu v ihv done h d;
    have e: π (propD σ (pAnd u v) ∧ propD σ (All (done ++ t)))
      { refine All_split σ (pAnd u v) t done d };
    refine IH g (u ⸬ v ⸬ (done ++ t)) h
      (∧ᵢ (∧ₑ₁ (∧ₑ₁ e)) (∧ᵢ (∧ₑ₂ (∧ₑ₁ e)) (∧ₑ₂ e)))
  }
  // p = pOr u v : both branches must succeed
  { assume u ihu v ihv done h d;
    have e: π (propD σ (pOr u v) ∧ propD σ (All (done ++ t)))
      { refine All_split σ (pOr u v) t done d };
    have p: π (prove n (u ⸬ (done ++ t)) g ∧ prove n (v ⸬ (done ++ t)) g)
      { refine ∧_istrue h };
    apply ∨ₑ (∧ₑ₁ e)
    { assume hu; refine IH g (u ⸬ (done ++ t)) (∧ₑ₁ p) (∧ᵢ hu (∧ₑ₂ e)) }
    { assume hv; refine IH g (v ⸬ (done ++ t)) (∧ₑ₂ p) (∧ᵢ hv (∧ₑ₂ e)) }
  }
  // p = pImpl u v : delegated
  { assume u ihu v ihv done h d;
    refine scan_imp_sound σ n IH g t IHt v u done h d
  }
  // p = pOther i : parked
  { assume i done h d;
    have e: π (propD σ (pOther i) ∧ propD σ (All (done ++ t)))
      { refine All_split σ (pOther i) t done d };
    refine IHt (pOther i ⸬ done) h (∧ᵢ (∧ₑ₁ e) (∧ₑ₂ e))
  }
end;

// The left phase, by induction on the hypotheses still to visit.
opaque symbol scan_sound (σ: 𝕃 o) (n: ℕ)
  (IH: Π (g: prop) (Γ: 𝕃 propS),
         π (prove n Γ g) → π (propD σ (All Γ)) → π (propD σ g))
  (g: prop) :
  Π (todo done: 𝕃 propS),
    π (scan n done todo g) →
    π (propD σ (All (done ++ todo))) →
    π (propD σ g) ≔
begin
  assume σ n IH g;
  induction
  { assume done h d; apply ⊥ₑ h }
  { assume p t IHt done h d;
    refine scan_cons_sound σ n IH g t IHt p done h d
  }
end;

// The right phase, by induction on the fuel.
opaque symbol prove_sound (σ: 𝕃 o) :
  Π (n: ℕ) (g: prop) (Γ: 𝕃 propS),
    π (prove n Γ g) → π (propD σ (All Γ)) → π (propD σ g) ≔
begin
  assume σ;
  induction
  // no fuel left
  { assume g Γ h d; apply ⊥ₑ h }
  { assume n IH;
    induction
    // ⊤R
    { assume Γ h d; apply ⊤ᵢ }
    // ⊥ goal: ⊥L or the left rules
    { assume Γ h d;
      have s: π (knows_false Γ ∨ scan n □ Γ pFalse) { refine ∨_istrue h };
      apply ∨ₑ s
      { assume hl; apply knows_false_sound σ Γ hl d }
      { assume hr; refine scan_sound σ n IH pFalse Γ □ hr d }
    }
    // ∧R
    { assume x ihx y ihy Γ h d;
      have p: π (prove n Γ x ∧ prove n Γ y) { refine ∧_istrue h };
      refine ∧ᵢ (IH x Γ (∧ₑ₁ p) d) (IH y Γ (∧ₑ₂ p) d)
    }
    // ∨R, then the left rules
    { assume x ihx y ihy Γ h d;
      have s: π (prove n Γ x ∨ (prove n Γ y or scan n □ Γ (pOr x y)))
        { refine ∨_istrue h };
      apply ∨ₑ s
      { assume hx; apply ∨ᵢ₁; refine IH x Γ hx d }
      { assume h2;
        have s2: π (prove n Γ y ∨ scan n □ Γ (pOr x y)) { refine ∨_istrue h2 };
        apply ∨ₑ s2
        { assume hy; apply ∨ᵢ₂; refine IH y Γ hy d }
        { assume hs; refine scan_sound σ n IH (pOr x y) Γ □ hs d }
      }
    }
    // ⇒R
    { assume x ihx y ihy Γ h d;
      assume hx; refine IH y (x ⸬ Γ) h (∧ᵢ hx d)
    }
    // atomic goal: axiom or the left rules
    { assume i Γ h d;
      have s: π (knows_var i Γ ∨ scan n □ Γ (pOther i)) { refine ∨_istrue h };
      apply ∨ₑ s
      { assume hl; apply knows_var_sound σ i Γ hl d }
      { assume hr; refine scan_sound σ n IH (pOther i) Γ □ hr d }
    }
  }
end;

///////////////////////////////////////////////////////////////////////////////
// Reification
///////////////////////////////////////////////////////////////////////////////

constant symbol R : TYPE;
constant symbol Index : ℕ → R;
constant symbol New : ℕ → R;

protected symbol case [a] : R → (ℕ → τ a) → (ℕ → τ a) → τ a;
rule case (Index $i) $f _ ↪ $f $i
with case (New $i) _ $g ↪ $g $i;

protected sequential symbol index: ℕ → Π [a], τ a → τ(list a) → R;
rule index $k _ □ ↪ New $k
with index $k $x ($x ⸬ _) ↪ Index $k // Here is the magic...
with index $k $x ($y ⸬ $l) ↪ index ($k +1) $x $l;

protected sequential symbol propReify: (𝕃 o) →  Prop → τ (propS × (list o));
rule propReify $ctx ⊤ ↪ (pTrue ‚ $ctx)
with propReify $ctx ⊥ ↪ (pFalse ‚ $ctx)
with propReify $ctx ($x ∧ $y) ↪ let res1 ≔  (propReify $ctx $x) in
                                let res2 ≔  (propReify (res1 ₂) $y) in
                                (pAnd (res1 ₁) (res2 ₁) ‚ (res2 ₂))
with propReify $ctx ($x ∨ $y) ↪ let res1 ≔  (propReify $ctx $x) in
                                let res2 ≔  (propReify (res1 ₂) $y) in
                                (pOr (res1 ₁) (res2 ₁) ‚ (res2 ₂))
with propReify $ctx ($x ⇒ ⊥) ↪ let res ≔  (propReify $ctx $x) in
                                (pNot (res ₁)‚ (res ₂))
with propReify $ctx ($x ⇒ $y) ↪ let res1 ≔  (propReify $ctx $x) in
                                let res2 ≔  (propReify (res1 ₂) $y) in
                                (pImpl (res1 ₁) (res2 ₁) ‚ (res2 ₂))
with propReify $ctx ($x ⇔ $y) ↪ let res1 ≔  (propReify $ctx $x) in
                                let res2 ≔  (propReify (res1 ₂) $y) in
                                (pIff (res1 ₁) (res2 ₁) ‚ (res2 ₂))
with propReify $ctx $x ↪
    case (index _0 $x $ctx) (λ i, pOther i ‚ $ctx) (λ i, pOther i ‚ ($ctx ++ ($x ⸬ □)));

protected symbol reify goal ≔ propReify □ goal;

symbol tauto_aux [goal] ≔
  let res ≔ reify goal in prove_sound (res ₂) (fuel (res ₁)) (res ₁) □;

symbol #tauto ≔ #refine "(tauto_aux ⊤ᵢ ⊤ᵢ)";

///////////////////////////////////////////////////////////////////////////////
// Examples
///////////////////////////////////////////////////////////////////////////////

// Purely propositional goal
private symbol example_prop (a b c d e g : Prop) :
  π ((a ∧ b) ∧ (c ∧ ⊤) ∧ d
     ⇒ (d ∧ (c ∧ a)) ∧ (e ∨ (g ∨ b)) ∧ (e ∧ g ⇒ (g ∧ b) ∧ (⊥ ∨ e))) ≔
begin assume a b c d e g; eval #tauto; end;

// Non-propositional formulas are abstracted as atoms, identified up to conversion.
private symbol example_atoms (x y z : ℕ) (p : ℕ → Prop) :
  π ((x ≤ y ∧ 2 + 1 ≤ z) ∧ (`∀ n, p n) ∧ x + y = z
     ⇒ ((x = z ∨ x + y = z) ∧ 3 ≤ z) ∧ ((`∃ n, p n) ⇒ (`∀ n, p n) ∧ x ≤ y)) ≔
begin assume x y z p; eval #tauto; end;

// The left rules: none of these were provable before.
private symbol example_or_left (a b : Prop) : π (a ∨ b ⇒ b ∨ a) ≔
begin assume a b; eval #tauto; end;

private symbol example_modus_ponens (a b : Prop) : π ((a ⇒ b) ⇒ a ⇒ b) ≔
begin assume a b; eval #tauto; end;

private symbol example_chain (a b c : Prop) :
  π ((a ⇒ b) ∧ (b ⇒ c) ⇒ a ⇒ c) ≔
begin assume a b c; eval #tauto; end;

private symbol example_curry (a b c : Prop) :
  π ((a ∧ b ⇒ c) ⇒ a ⇒ b ⇒ c) ≔
begin assume a b c; eval #tauto; end;

private symbol example_distrib (a b c : Prop) :
  π (a ∧ (b ∨ c) ⇔ (a ∧ b) ∨ (a ∧ c)) ≔
begin assume a b c; eval #tauto; end;

private symbol example_contrapos (a b : Prop) :
  π ((a ⇒ b) ⇒ ¬ b ⇒ ¬ a) ≔
begin assume a b; eval #tauto; end;

// Dyckhoff's ⇒⇒ rule is what makes this one terminate without loop-checking.
private symbol example_imp_imp (a b : Prop) :
  π (((a ⇒ b) ⇒ a) ⇒ (a ⇒ b) ⇒ b) ≔
begin assume a b; eval #tauto; end;
