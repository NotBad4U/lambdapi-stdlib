require open Stdlib.Prop;
require open Stdlib.Impred;
require open Stdlib.FOL;
require open Stdlib.Eq;
require open Stdlib.Nat;
require Stdlib.Bool;
require open Stdlib.Set;
require open Stdlib.List;
require open Stdlib.Prod;


inductive prop: TYPE ≔
|pTrue: prop
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

open Stdlib.Bool;

symbol prop_eq (l r: prop): τ bool;
rule prop_eq pTrue pTrue ↪ true
with prop_eq pTrue pFalse ↪ false
with prop_eq pTrue (pAnd _ _) ↪ false
with prop_eq pTrue (pOr _ _) ↪ false
with prop_eq pTrue (pImpl _ _) ↪ false
with prop_eq pTrue (pOther _) ↪ false

with prop_eq pFalse pFalse ↪ true
with prop_eq pFalse pTrue ↪ false
with prop_eq pFalse (pAnd _ _) ↪ false
with prop_eq pFalse (pOr _ _) ↪ false
with prop_eq pFalse (pImpl _ _) ↪ false
with prop_eq pFalse (pOther _) ↪ false

with prop_eq (pAnd $a $b) (pAnd $c $d) ↪ (prop_eq $a $c) and (prop_eq $b $d)
with prop_eq (pAnd _ _) pFalse ↪ false
with prop_eq (pAnd _ _) pTrue ↪ false
with prop_eq (pAnd _ _) (pOr _ _) ↪ false
with prop_eq (pAnd _ _) (pImpl _ _) ↪ false
with prop_eq (pAnd _ _) (pOther _) ↪ false

with prop_eq (pOr $a $b) (pOr $c $d) ↪ (prop_eq $a $c) and (prop_eq $b $d)
with prop_eq (pOr _ _) pFalse ↪ false
with prop_eq (pOr _ _) pTrue ↪ false
with prop_eq (pOr _ _) (pAnd _ _) ↪ false
with prop_eq (pOr _ _) (pImpl _ _) ↪ false
with prop_eq (pOr _ _) (pOther _) ↪ false

with prop_eq (pImpl $a $b) (pImpl $c $d) ↪ (prop_eq $a $c) and (prop_eq $b $d)
with prop_eq (pImpl _ _) pFalse ↪ false
with prop_eq (pImpl _ _) pTrue ↪ false
with prop_eq (pImpl _ _) (pAnd _ _) ↪ false
with prop_eq (pImpl _ _) (pOr _ _) ↪ false
with prop_eq (pImpl _ _) (pImpl _ _) ↪ false
with prop_eq (pImpl _ _) (pOther _) ↪ false


with prop_eq (pOther $i) (pOther $j) ↪ (eqn $i $j)
with prop_eq (pOther $i) pFalse ↪ false
with prop_eq (pOther $i) pTrue ↪ false
with prop_eq (pOther $i) (pAnd _ _) ↪ false
with prop_eq (pOther $i) (pOr _ _) ↪ false
with prop_eq (pOther $i) (pImpl _ _) ↪ false
with prop_eq (pOther $i) (pOther _) ↪ false
;

assert ⊢ prop_eq (pOr (pOther 0) (pOther 1)) (pOr (pOther 0) (pOther 1)) ≡ true;
assert ⊢ prop_eq (pOr (pOther 0) (pOther 1)) (pOr (pOther 1) (pOther 0)) ≡ false;

// Decidable equality on terms
opaque symbol prop_eq_sound (a b: prop): π (istrue (prop_eq a b)) → π (a = b)  ≔
begin
    induction
    { induction { reflexivity } { assume H; apply ⊥ₑ H; } { assume b' H c' H2 H3; apply ⊥ₑ H3 }  { assume b' H c' H2 H3; apply ⊥ₑ H3 } { assume b' H c' H2 H3; apply ⊥ₑ H3 } { assume idx H;  apply ⊥ₑ H } } 
    { induction { assume H; apply ⊥ₑ H; } { reflexivity }  { assume b' H c' H2 H3; apply ⊥ₑ H3 }  { assume b' H c' H2 H3; apply ⊥ₑ H3 } { assume b' H c' H2 H3; apply ⊥ₑ H3 } { assume idx H;  apply ⊥ₑ H } } 
    {
        assume a' IH b' IH2;
        induction
        {assume H3; apply ⊥ₑ H3; }
        {assume H3; apply ⊥ₑ H3; }
        { 
            simplify;  assume c' H' d' H2' H3;
            have g: π (prop_eq a' c' ∧ prop_eq b' d') { refine ∧_istrue H3 };
            rewrite left IH c' (∧ₑ₁ g);
            rewrite left IH2 d' (∧ₑ₂ g);
            reflexivity
        }
        { assume c' H' d' H2';  assume H3; apply ⊥ₑ H3; }
        { assume c' H' d' H2';  assume H3; apply ⊥ₑ H3; }
        { assume i;  assume H3; apply ⊥ₑ H3; }
    }
    {
        assume a' IH b' IH2;
        induction
        {assume H3; apply ⊥ₑ H3; }
        {assume H3; apply ⊥ₑ H3; }
        { assume c' H' d' H2';  assume H3; apply ⊥ₑ H3; }
        {
            simplify; assume c' H' d' H2' H3;
            have g: π (prop_eq a' c' ∧ prop_eq b' d')
            { refine ∧_istrue H3 };
            rewrite left IH c' (∧ₑ₁ g);
            rewrite left IH2 d' (∧ₑ₂ g);
            reflexivity
        }
        { assume c' H' d' H2';  assume H3; apply ⊥ₑ H3; }
        { assume i;  assume H3; apply ⊥ₑ H3; }
    }
    {
        assume a' IH b' IH2;
        induction
        {assume H3; apply ⊥ₑ H3; }
        {assume H3; apply ⊥ₑ H3; }
        { assume c' H' d' H2';  assume H3; apply ⊥ₑ H3; }
        { assume c' H' d' H2';  assume H3; apply ⊥ₑ H3; }
        { assume c' H' d' H2' H3;
            have g: π (prop_eq a' c' ∧ prop_eq b' d')
            { refine ∧_istrue H3 };
            rewrite left IH c' (∧ₑ₁ g);
            rewrite left IH2 d' (∧ₑ₂ g);
            reflexivity
        }
        { assume i;  assume H3; apply ⊥ₑ H3; }
    }
    {
        assume i;
        induction
        { assume H; apply ⊥ₑ H;  }
        { assume H; apply ⊥ₑ H;  }
        { assume x; assume H x' H2 Hbot; apply ⊥ₑ Hbot; }
        { assume x; assume H x' H2 Hbot; apply ⊥ₑ Hbot; }
        { assume x; assume H x' H2 Hbot; apply ⊥ₑ Hbot; }
        {
            assume j;
            assume H;
            rewrite (eqn_correct i j H);
            reflexivity  
        }
    }
end;

symbol knows (p: prop) (c: 𝕃 propS): 𝔹 ≔ ∈ prop_eq p c;

sequential symbol learn (p: prop) (c: 𝕃 propS) : 𝕃 propS;
rule learn pTrue $c ↪ $c
with learn pFalse $c ↪ pFalse ⸬ □
with learn (pAnd $l $r) $c ↪ learn $l (learn $r $c)
with learn $p $c ↪ $p ⸬ $c; //HACK: for simplicity

symbol provable (goal: prop) (known: 𝕃 propS) : 𝔹;
rule provable pTrue _ ↪ true
with provable pFalse $known ↪ knows pFalse $known
with provable (pAnd $l $r) $known ↪ (provable $l $known) and (provable $r $known)
with provable (pOr $l $r) $known ↪ (provable $l $known) or (provable $r $known)
with provable (pImpl $l $r) $known ↪ provable $r (learn $l $known)
with provable (pOther $i) $known ↪ (knows (pOther $i) $known) or (knows pFalse $known);

assertnot ⊢ provable (pAnd (pOther 0) pFalse) ((pOther 0) ⸬ □) ≡ true;
assert ⊢ provable (pAnd (pOther 0) pTrue) ((pOther 0) ⸬ □) ≡ true;

symbol foldr [a b: Set] : (τ a → τ b → τ b) → τ b → 𝕃 a → τ b;
rule foldr $f $z □ ↪ $z
with foldr $f $z ($x ⸬ $xs) ↪ $f $x (foldr $f $z $xs);

symbol All: 𝕃 propS → prop ≔ foldr (pAnd) pTrue;

symbol I: π ⊤;

opaque symbol learn_sound (ctx: 𝕃 o) (p: prop) (c: 𝕃 propS): π (propD ctx (All c)) → π ( propD ctx p) → π ( propD ctx (All (learn p c)))
≔ begin
    assume σ;
    induction
    { assume c; assume H; assume Htop; apply H }
    { assume c; assume H H2; refine ⊥ₑ H2  }
    { assume a IH b IH2 ctx H2 H3;
        apply ∧ᵢ 
        { refine  ∧ₑ₁ H3 } 
        {  apply ∧ᵢ { apply ∧ₑ₂ H3 } { refine H2 } }
    }
    { assume a IH b IH2 ctx H2 H3; 
        apply ∧ᵢ 
        { apply ∨ₑ H3 { assume H0; apply ∨ᵢ₁; refine H0 } { assume H0; apply ∨ᵢ₂; refine H0 }  }
        { refine H2 }
    }
    {
        assume a IH b IH2 ctx H2 H3;
        apply ∧ᵢ 
        { refine H3 }
        { refine H2 }
    }
    {
        assume i Γ H1 H2;
        apply ∧ᵢ { refine H2 } { refine H1 }
    }
end;


opaque symbol knows_sound (σ: 𝕃 o) (c: 𝕃 propS) (p: prop) : π ((knows p c) ⇒ (propD σ (All c)) ⇒  (propD σ p)) ≔
begin 
    assume σ;
    induction
    {
        simplify;
        assume p contra h;
        refine ⊥ₑ contra;
    }
    {
        simplify ∈;
        assume  h tl IH p H1 H2;
        have e: π (prop_eq p h ∨ ∈ prop_eq p tl) { refine ∨_istrue H1 };
        apply ∨ₑ e
        {
            assume p=h;
            rewrite prop_eq_sound p h p=h;
            apply ∧ₑ₁ H2
        }
        {
            assume Hp_in_tl;
            refine IH p Hp_in_tl (∧ₑ₂ H2) ;
        }
    }
end;

opaque symbol provable_sound (goal: prop) (hyps: 𝕃 propS) (ctx: 𝕃 o) :
    π (provable goal hyps) → 
    π (propD ctx (All hyps)) →
    π (propD ctx goal) ≔
begin
    induction
    { assume ctx σ H H2; apply I }
    { assume ctx σ H H2; apply (knows_sound σ ctx pFalse H);  apply H2 }
    { assume a IH1 b IH2 ctx' σ H  H2;
        have G: π ((provable a ctx') ∧ (provable b ctx') ) {
            refine ∧_istrue H
        };
        apply ∧ᵢ
        { refine (IH1 ctx' σ (∧ₑ₁ G)) H2 }
        { refine (IH2 ctx' σ (∧ₑ₂ G)) H2 };
    }
    {
        assume a IH1 b IH2 ctx' σ H H2;
        have G: π ((provable a ctx') ∨ (provable b ctx') ) {
            refine ∨_istrue H
        };
        apply ∨ₑ G
        {  assume Ga; apply ∨ᵢ₁; refine (IH1 ctx' σ Ga  H2) }
        { assume Gb; apply ∨ᵢ₂; refine (IH2 ctx' σ Gb H2) };
    }
    {
        
        assume a IH1 b IH2 ctx H σ H2 Ha;
        apply (IH2 (a ⸬ ctx) H σ);
        apply ∧ᵢ
        { apply Ha }
        { apply H2 }
    }
    {
       assume i hyps σ IH H2;
       have G: π ((∈ prop_eq (pOther i) hyps)  ∨ (∈ prop_eq pFalse hyps) ) {
        refine (∨_istrue IH); 
       };
       apply ∨ₑ G
       { assume Gl; apply (knows_sound σ hyps (pOther i) Gl H2); }
       { assume Gr; refine (@⊥ₑ (nth not_found σ i) (knows_sound σ hyps (pFalse) Gr H2))  }
    }
end;

constant symbol R : TYPE;
constant symbol Index : ℕ → R;
constant symbol New : ℕ → R;

symbol case [a] : R → (ℕ → τ a) → (ℕ → τ a) → τ a;
rule case (Index $i) $f _ ↪ $f $i
with case (New $i) _ $g ↪ $g $i;

sequential symbol index: ℕ → Π [a], τ a → τ(list a) → R;
rule index $k _ □ ↪ New $k
with index $k $x ($x ⸬ _) ↪ Index $k // Here is the magic...
with index $k $x ($y ⸬ $l) ↪ index ($k +1) $x $l;

sequential symbol propReify: (𝕃 o) →  Prop → τ (propS × (list o));
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

symbol reify goal ≔ propReify □ goal; 

symbol tauto_aux [goal] ≔ let res ≔ reify goal in provable_sound (res ₁) □ (res ₂);

require open Stdlib.Tactic;

symbol tauto ≔ #refine "(tauto_aux ⊤ᵢ ⊤ᵢ)";

private symbol example1: π ((⊤ ∧ ⊤) ⇒ ⊤ ∨ ⊤ ∧ (⊤ ⇒ ⊤)) ≔
begin eval tauto; end;

private symbol example2 a : π (a ∧ a ⇒ a) ≔
begin assume a; eval tauto; end;

private symbol example3: π (3 ≥ 0 ⇔ ⊤) ≔
begin eval tauto; end;