require open Stdlib.Prop Stdlib.Set Stdlib.FOL Stdlib.HOL;

constant symbol Lev: TYPE;
constant symbol lsuc: Lev → Lev;

notation lsuc prefix 10;


constant symbol Set₀: Lev;
symbol Set₁ ≔ lsuc Set₀;
symbol Set₂ ≔ lsuc lsuc Set₀;

symbol max : Lev → Lev → Lev;
rule max Set₀ $i ↪ $i
with max $i Set₀ ↪ $i
with max $x $x ↪ $x
with max (lsuc $n) (lsuc $m) ↪ lsuc (max $n $m);

// Internal layer ================================
// It represents the theory we want to study. It is often equipped with Univalence
// Axiom, which makes its equality different than the usual equality, and incompatible with axioms
// like Uniqueness of Identity Proofs (UIP, or K) and functional extensionality (FunExt).

// Internal Type
constant symbol T: Lev → TYPE;
// decoding internal function
injective symbol ε  [i: Lev] : T i → TYPE;

// include a universe `i` in the bigger universe
constant symbol t (i: Lev): T (lsuc i);
rule ε (t $i) ↪ T $i; // t(i) ∈ T (i + 1)

constant symbol l↑ [i: Lev]: T i → T (lsuc i);
rule ε (l↑ $a) ↪ ε $a;

constant symbol False [i] : T i;
constant symbol True [i] : T i;

constant symbol Nat [i: Lev] : T i;
symbol nat [i] ≔ @ε i Nat;

constant symbol z [i] : @ε i Nat;
constant symbol S [i] : (@nat i) → (@nat i);

type @S Set₀ (@z Set₀);

assert ⊢ @S Set₀ (@z Set₀): @ε Set₀ Nat;

type @Nat Set₀;
type @ε Set₀ Nat;

// Internal Pi type
constant symbol Pi [i j] (A: T i) (B: ε A → T j): T (max i j);

// Non dependent Pi
symbol ⇒ [i j] ≔ λ (A : T i) (B : T j), Pi A (λ _, B); notation ⇒ infix right 10;


symbol εPi [i j] ≔ λ (A : T i) (B : T j), ε (A ⇒ B);
rule ε (Pi $A $B) ↪ Π x : ε $A, ε ($B x);


constant symbol Σ [i j] (A: T i) (B: ε A → T j): T (max i j);

// def tSig := ( i : Lev => A : T i => B : ( eps i A -> T i)
// => eps i ( Sig i A B )).

symbol εΣ [i j] (A: T i) (B: ε A → T j) ≔ ε (Σ A B);
constant symbol pair [i j]:  Π (A: T i) (B: ε A → T j) (a : ε A), ε (B a) → εΣ A B;

symbol π₁ [i j] [A: T i] [B: ε A → T j]: εΣ A B → ε A;
symbol π₂ [i j] [A: T i] [B: ε A → T j] (p: εΣ A B): ε (B (π₁ p)); 

symbol × [i j] (A : T i) (B : T j) ≔ Σ A (λ _, B);


constant symbol Sum [i] (A: T i) (B: T i): T i;

constant symbol Eq [i] (A: T i) (x: @ε i A) (y: @ε i A): T i;  notation × infix right 10;

symbol εEq [i] A ≔ λ (x y : @ε i A), ε (Eq A x y);
constant symbol refl [i] [A : T i] (x : ε A) : @εEq i A x x;

symbol id [i] (A: T i) : ε A  → ε A ≔ λ x, x;

symbol eqJ [i j] : Π (A: T i) (x : ε A) 
    (P: Π (y : ε A), @εEq i A x y → T j), @ε j (P x (@refl i A x)) → Π (y: ε A) (p: @εEq i A x y), ε (P y p);

rule eqJ _ _ _ $x _ (refl _) ↪ $x;

// =^* in HoTT Book
symbol transport [i] : Π (A B: T i) (e: ε (Eq (t i) A B)), εPi A B
≔ begin assume i A B e x; refine eqJ (t i) A (λ y _, y) x B e end;


symbol CompoIdTypeL [i] ≔ λ (A B : T i), λ (f : εPi A B), λ (g : εPi B A), Pi A (λ x, Eq A ( g (f x)) x);

symbol CompoIdTypeR [i] ≔ λ (A B : T i), λ (f : εPi A B), λ (g : εPi B A), Pi B (λ x, Eq B (f (g x)) x);

symbol isEquiv [i] [A B: T i] ≔  
    λ (f: ε (A ⇒ B)), (Σ (B ⇒ A) (λ g, CompoIdTypeL A B f g)) × (Σ (B ⇒ A) (λ g, CompoIdTypeR A B f g));


// WeakUnivalence : l : Lev -> A : T l -> B : T l ->
//         eps (lsuc l) (Equiv (lsuc l) (TEq l A B) (lUp l (Equiv l A B))).

symbol Equiv [i] (A B: T i) ≔ Σ (A ⇒ B) (λ f, isEquiv f);

symbol sym [i] [A: T i] [x y: ε A]: εEq A x y →  εEq A y x ≔ eqJ A x (λ y _, Eq A y x) (refl x) y;

symbol idToEquiv [i] (A B: T i)  : εPi (Eq (t i) A B) (l↑ (Equiv A B))  ≔ begin
    assume i A B e;
    refine pair (A ⇒ B) (λ f, isEquiv f) (transport A B e) _;
    refine pair _ _ _ _ 
    {
        refine pair (B ⇒ A) (CompoIdTypeL A B (transport A B e)) (transport B A (sym e)) _;
        assume x;
        refine eqJ (t i) A (λ B e,(Eq A (transport B A (sym e) (transport A B e x)) x)) (refl x) B e;
    }
    {
        refine pair (B ⇒ A) (CompoIdTypeR A B (transport A B e)) (transport B A (sym e)) _;
        refine eqJ (t i) A  (λ B e, (CompoIdTypeR A B (transport A B e) (transport B A (sym e)))) (λ x, (refl x)) B e;
    }
end;


symbol ua [i] : Π (A B: T i), ε (isEquiv (idToEquiv A B));


// External layer ================================
// This theory will act as a sort of ’meta-theory’ of the internal. We will use its
// propositional equality as an intermediate equality between the definitional ones (there are two
// definitional equalities here, the internal and the external), and the propositional equality of the
// internal theory. It has additional axioms (UIP & FunExt) to make its propositional equality not
// slightly weaker but as powerful as the usual one.


// External Type
injective symbol xT: Lev → TYPE;
// decoding external function
symbol xε [i: Lev] : xT i → TYPE;

symbol xt (i: Lev): xT (lsuc i); 
rule xε (xt $i) ↪ xT $i; // Level i ⊂ i + 1 

symbol xl↑ [i: Lev]: xT i → xT (lsuc i);
rule xε (xl↑ $a) ↪ xε $a;

symbol xΠ [i] (A: xT i) (B: xε A → xT i): xT i;
symbol εΠ [i] ≔ λ (A : xT i) (B : xε A → xT i), xε (xΠ A B);

symbol xΣ [i] (A: xT i) (B: xε A): xT i;

symbol xSum [i] (A: xT i) (B: xT i): xT i;

symbol xEq [i] (A: xT i) (x: @xε i A) (y: @xε i A): xT i;

symbol c : Π (i: Lev), T i → xT i;

// equivalence of Internal Nat at level 0 to Nat at external level 0 
assert ⊢ c Set₀ Nat : xT Set₀;

//symbol tc [i: Lev] : T i → TYPE;

symbol tc [i: Lev] ≔ λ (A: T i), xε (c i A);

symbol isoUp : Π (i: Lev), Π (A: T i) , ε A →  tc A;
symbol isoDown : Π (i: Lev), Π (A: T i) , tc A →  ε A;

rule isoUp $i $A (isoDown $i $A $a) ↪ $a
with isoDown $i $A (isoUp $i $A $a) ↪ $a;


symbol xtEq [i] [A] ≔ λ (x y : @xε i A), xε (xEq A x y);
constant symbol xrefl [i] [A : xT i] (x : xε A) : @xtEq i A x x;

symbol ↑_xEq [i] ≔ λ (A B: xT i), @xEq (lsuc i) (xt i) A B;
symbol ↑_ε_xEq [i] ≔ λ (A B: xT i), @xε (lsuc i) (@↑_xEq i A B);
symbol ↑_xrefl [i] ≔ λ (A: xT i), @xrefl (lsuc i) (xt i) A;

type ↑_xrefl;

constant symbol xeqJ [i j] : Π (A: xT i) (x : @xε i A) 
    (P: Π (y : @xε i A), @xtEq i A x y → xT j), @xε j (P x (@xrefl i A x)) → Π (y: @xε i A) (p: @xtEq i A x y), @xε j (P y p);

// It has additional axioms (UIP & FunExt) to make its propositional equality not
// slightly weaker but as powerful as the usual one.

// symbol FunEx [i] [A: xT i] [B: xε A → xT i] (f g : @εΠ i A B) (p : Π (a : @xε i A), xtEq (f a) (g a)) :
//   @xtEq i (xΠ A B) f g;


// Coercion is injective
//symbol T1: Π (i: Lev) (A: T i) (B: T i), @xEq i A (c i A) (c i B);
