require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq;


constant symbol real : Set;

symbol ≤ : τ real → τ real → Prop;
 notation ≤ infix left 20;

// supremum of a (nonempty, bounded) real set.
symbol sup : (τ real → Prop) → τ real;

symbol add : τ real → τ real → τ real;

symbol zero : τ real;

symbol opp : τ real → τ real;

symbol mul : τ real → τ real → τ real;

symbol one : τ real;

symbol inv : τ real → τ real;

// Equality as the preorder equivalence
symbol eq (x y : τ real) : Prop ≔ x ≤ y ∧ y ≤ x;

// Set of upper bounds of a real set.
symbol ub (E : τ real → Prop) : τ real → Prop ≔ λ z, `∀ y, E y ⇒ y ≤ z;

// Set of downward closure of E where down E x ⟺ x ≤ y for some y such that E y.
symbol down (E : τ real → Prop) : τ real → Prop ≔ λ x, `∃ y, E y ∧ x ≤ y;

// === Real set supremum existence condition =====

symbol nonempty (E : τ real → Prop) : Prop ≔ `∃ x, E x;

symbol has_ub (E : τ real → Prop) : Prop ≔ nonempty (ub E);

symbol has_sup (E : τ real → Prop) : Prop ≔ nonempty E ∧ has_ub E;

// =====

// the complete-ordered-field axioms

// ≤ is a preorder.
symbol le_reflexive (x : τ real) : π (x ≤ x);
symbol le_transitive (x y z : τ real) : π (≤ x y ⇒ ≤ y z ⇒ ≤ x z);

// sup is the least upper bound.  sup_total is the constructive minimality
// axiom that (in Rocq) forces the excluded middle and totality of the order.
symbol sup_upper_bound (E : τ real → Prop) : π (has_sup E ⇒ ub E (sup E));

symbol sup_total (E : τ real → Prop) (x : τ real) :
  π (has_sup E ⇒ (down E x ∨ (sup E) ≤ x));

symbol add_monotone (x y z : τ real) : π (y ≤ z) → π ((add x y) ≤ (add x z));

symbol add_commutative (x y : τ real) : π (eq (add x y) (add y x));

symbol add_associative (x y z : τ real) : π (eq (add x (add y z)) (add (add x y) z));

symbol add_zero_left (x : τ real) : π (eq (add zero x) x);

symbol add_opposite_right (x : τ real) : π (eq (add x (opp x)) zero);

symbol mul_monotone (x y z : τ real) :
  π (≤ zero x ⇒ ≤ y z ⇒ ≤ (mul x y) (mul x z));

symbol mul_commutative (x y : τ real) : π (eq (mul x y) (mul y x));

symbol mul_associative (x y z : τ real) :
  π (eq (mul x (mul y z)) (mul (mul x y) z));

symbol mul_distributive_right (x y z : τ real) :
  π (eq (mul x (add y z)) (add (mul x y) (mul x z)));

symbol mul_one_left (x : τ real) : π (eq (mul one x) x);

symbol mul_inverse_right (x : τ real) :
  π (¬ (eq x zero) ⇒ eq (mul x (inv x)) one);

symbol one_nonzero : π (¬ (eq one zero));

// Antisymmetry of ≤ with respect to Leibniz equality.  This is the only
// axiom relating the setoid equality `eq` to `=`: it is not derivable from
// the axioms above, which constrain the structure only up to `eq` (a model
// that duplicates each real into two `eq`-equivalent copies satisfies all
// of them), but it holds in the standard model ℝ (cf. Rocq's Rle_antisym).
// https://rocq-prover.org/doc/V9.0.0/stdlib/Stdlib.Reals.RIneq.html#Rle_antisym
symbol le_antisymmetric (x y : τ real) : π (x ≤ y ⇒ y ≤ x ⇒ x = y);

// √2 : the square root of two

symbol two : τ real ≔ add one one;

symbol below_root2 : τ real → Prop ≔ λ x, zero ≤ x ∧ mul x x ≤ two;

// √2 =  sup { x | 0 ≤ x ∧ x·x ≤ 2 }
symbol sqrt2 : τ real ≔ sup below_root2;

// ---------------------------------------------------------------------------
// Specification of √2.
//
// E is nonempty (0 ∈ E) and bounded above (by 2), so `has_sup E` holds and the
// sup axioms apply.  From them the defining properties of √2 follow:
//     0 ≤ √2      and      √2 · √2 = 2.
// These are *theorems* about the definition above (not new axioms); their
// proofs are the usual completeness argument (squeeze √2·√2 between the two
// `sup` bounds), built on the ordered-field lemmas.  Stated here as the spec.
// ---------------------------------------------------------------------------
// ===========================================================================
// A. order / eq combinators   (fully explicit arguments)
// ===========================================================================

symbol le_refl x : π (x ≤ x) ≔ le_reflexive x;

symbol le_tr x y z : π (x ≤ y) → π (y ≤ z) → π (x ≤ z) ≔
  λ h1 h2, le_transitive x y z h1 h2;

symbol eq_le x y : π (eq x y) → π (x ≤ y) ≔ λ h, ∧ₑ₁ h;
symbol eq_ge x y : π (eq x y) → π (y ≤ x) ≔ λ h, ∧ₑ₂ h;

symbol eq_refl' x : π (eq x x) ≔ ∧ᵢ (le_refl x) (le_refl x);

symbol eq_sym' x y : π (eq x y) → π (eq y x) ≔ λ h, ∧ᵢ (∧ₑ₂ h) (∧ₑ₁ h);

symbol eq_tr x y z : π (eq x y) → π (eq y z) → π (eq x z) ≔
  λ h1 h2, ∧ᵢ (le_transitive x y z (∧ₑ₁ h1) (∧ₑ₁ h2))
              (le_transitive z y x (∧ₑ₂ h2) (∧ₑ₂ h1));

symbol le_eq_tr x y z : π (x ≤ y) → π (eq y z) → π (x ≤ z) ≔
  λ h e, le_transitive x y z h (∧ₑ₁ e);
symbol eq_le_tr x y z : π (eq x y) → π (y ≤ z) → π (x ≤ z) ≔
  λ e h, le_transitive x y z (∧ₑ₁ e) h;

// `eq` coincides with Leibniz equality: `le_antisymmetric` gives the forward
// direction; the converse is transport along `ind_eq` (no axiom needed).
symbol leibniz_of_eq x y : π (eq x y) → π (x = y) ≔
  λ h, le_antisymmetric x y (∧ₑ₁ h) (∧ₑ₂ h);

symbol eq_of_leibniz x y : π (x = y) → π (eq x y) ≔
  λ h, ind_eq h (λ z, eq z y) (eq_refl' y);

symbol eq_iff_leibniz x y : π (eq x y ⇔ x = y) ≔
  ∧ᵢ (leibniz_of_eq x y) (eq_of_leibniz x y);

// ===========================================================================
// B. additive group lemmas (up to `eq`)
// ===========================================================================

symbol add_zero_r x : π (eq (add x zero) x) ≔
  eq_tr (add x zero) (add zero x) x (add_commutative x zero) (add_zero_left x);

symbol add_opp_l x : π (eq (add (opp x) x) zero) ≔
  eq_tr (add (opp x) x) (add x (opp x)) zero (add_commutative (opp x) x) (add_opposite_right x);

symbol add_cong_r z x y : π (eq x y) → π (eq (add z x) (add z y)) ≔
  λ h, ∧ᵢ (add_monotone z x y (∧ₑ₁ h)) (add_monotone z y x (∧ₑ₂ h));

symbol add_cong_l z x y : π (eq x y) → π (eq (add x z) (add y z)) ≔
  λ h, eq_tr (add x z) (add z x) (add y z) (add_commutative x z)
        (eq_tr (add z x) (add z y) (add y z) (add_cong_r z x y h) (add_commutative z y));

symbol add_cong a b c d : π (eq a b) → π (eq c d) → π (eq (add a c) (add b d)) ≔
  λ h1 h2, eq_tr (add a c) (add b c) (add b d) (add_cong_l c a b h1) (add_cong_r b c d h2);

symbol add_le_mono_r z x y : π (x ≤ y) → π (add x z ≤ add y z) ≔
  λ h, eq_le_tr (add x z) (add z x) (add y z) (add_commutative x z)
        (le_eq_tr (add z x) (add z y) (add y z) (add_monotone z x y h) (add_commutative z y));

symbol add_le_mono a b c d : π (a ≤ b) → π (c ≤ d) → π (add a c ≤ add b d) ≔
  λ hab hcd, le_tr (add a c) (add b c) (add b d) (add_le_mono_r c a b hab) (add_monotone b c d hcd);

// c == c + c  =>  c == 0
symbol self_eq_double_imp_zero c : π (eq c (add c c)) → π (eq c zero) ≔
  λ h, eq_sym' zero c
    (eq_tr zero (add (opp c) c) c (eq_sym' (add (opp c) c) zero (add_opp_l c))
      (eq_tr (add (opp c) c) (add (opp c) (add c c)) c (add_cong_r (opp c) c (add c c) h)
        (eq_tr (add (opp c) (add c c)) (add (add (opp c) c) c) c (add_associative (opp c) c c)
          (eq_tr (add (add (opp c) c) c) (add zero c) c (add_cong_l c (add (opp c) c) zero (add_opp_l c))
            (add_zero_left c)))));

symbol neg_of_nonpos x : π (x ≤ zero) → π (zero ≤ opp x) ≔
  λ h, eq_le_tr zero (add x (opp x)) (opp x) (eq_sym' (add x (opp x)) zero (add_opposite_right x))
        (le_eq_tr (add x (opp x)) (add zero (opp x)) (opp x) (add_le_mono_r (opp x) x zero h) (add_zero_left (opp x)));

// ===========================================================================
// C. order totality (from the sup axioms) + multiplication basics
// ===========================================================================

// totality: derived from `sup_total` applied to the down-set {w | w ≤ y}.
symbol le_total x y : π (x ≤ y ∨ y ≤ x) ≔
begin
  assume x y;
  have hs : π (has_sup (λ w, w ≤ y)) {
    refine ∧ᵢ (∃ᵢ y (le_refl y)) (∃ᵢ y (λ w hw, hw)) };
  refine ∨ₑ (sup_total (λ w, w ≤ y) x hs) _ _
  { assume hd; refine ∃ₑ hd _; assume w hw;
    refine ∨ᵢ₁ (le_tr x w y (∧ₑ₂ hw) (∧ₑ₁ hw)) }
  { assume hle;
    refine ∨ᵢ₂ (le_tr y (sup (λ w, w ≤ y)) x
                  (sup_upper_bound (λ w, w ≤ y) hs y (le_refl y)) hle) }
end;

// a·0 == 0 when 0 ≤ a  (cancel trick; no sign lemmas needed)
symbol mul_zero_r_nonneg a : π (zero ≤ a) → π (eq (mul a zero) zero) ≔
  λ h, self_eq_double_imp_zero (mul a zero)
    (eq_tr (mul a zero) (mul a (add zero zero)) (add (mul a zero) (mul a zero))
       (eq_sym' (mul a (add zero zero)) (mul a zero)
          (∧ᵢ (mul_monotone a (add zero zero) zero h (eq_le (add zero zero) zero (add_zero_left zero)))
              (mul_monotone a zero (add zero zero) h (eq_ge (add zero zero) zero (add_zero_left zero)))))
       (mul_distributive_right a zero zero));

symbol mul_one_r x : π (eq (mul x one) x) ≔
  eq_tr (mul x one) (mul one x) x (mul_commutative x one) (mul_one_left x);

// 0 ≤ 1  (if 1 ≤ 0 then (-1)·1 = -1 ≤ 0 and -1 ≥ 0, forcing 1 = 0)
symbol zero_le_one : π (zero ≤ one) ≔
begin
  refine ∨ₑ (le_total one zero) _ _
  { assume h;
    have hop : π (zero ≤ opp one) { refine neg_of_nonpos one h };
    have hm : π (mul (opp one) one ≤ mul (opp one) zero) {
      refine mul_monotone (opp one) one zero hop h };
    have hz : π (eq (mul (opp one) zero) zero) { refine mul_zero_r_nonneg (opp one) hop };
    have ho : π (eq (mul (opp one) one) (opp one)) { refine mul_one_r (opp one) };
    have h1 : π (opp one ≤ zero) {
      refine eq_le_tr (opp one) (mul (opp one) one) zero (eq_sym' (mul (opp one) one) (opp one) ho) (le_eq_tr (mul (opp one) one) (mul (opp one) zero) zero hm hz) };
    have h2 : π (eq (opp one) zero) { refine ∧ᵢ h1 hop };
    have h3 : π (eq zero one) {
      refine eq_tr zero (add one (opp one)) one (eq_sym' (add one (opp one)) zero (add_opposite_right one))
               (eq_tr (add one (opp one)) (add one zero) one (add_cong_r one (opp one) zero h2) (add_zero_r one)) };
    refine ⊥ₑ (one_nonzero (eq_sym' zero one h3)) }
  { assume h; refine h }
end;

// left cancellation for ≤
symbol add_opp_cancel_l z x : π (eq (add (opp z) (add z x)) x) ≔
  eq_tr (add (opp z) (add z x)) (add (add (opp z) z) x) x (add_associative (opp z) z x)
    (eq_tr (add (add (opp z) z) x) (add zero x) x (add_cong_l x (add (opp z) z) zero (add_opp_l z)) (add_zero_left x));

symbol add_le_cancel_l z x y : π (add z x ≤ add z y) → π (x ≤ y) ≔
  λ h, eq_le_tr x (add (opp z) (add z x)) y (eq_sym' (add (opp z) (add z x)) x (add_opp_cancel_l z x))
        (le_eq_tr (add (opp z) (add z x)) (add (opp z) (add z y)) y (add_monotone (opp z) (add z x) (add z y) h)
          (add_opp_cancel_l z y));

// constants
symbol zero_le_two : π (zero ≤ two) ≔
  eq_le_tr zero (add zero zero) two (eq_sym' (add zero zero) zero (add_zero_left zero))
    (add_le_mono zero one zero one zero_le_one zero_le_one);

symbol one_le_two : π (one ≤ two) ≔
  eq_le_tr one (add one zero) two (eq_sym' (add one zero) one (add_zero_r one))
    (add_monotone one zero one zero_le_one);

symbol not_one_le_zero : π (one ≤ zero) → π ⊥ ≔
  λ h, one_nonzero (∧ᵢ h zero_le_one);

symbol not_two_le_zero : π (two ≤ zero) → π ⊥ ≔
  λ h, not_one_le_zero (le_tr one two zero one_le_two h);

// monotonicity of squaring on the nonnegative reals
symbol sqr_mono a b : π (zero ≤ a) → π (a ≤ b) → π (mul a a ≤ mul b b) ≔
  λ h0 hab, le_tr (mul a a) (mul a b) (mul b b) (mul_monotone a a b h0 hab)
    (eq_le_tr (mul a b) (mul b a) (mul b b) (mul_commutative a b)
       (mul_monotone b a b (le_tr zero a b h0 hab) hab));

// 2·2 == 2+2
symbol two_mul_two : π (eq (mul two two) (add two two)) ≔
  eq_tr (mul two two) (add (mul two one) (mul two one)) (add two two)
    (mul_distributive_right two one one)
    (add_cong (mul two one) two (mul two one) two (mul_one_r two) (mul_one_r two));

// 0 ∈ below_root2
symbol below_root2_zero : π (below_root2 zero) ≔
  ∧ᵢ (le_refl zero)
     (eq_le_tr (mul zero zero) zero two (mul_zero_r_nonneg zero (le_refl zero)) zero_le_two);

// ===========================================================================
// Theorem 1 : below_root2 has a supremum
// ===========================================================================
symbol below_root2_has_sup : π (has_sup below_root2) ≔
begin
  refine ∧ᵢ _ _
  { refine ∃ᵢ zero below_root2_zero }
  { refine ∃ᵢ two _;
    assume y hy;
    refine ∨ₑ (le_total y two) _ _
    { assume hle; refine hle }
    { assume hge;
      have h4 : π (add two two ≤ two) {
        refine le_tr (add two two) (mul two two) two
          (eq_ge (mul two two) (add two two) two_mul_two)
          (le_tr (mul two two) (mul y y) two (sqr_mono two y zero_le_two hge) (∧ₑ₂ hy)) };
      have h6 : π (two ≤ zero) {
        refine add_le_cancel_l two two zero
          (le_eq_tr (add two two) two (add two zero) h4
            (eq_sym' (add two zero) two (add_zero_r two))) };
      refine ⊥ₑ (not_two_le_zero h6) } }
end;

// ===========================================================================
// Theorem 2 : 0 ≤ √2
// ===========================================================================
symbol sqrt2_nonneg : π (zero ≤ sqrt2) ≔
  sup_upper_bound below_root2 below_root2_has_sup zero below_root2_zero;

// ===========================================================================
// D. sign / ring theory (multiplication is a congruence for `eq`)
// ===========================================================================

symbol opp_opp x : π (eq (opp (opp x)) x) ≔
  eq_tr (opp (opp x)) (add zero (opp (opp x))) x
   (eq_sym' (add zero (opp (opp x))) (opp (opp x)) (add_zero_left (opp (opp x))))
   (eq_tr (add zero (opp (opp x))) (add (add x (opp x)) (opp (opp x))) x
          (add_cong_l (opp (opp x)) zero (add x (opp x))
             (eq_sym' (add x (opp x)) zero (add_opposite_right x)))
    (eq_tr (add (add x (opp x)) (opp (opp x))) (add x (add (opp x) (opp (opp x)))) x
           (eq_sym' (add x (add (opp x) (opp (opp x)))) (add (add x (opp x)) (opp (opp x)))
              (add_associative x (opp x) (opp (opp x))))
     (eq_tr (add x (add (opp x) (opp (opp x)))) (add x zero) x
            (add_cong_r x (add (opp x) (opp (opp x))) zero (add_opposite_right (opp x)))
      (add_zero_r x))));

symbol eq_opp_of_add_zero a b : π (eq (add a b) zero) → π (eq a (opp b)) ≔
  λ h, eq_tr a (add a zero) (opp b) (eq_sym' (add a zero) a (add_zero_r a))
       (eq_tr (add a zero) (add a (add b (opp b))) (opp b)
          (add_cong_r a zero (add b (opp b))
             (eq_sym' (add b (opp b)) zero (add_opposite_right b)))
        (eq_tr (add a (add b (opp b))) (add (add a b) (opp b)) (opp b)
           (add_associative a b (opp b))
         (eq_tr (add (add a b) (opp b)) (add zero (opp b)) (opp b)
            (add_cong_l (opp b) (add a b) zero h)
          (add_zero_left (opp b)))));

symbol mul_distributive_left a b c :
  π (eq (mul (add a b) c) (add (mul a c) (mul b c))) ≔
  eq_tr (mul (add a b) c) (mul c (add a b)) (add (mul a c) (mul b c))
   (mul_commutative (add a b) c)
   (eq_tr (mul c (add a b)) (add (mul c a) (mul c b)) (add (mul a c) (mul b c))
          (mul_distributive_right c a b)
    (add_cong (mul c a) (mul a c) (mul c b) (mul b c)
       (mul_commutative c a) (mul_commutative c b)));

// p = 0, b ≥ 0  =>  p·b = 0   (monotonicity only, no sign lemmas)
symbol Lnn (p b : τ real) : π (eq p zero) → π (zero ≤ b) → π (eq (mul p b) zero) ≔
  λ hp hb, ∧ᵢ
    (eq_le_tr (mul p b) (mul b p) zero (mul_commutative p b)
       (le_eq_tr (mul b p) (mul b zero) zero (mul_monotone b p zero hb (eq_le p zero hp)) (mul_zero_r_nonneg b hb)))
    (le_eq_tr zero (mul b p) (mul p b)
       (eq_le_tr zero (mul b zero) (mul b p) (eq_sym' (mul b zero) zero (mul_zero_r_nonneg b hb))
          (mul_monotone b zero p hb (eq_ge p zero hp)))
       (mul_commutative b p));

symbol Rnn (p b : τ real) : π (eq p zero) → π (zero ≤ b) → π (eq (mul b p) zero) ≔
  λ hp hb, eq_tr (mul b p) (mul p b) zero (mul_commutative b p) (Lnn p b hp hb);

// p = 0  =>  p·b = 0   (any sign of b)
symbol L (p b : τ real) : π (eq p zero) → π (eq (mul p b) zero) ≔
begin
  assume p b hp;
  refine ∨ₑ (le_total zero b) _ _
  { assume hb; refine Lnn p b hp hb }
  { assume hb;
    have step1 : π (eq (mul (opp b) p) zero) { refine Rnn p (opp b) hp (neg_of_nonpos b hb) };
    have step2 : π (eq (add (mul b p) (mul (opp b) p)) zero) {
      refine eq_tr (add (mul b p) (mul (opp b) p)) (mul (add b (opp b)) p) zero
               (eq_sym' (mul (add b (opp b)) p) (add (mul b p) (mul (opp b) p)) (mul_distributive_left b (opp b) p))
               (Lnn (add b (opp b)) p (add_opposite_right b) (eq_ge p zero hp)) };
    have step3 : π (eq (mul b p) zero) {
      refine eq_tr (mul b p) (add (mul b p) (mul (opp b) p)) zero
               (eq_tr (mul b p) (add (mul b p) zero) (add (mul b p) (mul (opp b) p))
                  (eq_sym' (add (mul b p) zero) (mul b p) (add_zero_r (mul b p)))
                  (add_cong_r (mul b p) zero (mul (opp b) p) (eq_sym' (mul (opp b) p) zero step1)))
               step2 };
    refine eq_tr (mul p b) (mul b p) zero (mul_commutative p b) step3 }
end;

symbol mul_zero_l b : π (eq (mul zero b) zero) ≔ L zero b (eq_refl' zero);
symbol mul_zero_r a : π (eq (mul a zero) zero) ≔
  eq_tr (mul a zero) (mul zero a) zero (mul_commutative a zero) (L zero a (eq_refl' zero));

symbol neg_mul a b : π (eq (mul (opp a) b) (opp (mul a b))) ≔
  eq_opp_of_add_zero (mul (opp a) b) (mul a b)
    (eq_tr (add (mul (opp a) b) (mul a b)) (mul (add (opp a) a) b) zero
       (eq_sym' (mul (add (opp a) a) b) (add (mul (opp a) b) (mul a b)) (mul_distributive_left (opp a) a b))
       (L (add (opp a) a) b (add_opp_l a)));

// opp reverses ≤, hence is a congruence and injective for `eq`
symbol opp_le u v : π (u ≤ v) → π (opp v ≤ opp u) ≔
  λ h, eq_le_tr (opp v) (add (opp u) (add u (opp v))) (opp u)
        (eq_tr (opp v) (add zero (opp v)) (add (opp u) (add u (opp v)))
          (eq_sym' (add zero (opp v)) (opp v) (add_zero_left (opp v)))
          (eq_tr (add zero (opp v)) (add (add (opp u) u) (opp v)) (add (opp u) (add u (opp v)))
            (add_cong_l (opp v) zero (add (opp u) u) (eq_sym' (add (opp u) u) zero (add_opp_l u)))
            (eq_sym' (add (opp u) (add u (opp v))) (add (add (opp u) u) (opp v))
              (add_associative (opp u) u (opp v)))))
        (le_eq_tr (add (opp u) (add u (opp v))) (add (opp u) (add v (opp v))) (opp u)
           (add_monotone (opp u) (add u (opp v)) (add v (opp v)) (add_le_mono_r (opp v) u v h))
           (eq_sym' (opp u) (add (opp u) (add v (opp v)))
              (eq_tr (opp u) (add (opp u) zero) (add (opp u) (add v (opp v)))
                (eq_sym' (add (opp u) zero) (opp u) (add_zero_r (opp u)))
                (add_cong_r (opp u) zero (add v (opp v))
                  (eq_sym' (add v (opp v)) zero (add_opposite_right v))))));

symbol opp_cong u v : π (eq u v) → π (eq (opp u) (opp v)) ≔
  λ h, ∧ᵢ (opp_le v u (∧ₑ₂ h)) (opp_le u v (∧ₑ₁ h));

symbol opp_inj u v : π (eq (opp u) (opp v)) → π (eq u v) ≔
  λ h, eq_tr u (opp (opp u)) v (eq_sym' (opp (opp u)) u (opp_opp u))
         (eq_tr (opp (opp u)) (opp (opp v)) v (opp_cong (opp u) (opp v) h) (opp_opp v));

// multiplication is a congruence for `eq`
symbol mul_cong_r c x y : π (eq x y) → π (eq (mul c x) (mul c y)) ≔
begin
  assume c x y h;
  refine ∨ₑ (le_total zero c) _ _
  { assume hc; refine ∧ᵢ (mul_monotone c x y hc (∧ₑ₁ h)) (mul_monotone c y x hc (∧ₑ₂ h)) }
  { assume hc;
    have e0 : π (eq (mul (opp c) x) (mul (opp c) y)) {
      refine ∧ᵢ (mul_monotone (opp c) x y (neg_of_nonpos c hc) (∧ₑ₁ h))
                (mul_monotone (opp c) y x (neg_of_nonpos c hc) (∧ₑ₂ h)) };
    refine opp_inj (mul c x) (mul c y)
             (eq_tr (opp (mul c x)) (mul (opp c) x) (opp (mul c y))
               (eq_sym' (mul (opp c) x) (opp (mul c x)) (neg_mul c x))
               (eq_tr (mul (opp c) x) (mul (opp c) y) (opp (mul c y)) e0 (neg_mul c y))) }
end;

symbol mul_cong_l c x y : π (eq x y) → π (eq (mul x c) (mul y c)) ≔
  λ h, eq_tr (mul x c) (mul c x) (mul y c) (mul_commutative x c)
        (eq_tr (mul c x) (mul c y) (mul y c) (mul_cong_r c x y h) (mul_commutative c y));

symbol mul_cong a b c d : π (eq a b) → π (eq c d) → π (eq (mul a c) (mul b d)) ≔
  λ h1 h2, eq_tr (mul a c) (mul b c) (mul b d) (mul_cong_l c a b h1) (mul_cong_r b c d h2);

// ===========================================================================
// E. sign / subtraction / inverse helpers  (toward √2·√2 = 2)
// ===========================================================================

symbol opp_zero : π (eq (opp zero) zero) ≔
  eq_tr (opp zero) (add zero (opp zero)) zero
    (eq_sym' (add zero (opp zero)) (opp zero) (add_zero_left (opp zero)))
    (add_opposite_right zero);

symbol mul_neg_r a b : π (eq (mul a (opp b)) (opp (mul a b))) ≔
  eq_tr (mul a (opp b)) (mul (opp b) a) (opp (mul a b)) (mul_commutative a (opp b))
    (eq_tr (mul (opp b) a) (opp (mul b a)) (opp (mul a b)) (neg_mul b a)
      (opp_cong (mul b a) (mul a b) (mul_commutative b a)));

symbol opp_mul_opp x : π (eq (mul (opp x) (opp x)) (mul x x)) ≔
  eq_tr (mul (opp x) (opp x)) (opp (mul x (opp x))) (mul x x) (neg_mul x (opp x))
    (eq_tr (opp (mul x (opp x))) (opp (opp (mul x x))) (mul x x)
      (opp_cong (mul x (opp x)) (opp (mul x x)) (mul_neg_r x x)) (opp_opp (mul x x)));

symbol mul_nonneg a b : π (zero ≤ a) → π (zero ≤ b) → π (zero ≤ mul a b) ≔
  λ ha hb, eq_le_tr zero (mul a zero) (mul a b)
             (eq_sym' (mul a zero) zero (mul_zero_r_nonneg a ha))
             (mul_monotone a zero b ha hb);

symbol square_nonneg x : π (zero ≤ mul x x) ≔
begin
  assume x;
  refine ∨ₑ (le_total zero x) _ _
  { assume h; refine eq_le_tr zero (mul x zero) (mul x x) (eq_sym' (mul x zero) zero (mul_zero_r_nonneg x h)) (mul_monotone x zero x h h) }
  { assume h;
    have hop : π (zero ≤ opp x) { refine neg_of_nonpos x h };
    refine le_eq_tr zero (mul (opp x) (opp x)) (mul x x)
       (eq_le_tr zero (mul (opp x) zero) (mul (opp x) (opp x))
          (eq_sym' (mul (opp x) zero) zero (mul_zero_r_nonneg (opp x) hop))
          (mul_monotone (opp x) zero (opp x) hop hop))
       (opp_mul_opp x) }
end;

symbol opp_nonpos_of_nonneg x : π (zero ≤ x) → π (opp x ≤ zero) ≔
  λ h, le_eq_tr (opp x) (opp zero) zero (opp_le zero x h) opp_zero;

symbol sub_nonneg_of_le a b : π (a ≤ b) → π (zero ≤ add b (opp a)) ≔
  λ h, eq_le_tr zero (add a (opp a)) (add b (opp a)) (eq_sym' (add a (opp a)) zero (add_opposite_right a)) (add_le_mono_r (opp a) a b h);

symbol sub_undo a b : π (eq (add (add b (opp a)) a) b) ≔
  eq_tr (add (add b (opp a)) a) (add b (add (opp a) a)) b (eq_sym' (add b (add (opp a) a)) (add (add b (opp a)) a) (add_associative b (opp a) a))
    (eq_tr (add b (add (opp a) a)) (add b zero) b (add_cong_r b (add (opp a) a) zero (add_opp_l a)) (add_zero_r b));

symbol le_of_sub_nonneg a b : π (zero ≤ add b (opp a)) → π (a ≤ b) ≔
  λ h, eq_le_tr a (add zero a) b (eq_sym' (add zero a) a (add_zero_left a))
        (le_eq_tr (add zero a) (add (add b (opp a)) a) b (add_le_mono_r a zero (add b (opp a)) h) (sub_undo a b));

symbol add_eq_cancel_l z x y : π (eq (add z x) (add z y)) → π (eq x y) ≔
  λ h, ∧ᵢ (add_le_cancel_l z x y (eq_le (add z x) (add z y) h)) (add_le_cancel_l z y x (eq_ge (add z x) (add z y) h));

// ---- more constant / multiplicative helpers ----

symbol two_mul_eq_add s : π (eq (mul two s) (add s s)) ≔
  eq_tr (mul two s) (add (mul one s) (mul one s)) (add s s) (mul_distributive_left one one s)
    (add_cong (mul one s) s (mul one s) s (mul_one_left s) (mul_one_left s));

symbol not_two_le_one : π (two ≤ one) → π ⊥ ≔
  λ h, one_nonzero
    (add_eq_cancel_l one one zero (eq_tr two one (add one zero) (∧ᵢ h one_le_two) (eq_sym' (add one zero) one (add_zero_r one))));

symbol mul_le_mono_r c x y : π (zero ≤ c) → π (x ≤ y) → π (mul x c ≤ mul y c) ≔
  λ hc h, eq_le_tr (mul x c) (mul c x) (mul y c) (mul_commutative x c)
            (le_eq_tr (mul c x) (mul c y) (mul y c) (mul_monotone c x y hc h) (mul_commutative c y));

symbol mul_inv_cancel D x : π (¬ (eq D zero)) → π (eq (mul D (mul x (inv D))) x) ≔
  λ hD, eq_tr (mul D (mul x (inv D))) (mul (mul D x) (inv D)) x (mul_associative D x (inv D))
         (eq_tr (mul (mul D x) (inv D)) (mul (mul x D) (inv D)) x (mul_cong_l (inv D) (mul D x) (mul x D) (mul_commutative D x))
           (eq_tr (mul (mul x D) (inv D)) (mul x (mul D (inv D))) x (eq_sym' (mul x (mul D (inv D))) (mul (mul x D) (inv D)) (mul_associative x D (inv D)))
             (eq_tr (mul x (mul D (inv D))) (mul x one) x (mul_cong_r x (mul D (inv D)) one (mul_inverse_right D hD))
               (mul_one_r x))));

symbol le_of_sub_nonpos a b : π (add b (opp a) ≤ zero) → π (b ≤ a) ≔
  λ h, eq_le_tr b (add (add b (opp a)) a) a (eq_sym' (add (add b (opp a)) a) b (sub_undo a b))
        (le_eq_tr (add (add b (opp a)) a) (add zero a) a (add_le_mono_r a (add b (opp a)) zero h) (add_zero_left a));

symbol below_root2_one : π (below_root2 one) ≔
  ∧ᵢ zero_le_one (eq_le_tr (mul one one) one two (mul_one_r one) one_le_two);

symbol one_le_sqrt2 : π (one ≤ sqrt2) ≔
  sup_upper_bound below_root2 below_root2_has_sup one below_root2_one;

// D = 2s+2,  δ = 2 − s²,  ε = δ/D
symbol Dval : τ real ≔ add (mul two sqrt2) two;
symbol delta2 : τ real ≔ add two (opp (mul sqrt2 sqrt2));
symbol eps2 : τ real ≔ mul delta2 (inv Dval);

symbol two_le_D : π (two ≤ Dval) ≔
  eq_le_tr two (add zero two) Dval (eq_sym' (add zero two) two (add_zero_left two))
    (add_le_mono_r two zero (mul two sqrt2) (mul_nonneg two sqrt2 zero_le_two sqrt2_nonneg));

symbol one_le_D : π (one ≤ Dval) ≔ le_tr one two Dval one_le_two two_le_D;
symbol zero_le_D : π (zero ≤ Dval) ≔ le_tr zero two Dval zero_le_two two_le_D;
symbol D_pos : π (Dval ≤ zero) → π ⊥ ≔ λ h, not_one_le_zero (le_tr one Dval zero one_le_D h);
symbol D_ne_zero : π (¬ (eq Dval zero)) ≔ λ he, D_pos (eq_le Dval zero he);

symbol D_inv_one : π (eq (mul Dval (inv Dval)) one) ≔ mul_inverse_right Dval D_ne_zero;

symbol inv_D_pos : π (inv Dval ≤ zero) → π ⊥ ≔
  λ h, not_one_le_zero
    (eq_le_tr one (mul Dval (inv Dval)) zero (eq_sym' (mul Dval (inv Dval)) one D_inv_one)
       (le_eq_tr (mul Dval (inv Dval)) (mul Dval zero) zero (mul_monotone Dval (inv Dval) zero zero_le_D h)
          (mul_zero_r_nonneg Dval zero_le_D)));

symbol zero_le_invD : π (zero ≤ inv Dval) ≔
begin
  refine ∨ₑ (le_total zero (inv Dval)) _ _
  { assume h; refine h }
  { assume h; refine ⊥ₑ (inv_D_pos h) }
end;

symbol invD_le_one : π (inv Dval ≤ one) ≔
begin
  refine ∨ₑ (le_total (inv Dval) one) _ _
  { assume h; refine h }
  { assume h;
    have hD1 : π (Dval ≤ one) {
      refine eq_le_tr Dval (mul Dval one) one (eq_sym' (mul Dval one) Dval (mul_one_r Dval))
               (le_eq_tr (mul Dval one) (mul Dval (inv Dval)) one (mul_monotone Dval one (inv Dval) zero_le_D h) D_inv_one) };
    refine ⊥ₑ (not_two_le_one (le_tr two Dval one two_le_D hD1)) }
end;

symbol D_eps : π (eq (mul Dval eps2) delta2) ≔ mul_inv_cancel Dval delta2 D_ne_zero;

symbol delta_le_two : π (delta2 ≤ two) ≔
  le_eq_tr delta2 (add two zero) two
    (add_monotone two (opp (mul sqrt2 sqrt2)) zero (opp_nonpos_of_nonneg (mul sqrt2 sqrt2) (square_nonneg sqrt2)))
    (add_zero_r two);

symbol eps_le_two : π (eps2 ≤ two) ≔
  le_tr eps2 (mul two (inv Dval)) two (mul_le_mono_r (inv Dval) delta2 two zero_le_invD delta_le_two)
    (le_eq_tr (mul two (inv Dval)) (mul two one) two (mul_monotone two (inv Dval) one zero_le_two invD_le_one) (mul_one_r two));

// (s+e)² == s² + e·(2s+e)   [written with 2s as s+s]
symbol sq_add s e :
  π (eq (mul (add s e) (add s e)) (add (mul s s) (mul e (add (add s s) e)))) ≔
  eq_tr (mul (add s e) (add s e))
        (add (mul s (add s e)) (mul e (add s e)))
        (add (mul s s) (mul e (add (add s s) e)))
        (mul_distributive_left s e (add s e))
   (eq_tr (add (mul s (add s e)) (mul e (add s e)))
          (add (add (mul s s) (mul s e)) (add (mul e s) (mul e e)))
          (add (mul s s) (mul e (add (add s s) e)))
          (add_cong (mul s (add s e)) (add (mul s s) (mul s e))
                    (mul e (add s e)) (add (mul e s) (mul e e))
                    (mul_distributive_right s s e) (mul_distributive_right e s e))
    (eq_tr (add (add (mul s s) (mul s e)) (add (mul e s) (mul e e)))
           (add (add (mul s s) (mul e s)) (add (mul e s) (mul e e)))
           (add (mul s s) (mul e (add (add s s) e)))
           (add_cong_l (add (mul e s) (mul e e))
                       (add (mul s s) (mul s e)) (add (mul s s) (mul e s))
                       (add_cong_r (mul s s) (mul s e) (mul e s) (mul_commutative s e)))
     (eq_tr (add (add (mul s s) (mul e s)) (add (mul e s) (mul e e)))
            (add (mul s s) (add (mul e s) (add (mul e s) (mul e e))))
            (add (mul s s) (mul e (add (add s s) e)))
            (eq_sym' (add (mul s s) (add (mul e s) (add (mul e s) (mul e e))))
                     (add (add (mul s s) (mul e s)) (add (mul e s) (mul e e)))
                     (add_associative (mul s s) (mul e s) (add (mul e s) (mul e e))))
      (eq_tr (add (mul s s) (add (mul e s) (add (mul e s) (mul e e))))
             (add (mul s s) (add (add (mul e s) (mul e s)) (mul e e)))
             (add (mul s s) (mul e (add (add s s) e)))
             (add_cong_r (mul s s)
                         (add (mul e s) (add (mul e s) (mul e e)))
                         (add (add (mul e s) (mul e s)) (mul e e))
                         (add_associative (mul e s) (mul e s) (mul e e)))
        (add_cong_r (mul s s)
           (add (add (mul e s) (mul e s)) (mul e e))
           (mul e (add (add s s) e))
           (eq_sym' (mul e (add (add s s) e))
                    (add (add (mul e s) (mul e s)) (mul e e))
                    (eq_tr (mul e (add (add s s) e))
                           (add (mul e (add s s)) (mul e e))
                           (add (add (mul e s) (mul e s)) (mul e e))
                           (mul_distributive_right e (add s s) e)
                       (add_cong_l (mul e e)
                                   (mul e (add s s)) (add (mul e s) (mul e s))
                                   (mul_distributive_right e s s))))))))) ;

// s² + δ == 2
symbol sq_plus_delta : π (eq (add (mul sqrt2 sqrt2) delta2) two) ≔
  eq_tr (add (mul sqrt2 sqrt2) delta2)
        (add (mul sqrt2 sqrt2) (add (opp (mul sqrt2 sqrt2)) two))
        two
        (add_cong_r (mul sqrt2 sqrt2)
                    (add two (opp (mul sqrt2 sqrt2)))
                    (add (opp (mul sqrt2 sqrt2)) two)
                    (add_commutative two (opp (mul sqrt2 sqrt2))))
   (eq_tr (add (mul sqrt2 sqrt2) (add (opp (mul sqrt2 sqrt2)) two))
          (add (add (mul sqrt2 sqrt2) (opp (mul sqrt2 sqrt2))) two)
          two
          (add_associative (mul sqrt2 sqrt2) (opp (mul sqrt2 sqrt2)) two)
    (eq_tr (add (add (mul sqrt2 sqrt2) (opp (mul sqrt2 sqrt2))) two)
           (add zero two)
           two
           (add_cong_l two
                       (add (mul sqrt2 sqrt2) (opp (mul sqrt2 sqrt2))) zero
                       (add_opposite_right (mul sqrt2 sqrt2)))
      (add_zero_left two)));

// ===========================================================================
// Theorem 3, one direction : 2 ≤ √2·√2
// (rule out √2² < 2 : then s+ε ∈ E with ε>0, contradicting s = sup)
// ===========================================================================
symbol two_le_sqrt2_sq : π (two ≤ mul sqrt2 sqrt2) ≔
begin
  refine ∨ₑ (le_total two (mul sqrt2 sqrt2)) _ _
  { assume hyes; refine hyes }
  { assume hs2;   // hs2 : √2² ≤ 2 ; the ε-argument forces ε = 0, hence δ = 0, hence 2 ≤ √2²
    have dnn : π (zero ≤ delta2) { refine sub_nonneg_of_le (mul sqrt2 sqrt2) two hs2 };
    have enn : π (zero ≤ eps2) { refine mul_nonneg delta2 (inv Dval) dnn zero_le_invD };
    have mem_nonneg : π (zero ≤ add sqrt2 eps2) {
      refine eq_le_tr zero (add zero zero) (add sqrt2 eps2) (eq_sym' (add zero zero) zero (add_zero_left zero)) (add_le_mono zero sqrt2 zero eps2 sqrt2_nonneg enn) };
    have Wbound : π (mul eps2 (add (add sqrt2 sqrt2) eps2) ≤ delta2) {
      refine le_eq_tr (mul eps2 (add (add sqrt2 sqrt2) eps2)) (mul eps2 Dval) delta2
        (mul_monotone eps2 (add (add sqrt2 sqrt2) eps2) Dval enn
           (add_le_mono (add sqrt2 sqrt2) (mul two sqrt2) eps2 two (eq_le (add sqrt2 sqrt2) (mul two sqrt2) (eq_sym' (mul two sqrt2) (add sqrt2 sqrt2) (two_mul_eq_add sqrt2))) eps_le_two))
        (eq_tr (mul eps2 Dval) (mul Dval eps2) delta2 (mul_commutative eps2 Dval) D_eps) };
    have sq_le : π (mul (add sqrt2 eps2) (add sqrt2 eps2) ≤ two) {
      refine eq_le_tr (mul (add sqrt2 eps2) (add sqrt2 eps2)) (add (mul sqrt2 sqrt2) (mul eps2 (add (add sqrt2 sqrt2) eps2))) two (sq_add sqrt2 eps2)
        (le_eq_tr (add (mul sqrt2 sqrt2) (mul eps2 (add (add sqrt2 sqrt2) eps2))) (add (mul sqrt2 sqrt2) delta2) two
           (add_monotone (mul sqrt2 sqrt2) (mul eps2 (add (add sqrt2 sqrt2) eps2)) delta2 Wbound)
           sq_plus_delta) };
    have le_s : π (add sqrt2 eps2 ≤ sqrt2) {
      refine sup_upper_bound below_root2 below_root2_has_sup (add sqrt2 eps2)
               (∧ᵢ mem_nonneg sq_le) };
    have eps_le_zero : π (eps2 ≤ zero) {
      refine add_le_cancel_l sqrt2 eps2 zero (le_eq_tr (add sqrt2 eps2) sqrt2 (add sqrt2 zero) le_s (eq_sym' (add sqrt2 zero) sqrt2 (add_zero_r sqrt2))) };
    have eps_zero : π (eq eps2 zero) { refine ∧ᵢ eps_le_zero enn };
    have delta_zero : π (eq delta2 zero) {
      refine eq_tr delta2 (mul Dval eps2) zero (eq_sym' (mul Dval eps2) delta2 D_eps)
               (eq_tr (mul Dval eps2) (mul Dval zero) zero (mul_cong_r Dval eps2 zero eps_zero) (mul_zero_r Dval)) };
    refine le_of_sub_nonpos (mul sqrt2 sqrt2) two (eq_le delta2 zero delta_zero) }
end;

// ---------------------------------------------------------------------------
// REMAINING SIDE (Part A) — NOT yet proven, kept as an axiom.
//   √2·√2 ≤ 2 :  rule out √2² > 2 by exhibiting an upper bound of E smaller
//   than √2 (the s−ε / sup-minimality argument via `sup_total`).
// ---------------------------------------------------------------------------
symbol sqrt2_sq_le_two : π (mul sqrt2 sqrt2 ≤ two);

// √2·√2 = 2  (proven modulo the single remaining one-sided axiom above)
symbol sqrt2_squared : π (eq (mul sqrt2 sqrt2) two) ≔
  ∧ᵢ sqrt2_sq_le_two two_le_sqrt2_sq;

// ==== Model for the classical Dedekind reals ====
// Inspired by https://rocq-prover.org/doc/V9.0.0/stdlib/Stdlib.Reals.ClassicalDedekindReals.html#DReal

require open Stdlib.Q;

symbol qbool ≔ rat ⤳ bool;

// isLowerCut f predicate — f is the characteristic function of a lower Dedekind cut:
// - nonempty
// - bounded above
// - downward closed
// - without a greatest element
symbol isLowerCut (f : τ qbool) : Prop ≔
      (`∃ q, istrue (f q))                                     // nonempty
    ∧ (`∃ q, ¬ (istrue (f q)))                                 // bounded above
    ∧ (`∀ q, `∀ r, istrue (f q) ⇒ r ᵣ≤ q ⇒ istrue (f r))       // downward closed
    ∧ (`∀ q, istrue (f q) ⇒ `∃ r, (q ᵣ< r) ∧ istrue (f r));    // no greatest element

// Classical Dedekind reals definition
symbol DReal : Set ≔ Sigma isLowerCut; // { f : Q -> bool | isLowerCut f }

symbol cut_of (x : τ DReal) : τ qbool ≔ x s₁;

symbol cut_of_spec (x : τ DReal) : π (isLowerCut (cut_of x)) ≔ x s₂;

// ===========================================================================
// ROADMAP — building a model of the axioms above out of `DReal` + Stdlib.Q
//
// Summary: the scaffolding is easy, the arithmetic is not.  Everything that is
// specific to *being a model* (classical axioms, extensionality, decidable
// cuts) is already available or ~50 lines away.  The cost is essentially all
// in ℚ, which is currently far from a field.
// ===========================================================================

// --- 1. What already works in our favour ----------------------------------
//
// * Dedekind cuts are the ONLY viable choice, and they fit these axioms.
//   `le_antisymmetric` above demands `eq x y → x = y` (Leibniz).  Cauchy
//   sequences cannot satisfy that without quotient types, which Lambdapi does
//   not have.  Cuts can: funExt (Stdlib.FunExt) + eq_Σ (Stdlib.Prod, already
//   postulated) + case analysis on 𝔹 give "same members ⇒ equal Σ-pair".  So
//   that axiom — the scary-looking one — is among the EASIER ones here.
//
// * ℚ has canonical representatives.  `/` normalizes through Z_red_Stein, so
//   `frac 2 4` and `frac 1 2` are convertible, and `ᵣ≐_decides` gives Leibniz
//   equality from the comparison.  Hence no setoid layer on ℚ: a cut really is
//   a function on ℚ and `f` is automatically well defined.
//
// * Boolean cuts are free.  `isLowerCut` needs ℚ → 𝔹, and `isLt (x ᵣ≐ y)` is
//   exactly that; `ᵣ<` is *defined* as its `istrue`, so the bridge lemmas are
//   `reflexivity`.
//
// * The `Prop → 𝔹` decision operator needed for `sup` is derivable in ~10
//   lines:  dec p ≔ ε (λ b, istrue b ⇔ p),  spec from εᵢ (Stdlib.Epsilon) and
//   em (Stdlib.Classic).  Without it the sup cut cannot even be defined, since
//   the union condition is a Prop, not a 𝔹.
//
// * Mechanically, instantiating costs one edit: `real` is declared `constant`
//   above, so it cannot receive `rule real ↪ DReal`.  Either drop `constant`,
//   or keep this file abstract and prove the 15 axiom statements verbatim as
//   theorems in a separate DRealModel.lp.

// --- 2. The actual blocker: ℚ is neither a field nor an ordered set --------
//
//   needed                                  | status in Stdlib.Q
//   ----------------------------------------+---------------------------------
//   ᵣ≤ transitive                           | MISSING (refl/total/antisym only)
//   ᵣ≤ compatible with ᵣ+ and *ᵣ            | MISSING entirely
//   density  (q ᵣ< r → ∃ m, q ᵣ< m ᵣ< r)    | MISSING
//   Archimedean (∀ q, ∃ n:ℤ, q ᵣ< inj_z n)  | MISSING
//   subtraction ᵣ-                          | DECLARED WITH NO RULES
//   additive inverse  x ᵣ+ —ᵣ x = 0         | MISSING
//   multiplicative inverse                  | NO SYMBOL AT ALL
//   *ᵣ associativity                        | MISSING
//   distributivity (ᵣdistr*+)               | ADMITTED AXIOM
//
// Every real-number axiom bottoms out in these: `le_transitive` needs ℚ
// transitivity, cut addition needs density + Archimedean, `mul_inverse_right`
// needs ℚ inverses that do not exist yet.
//
// Cost multiplier: each ℚ lemma must survive `frac` normalization.  Compare
// `ᵣ+_assoc_div`, ~130 lines of pure rewrite plumbing for ONE associativity.
//
// HIGHEST-LEVERAGE STEP: prove the order analogue of `frac_eq` once —
//     d1 > 0 → d2 > 0 → (n1 / d1 ᵣ≤ n2 / d2  ⇔  n1 * d2 ≤ n2 * d1)
// plus "every ℚ is `frac n d` with d > 0".  Then transitivity, +-compat,
// *-compat and density all collapse to ℤ facts that Stdlib.Z already has,
// instead of repeating the ᵣ+_assoc_div experience a dozen times.

// --- 3. Difficulty of the 15 axioms, once ℚ is done ------------------------
//
// EASY      le_reflexive, le_transitive, one_nonzero, le_antisymmetric,
//           add_zero_left, add_commutative, add_associative, add_monotone
// MODERATE  cut addition itself (nonempty / bounded / open),
//           add_opposite_right  (−X = {q | ∃ r>0, −q−r ∉ X}: needs Archimedean
//             and density in earnest),
//           sup (must be TOTAL, so `em` on has_sup with a default value),
//           sup_upper_bound, sup_total
// HARD      mul and inv: sign case analysis, defined on the positives then
//           extended.  This is where Rocq's ClassicalDedekindReals spends most
//           of its length.  mul_associative, mul_distributive_right,
//           mul_inverse_right and mul_monotone all sit downstream of it.

// --- 4. Estimate -----------------------------------------------------------
//
// Roughly 1–2k lines to finish ℚ, then 1.5–3k lines for the cut construction
// and the axioms, in the proof style of this development.  For calibration:
// Rocq's ClassicalDedekindReals.v is ~1000 lines, but it sits on top of QArith
// — several thousand lines we would be writing first.

// --- 5. Cheapest next step, for a fast signal ------------------------------
//
// Instantiate `real ≔ rat` FIRST.  ℚ satisfies 13 of the 15 axioms: all but
// sup_upper_bound / sup_total, which are genuinely false for ℚ (so it is not a
// model, and `sup` would be a dummy).  But it costs only the ℚ lemmas needed
// for the cut model anyway, exercises the whole instantiation plumbing (the
// `constant` issue, whether the axiom statements are satisfiable as written),
// and smokes out any axiom that is accidentally too strong — all before
// committing to the cut construction.  `le_antisymmetric` is immediate there,
// since `ᵣ≤_antisym` already delivers Leibniz equality.
