// classical logic

require open Stdlib.Set Stdlib.Prop Stdlib.FOL;

symbol em p : π (p ∨ ¬ p); // excluded middle

opaque symbol ¬¬ₑ p : π (¬ ¬ p) → π p ≔
begin
assume p nnp; apply ∨ₑ (em p)
{ assume h; refine h }
{ assume np; apply ⊥ₑ; refine nnp np }
end;

opaque symbol ∨¬ᵢ p q : π (p ⇒ q) → π (¬ p ∨ q) ≔
begin
assume p q pq; apply ∨ₑ (em p)
{ assume hp; refine ∨ᵢ₂ _; refine pq hp }
{ assume np; refine ∨ᵢ₁ np }
end;

opaque symbol ∃¬ᵢ a p : π (¬ (∀ p)) → π (`∃ x : τ a, ¬ (p x)) ≔
begin
assume a p not_all_p; apply ∨ₑ (em (`∃ x, ¬ (p x)))
{ assume h; apply h }
{ assume not_ex_not_p; apply ⊥ₑ; apply not_all_p;
  have h: π (`∀ x, ¬ ¬ (p x))
    { refine ¬∃ (λ x, ¬ (p x)) _; refine not_ex_not_p};
  assume x; apply ¬¬ₑ; refine h x
}
end;

opaque symbol not_and_or [p q] : π (¬ (p ∧ q)) → π (¬ p ∨ ¬ q) ≔
begin
  assume p q H;
  admit
end;

opaque symbol or_not_and [p q] : π (¬ p ∨ ¬ q) → π (¬ (p ∧ q)) ≔
begin
admitted;

opaque symbol not_or_and [p q] : π (¬ (p ∨ q)) → π (¬ p ∧ ¬ q) ≔
begin
admitted;

opaque symbol and_not_or [p q] : π (¬ p ∧ ¬ q) → π (¬ (p ∨ q)) ≔
begin
admitted;

opaque symbol or_to_imply [p q] : π ((¬ p) ∨ q) → π (p ⇒ q) ≔
begin
admitted;

opaque symbol imply_to_and [p q] : π (¬ (p ⇒ q)) → π (p ∧ (¬ q)) ≔
begin
admitted;

opaque symbol imply_to_or [p q] : π (p ⇒ q) → π ((¬ p) ∨ q) ≔
begin
admitted;

opaque symbol pierce [p] : π ((p ⇒ ⊥) ⇒ p) → π p ≔
begin
admitted;

opaque symbol ¬ₑ [p q] : π (¬ p) → π p → π q ≔
begin assume p q Hnp Hp; refine ⊥ₑ (Hnp Hp) end;


opaque symbol nforall_ex [a] p : π ((¬ (`∀ (x : τ a), p x)) ⇔ (`∃ (x : τ a), ¬ p x)) ≔ begin admit end;

opaque symbol nex_forall [a] p : π ((¬ (`∃ (x : τ a), p x)) ⇔ (`∀ (x : τ a), ¬ p x)) ≔ begin admit end;
