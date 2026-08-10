// Dedekind reals as decidable lower cuts of ℚ.
//
// Rocq:
//   Definition DReal : Set := { f : Q -> bool | isLowerCut f }.
//
// `{ x : A | P x }` is Rocq's `sig`, i.e. a dependent pair whose second
// component is a *proof*. That is exactly `Σ` (code name `Sigma`), so the
// translation is `Sigma isLowerCut`. Note we use the `Σ` of Stdlib.Prod, not
// the one in Stdlib.Sigma: the latter re-declares its own `Set`/`τ`/`π`/`=`
// and so cannot be combined with the rest of the library.

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Bool
  Stdlib.HOL Stdlib.Prod Stdlib.Q;

