import Mathlib
import Submission.Work.SSSR.Filtration
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits
/-- **`d¹` depends only on the filtration functor `ξ.F`.**  If two filtrations of the same chain
complex have the same underlying functor `F`, then their differentials `d¹` are identified by the
canonical transports `eqToHom` of the graded pieces.  The point is that `kF` is the connecting map
`δ` of the short exact sequence `0 → F_s → F_{s+1} → F_{s+1}/F_s → 0`, whose `ShortExact` structure
is a `Prop` and hence proof-irrelevant, while `jF` is `homologyMap (cokernel.π (incF F (s-1)))`
(the identity for `s = 0`), which mentions `F` only.

Suggested route: prove the two halves separately, namely
`eqToHom (congrArg (fun F => (grF F (s+1)).homology ((s+1)+t)) h) ≫ kF ξ' s t
  = kF ξ s t ≫ eqToHom (congrArg (fun F => (F.obj s).homology (s+t)) h)` and
`eqToHom (congrArg (fun F => (F.obj s).homology (s+t)) h) ≫ jF ξ' s t
  = jF ξ s t ≫ eqToHom (congrArg (fun F => (grF F s).homology (s+t)) h)`,
then compose. Unpack both filtrations with `cases ξ` / `cases ξ'`, use the fact that
`ShortComplex.ShortExact` is a `Prop` (so `sesF_shortExact` is proof-irrelevant), and finish by
`subst`/`simp`. -/
theorem d1_eqToHom_conj {C : ChainComplex (ModuleCat R) ℕ} (ξ ξ' : Work.SSSR.Filtration R C)
    (h : ξ.F = ξ'.F) (s t : ℕ) :
    eqToHom (congrArg (fun F => (Work.SSSR.grF F (s+1)).homology ((s+1)+t)) h) ≫ Work.SSSR.d1 ξ' s t
      = Work.SSSR.d1 ξ s t ≫ eqToHom (congrArg (fun F => (Work.SSSR.grF F s).homology (s+t)) h) := by
  -- Unpack both filtrations.  `d1` only involves the functor field `F` and the `Prop`-valued
  -- `mono` field, so after rewriting `F'` as `F` the two sides are definitionally equal.
  cases ξ with
  | mk F mono incl mono_incl compat sat =>
  cases ξ' with
  | mk F' mono' incl' mono_incl' compat' sat' =>
  change F = F' at h
  subst h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  -- Both sides are now `d1` of two filtrations with the same functor field; these agree
  -- definitionally because `ShortExact` is a `Prop`.
  rfl

end Work.SSSR
