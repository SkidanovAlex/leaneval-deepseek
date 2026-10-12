import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.Submodule.LinearMap
import Submission.Work.BoseB4.Cre_cre_comm
import Submission.Work.BoseB4.ModeFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

/-- Creation operators of superpositions commute.

`creOf m f = ∑ l, f l • cre m l` is a linear combination of the single-mode
creation operators `cre m l`, which act on the monomial-coefficient model of the
Fock space by the shifts `p ↦ p(· − e_l)`.  Singles commute by
`Work.BoseB4.Cre_cre_comm`, and a double sum of commuting terms may be evaluated in
either order, whence the same holds for the superpositions.

Pointwise, for `p : RealFock m`,
`creOf m f (creOf m g p) = ∑ a, ∑ b, (f a * g b) • (cre m a (cre m b p))`, and
`creOf m g (creOf m f p) = ∑ a, ∑ b, (g a * f b) • (cre m a (cre m b p))`; the
latter, after swapping the order of summation and moving into the first sum with
`Cre_cre_comm`, is the former term by term. -/
theorem CreOf_cre_comm {m : ℕ} (f g : Fin m → ℝ) :
    (Work.BoseB4.creOf m f).comp (Work.BoseB4.creOf m g)
      = (Work.BoseB4.creOf m g).comp (Work.BoseB4.creOf m f) := by
  apply LinearMap.ext
  intro p
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [Work.BoseB4.creOf, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    Finset.smul_sum, smul_smul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← LinearMap.comp_apply, Work.BoseB4.Cre_cre_comm, LinearMap.comp_apply, mul_comm]

end Work.BoseB4
