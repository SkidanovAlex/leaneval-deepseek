import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Submission.Work.SSGRoute.ExtH1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Short exactness of the augmentation sequence `0 → I → k[G] → k → 0`

We prove that the short complex `augSES G` (the augmentation sequence of the group ring
`k[G]`, `k = Coeff = ULift ℤ`) is short exact.  Since `I = ker ε` with `ε : k[G] → k` the
augmentation, this is a purely set-theoretic statement on the underlying modules: the
monomorphism `I ↪ k[G]` is mono (definitionally the subtype inclusion) and `ε` is epi, and
any `x` with `ε x = 0` lies in `I` by definition.

The elementwise criterion `Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise`
does exactly this for representations over an arbitrary commutative ring; we apply it at
`k = Coeff`.
-/

namespace Work.SSGRoute

open CategoryTheory

theorem augSES_shortExact (G : Type) [Group G] :
    CategoryTheory.ShortComplex.ShortExact (Work.SSGRoute.ExtH1.augSES G) := by
  refine Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise
    (k := SSGRoute.PTExt.Coeff) (G := G) (ExtH1.augSES G) (ExtH1.instMonoAugIncl G)
    (ExtH1.epi_augHom G) ?_
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

end Work.SSGRoute
