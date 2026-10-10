import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Ring
import Submission.Work.GroupCohomology.ConnectingLift
import Submission.Work.GroupCohomology.CyclicTriv
import Submission.Work.GroupCohomology.Shapiro
import Submission.Work.GroupCohomology.TrivialGroup
import Submission.Work.GroupCohomology.Vanishing
import Submission.Work.Tate.DimensionShiftH
import Submission.Work.Tate.Equivs
import Submission.Work.Tate.Hm1ToCoinv_injective
import Submission.Work.Tate.coind_augmentation_eq_ker_norm
import Submission.Work.Tate.coind_norm_eq_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `𝔽_p`-linear dual of a finite `𝔽_p[G]`-module

Auxiliary vocabulary for `Work.SSGRoute.sha2_image_of_Hm2`: the finite-group Tate duality
`Ĥ⁻²(G, M^*) ≅ H¹(G, M)^∨` (which identifies the workspace model `Work.Tate.Hm2` of `Ĥ⁻²`
with the dual of `H¹`) needs the dual module `M^* = Hom(M, 𝔽_p)` with its dual `G`-action
`(g • f) m = f (g⁻¹ • m)`.

This file only provides the module and its instances; the duality itself is a separate lemma.
-/

namespace Work.SSGRoute

/-- The `𝔽_p`-linear dual of a `ZMod p`-module `M`. -/
abbrev DualMod (p : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod p) M] : Type :=
  M →ₗ[ZMod p] ZMod p

namespace DualMod

variable (p : ℕ) {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction G M] [SMulCommClass G (ZMod p) M]

/-- The dual action on `Hom(M, 𝔽_p)`: `(g • f) m = f (g⁻¹ • m)`. -/
def dualSMul (g : G) (f : DualMod p M) : DualMod p M where
  toFun m := f (g⁻¹ • m)
  map_add' m n := by simp
  map_smul' c m := by
    rw [smul_comm, map_smul]
    rfl

instance : SMul G (DualMod p M) := ⟨dualSMul p⟩

@[simp] lemma dualSMul_apply (g : G) (f : DualMod p M) (m : M) :
    (g • f : DualMod p M) m = f (g⁻¹ • m) := rfl

instance : DistribMulAction G (DualMod p M) where
  one_smul f := by ext m; simp
  mul_smul g h f := by ext m; simp [mul_smul]
  smul_zero g := by ext m; simp
  smul_add g f h := by ext m; simp

instance : SMulCommClass G (ZMod p) (DualMod p M) where
  smul_comm g c f := by
    ext m
    simp only [dualSMul_apply, LinearMap.smul_apply]

end DualMod

end Work.SSGRoute
