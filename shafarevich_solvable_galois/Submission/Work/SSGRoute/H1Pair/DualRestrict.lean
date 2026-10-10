import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

namespace Work.SSGRoute.H1Pair

/-- The action of `Gal(N/k)` on `DualMod p M` through `πN`, written as `Module.Dual.transpose` of
the action on `M` (the form produced by `Representation.dual`). -/
theorem comp_dual_eq_dualMod (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K N : IntermediateField k Ω) (πN : (N ≃ₐ[k] N) →* (K ≃ₐ[k] K))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] :
    (Rep.res πN (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) M))).ρ.dual
      = (Rep.res πN (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p M)))).ρ := by
  ext σ φ m
  have h1 := DFunLike.congr_fun (Rep.res_obj_ρ πN
    (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) M))) σ⁻¹
  have h2 := DFunLike.congr_fun (Rep.res_obj_ρ πN
    (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p M)))) σ
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, h1, h2,
    MonoidHom.comp_apply, MonoidHom.comp_apply,
    Representation.ofDistribMulAction_apply_apply,
    Representation.ofDistribMulAction_apply_apply,
    Work.SSGRoute.DualMod.dualSMul_apply, map_inv]

/-- The dual of the restricted representation is the restriction of the `DualMod` representation. -/
theorem of_dual_res_eq_res_dualMod (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K N : IntermediateField k Ω) (πN : (N ≃ₐ[k] N) →* (K ≃ₐ[k] K))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] :
    Rep.of ((Rep.res πN (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) M))).ρ.dual)
      = Rep.res πN (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p M))) := by
  rw [comp_dual_eq_dualMod p k Ω K N πN M]

end Work.SSGRoute.H1Pair
