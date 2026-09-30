import Mathlib
import Submission.Work.HomologyMV.Concrete
import Submission.Work.HomologyMV.LinAlg
import Submission.Work.HomologyMV.ker_toLin_iso_int_of_normalForm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HomologyMV

open CategoryTheory

/-- Kernel certificate for the concrete Mayer–Vietoris matrices `wConcrete`, i.e. `KernelCert wConcrete`: the kernel of `φ₀`, `φ₁`, `φ₂` is zero (from the explicit left inverses `inv0Mat`, `inv1Mat`, `inv2Mat`), the kernel of `φ₃` is `ℤ` (from the unimodular normal form `P3Mat` via `ker_toLin_iso_int_of_normalForm`), and the kernel of `φ_k` is zero for `k ≥ 4` and for `k < 0` (where both model groups are zero, so the kernel is a trivial module). -/
theorem wConcrete_ker : KernelCert wConcrete := by
  intro k hk
  rcases lt_or_ge k 4 with hk4 | hk4
  · -- degrees `0, 1, 2, 3`
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl | rfl | rfl
    · -- degree `0`: `φ₀` is injective, with left inverse `inv0Mat`
      have hker : (wConcrete 0).hom.ker = ⊥ := by
        rw [wConcrete_hom, allPhi_zero]
        exact ker_toLin'_eq_bot_of_mul_eq_one phi0Mat inv0Mat inv0Mat_mul_phi0Mat
      rw [hker, kerModel_eq_zero 0 (by norm_num)]
      have : Subsingleton ↥(freeMod 0) := subsingleton_freeMod_zero
      exact linearEquiv_of_subsingleton
    · -- degree `1`: `φ₁` is an isomorphism, with inverse `inv1Mat`
      have hker : (wConcrete 1).hom.ker = ⊥ := by
        rw [wConcrete_hom, allPhi_one]
        exact ker_toLin'_eq_bot_of_mul_eq_one phi1Mat inv1Mat inv1Mat_mul_phi1Mat
      rw [hker, kerModel_eq_zero 1 (by norm_num)]
      have : Subsingleton ↥(freeMod 0) := subsingleton_freeMod_zero
      exact linearEquiv_of_subsingleton
    · -- degree `2`: `φ₂` is an isomorphism, with inverse `inv2Mat`
      have hker : (wConcrete 2).hom.ker = ⊥ := by
        rw [wConcrete_hom, allPhi_two]
        exact ker_toLin'_eq_bot_of_mul_eq_one phi2Mat inv2Mat inv2Mat_mul_phi2Mat
      rw [hker, kerModel_eq_zero 2 (by norm_num)]
      have : Subsingleton ↥(freeMod 0) := subsingleton_freeMod_zero
      exact linearEquiv_of_subsingleton
    · -- degree `3`: `φ₃` has kernel `ℤ`, via the unimodular normal form `P3Mat`
      rw [wConcrete_hom, allPhi_three, kerModel_three]
      exact ker_toLin_iso_int_of_normalForm 4 phi3Mat P3Mat Q3Mat
        P3Mat_mul_Q3Mat Q3Mat_mul_P3Mat phi3Mat_mul_P3Mat
  · -- degrees `≥ 4`: both model groups are trivial, so is the kernel
    rw [kerModel_eq_zero_of_ge k hk4]
    have : Subsingleton ↥(ModelM k) := subsingleton_modelM_of_ge k hk4
    have : Subsingleton ↥(freeMod 0) := subsingleton_freeMod_zero
    exact linearEquiv_of_subsingleton

end Work.HomologyMV
