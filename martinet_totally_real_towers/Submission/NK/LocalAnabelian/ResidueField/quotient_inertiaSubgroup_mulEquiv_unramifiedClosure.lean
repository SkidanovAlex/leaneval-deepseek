import Mathlib
import Submission.NK.LocalAnabelian.ResidueField.Defs
import Submission.NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure

namespace NK.LocalAnabelian.ResidueField

open scoped Classical
open IntermediateField

set_option linter.style.haveILetI false

/-- The quotient of `Gal(K'/κ)` by the inertia subgroup is the automorphism group of the
maximal unramified extension inside `K'`. -/
theorem quotient_inertiaSubgroup_mulEquiv_unramifiedClosure {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsGalois κ K'] (p : ℕ)
    (hgal : IsGalois κ (unramifiedClosure (κ := κ) (K' := K') p)) :
    Nonempty (Gal(K'/κ) ⧸ inertiaSubgroup (κ := κ) (K' := K') p ≃*
      (↥(unramifiedClosure (κ := κ) (K' := K') p) ≃ₐ[κ]
        ↥(unramifiedClosure (κ := κ) (K' := K') p))) := by
  let L := unramifiedClosure (κ := κ) (K' := K') p
  haveI : Normal κ L := hgal.to_normal
  let ρ : Gal(K'/κ) →* (L ≃ₐ[κ] L) := AlgEquiv.restrictNormalHom (F := κ) (K₁ := K') L
  have hsurj : Function.Surjective ρ := by
    simpa only [ρ] using AlgEquiv.restrictNormalHom_surjective (F := κ) (K₁ := ↥L) (E := K')
  have hker : inertiaSubgroup (κ := κ) (K' := K') p = ρ.ker := by
    rw [show ρ.ker = L.fixingSubgroup from IntermediateField.restrictNormalHom_ker L]
    exact inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure p
  exact ⟨QuotientGroup.liftEquiv (inertiaSubgroup (κ := κ) (K' := K') p) (φ := ρ) hsurj hker⟩

end NK.LocalAnabelian.ResidueField
