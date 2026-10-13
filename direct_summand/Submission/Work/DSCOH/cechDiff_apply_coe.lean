import Mathlib
import Submission.Work.DSCOH.Cech
import Submission.Work.DSCOH.resAt_degZero

namespace Work.DSCOH

/-- The underlying element in the chart localization of `degPartRestrict ψ h y` is `ψ` applied to
the underlying element of `y` (the compatibility proof `h` is not used, being a proposition). -/
private lemma degPartRestrict_coe {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    {ℳ : ℕ → Submodule A M} {S T : Finset (Fin n)}
    (ψ : locAt (A := A) (M := M) S →ₗ[Poly A n] locAt (A := A) (M := M) T)
    (h : ∀ x ∈ degZero (A := A) ℳ S, ψ x ∈ degZero (A := A) ℳ T) (y : degZero (A := A) ℳ S) :
    ((degPartRestrict (A := A) (M := M) ℳ ψ h y : degZero (A := A) ℳ T) :
      locAt (A := A) (M := M) T) = ψ y.1 := rfl

theorem cechDiff_apply_coe {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] (q : ℕ)
    (x : CechTerm (A := A) (n := n) (M := M) ℳ q)
    (T : {S : Finset (Fin n) // S.card = q + 1 + 1}) :
    ((cechDiff (A := A) (n := n) (M := M) ℳ q x) T : locAt (A := A) (M := M) T.1) =
      ∑ i ∈ T.1.attach, ((-1 : ℤ) ^ ((T.1.filter fun j => j < i.1)).card) •
        resAt (M := M) (Finset.erase_subset i.1 T.1)
          (x ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩ :
            locAt (A := A) (M := M) (T.1.erase i.1)) := by
  -- Expand the differential: `cechDiff = LinearMap.pi cechDiffComp`, `cechDiffComp` is a sum of
  -- linear maps, and push the coercion `degZero ℳ T.1 → locAt T.1` through the sum and the scalars.
  simp only [cechDiff, LinearMap.pi_apply, cechDiffComp, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.coe_sum, degPartRestrict_coe, AddSubgroupClass.coe_zsmul]

end Work.DSCOH
