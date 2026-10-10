import Mathlib.FieldTheory.IsSepClosed
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

-- `IntermediateField ℚ (AlgebraicClosure ℚ)` carries several non-definitionally-equal instance
-- paths (see `Submission/Work/AbsoluteGalois/Basic.lean`); full definitional unfolding makes the
-- transport between them transparent to `isDefEq`.
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

theorem flowKernel_fixedField (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (n i j : ℕ)
    (ψ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ)) (hsurj : Function.Surjective ψ)
    (hflow : ∀ σ, Work.CohomologicalShrinking.flowQuot p (K ≃ₐ[ℚ] K) n i j (ψ σ) =
      AlgEquiv.restrictNormalHom K σ) :
    ∃ N : IntermediateField ℚ SSGRoute.QBar, FiniteDimensional ℚ N ∧ IsGalois ℚ N ∧ K ≤ N ∧
      (∀ σ : SSGRoute.GalQ, σ ∈ N.fixingSubgroup ↔ ψ σ = 1) ∧
      (∀ A : ValuationSubring SSGRoute.QBar,
        SSGRoute.IsSplitIn ℚ N A ↔ ∀ σ ∈ SSGRoute.decomp ℚ A, ψ σ = 1) ∧
      ∀ A : ValuationSubring SSGRoute.QBar,
        SSGRoute.IsRamifiedIn ℚ N A ↔ ∃ σ, SSGRoute.IsInertia ℚ A σ ∧ ψ σ ≠ 1 := by
  classical
  -- `ℚ̄/ℚ` is Galois; this needs `IsAlgClosure ℚ (AlgebraicClosure ℚ)` to be found by
  -- type class search (Mathlib's instance is registered with a transparency option that hides
  -- it — see `Submission/Work/AbsoluteGalois/Basic.lean`).
  haveI hAlgClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI hGalQ : IsGalois ℚ SSGRoute.QBar :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  -- the candidate is the fixed field of the (open, hence closed) kernel of `ψ`
  have hclosed : IsClosed (ψ.ker : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    Subgroup.isClosed_of_isOpen ψ.ker hopen
  let N : IntermediateField ℚ SSGRoute.QBar := IntermediateField.fixedField ψ.ker
  have hfix : N.fixingSubgroup = ψ.ker := by
    have h := InfiniteGalois.fixingSubgroup_fixedField (k := ℚ) (K := AlgebraicClosure ℚ)
      (⟨ψ.ker, hclosed⟩ : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    simpa [N] using h
  refine ⟨N, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `N/ℚ` is finite because `ψ.ker` is open
    refine (InfiniteGalois.isOpen_iff_finite (k := ℚ) (K := AlgebraicClosure ℚ) N).mp ?_
    rw [hfix]
    exact hopen
  · -- `N/ℚ` is Galois because `ψ.ker` is normal
    exact IsGalois.of_fixedField_normal_subgroup (K := ℚ) (L := AlgebraicClosure ℚ) ψ.ker
      (hn := MonoidHom.normal_ker ψ)
  · -- `K ≤ N` because `ψ.ker ≤ Gal(ℚ̄/K)`
    show K ≤ IntermediateField.fixedField ψ.ker
    rw [IntermediateField.le_iff_le]
    intro σ hσ
    have hKnorm : Normal ℚ K := inferInstance
    rw [← @IntermediateField.restrictNormalHom_ker ℚ (AlgebraicClosure ℚ) _ _ _ K hKnorm,
      MonoidHom.mem_ker]
    rw [← hflow σ, MonoidHom.mem_ker.mp hσ, map_one]
  · intro σ
    rw [hfix, MonoidHom.mem_ker]
  · intro A
    rw [SSGRoute.IsSplitIn, SetLike.le_def]
    constructor
    · intro h σ hσ
      exact MonoidHom.mem_ker.mp (hfix ▸ h hσ)
    · intro h σ hσ
      exact hfix.symm ▸ MonoidHom.mem_ker.mpr (h σ hσ)
  · intro A
    rw [SSGRoute.IsRamifiedIn, hfix]
    constructor
    · rintro ⟨σ, hI, hne⟩
      exact ⟨σ, hI, fun h => hne (MonoidHom.mem_ker.mpr h)⟩
    · rintro ⟨σ, hI, hne⟩
      exact ⟨σ, hI, fun h => hne (MonoidHom.mem_ker.mp h)⟩

end Work.SSGRoute
