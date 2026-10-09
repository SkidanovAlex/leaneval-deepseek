import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.AbsoluteGalois.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute

/-- Base case `τ = (1,1)` of Theorem 15 of Schmidt–Wingberg over `ℚ`: the refined filtration
satisfies `F(n)^{(1,1)} = F(n)`, hence `F(n)/F(n)^{(1,1)}` is trivial and `φ σ = (1, res σ)`
is a Scholz solution: it is surjective, its kernel is the open subgroup `K.fixingSubgroup`,
and both Scholz conditions (i) and (ii) are immediate because `φ σ = 1 ↔ σ ∈ K.fixingSubgroup`. -/
theorem scholz_one_one (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n : ℕ) (hn : 1 ≤ n) :
    ∃ φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n 1 1,
      SSGRoute.IsScholzSolution p K n 1 1 φ := by
  -- The left factor `F(n)/F(n)^{(1,1)}` is trivial, because `F(n)^{(1,1)} = F(n)`.
  haveI hsub : Subsingleton (Work.CohomologicalShrinking.flowQuotient p (K ≃ₐ[ℚ] K) n 1 1) := by
    have h : Work.CohomologicalShrinking.flowTerm p (K ≃ₐ[ℚ] K) n 1 1 = ⊤ := by
      rw [Work.CohomologicalShrinking.flowTerm, Work.CohomologicalShrinking.refinedTerm_one,
        Work.CohomologicalShrinking.pSeries_one]
    rw [Work.CohomologicalShrinking.flowQuotient]
    apply QuotientGroup.subsingleton_iff.mpr
    ext x
    simp [h]
  -- `φ σ = (1, res σ)`.
  let φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n 1 1 :=
    (SemidirectProduct.inr).comp (Work.AbsoluteGalois.restrictHom K)
  have hφval : ∀ σ : SSGRoute.GalQ,
      φ σ = SemidirectProduct.inr (Work.AbsoluteGalois.restrictHom K σ) := fun _ => rfl
  -- `φ σ = 1 ↔ σ ∈ K.fixingSubgroup`.
  have hφ1 : ∀ σ : SSGRoute.GalQ, φ σ = 1 ↔ σ ∈ K.fixingSubgroup := by
    intro σ
    rw [hφval σ, ← map_one (SemidirectProduct.inr), SemidirectProduct.inr_inj,
      ← Work.AbsoluteGalois.restrictHom_ker K]
    exact Iff.rfl
  refine ⟨φ, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- surjectivity
    intro y
    obtain ⟨σ, hσ⟩ := Work.AbsoluteGalois.restrictHom_surjective K y.right
    refine ⟨σ, ?_⟩
    have hy : y = SemidirectProduct.inr y.right := by
      have h := SemidirectProduct.inl_left_mul_inr_right y
      rw [show y.left = (1 : Work.CohomologicalShrinking.flowQuotient p (K ≃ₐ[ℚ] K) n 1 1)
            from Subsingleton.elim _ _] at h
      simpa using h.symm
    rw [hφval σ, hσ, ← hy]
  · -- the kernel is the open subgroup `K.fixingSubgroup`
    have hker : (φ.ker : Set SSGRoute.GalQ) = (K.fixingSubgroup : Set SSGRoute.GalQ) := by
      ext σ
      simpa using hφ1 σ
    rw [hker]
    exact IntermediateField.fixingSubgroup_isOpen K
  · -- compatibility with restriction to `K`
    intro σ
    exact SemidirectProduct.rightHom_inr _
  · -- Scholz conditions (i), (ii), (iii)
    refine ⟨?_, ?_, ?_⟩
    · intro A hA σ hσ hmem
      exact (hφ1 σ).mpr hmem
    · intro c hc hmem
      exact (hφ1 c).mpr hmem
    · intro A hA h
      obtain ⟨σ, -, hmem, hne⟩ := h
      exact absurd ((hφ1 σ).mpr hmem) hne

end Work.SSGRoute
