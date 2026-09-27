import Mathlib
import Submission.Work.EKLCompSym.Basic

namespace Work.EKLCompSym

open Work.EKLContract MeasureTheory

/-- `iso τ` packaged as a measurable equivalence of `X₃` (it is a homeomorphism, since its
inverse is `iso τ⁻¹`). -/
noncomputable def isoEquiv (τ : Equiv.Perm (Fin 3)) : X3 ≃ᵐ X3 where
  toFun := iso τ
  invFun := iso τ⁻¹
  left_inv := iso_symm_left τ
  right_inv := iso_symm_right τ
  measurable_toFun := measurable_iso τ
  measurable_invFun := measurable_iso τ⁻¹

/-- A measurable equivalence pushes measures forward compatibly on *every* set, not only on the
measurable ones. -/
theorem map_iso_apply (μ : MeasureTheory.Measure X3) (τ : Equiv.Perm (Fin 3)) (s : Set X3) :
    (MeasureTheory.Measure.map (iso τ) μ) s = μ ((iso τ) ⁻¹' s) :=
  MeasurableEquiv.map_apply (isoEquiv τ) s

/-- The pushforward of a null set under the bijection `iso τ` is null. -/
theorem map_iso_image_null {μ : MeasureTheory.Measure X3} (τ : Equiv.Perm (Fin 3))
    {N : Set X3} (hN : μ N = 0) : (MeasureTheory.Measure.map (iso τ) μ) (iso τ '' N) = 0 := by
  rw [map_iso_apply μ τ (iso τ '' N), Set.preimage_image_eq _ (iso_injective τ)]
  exact hN

theorem nonExceptional_map_iso {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (τ : Equiv.Perm (Fin 3))
    {a b c : Fin 3} (hab : a ≠ b) (hτ : τ⁻¹ a ≠ τ⁻¹ b)
    (h : Work.EKLContract.NonExceptional μ hab c) :
    Work.EKLContract.NonExceptional (MeasureTheory.Measure.map (Work.EKLCompSym.iso τ) μ) hτ (τ⁻¹ c) := by
  obtain ⟨N, hN, hprop⟩ := h
  refine ⟨iso τ '' N, map_iso_image_null τ hN, ?_⟩
  intro K hK hdisj hKpos δ hδ
  -- pull the compact set back along `iso τ`
  have hK'pre : (iso τ) ⁻¹' K = iso τ⁻¹ '' K := by
    ext x
    constructor
    · intro hx
      exact ⟨iso τ x, hx, iso_symm_left τ x⟩
    · rintro ⟨y, hyK, rfl⟩
      show iso τ (iso τ⁻¹ y) ∈ K
      rwa [iso_symm_right τ y]
  have hK'comp : IsCompact ((iso τ) ⁻¹' K) := by
    rw [hK'pre]
    exact hK.image (continuous_iso τ⁻¹)
  have hdisj' : Disjoint ((iso τ) ⁻¹' K) N := by
    rw [Set.disjoint_left]
    intro x hxK hxN
    exact (Set.disjoint_left.mp hdisj) hxK (Set.mem_image_of_mem (iso τ) hxN)
  have hK'pos : 0 < μ ((iso τ) ⁻¹' K) := by
    rw [← map_iso_apply μ τ K]
    exact hKpos
  obtain ⟨z', hz'K', s, g', hg'V, hret', heq', hg'not⟩ :=
    hprop ((iso τ) ⁻¹' K) hK'comp hdisj' hK'pos δ hδ
  refine ⟨iso τ z', hz'K', s, conjPerm τ g', (conjPerm_mem_V_iff τ g' δ).mpr hg'V, ?_, ?_, ?_⟩
  · rw [← conjPerm_apply_aPrime τ c s, ← iso_smul τ (aPrime c s) z']
    exact hret'
  · rw [← conjPerm_apply_aPrime τ c s, ← iso_smul τ (aPrime c s) z', ← iso_smul τ g' z', heq']
  · intro hmem
    exact hg'not ((conjPerm_mem_Lset_iff τ hab hτ g').mp hmem)

end Work.EKLCompSym
