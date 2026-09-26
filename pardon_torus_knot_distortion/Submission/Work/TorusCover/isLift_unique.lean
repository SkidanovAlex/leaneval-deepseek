import Mathlib
import Submission.Work.TorusCover.Basic

namespace Work.TorusCover

/-- A lift of `γ` through a parametrised torus is determined by its value at any single point:
two lifts agreeing at `0` are equal.  This is the standard uniqueness of lifts into a covering
space, using that the period lattice `2πℤ²` is discrete and `ℝ` is connected. -/
theorem isLift_unique (P : Work.TorusCover.TorusParam) {γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3}
    {Λ Λ' : ℝ → ℝ × ℝ} (h : Work.TorusCover.IsLift P.psi γ Λ)
    (h' : Work.TorusCover.IsLift P.psi γ Λ') (h0 : Λ 0 = Λ' 0) : Λ = Λ' := by
  have hf : Continuous (fun t : ℝ => Λ t - Λ' t) := h.1.sub h'.1
  -- the difference of the two lifts always lies in the period lattice
  have hmem : ∀ t, Λ t - Λ' t ∈ lattice := by
    intro t
    rw [← P.psiMap_eq_iff]
    simp only [psiMap_apply]
    rw [h.2 t, h'.2 t]
  -- hence the difference is locally constant (the lattice is discrete)
  have hlc : IsLocallyConstant (fun t : ℝ => Λ t - Λ' t) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro t
    obtain ⟨u, huopen, hu⟩ :=
      (isDiscrete_iff_forall_mem_exists_isOpen.mp isDiscrete_lattice)
        (Λ t - Λ' t) (hmem t)
    have htu : Λ t - Λ' t ∈ u := by
      have : Λ t - Λ' t ∈ u ∩ (lattice : Set (ℝ × ℝ)) := by
        rw [hu]; exact Set.mem_singleton _
      exact this.1
    refine ⟨(fun t : ℝ => Λ t - Λ' t) ⁻¹' u, hf.isOpen_preimage u huopen, htu, ?_⟩
    intro s hs
    have hs' : Λ s - Λ' s ∈ u := hs
    have : Λ s - Λ' s ∈ u ∩ (lattice : Set (ℝ × ℝ)) := ⟨hs', hmem s⟩
    rw [hu] at this
    exact Set.mem_singleton_iff.mp this
  -- a locally constant function on the connected space `ℝ` is constant
  have hconst : ∀ t, Λ t - Λ' t = Λ 0 - Λ' 0 := fun t =>
    hlc.apply_eq_of_preconnectedSpace t 0
  funext t
  have ht := hconst t
  rw [h0, sub_self] at ht
  exact sub_eq_zero.mp ht

end Work.TorusCover
