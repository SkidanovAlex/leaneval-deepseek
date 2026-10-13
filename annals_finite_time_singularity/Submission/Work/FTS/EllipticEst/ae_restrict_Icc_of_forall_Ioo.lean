import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

theorem ae_restrict_Icc_of_forall_Ioo {p : ℝ → Prop}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))), p θ := by
  -- The only points of `[0, π/2]` at which `p` may fail are the two endpoints.
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_
    (Set.Finite.measure_zero
      ((Set.finite_singleton (Real.pi / 2)).insert (0 : ℝ)) MeasureTheory.volume)
  intro θ hθ
  simp only [Set.mem_ofPred_eq] at hθ
  push Not at hθ
  obtain ⟨hIcc, hp⟩ := hθ
  rw [Set.mem_Icc] at hIcc
  obtain ⟨h0, hpi⟩ := hIcc
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨hne0, hnepi⟩ := hcon
  exact hp (h θ ⟨lt_of_le_of_ne h0 (Ne.symm hne0), lt_of_le_of_ne hpi hnepi⟩)

end Work.FTS.EllipticEst
