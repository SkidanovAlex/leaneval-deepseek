import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

theorem slice_ang_split (k : ℕ) (γ : ℝ) {u : ℝ → ℝ}
    (hInt : MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      = (∫ θ in Set.Icc 0 (3 * Real.pi / 8), (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        + (∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2), (iteratedDeriv (k + 2) u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) := by
  have h3 : (0 : ℝ) ≤ 3 * Real.pi / 8 := by positivity
  have h3' : 3 * Real.pi / 8 ≤ Real.pi / 2 := by
    have := Real.pi_pos; linarith
  have hsub1 : Set.Icc (0 : ℝ) (3 * Real.pi / 8) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨hx.1, le_trans hx.2 h3'⟩
  have hsub2 : Set.Icc (3 * Real.pi / 8) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_trans h3 hx.1, hx.2⟩
  have hU : Set.Icc (0 : ℝ) (3 * Real.pi / 8) ∪ Set.Icc (3 * Real.pi / 8) (Real.pi / 2)
      = Work.Spaces.Iθ := by
    ext x; constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, le_trans hx.2 h3'⟩
      · exact ⟨le_trans h3 hx.1, hx.2⟩
    · intro hx
      rcases le_total x (3 * Real.pi / 8) with h | h
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨h, hx.2⟩
  have hdisj : MeasureTheory.AEDisjoint MeasureTheory.volume
      (Set.Icc (0 : ℝ) (3 * Real.pi / 8)) (Set.Icc (3 * Real.pi / 8) (Real.pi / 2)) := by
    show MeasureTheory.volume (Set.Icc (0 : ℝ) (3 * Real.pi / 8)
      ∩ Set.Icc (3 * Real.pi / 8) (Real.pi / 2)) = 0
    refine MeasureTheory.measure_mono_null (t := ({3 * Real.pi / 8} : Set ℝ))
      (fun x hx => ?_) (Real.volume_singleton (a := 3 * Real.pi / 8))
    rw [Set.mem_inter_iff] at hx
    exact le_antisymm hx.1.2 hx.2.1
  rw [← hU]
  exact MeasureTheory.setIntegral_union₀ hdisj (measurableSet_Icc.nullMeasurableSet)
      (hInt.mono_set hsub1) (hInt.mono_set hsub2)

end Work.FTS.EllipticEst.remov
