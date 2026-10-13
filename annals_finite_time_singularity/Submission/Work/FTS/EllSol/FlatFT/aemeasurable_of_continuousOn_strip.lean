import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Have
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open scoped symmDiff

/-- A function on `ℝ × ℝ` which is continuous on the open strip `univ × (0, π/2)` is almost
everywhere measurable for the product of Lebesgue measure with Lebesgue measure restricted to
`Iθ = [0, π/2]`.  Indeed the strip `univ × Iθ` and the set where `F` is known to be continuous
differ by the null set `univ × {0, π/2}`, and restriction to a set is invariant under modification
of the set on a null set. -/
theorem aemeasurable_of_continuousOn_strip {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEMeasurable F ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) := by
  -- `univ × {0, π/2}` is null for the product of Lebesgue measures.
  have hzero : (MeasureTheory.volume.prod MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      ((Set.univ : Set ℝ) ×ˢ ({0, Real.pi / 2} : Set ℝ)) = 0 := by
    have hsub : ({0, Real.pi / 2} : Set ℝ) ⊆ ({0} : Set ℝ) ∪ {Real.pi / 2} := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] at hx ⊢
      tauto
    have h0 : MeasureTheory.volume ({0, Real.pi / 2} : Set ℝ) = 0 :=
      MeasureTheory.measure_mono_null hsub
        (MeasureTheory.measure_union_null Real.volume_singleton Real.volume_singleton)
    rw [MeasureTheory.Measure.prod_prod, h0]
    simp
  -- `Iθ` and `(0, π/2)` differ only by the endpoints.
  have hsubI : (Work.Spaces.Iθ ∆ Set.Ioo 0 (Real.pi / 2)) ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    rw [Set.mem_symmDiff] at hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hθ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [Set.mem_Ioo] at h2
      by_cases h : θ ≤ 0
      · left; linarith [h1.1]
      · right
        have h' : 0 < θ := not_le.mp h
        by_contra hc
        exact h2 ⟨h', lt_of_le_of_ne h1.2 hc⟩
    · simp only [Set.mem_Ioo] at h1
      exfalso
      exact h2 ⟨le_of_lt h1.1, le_of_lt h1.2⟩
  -- hence `univ × Iθ` and `univ × (0, π/2)` agree almost everywhere.
  have hsym : ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ) ∆
        ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
      ⊆ (Set.univ : Set ℝ) ×ˢ ({0, Real.pi / 2} : Set ℝ) := by
    intro p hp
    simp only [Set.mem_symmDiff, Set.mem_prod, Set.mem_univ, true_and] at hp ⊢
    exact hsubI hp
  have hnull := MeasureTheory.measure_mono_null hsym hzero
  have hae : ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ)
      =ᵐ[(MeasureTheory.volume.prod MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))]
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.measure_symmDiff_eq_zero_iff.mp hnull
  have hrestrict := MeasureTheory.Measure.restrict_congr_set hae
  -- the product measure with a restricted second factor is a restriction of the product measure.
  have hprod : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume).restrict
        ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ)
      = (MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) := by
    rw [← MeasureTheory.Measure.prod_restrict
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) Set.univ Work.Spaces.Iθ,
      MeasureTheory.Measure.restrict_univ]
  rw [← hprod, hrestrict]
  exact hF.aemeasurable (MeasurableSet.univ.prod measurableSet_Ioo)

end Work.FTS.EllSol.FlatFT
