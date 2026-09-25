import Mathlib

open MeasureTheory Filter ENNReal

namespace Work.BourgainPlan.IonescuWainger

/-- Truncating an arbitrary function `h : ℤ → ℂ` to the symmetric intervals `Icc (-j) j`
and integrating the `p`-th power against the counting measure converges, as `j → ∞`,
to the full integral.  This is the monotone convergence theorem applied to the
increasing family of truncated functions. -/
theorem tendsto_lintegral_Icc_truncation (p : ℝ) (hp : 0 < p) (h : ℤ → ℂ) :
    Filter.Tendsto
      (fun j : ℕ => ∫⁻ k : ℤ,
        ENNReal.ofReal ‖(if k ∈ Finset.Icc (-(j : ℤ)) (j : ℤ) then h k else 0 : ℂ)‖ ^ p
          ∂MeasureTheory.Measure.count)
      Filter.atTop
      (nhds (∫⁻ k : ℤ, ENNReal.ofReal ‖h k‖ ^ p ∂MeasureTheory.Measure.count)) := by
  refine MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
    (μ := MeasureTheory.Measure.count)
    (f := fun j k => ENNReal.ofReal ‖(if k ∈ Finset.Icc (-(j : ℤ)) (j : ℤ) then h k else 0 : ℂ)‖ ^ p)
    (F := fun k => ENNReal.ofReal ‖h k‖ ^ p) ?_ ?_ ?_
  · -- measurability of the truncations (every function on `ℤ` is measurable)
    intro n
    exact (measurable_of_countable _).aemeasurable
  · -- monotonicity in `j` of the truncations
    filter_upwards with k
    intro a b hab
    have hsub : Finset.Icc (-(a : ℤ)) (a : ℤ) ⊆ Finset.Icc (-(b : ℤ)) (b : ℤ) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      obtain ⟨h1, h2⟩ := hk
      constructor <;> omega
    show ENNReal.ofReal ‖(if k ∈ Finset.Icc (-(a : ℤ)) (a : ℤ) then h k else 0 : ℂ)‖ ^ p ≤
      ENNReal.ofReal ‖(if k ∈ Finset.Icc (-(b : ℤ)) (b : ℤ) then h k else 0 : ℂ)‖ ^ p
    by_cases hb : k ∈ Finset.Icc (-(b : ℤ)) (b : ℤ)
    · rw [if_pos hb]
      by_cases ha : k ∈ Finset.Icc (-(a : ℤ)) (a : ℤ)
      · rw [if_pos ha]
      · rw [if_neg ha]
        simp only [norm_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hp]
        exact zero_le
    · have ha : k ∉ Finset.Icc (-(a : ℤ)) (a : ℤ) := fun hm => hb (hsub hm)
      rw [if_neg ha, if_neg hb]
  · -- pointwise convergence: each `k` lies in `Icc (-j) j` for all large `j`
    refine Filter.Eventually.of_forall (fun k => ?_)
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop k.natAbs] with n hn
    have hmem : k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      simp only [Finset.mem_Icc]
      constructor
      · have h1 : -(n : ℤ) ≤ -((k.natAbs : ℤ)) := by omega
        have h2 : -((k.natAbs : ℤ)) ≤ k := by
          rw [Int.natCast_natAbs]; exact neg_abs_le k
        linarith
      · have h2 : (k.natAbs : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
        linarith [Int.le_natAbs (a := k)]
    rw [if_pos hmem]

end Work.BourgainPlan.IonescuWainger
