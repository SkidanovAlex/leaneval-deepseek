import Mathlib
import Submission.Work.BourgainPlan.Oscillation.Lacunary.tscale_defs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.sqfn_no_per

namespace Work.BourgainPlan.Oscillation.Lacunary

open MeasureTheory Finset
open scoped BigOperators ENNReal

noncomputable section

/-- The circle multiplier of the flooring gap at scale `i`: `r θ` on the annulus
`(t ρ^{-i}, t / ⌊ρ^i⌋]` and `0` elsewhere. -/
def gapMult (ρ t : ℝ) (r : ℝ → ℂ) : ℕ → ℝ → ℂ :=
  fun i θ => r θ * (if t * ρ ^ (-(i:ℤ)) < θ ∧
      θ ≤ t / (lacScale ρ i : ℝ) then (1:ℂ) else 0)

/-- `gapFam` is the Fourier integral with the multiplier `gapMult`. -/
lemma gapFam_eq_mult (ρ t : ℝ) (r : ℝ → ℂ) (f : ℤ → ℂ) (T : Finset ℤ) (i : ℕ) (x : ℤ) :
    gapFam ρ t r f T i x =
      ∫ θ in (0:ℝ)..1, gapMult ρ t r i θ *
        (∑ n ∈ T, f n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))) *
        Complex.exp (-(2*Real.pi*Complex.I*((x:ℤ):ℂ)*(θ:ℂ))) := rfl

theorem gapFam_sq_le (ρ t cap M : ℝ) (hM : 0 < M) (hcap : 0 ≤ cap)
    (hcount : ∀ (θ : ℝ) (s : Finset ℕ),
      ∑ i ∈ s, (if t * ρ ^ (-(i:ℤ)) < θ ∧
          θ ≤ t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) then (1:ℝ) else 0) ≤ M)
    (r : ℝ → ℂ) (hr : Measurable r) (hrb : ∀ θ, ‖r θ‖ ≤ cap)
    (f : ℤ → ℂ) (T : Finset ℤ) :
    (∑' i : ℕ, ∫⁻ x : ℤ,
        ‖Work.BourgainPlan.Oscillation.Lacunary.gapFam ρ t r f T i x‖ₑ ^ (2:ℝ)
      ∂MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal (M * cap ^ 2) *
          ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  classical
  have hA : 0 ≤ M * cap ^ 2 := mul_nonneg hM.le (sq_nonneg cap)
  have hm : ∀ j, Measurable (gapMult ρ t r j) := by
    intro j
    refine hr.mul ?_
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_Ioc
  have hb : ∀ j, ∃ C : ℝ, ∀ θ, ‖gapMult ρ t r j θ‖ ≤ C := by
    intro j
    refine ⟨cap, fun θ => ?_⟩
    have hle : ‖(if t * ρ ^ (-(j:ℤ)) < θ ∧
        θ ≤ t / (lacScale ρ j : ℝ) then (1:ℂ) else 0)‖ ≤ 1 := by
      split_ifs <;> simp
    calc ‖gapMult ρ t r j θ‖
        = ‖r θ‖ * ‖(if t * ρ ^ (-(j:ℤ)) < θ ∧
            θ ≤ t / (lacScale ρ j : ℝ) then (1:ℂ) else 0)‖ := by
          simp only [gapMult, norm_mul]
      _ ≤ cap * 1 := mul_le_mul (hrb θ) hle (by positivity) hcap
      _ = cap := by ring
  have hsum : ∀ θ, Summable (fun j : ℕ => ‖gapMult ρ t r j θ‖ ^ 2) ∧
      ∑' j : ℕ, ‖gapMult ρ t r j θ‖ ^ 2 ≤ Real.sqrt (M * cap ^ 2) ^ 2 := by
    intro θ
    let ind : ℕ → ℝ := fun j => if t * ρ ^ (-(j:ℤ)) < θ ∧
        θ ≤ t / (lacScale ρ j : ℝ) then (1:ℝ) else 0
    have hind : ∀ j, ind j = (if t * ρ ^ (-(j:ℤ)) < θ ∧
        θ ≤ t / (lacScale ρ j : ℝ) then (1:ℝ) else 0) := fun j => rfl
    have hind_nn : ∀ j, 0 ≤ ind j := by
      intro j; rw [hind j]; split_ifs <;> norm_num
    have hcount_ind : ∀ s : Finset ℕ, ∑ j ∈ s, ind j ≤ M := by
      intro s
      have : ∑ j ∈ s, ind j = ∑ j ∈ s, (if t * ρ ^ (-(j:ℤ)) < θ ∧
          θ ≤ t / (lacScale ρ j : ℝ) then (1:ℝ) else 0) :=
        Finset.sum_congr rfl (fun j _ => hind j)
      rw [this]; exact hcount θ s
    have hind_summ : Summable ind := summable_of_sum_le hind_nn hcount_ind
    have hind_le : ∑' j, ind j ≤ M := Real.tsum_le_of_sum_le hind_nn hcount_ind
    have hbound : ∀ j, ‖gapMult ρ t r j θ‖ ^ 2 ≤ cap ^ 2 * ind j := by
      intro j
      by_cases hj : t * ρ ^ (-(j:ℤ)) < θ ∧ θ ≤ t / (lacScale ρ j : ℝ)
      · have h1 : gapMult ρ t r j θ = r θ := by
          simp only [gapMult]; rw [if_pos hj, mul_one]
        have h2 : ind j = 1 := by rw [hind j, if_pos hj]
        rw [h1, h2, mul_one]
        exact pow_le_pow_left₀ (norm_nonneg _) (hrb θ) 2
      · have h1 : gapMult ρ t r j θ = 0 := by
          simp only [gapMult]; rw [if_neg hj, mul_zero]
        have h2 : ind j = 0 := by rw [hind j, if_neg hj]
        rw [h1, h2, mul_zero]
        simp
    have hbound_summ : Summable (fun j => cap ^ 2 * ind j) := hind_summ.mul_left (cap ^ 2)
    have hm_summ : Summable (fun j => ‖gapMult ρ t r j θ‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun j => sq_nonneg _) hbound hbound_summ
    refine ⟨hm_summ, ?_⟩
    rw [Real.sq_sqrt hA]
    calc ∑' j : ℕ, ‖gapMult ρ t r j θ‖ ^ 2
        ≤ ∑' j : ℕ, cap ^ 2 * ind j := hm_summ.tsum_le_tsum hbound hbound_summ
      _ = cap ^ 2 * ∑' j : ℕ, ind j := tsum_mul_left
      _ ≤ cap ^ 2 * M := mul_le_mul_of_nonneg_left hind_le (sq_nonneg cap)
      _ = M * cap ^ 2 := by ring
  have hLHS : (∑' i : ℕ, ∫⁻ x : ℤ,
        ‖gapFam ρ t r f T i x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count)
      = ∫⁻ x : ℤ, (∑' i : ℕ, ‖gapFam ρ t r f T i x‖ₑ ^ (2:ℝ))
          ∂MeasureTheory.Measure.count := by
    simp_rw [lintegral_count]
    exact ENNReal.tsum_comm
  rw [hLHS]
  calc ∫⁻ x : ℤ, (∑' i : ℕ, ‖gapFam ρ t r f T i x‖ₑ ^ (2:ℝ))
          ∂MeasureTheory.Measure.count
      = ∫⁻ x : ℤ, (∑' i : ℕ, ‖∫ θ in (0:ℝ)..1, gapMult ρ t r i θ *
            (∑ n ∈ T, f n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))) *
            Complex.exp (-(2*Real.pi*Complex.I*((x:ℤ):ℂ)*(θ:ℂ)))‖ₑ ^ (2:ℝ))
          ∂MeasureTheory.Measure.count := by
        refine lintegral_congr (fun x => ?_)
        exact tsum_congr (fun i => by rw [gapFam_eq_mult])
    _ ≤ ENNReal.ofReal (Real.sqrt (M * cap ^ 2) ^ 2) *
          ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
        sqfn_no_per (gapMult ρ t r) (Real.sqrt (M * cap ^ 2)) hm hb hsum f T
    _ = ENNReal.ofReal (M * cap ^ 2) *
          ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
        rw [Real.sq_sqrt hA]

end

end Work.BourgainPlan.Oscillation.Lacunary
