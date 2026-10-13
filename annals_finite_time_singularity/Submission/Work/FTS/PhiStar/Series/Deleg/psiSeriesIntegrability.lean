/-
# `psiSeriesIntegrability` — the integrability/continuity hypotheses of `deriv_series`

The termwise-differentiation theorem `Work.FTS.PhiStar.Series.deriv_series`
(`Series/BslOp/Deriv.lean`) carries the hypothesis bundle `hInt`
(`Series/BslOp/Setup.lean`), which is exactly:

* `t ↦ cmode m (RemSource α ψ) t` continuous on `Ioi 0`;
* `t ↦ cmode m (RemSource α ψ) t · t^((2m+5)/α − 1)` integrable on `Ioo 0 1`;
* `t ↦ cmode m (RemSource α ψ) t · t^(−2m/α − 1)` integrable on `Ioi 1`;
* and the same three statements for the radial profile `𝒜φ = VocabO.phiA α`.

Since `RemSource α ψ z θ = α²·(𝒜φ)(z)·ψ(θ)` is *separable in `z`*,
`Series/RemSetup.lean` proves

  `cmode m (RemSource α ψ) t = α²·(𝒜φ)(t)·bmode m ψ`,

so each `cmode`-conjunct is literally a scalar multiple of the corresponding `phiA`-conjunct
and the whole content is the three analytic facts about `𝒜φ` proved here from the explicit
form `Work.FTS.PhiStar.phiA_eq`:

  `𝒜φ(z) = 4αz²(z−2)/(1+z)⁴ + 2(5+α)z(1−z)/(1+z)³`   (`z ≠ −1`).

Consequences (`ψ` is completely unconstrained — no measurability of `ψ` is needed):
`𝒜φ` is rational with its only pole at `z = −1`, hence continuous on `Ioi 0`;
`|𝒜φ(t)| ≤ (10α+10)·t` on `(0,1)` and `|𝒜φ(t)| ≤ (14α+10)/t` on `(1,∞)`, which give
integrability against the two power weights because `(2m+5)/α > 0` and `−2m/α − 2 < −1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.phiAj_smooth2
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Deleg

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The three analytic facts about `𝒜φ = VocabO.phiA α` -/

/-- `𝒜φ` is continuous on the positive half-line: it is a rational function whose only pole
is at `z = −1`. -/
theorem psiSeriesIntegrability_phiACont (α : ℝ) :
    ContinuousOn (Work.FTS.VocabO.phiA α) (Set.Ioi 0) := by
  refine ContinuousOn.congr (f := fun z : ℝ =>
    4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4
      + 2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3) ?_ ?_
  · have hne4 : ∀ x ∈ Set.Ioi (0 : ℝ), (1 + x) ^ 4 ≠ 0 := by
      intro x hx
      have hx' : (0 : ℝ) < x := hx
      have h1x : (0 : ℝ) < 1 + x := by linarith
      positivity
    have hne3 : ∀ x ∈ Set.Ioi (0 : ℝ), (1 + x) ^ 3 ≠ 0 := by
      intro x hx
      have hx' : (0 : ℝ) < x := hx
      have h1x : (0 : ℝ) < 1 + x := by linarith
      positivity
    fun_prop
  · intro z hz
    exact Work.FTS.PhiStar.phiA_eq α z (by
      intro h
      rw [h] at hz
      norm_num at hz)

/-- **Small-`z` domination**: `|𝒜φ(t)| ≤ (10α+10)·t` on `(0,1)`. -/
theorem psiSeriesIntegrability_phiA_bound_small {α : ℝ} (hα : 0 < α) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    |Work.FTS.VocabO.phiA α t| ≤ (10 * α + 10) * t := by
  have ht0 : (0 : ℝ) < t := ht.1
  have ht1 : t < 1 := ht.2
  have htne : t ≠ -1 := by linarith
  have ht4 : (0 : ℝ) < (1 + t) ^ 4 := by positivity
  have ht3 : (0 : ℝ) < (1 + t) ^ 3 := by positivity
  have h1 : |4 * α * t ^ 2 * (t - 2) / (1 + t) ^ 4| ≤ 8 * α * t := by
    rw [abs_div, abs_of_pos ht4, div_le_iff₀ ht4]
    have habs : |4 * α * t ^ 2 * (t - 2)| = 4 * α * t ^ 2 * (2 - t) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hα,
        abs_of_nonneg (sq_nonneg t), abs_of_nonpos (by linarith : t - 2 ≤ 0)]
      ring
    rw [habs]
    have hA : 4 * α * t ^ 2 * (2 - t) ≤ 8 * α * t ^ 2 := by
      have h2t : 2 - t ≤ 2 := by linarith
      have hnn : (0 : ℝ) ≤ 4 * α * t ^ 2 := by positivity
      calc 4 * α * t ^ 2 * (2 - t) ≤ 4 * α * t ^ 2 * 2 :=
            mul_le_mul_of_nonneg_left h2t hnn
        _ = 8 * α * t ^ 2 := by ring
    have hB : 8 * α * t ^ 2 ≤ 8 * α * t * (1 + t) ^ 4 := by
      have h4 : t ≤ (1 + t) ^ 4 := by
        have h5 : (1 : ℝ) ≤ (1 + t) ^ 4 := one_le_pow₀ (by linarith)
        linarith
      have hnn : (0 : ℝ) ≤ 8 * α * t := by positivity
      calc 8 * α * t ^ 2 = 8 * α * t * t := by ring
        _ ≤ 8 * α * t * (1 + t) ^ 4 := mul_le_mul_of_nonneg_left h4 hnn
    linarith
  have h2 : |2 * (5 + α) * t * (1 - t) / (1 + t) ^ 3| ≤ 2 * (5 + α) * t := by
    rw [abs_div, abs_of_pos ht3, div_le_iff₀ ht3]
    have habs : |2 * (5 + α) * t * (1 - t)| = 2 * (5 + α) * t * (1 - t) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by linarith : (0 : ℝ) < 5 + α), abs_of_nonneg ht0.le,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)]
    rw [habs]
    have hA : 1 - t ≤ (1 + t) ^ 3 := by
      have h3 : (1 : ℝ) ≤ (1 + t) ^ 3 := one_le_pow₀ (by linarith)
      linarith
    have hnn : (0 : ℝ) ≤ 2 * (5 + α) * t := by positivity
    exact mul_le_mul_of_nonneg_left hA hnn
  rw [Work.FTS.PhiStar.phiA_eq α t htne]
  calc |4 * α * t ^ 2 * (t - 2) / (1 + t) ^ 4
        + 2 * (5 + α) * t * (1 - t) / (1 + t) ^ 3|
      ≤ |4 * α * t ^ 2 * (t - 2) / (1 + t) ^ 4|
        + |2 * (5 + α) * t * (1 - t) / (1 + t) ^ 3| := abs_add_le _ _
    _ ≤ 8 * α * t + 2 * (5 + α) * t := by linarith
    _ = (10 * α + 10) * t := by ring

/-- **Large-`z` domination**: `|𝒜φ(t)| ≤ (14α+10)/t` on `(1,∞)`. -/
theorem psiSeriesIntegrability_phiA_bound_large {α : ℝ} (hα : 0 < α) {t : ℝ}
    (ht : t ∈ Set.Ioi (1 : ℝ)) :
    |Work.FTS.VocabO.phiA α t| ≤ (14 * α + 10) / t := by
  have ht1 : (1 : ℝ) < t := ht
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
  have htne : t ≠ -1 := by linarith
  have ht4 : (0 : ℝ) < (1 + t) ^ 4 := by positivity
  have ht3 : (0 : ℝ) < (1 + t) ^ 3 := by positivity
  have h1 : |4 * α * t ^ 2 * (t - 2) / (1 + t) ^ 4| ≤ 12 * α / t := by
    rw [abs_div, abs_of_pos ht4, div_le_div_iff₀ ht4 ht0]
    have habs : |4 * α * t ^ 2 * (t - 2)| = 4 * α * t ^ 2 * |t - 2| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hα,
        abs_of_nonneg (sq_nonneg t)]
    rw [habs]
    have hle : |t - 2| ≤ 3 * t := by
      rw [abs_le]
      constructor <;> linarith
    have h44 : t ^ 4 ≤ (1 + t) ^ 4 := pow_le_pow_left₀ ht0.le (by linarith) 4
    have hA : 4 * α * t ^ 2 * |t - 2| * t ≤ 4 * α * t ^ 2 * (3 * t) * t := by
      have hnn : (0 : ℝ) ≤ 4 * α * t ^ 2 * t := by positivity
      calc 4 * α * t ^ 2 * |t - 2| * t = (4 * α * t ^ 2 * t) * |t - 2| := by ring
        _ ≤ (4 * α * t ^ 2 * t) * (3 * t) := mul_le_mul_of_nonneg_left hle hnn
        _ = 4 * α * t ^ 2 * (3 * t) * t := by ring
    have hB : 4 * α * t ^ 2 * (3 * t) * t ≤ 12 * α * (1 + t) ^ 4 := by
      have h12 : 4 * α * t ^ 2 * (3 * t) * t = 12 * α * t ^ 4 := by ring
      rw [h12]
      exact mul_le_mul_of_nonneg_left h44 (by positivity)
    linarith
  have h2 : |2 * (5 + α) * t * (1 - t) / (1 + t) ^ 3| ≤ 2 * (5 + α) / t := by
    rw [abs_div, abs_of_pos ht3, div_le_div_iff₀ ht3 ht0]
    have habs : |2 * (5 + α) * t * (1 - t)| = 2 * (5 + α) * t * |1 - t| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by linarith : (0 : ℝ) < 5 + α), abs_of_nonneg ht0.le]
    rw [habs]
    have hle : |1 - t| ≤ t := by
      rw [abs_le]
      constructor <;> linarith
    have h33 : t ^ 3 ≤ (1 + t) ^ 3 := pow_le_pow_left₀ ht0.le (by linarith) 3
    have hA : 2 * (5 + α) * t * |1 - t| * t ≤ 2 * (5 + α) * t * t * t := by
      have hnn : (0 : ℝ) ≤ 2 * (5 + α) * t * t := by positivity
      calc 2 * (5 + α) * t * |1 - t| * t = (2 * (5 + α) * t * t) * |1 - t| := by ring
        _ ≤ (2 * (5 + α) * t * t) * t := mul_le_mul_of_nonneg_left hle hnn
        _ = 2 * (5 + α) * t * t * t := by ring
    have hB : 2 * (5 + α) * t * t * t ≤ 2 * (5 + α) * (1 + t) ^ 3 := by
      have h13 : 2 * (5 + α) * t * t * t = 2 * (5 + α) * t ^ 3 := by ring
      rw [h13]
      exact mul_le_mul_of_nonneg_left h33 (by positivity)
    linarith
  rw [Work.FTS.PhiStar.phiA_eq α t htne]
  calc |4 * α * t ^ 2 * (t - 2) / (1 + t) ^ 4
        + 2 * (5 + α) * t * (1 - t) / (1 + t) ^ 3|
      ≤ |4 * α * t ^ 2 * (t - 2) / (1 + t) ^ 4|
        + |2 * (5 + α) * t * (1 - t) / (1 + t) ^ 3| := abs_add_le _ _
    _ ≤ 12 * α / t + 2 * (5 + α) / t := by linarith
    _ = (14 * α + 10) / t := by ring

/-- **Integrability near `0`**: `𝒜φ(t)·t^{(2m+5)/α−1}` is integrable on `(0,1)`.

The integrand is `O(t^{(2m+5)/α})` and `(2m+5)/α > 0`, so `t^{(2m+5)/α−1}` is even locally
bounded there. -/
theorem psiSeriesIntegrability_phiAIntSmall (α : ℝ) (hα : 0 < α) (m : ℕ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.FTS.VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1) := by
  set β : ℝ := (2 * (m : ℝ) + 5) / α - 1 with hβ
  have hunit : (1 : ℝ) + β = (2 * (m : ℝ) + 5) / α := by
    rw [hβ]; ring
  have hexp : -1 < (2 * (m : ℝ) + 5) / α := by
    have h2m : (0 : ℝ) < 2 * (m : ℝ) + 5 := by positivity
    have hd : (0 : ℝ) < (2 * (m : ℝ) + 5) / α := div_pos h2m hα
    linarith
  have hmaj : MeasureTheory.IntegrableOn
      (fun t : ℝ => (10 * α + 10) * t ^ ((2 * (m : ℝ) + 5) / α)) (Set.Ioo 0 1) :=
    MeasureTheory.Integrable.const_mul
      ((intervalIntegral.integrableOn_Ioo_rpow_iff (s := (2 * (m : ℝ) + 5) / α)
        (t := (1 : ℝ)) one_pos).2 hexp) (10 * α + 10)
  have hpow : ContinuousOn (fun x : ℝ => x ^ β) (Set.Ioi 0) :=
    fun x hx => (Real.continuousAt_rpow_const x β (Or.inl (ne_of_gt hx))).continuousWithinAt
  have hcont : ContinuousOn (fun t : ℝ => Work.FTS.VocabO.phiA α t * t ^ β)
      (Set.Ioo 0 1) :=
    ((psiSeriesIntegrability_phiACont α).mul hpow).mono (fun x hx => hx.1)
  refine MeasureTheory.Integrable.mono' hmaj
    (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
  have ht0 : (0 : ℝ) < t := ht.1
  have hb := psiSeriesIntegrability_phiA_bound_small hα ht
  have hβpos : (0 : ℝ) < t ^ β := Real.rpow_pos_of_pos ht0 β
  have hmul : (t : ℝ) * t ^ β = t ^ (1 + β) := by
    rw [Real.rpow_add ht0 1 β, Real.rpow_one]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hβpos]
  calc |Work.FTS.VocabO.phiA α t| * t ^ β
      ≤ ((10 * α + 10) * t) * t ^ β := mul_le_mul_of_nonneg_right hb hβpos.le
    _ = (10 * α + 10) * (t * t ^ β) := by ring
    _ = (10 * α + 10) * t ^ (1 + β) := by rw [hmul]
    _ = (10 * α + 10) * t ^ ((2 * (m : ℝ) + 5) / α) := by rw [hunit]

/-- **Integrability at `∞`**: `𝒜φ(t)·t^{−2m/α−1}` is integrable on `(1,∞)`.

The integrand is `O(t^{−2m/α−2})` and `−2m/α − 2 < −1`. -/
theorem psiSeriesIntegrability_phiAIntLarge (α : ℝ) (hα : 0 < α) (m : ℕ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.FTS.VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1) := by
  set γ : ℝ := -(2 * (m : ℝ) / α) - 1 with hγ
  have hexp : γ - 1 < -1 := by
    rw [hγ]
    have : (0 : ℝ) ≤ 2 * (m : ℝ) / α := by positivity
    linarith
  have hmaj : MeasureTheory.IntegrableOn
      (fun t : ℝ => (14 * α + 10) * t ^ (γ - 1)) (Set.Ioi 1) :=
    MeasureTheory.Integrable.const_mul
      ((integrableOn_Ioi_rpow_iff (s := γ - 1) (t := (1 : ℝ)) one_pos).2 hexp) (14 * α + 10)
  have hpow : ContinuousOn (fun x : ℝ => x ^ γ) (Set.Ioi 0) :=
    fun x hx => (Real.continuousAt_rpow_const x γ (Or.inl (ne_of_gt hx))).continuousWithinAt
  have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi (by norm_num)
  have hcont : ContinuousOn (fun t : ℝ => Work.FTS.VocabO.phiA α t * t ^ γ)
      (Set.Ioi 1) :=
    ((psiSeriesIntegrability_phiACont α).mul hpow).mono hsub
  refine MeasureTheory.Integrable.mono' hmaj
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hb := psiSeriesIntegrability_phiA_bound_large hα ht
  have hγpos : (0 : ℝ) < t ^ γ := Real.rpow_pos_of_pos ht0 γ
  have hmul : (t : ℝ)⁻¹ * t ^ γ = t ^ (γ - 1) := by
    rw [← Real.rpow_neg_one t, ← Real.rpow_add ht0 (-1) γ]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hγpos]
  calc |Work.FTS.VocabO.phiA α t| * t ^ γ
      ≤ ((14 * α + 10) / t) * t ^ γ := mul_le_mul_of_nonneg_right hb hγpos.le
    _ = (14 * α + 10) * (t⁻¹ * t ^ γ) := by ring
    _ = (14 * α + 10) * t ^ (γ - 1) := by rw [hmul]

/-! ## The target -/

theorem psiSeriesIntegrability (α : ℝ) (hα : 0 < α) (ψ : ℝ → ℝ) :
    (∀ m : ℕ, ContinuousOn (fun t => Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t) (Set.Ioi 0)) ∧
    (∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1)) ∧
    (∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) ∧
    ContinuousOn (Work.FTS.VocabO.phiA α) (Set.Ioi 0) ∧
    (∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1)) ∧
    (∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) := by
  refine ⟨?_, ?_, ?_, psiSeriesIntegrability_phiACont α,
    fun m => psiSeriesIntegrability_phiAIntSmall α hα m,
    fun m => psiSeriesIntegrability_phiAIntLarge α hα m⟩
  · -- continuity of the `cmode`-slices, from `cmode m (RemSource α ψ) = α²·bmode m ψ·𝒜φ`
    intro m
    refine ContinuousOn.congr (f := fun t : ℝ =>
      (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ) * Work.FTS.VocabO.phiA α t) ?_ ?_
    · exact (psiSeriesIntegrability_phiACont α).const_mul _
    · intro t ht
      simp only [Work.FTS.PhiStar.Series.cmode_RemSource]
      ring
  · intro m
    have h1 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ)
          * (Work.FTS.VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1)))
        (Set.Ioo 0 1) :=
      MeasureTheory.Integrable.const_mul (psiSeriesIntegrability_phiAIntSmall α hα m) _
    refine h1.congr_fun ?_ measurableSet_Ioo
    intro t ht
    simp only [Work.FTS.PhiStar.Series.cmode_RemSource]
    ring
  · intro m
    have h1 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ)
          * (Work.FTS.VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1)))
        (Set.Ioi 1) :=
      MeasureTheory.Integrable.const_mul (psiSeriesIntegrability_phiAIntLarge α hα m) _
    refine h1.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [Work.FTS.PhiStar.Series.cmode_RemSource]
    ring

end Work.FTS.PhiStar.Series.Deleg
