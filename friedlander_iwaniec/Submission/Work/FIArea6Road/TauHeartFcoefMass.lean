import Mathlib
import Submission.Work.FIArea6Road.TauHeartDefs

namespace Work.FIArea6Road

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- **Bound for the `ℤ`-sum of `(1 + (θℓ)²)⁻¹`.**

`Σ_{ℓ∈ℤ} (1 + (θℓ)²)⁻¹ ≤ 1 + 4/θ` for `θ > 0`.

Decomposing the `ℤ`-sum as `ℓ = 0` plus the two half-lines, the sum equals
`1 + 2·Σ_{n≥1}(1+(θn)²)⁻¹`.  The function `x ↦ (1+(θx)²)⁻¹` is nonnegative, antitone on
`[0,∞)` and integrable with `∫_0^∞ (1+(θx)²)⁻¹ dx = π/(2θ)`, so the integral test gives
`Σ_{n≥1}(1+(θn)²)⁻¹ ≤ π/(2θ)`; hence the total is at most `1 + π/θ ≤ 1 + 4/θ`. -/
theorem zsumInvBound (θ : ℝ) (hθ : 0 < θ) :
    ∑' ℓ : ℤ, (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹ ≤ 1 + 4 / θ := by
  set F : ℝ → ℝ := fun x => (1 + (θ * x) ^ 2)⁻¹ with hF
  set f : ℤ → ℝ := fun ℓ => F (ℓ : ℝ) with hf
  have heven : Function.Even f := by
    intro ℓ
    simp only [hf, hF, Int.cast_neg, mul_neg, neg_sq]
  have hsumm : Summable f := by
    simp only [hf, hF]
    exact Work.FIArea5.S16.int_summ θ hθ
  have hanti : AntitoneOn F (Set.Ici 0) := by
    simp only [hF]
    intro a ha b hb hab
    rw [Set.mem_Ici] at ha hb
    have h1 : (1:ℝ) + (θ*a)^2 ≤ 1 + (θ*b)^2 := by
      have h2 : (θ*a)^2 ≤ (θ*b)^2 := by
        have ha0 : 0 ≤ θ * a := by positivity
        have hab' : θ * a ≤ θ * b := by nlinarith
        have := mul_self_le_mul_self ha0 hab'
        simpa [sq] using this
      linarith
    rw [inv_le_inv₀ (by positivity : (0:ℝ) < 1 + (θ*b)^2) (by positivity : (0:ℝ) < 1 + (θ*a)^2)]
    exact h1
  have hint : IntegrableOn F (Set.Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => (1 + x^2)⁻¹) (0:ℝ) hθ).mpr
      (integrable_inv_one_add_sq.integrableOn)
    simpa only [hF, mul_zero] using h
  have hnn : ∀ t ∈ Set.Ioi 0, 0 ≤ F t := by intro t ht; simp only [hF]; positivity
  have hfin : ∫ x in Set.Ioi (0:ℝ), F x = Real.pi / (2*θ) := by
    have h := integral_comp_mul_left_Ioi (fun x : ℝ => (1 + x^2)⁻¹) (0:ℝ) hθ
    rw [mul_zero] at h
    simp only [hF]
    rw [h, integral_Ioi_inv_one_add_sq]
    simp only [Real.arctan_zero, sub_zero, smul_eq_mul]
    field_simp
  have heq : ∑' n : ℕ, f (n+1) = ∑' n : ℕ, F (↑(n+1) : ℝ) := by
    apply tsum_congr; intro n
    simp only [hf]
    congr 1
  have hS : ∑' n : ℕ, f (n+1) ≤ Real.pi / (2*θ) := by
    rw [heq]
    have h := AntitoneOn.tsum_add_one_le_integral hanti hint hnn
    rw [hfin] at h
    exact h
  have hdec : ∑' ℓ : ℤ, f ℓ = f 0 + 2 * ∑' n : ℕ, f (n+1) := by
    have hpos : Summable (fun n : ℕ => f (n:ℤ)) := hsumm.comp_injective Nat.cast_injective
    have hneg : Summable (fun n : ℕ => f (-(n:ℤ))) :=
      hsumm.comp_injective (neg_injective.comp Nat.cast_injective)
    have hmain := Summable.tsum_of_nat_of_neg hpos hneg
    have hsym : ∑' n : ℕ, f (-(n:ℤ)) = ∑' n : ℕ, f (n:ℤ) := by
      apply tsum_congr; intro n
      simp only [hf, hF, Int.cast_neg, mul_neg, neg_sq]
    have hzero : ∑' n : ℕ, f (n:ℤ) = f 0 + ∑' n : ℕ, f (n+1) := by
      simpa using hpos.tsum_eq_zero_add
    rw [hmain, hsym, hzero]; ring
  have hf0 : f 0 = 1 := by simp [hf, hF]
  rw [show ∑' ℓ : ℤ, (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹ = ∑' ℓ : ℤ, f ℓ from by
        simp only [hf, hF]]
  rw [hdec, hf0]
  have hS2 : 2 * (∑' n : ℕ, f (n+1)) ≤ 4 / θ := by
    have h2 : 2 * (Real.pi / (2*θ)) ≤ 4 / θ := by
      rw [show 2 * (Real.pi/(2*θ)) = Real.pi/θ from by field_simp]
      exact div_le_div_of_nonneg_right (le_of_lt Real.pi_lt_four) (le_of_lt hθ)
    linarith [hS, h2]
  linarith [hS2]

/-- **The total mass of the Fourier coefficients of `q`.**

`Σ_ℓ |q̂(ℓ)| ≤ 10⁷` for `θ ∈ (0,1]`, from `Work.FIArea5.S16.fcoef_bound`
(`|q̂(ℓ)| ≤ (1/2π)·10⁷·θ·(1+(θℓ)²)^{−1}`) and
`Σ_{ℓ∈ℤ}(1+(θℓ)²)^{−1} ≤ 1 + 4/θ` (split the `ℤ`-sum at `|ℓ| ≤ 1/θ`; the two tails are each
`≤ 1/θ`).  Hence `(1/2π)·10⁷·θ·(1+4/θ) ≤ 10⁷`. -/
theorem TauHeartFcoefMass (q : ℝ → ℝ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hqC : ContDiff ℝ 2 q) (hq0 : ∀ α, 0 ≤ q α) (hq1 : ∀ α, q α ≤ 1)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ)
    (hd2 : ∀ α, |iteratedDeriv 2 q α| ≤ 1048576 / θ ^ 2) :
    ∑' ℓ : ℤ, ‖Work.FIArea5.S16.fcoef q ℓ‖ ≤ 10000000 := by
  have hsumm_g : Summable (fun ℓ : ℤ => (1 + (θ * (ℓ:ℝ))^2)⁻¹) :=
    Work.FIArea5.S16.int_summ θ hθ
  have hsumm_f : Summable (Work.FIArea5.S16.fcoef q) :=
    Work.FIArea5.S16.fcoef_summable q θ hθ hθ1 hqC hq0 hq1 hqsupp hd2
  have hsumm_norm : Summable (fun ℓ : ℤ => ‖Work.FIArea5.S16.fcoef q ℓ‖) := hsumm_f.norm
  have hbn : ∀ ℓ : ℤ, ‖Work.FIArea5.S16.fcoef q ℓ‖
      ≤ (1 / (2 * Real.pi) * (10000000 * θ)) * (1 + (θ * (ℓ:ℝ))^2)⁻¹ := by
    intro ℓ
    have h := Work.FIArea5.S16.fcoef_bound q θ hθ hθ1 hqC hq0 hq1 hqsupp hd2 ℓ
    calc ‖Work.FIArea5.S16.fcoef q ℓ‖
        ≤ (1 / (2 * Real.pi)) * (10000000 * θ * (1 + (θ * (ℓ:ℝ))^2)⁻¹) := h
      _ = (1 / (2 * Real.pi) * (10000000 * θ)) * (1 + (θ * (ℓ:ℝ))^2)⁻¹ := by ring
  have hsumm_cg : Summable (fun ℓ : ℤ => (1 / (2*Real.pi) * (10000000*θ)) * (1+(θ*(ℓ:ℝ))^2)⁻¹) :=
    hsumm_g.mul_left _
  have hle : ∑' ℓ : ℤ, ‖Work.FIArea5.S16.fcoef q ℓ‖
      ≤ (1 / (2*Real.pi) * (10000000*θ)) * ∑' ℓ : ℤ, (1+(θ*(ℓ:ℝ))^2)⁻¹ := by
    have h := Summable.tsum_le_tsum hbn hsumm_norm hsumm_cg
    rwa [tsum_mul_left] at h
  have hstep : (1 / (2*Real.pi) * (10000000*θ)) * ∑' ℓ : ℤ, (1+(θ*(ℓ:ℝ))^2)⁻¹
      ≤ (1 / (2*Real.pi) * (10000000*θ)) * (1 + 4/θ) :=
    mul_le_mul_of_nonneg_left (zsumInvBound θ hθ) (by positivity)
  have harith : (1 / (2*Real.pi) * (10000000*θ)) * (1 + 4/θ) ≤ 10000000 := by
    have hπ : (5:ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hθ4 : θ + 4 ≤ 5 := by linarith
    have key : θ + 4 ≤ 2 * Real.pi := le_of_lt (lt_of_le_of_lt hθ4 hπ)
    calc (1 / (2*Real.pi) * (10000000*θ)) * (1 + 4/θ)
        = (1/(2*Real.pi) * 10000000) * (θ + 4) := by field_simp
      _ ≤ (1/(2*Real.pi) * 10000000) * (2*Real.pi) :=
            mul_le_mul_of_nonneg_left key (by positivity)
      _ = 10000000 := by field_simp
  linarith [hle, hstep, harith]

end

end Work.FIArea6Road
