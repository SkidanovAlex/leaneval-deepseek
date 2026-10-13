/-
# `Work.FTS.RegPkgGal.R6.clock_fields` — the clock fields of the modulation

`Avort m τ = exp(-∫_0^τ (1 + m))` and `Bdyn m τ = exp(-∫_0^τ (1 - m))` are the vorticity
amplitude and the space scale of the reconstruction (design §2, item 8).  The single clock datum
is a function `m` (the dynamical modulation `muDyn`) which is continuous on `(-1, S+1)`, bounded
by `1/2` there, and `α`-Hölder on `[0,S]`; that is exactly what the modulation fixed point
produces.

The two functions are one and the same object with the sign of `m` flipped:
`Avort m = gpow m 1` and `Bdyn m = gpow m (-1)` where

  `gpow m c τ = exp(-∫_0^τ (1 + c·m))`,

so everything is proved once for `gpow` with an arbitrary `c` of modulus `1` and transported.
The elementary input is that `1/2 ≤ 1 ± m ≤ 3/2` on `[0,S]`, whence `τ/2 ≤ ∫_0^τ (1 ± m) ≤ 3τ/2`
for `τ ∈ [0,S]` and therefore

* `gpow` is positive and bounded above by `1`, and below by `exp(-3S/2)`, on `[0,S]`;
* `gpow` is differentiable on `[0,S]` with `deriv (gpow m c) τ = -(1 + c·m τ)·gpow m c τ`
  (fundamental theorem of calculus), so `|deriv| ≤ 3/2` there;
* `gpow` is `3/2`-Lipschitz on `[0,S]` (mean value theorem), and the derivative is `α`-Hölder
  there with constant `L + (9/4)·S^{1-α}`: the Hölder modulus of `m` controls the first factor
  `1 + c·m τ`, and the Lipschitz modulus of `gpow` controls the second (the extra `|τ - τ'|` is
  absorbed by `|τ - τ'| ≤ S^{1-α}|τ - τ'|^α` because `α ≤ 1`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.RegPkgGal.RVocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter MeasureTheory intervalIntegral
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R6

set_option autoImplicit false

/-- `gpow m c τ = exp(-∫_0^τ (1 + c·m))`.  `Avort m` is `c = 1` and `Bdyn m` is `c = -1`. -/
def gpow (m : ℝ → ℝ) (c τ : ℝ) : ℝ :=
  Real.exp (-∫ s in (0 : ℝ)..τ, (1 + c * m s))

theorem Avort_eq_gpow (m : ℝ → ℝ) : Work.FTS.RegPkgGal.Avort m = gpow m 1 := by
  funext τ
  simp [Work.FTS.RegPkgGal.Avort, gpow]

theorem Bdyn_eq_gpow (m : ℝ → ℝ) : Work.FTS.RegPkgGal.Bdyn m = gpow m (-1) := by
  funext τ
  simp [Work.FTS.RegPkgGal.Bdyn, gpow, sub_eq_add_neg]

theorem contOn_uIcc {m : ℝ → ℝ} {S τ : ℝ} (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Icc (0 : ℝ) S) : ContinuousOn m (Set.uIcc (0 : ℝ) τ) := by
  refine hm.mono ?_
  intro x hx
  rw [Set.uIcc_of_le hτ.1] at hx
  exact ⟨by linarith [hx.1], by linarith [hx.2, hτ.2]⟩

/-- `1 + c·x ∈ [1/2, 3/2]` for `|c| = 1`, `|x| ≤ 1/2`. -/
theorem abs_one_add {c x : ℝ} (hc : |c| = 1) (hx : |x| ≤ 1 / 2) : |1 + c * x| ≤ 3 / 2 := by
  have habs : |c * x| ≤ 1 / 2 := by rw [abs_mul, hc, one_mul]; exact hx
  have h := abs_le.mp habs
  rw [abs_le]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The fundamental theorem of calculus for the clock: on `[0,S]` the derivative of `gpow` is
`-(1 + c·m τ)` times its value. -/
theorem gpow_hasDerivAt {m : ℝ → ℝ} {c S τ : ℝ}
    (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Icc (0 : ℝ) S) :
    HasDerivAt (gpow m c) (-(1 + c * m τ) * gpow m c τ) τ := by
  have hmem : τ ∈ Set.Ioo (-1 : ℝ) (S + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hmτ : ContinuousAt m τ := hm.continuousAt (isOpen_Ioo.mem_nhds hmem)
  have hfτ : ContinuousAt (fun s : ℝ => 1 + c * m s) τ := (hmτ.const_mul c).const_add 1
  have hmono : ContinuousOn m (Set.uIcc (0 : ℝ) τ) := contOn_uIcc hm hτ
  have hcOnIoo : ContinuousOn (fun s : ℝ => 1 + c * m s) (Set.Ioo (-1) (S + 1)) :=
    (hm.const_mul c).const_add 1
  have hcOn : ContinuousOn (fun s : ℝ => 1 + c * m s) (Set.uIcc (0 : ℝ) τ) :=
    (hmono.const_mul c).const_add 1
  have hint : IntervalIntegrable (fun s : ℝ => 1 + c * m s) volume (0 : ℝ) τ :=
    hcOn.intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter (fun s : ℝ => 1 + c * m s) (𝓝 τ) volume :=
    hcOnIoo.stronglyMeasurableAtFilter isOpen_Ioo τ hmem
  have hderiv : HasDerivAt (fun u : ℝ => ∫ x in (0 : ℝ)..u, (1 + c * m x)) (1 + c * m τ) τ :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hfτ
  have h2 : HasDerivAt (fun u : ℝ => Real.exp (-∫ x in (0 : ℝ)..u, (1 + c * m x)))
      (Real.exp (-∫ x in (0 : ℝ)..τ, (1 + c * m x)) * (-(1 + c * m τ))) τ := hderiv.neg.exp
  have h3 : HasDerivAt (gpow m c)
      (Real.exp (-∫ x in (0 : ℝ)..τ, (1 + c * m x)) * (-(1 + c * m τ))) τ := by
    rw [show gpow m c = fun u : ℝ => Real.exp (-∫ x in (0 : ℝ)..u, (1 + c * m x)) from rfl]
    exact h2
  exact h3.congr_deriv (by rw [gpow]; ring)

theorem gpow_deriv_eq {m : ℝ → ℝ} {c S τ : ℝ}
    (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Icc (0 : ℝ) S) :
    deriv (gpow m c) τ = -(1 + c * m τ) * gpow m c τ :=
  (gpow_hasDerivAt hm hτ).deriv

/-- `|gpow m c τ| ≤ 1` on `[0,S]` (the exponent of the exponential is nonpositive). -/
theorem gpow_abs_le_one {m : ℝ → ℝ} {c S τ : ℝ} (hc : |c| = 1)
    (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hmb : ∀ s ∈ Set.Icc (0 : ℝ) S, |m s| ≤ 1 / 2)
    (hτ : τ ∈ Set.Icc (0 : ℝ) S) : |gpow m c τ| ≤ 1 := by
  have hmono : ContinuousOn m (Set.uIcc (0 : ℝ) τ) := contOn_uIcc hm hτ
  have hcOn : ContinuousOn (fun s : ℝ => 1 + c * m s) (Set.uIcc (0 : ℝ) τ) :=
    (hmono.const_mul c).const_add 1
  have hInt : IntervalIntegrable (fun s : ℝ => 1 + c * m s) volume (0 : ℝ) τ :=
    hcOn.intervalIntegrable
  have hInt1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 2) volume (0 : ℝ) τ :=
    continuous_const.intervalIntegrable _ _
  have hpt : ∀ x ∈ Set.Icc (0 : ℝ) τ, (1 : ℝ) / 2 ≤ 1 + c * m x := by
    intro x hx
    have hxS : x ∈ Set.Icc (0 : ℝ) S := ⟨hx.1, le_trans hx.2 hτ.2⟩
    have habs : |c * m x| ≤ 1 / 2 := by rw [abs_mul, hc, one_mul]; exact hmb x hxS
    have := abs_le.mp habs
    linarith [this.1]
  have h1 : (∫ s in (0 : ℝ)..τ, ((1 : ℝ) / 2)) ≤ ∫ s in (0 : ℝ)..τ, (1 + c * m s) :=
    intervalIntegral.integral_mono_on hτ.1 hInt1 hInt hpt
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h1
  rw [abs_of_pos (show (0 : ℝ) < gpow m c τ from Real.exp_pos _)]
  have hI : -(∫ s in (0 : ℝ)..τ, (1 + c * m s)) ≤ 0 := by linarith [h1, hτ.1]
  calc gpow m c τ = Real.exp (-(∫ s in (0 : ℝ)..τ, (1 + c * m s))) := rfl
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hI
    _ = 1 := Real.exp_zero

/-- `|deriv (gpow m c) τ| ≤ 3/2` on `[0,S]`. -/
theorem gpow_deriv_bound {m : ℝ → ℝ} {c S τ : ℝ} (hc : |c| = 1)
    (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hmb : ∀ s ∈ Set.Icc (0 : ℝ) S, |m s| ≤ 1 / 2)
    (hτ : τ ∈ Set.Icc (0 : ℝ) S) : |deriv (gpow m c) τ| ≤ 3 / 2 := by
  rw [gpow_deriv_eq hm hτ, abs_mul, abs_neg]
  calc |1 + c * m τ| * |gpow m c τ| ≤ (3 / 2) * 1 :=
        mul_le_mul (abs_one_add hc (hmb τ hτ)) (gpow_abs_le_one hc hm hmb hτ)
          (abs_nonneg _) (by norm_num)
    _ = 3 / 2 := by norm_num

/-- `gpow` is bounded above and below by positive constants on `[0,S]`. -/
theorem gpow_bounds {m : ℝ → ℝ} {c S : ℝ} (hc : |c| = 1)
    (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hmb : ∀ s ∈ Set.Icc (0 : ℝ) S, |m s| ≤ 1 / 2) :
    ∃ a₀ a₁ : ℝ, 0 < a₀ ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, a₀ ≤ gpow m c τ ∧ gpow m c τ ≤ a₁ := by
  refine ⟨Real.exp (-(3 * S / 2)), 1, Real.exp_pos _, fun τ hτ => ⟨?_, ?_⟩⟩
  · have hmono : ContinuousOn m (Set.uIcc (0 : ℝ) τ) := contOn_uIcc hm hτ
    have hcOn : ContinuousOn (fun s : ℝ => 1 + c * m s) (Set.uIcc (0 : ℝ) τ) :=
      (hmono.const_mul c).const_add 1
    have hInt : IntervalIntegrable (fun s : ℝ => 1 + c * m s) volume (0 : ℝ) τ :=
      hcOn.intervalIntegrable
    have hInt3 : IntervalIntegrable (fun _ : ℝ => (3 : ℝ) / 2) volume (0 : ℝ) τ :=
      continuous_const.intervalIntegrable _ _
    have hpt : ∀ x ∈ Set.Icc (0 : ℝ) τ, 1 + c * m x ≤ (3 : ℝ) / 2 := by
      intro x hx
      have hxS : x ∈ Set.Icc (0 : ℝ) S := ⟨hx.1, le_trans hx.2 hτ.2⟩
      have habs : |c * m x| ≤ 1 / 2 := by rw [abs_mul, hc, one_mul]; exact hmb x hxS
      have := abs_le.mp habs
      linarith [this.2]
    have h2 : (∫ s in (0 : ℝ)..τ, (1 + c * m s)) ≤ ∫ s in (0 : ℝ)..τ, ((3 : ℝ) / 2) :=
      intervalIntegral.integral_mono_on hτ.1 hInt hInt3 hpt
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h2
    have hI : -(3 * S / 2) ≤ -(∫ s in (0 : ℝ)..τ, (1 + c * m s)) := by linarith [h2, hτ.2]
    calc Real.exp (-(3 * S / 2)) ≤ Real.exp (-(∫ s in (0 : ℝ)..τ, (1 + c * m s))) :=
          Real.exp_le_exp.mpr hI
      _ = gpow m c τ := rfl
  · have hmono : ContinuousOn m (Set.uIcc (0 : ℝ) τ) := contOn_uIcc hm hτ
    have hcOn : ContinuousOn (fun s : ℝ => 1 + c * m s) (Set.uIcc (0 : ℝ) τ) :=
      (hmono.const_mul c).const_add 1
    have hInt : IntervalIntegrable (fun s : ℝ => 1 + c * m s) volume (0 : ℝ) τ :=
      hcOn.intervalIntegrable
    have hInt1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 2) volume (0 : ℝ) τ :=
      continuous_const.intervalIntegrable _ _
    have hpt : ∀ x ∈ Set.Icc (0 : ℝ) τ, (1 : ℝ) / 2 ≤ 1 + c * m x := by
      intro x hx
      have hxS : x ∈ Set.Icc (0 : ℝ) S := ⟨hx.1, le_trans hx.2 hτ.2⟩
      have habs : |c * m x| ≤ 1 / 2 := by rw [abs_mul, hc, one_mul]; exact hmb x hxS
      have := abs_le.mp habs
      linarith [this.1]
    have h1 : (∫ s in (0 : ℝ)..τ, ((1 : ℝ) / 2)) ≤ ∫ s in (0 : ℝ)..τ, (1 + c * m s) :=
      intervalIntegral.integral_mono_on hτ.1 hInt1 hInt hpt
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h1
    have hI : -(∫ s in (0 : ℝ)..τ, (1 + c * m s)) ≤ 0 := by linarith [h1, hτ.1]
    calc gpow m c τ = Real.exp (-(∫ s in (0 : ℝ)..τ, (1 + c * m s))) := rfl
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hI
      _ = 1 := Real.exp_zero

/-- `gpow` is `3/2`-Lipschitz on `[0,S]`. -/
theorem gpow_lipschitz {m : ℝ → ℝ} {c S : ℝ} (hc : |c| = 1)
    (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hmb : ∀ s ∈ Set.Icc (0 : ℝ) S, |m s| ≤ 1 / 2) :
    ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      |gpow m c τ - gpow m c τ'| ≤ (3 / 2) * |τ - τ'| := by
  intro τ hτ τ' hτ'
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := gpow m c)
    (s := Set.Icc (0 : ℝ) S) (C := 3 / 2) (x := τ') (y := τ)
    (fun x hx => (gpow_hasDerivAt hm hx).differentiableAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact gpow_deriv_bound hc hm hmb hx)
    (convex_Icc _ _) hτ' hτ
  simpa only [Real.norm_eq_abs] using h

/-- The derivative of `gpow` is `α`-Hölder on `[0,S]`. -/
theorem gpow_deriv_holder {m : ℝ → ℝ} {c α L S : ℝ} (hc : |c| = 1) (hα : 0 < α) (hα1 : α ≤ 1)
    (hL : 0 ≤ L)
    (hm : ContinuousOn m (Set.Ioo (-1) (S + 1)))
    (hmb : ∀ s ∈ Set.Icc (0 : ℝ) S, |m s| ≤ 1 / 2)
    (hmh : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      |m τ - m τ'| ≤ L * |τ - τ'| ^ α) :
    ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      |deriv (gpow m c) τ - deriv (gpow m c) τ'| ≤
        (L + 9 / 4 * S ^ (1 - α)) * |τ - τ'| ^ α := by
  intro τ hτ τ' hτ'
  rw [gpow_deriv_eq hm hτ, gpow_deriv_eq hm hτ']
  have hE : -(1 + c * m τ) * gpow m c τ - (-(1 + c * m τ') * gpow m c τ')
      = (1 + c * m τ') * (gpow m c τ' - gpow m c τ) + c * (m τ' - m τ) * gpow m c τ := by
    ring
  rw [hE]
  have hA : |1 + c * m τ'| ≤ 3 / 2 := abs_one_add hc (hmb τ' hτ')
  have hB : |gpow m c τ' - gpow m c τ| ≤ 3 / 2 * |τ - τ'| := by
    simpa only [abs_sub_comm τ' τ] using gpow_lipschitz hc hm hmb τ' hτ' τ hτ
  have hC : |c * (m τ' - m τ)| ≤ L * |τ - τ'| ^ α := by
    rw [abs_mul, hc, one_mul]
    simpa only [abs_sub_comm τ' τ] using hmh τ' hτ' τ hτ
  have hD : |gpow m c τ| ≤ 1 := gpow_abs_le_one hc hm hmb hτ
  have h1 : |(1 + c * m τ') * (gpow m c τ' - gpow m c τ)| ≤ (3 / 2) * (3 / 2) * |τ - τ'| := by
    rw [abs_mul]
    calc |1 + c * m τ'| * |gpow m c τ' - gpow m c τ|
          ≤ (3 / 2) * ((3 / 2) * |τ - τ'|) :=
          mul_le_mul hA hB (abs_nonneg _) (by positivity)
      _ = (3 / 2) * (3 / 2) * |τ - τ'| := by ring
  have h2 : |c * (m τ' - m τ) * gpow m c τ| ≤ L * |τ - τ'| ^ α := by
    rw [abs_mul]
    calc |c * (m τ' - m τ)| * |gpow m c τ| ≤ (L * |τ - τ'| ^ α) * 1 :=
          mul_le_mul hC hD (abs_nonneg _) (mul_nonneg hL (Real.rpow_nonneg (abs_nonneg _) α))
      _ = L * |τ - τ'| ^ α := by ring
  have h3 : |(1 + c * m τ') * (gpow m c τ' - gpow m c τ) + c * (m τ' - m τ) * gpow m c τ|
      ≤ (3 / 2) * (3 / 2) * |τ - τ'| + L * |τ - τ'| ^ α :=
    (abs_add_le _ _).trans (add_le_add h1 h2)
  have ht0 : 0 ≤ |τ - τ'| := abs_nonneg _
  have htS : |τ - τ'| ≤ S := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hτ.2, hτ'.1], by linarith [hτ'.2, hτ.1]⟩
  have hlt : |τ - τ'| ≤ S ^ (1 - α) * |τ - τ'| ^ α := by
    rcases eq_or_lt_of_le ht0 with h0 | hpos
    · rw [← h0, Real.zero_rpow (ne_of_gt hα), mul_zero]
    · have hr1 : |τ - τ'| ^ (1 - α) ≤ S ^ (1 - α) :=
        Real.rpow_le_rpow (le_of_lt hpos) htS (by linarith)
      have hr2 : |τ - τ'| ^ (1 - α) * |τ - τ'| ^ α = |τ - τ'| := by
        rw [← Real.rpow_add hpos, show (1 - α) + α = 1 by ring, Real.rpow_one]
      calc |τ - τ'| = |τ - τ'| ^ (1 - α) * |τ - τ'| ^ α := hr2.symm
        _ ≤ S ^ (1 - α) * |τ - τ'| ^ α :=
            mul_le_mul_of_nonneg_right hr1 (Real.rpow_nonneg (le_of_lt hpos) α)
  calc |(1 + c * m τ') * (gpow m c τ' - gpow m c τ) + c * (m τ' - m τ) * gpow m c τ|
        ≤ (3 / 2) * (3 / 2) * |τ - τ'| + L * |τ - τ'| ^ α := h3
    _ ≤ (3 / 2) * (3 / 2) * (S ^ (1 - α) * |τ - τ'| ^ α) + L * |τ - τ'| ^ α := by
        have h := mul_le_mul_of_nonneg_left hlt (by norm_num : (0 : ℝ) ≤ (3 / 2) * (3 / 2))
        linarith
    _ = (L + 9 / 4 * S ^ (1 - α)) * |τ - τ'| ^ α := by ring

theorem clock_fields {m : ℝ → ℝ} {α S : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hm : ContinuousOn m (Set.Ioo (-1 : ℝ) (S + 1)))
    (hmb : ∀ τ : ℝ, τ ∈ Set.Ioo (-1 : ℝ) (S + 1) → |m τ| ≤ 1 / 2)
    (hmh : ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |m τ - m τ'| ≤ L * |τ - τ'| ^ α) :
    (∀ τ ∈ Set.Icc 0 S, 0 < Work.FTS.RegPkgGal.Avort m τ) ∧
    (∀ τ ∈ Set.Icc 0 S, 0 < Work.FTS.RegPkgGal.Bdyn m τ) ∧
    (∃ a₀ a₁ : ℝ, 0 < a₀ ∧ ∀ τ ∈ Set.Icc 0 S,
      a₀ ≤ Work.FTS.RegPkgGal.Avort m τ ∧ Work.FTS.RegPkgGal.Avort m τ ≤ a₁) ∧
    (∃ b₀ b₁ : ℝ, 0 < b₀ ∧ ∀ τ ∈ Set.Icc 0 S,
      b₀ ≤ Work.FTS.RegPkgGal.Bdyn m τ ∧ Work.FTS.RegPkgGal.Bdyn m τ ≤ b₁) ∧
    (∀ τ ∈ Set.Icc 0 S,
      HasDerivAt (Work.FTS.RegPkgGal.Avort m) (deriv (Work.FTS.RegPkgGal.Avort m) τ) τ) ∧
    (∀ τ ∈ Set.Icc 0 S,
      HasDerivAt (Work.FTS.RegPkgGal.Bdyn m) (deriv (Work.FTS.RegPkgGal.Bdyn m) τ) τ) ∧
    (∃ a₂ : ℝ, ∀ τ ∈ Set.Icc 0 S, |deriv (Work.FTS.RegPkgGal.Avort m) τ| ≤ a₂) ∧
    (∃ b₂ : ℝ, ∀ τ ∈ Set.Icc 0 S, |deriv (Work.FTS.RegPkgGal.Bdyn m) τ| ≤ b₂) ∧
    (∃ a₃ : ℝ, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |deriv (Work.FTS.RegPkgGal.Avort m) τ - deriv (Work.FTS.RegPkgGal.Avort m) τ'|
        ≤ a₃ * |τ - τ'| ^ α) ∧
    (∃ b₃ : ℝ, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |deriv (Work.FTS.RegPkgGal.Bdyn m) τ - deriv (Work.FTS.RegPkgGal.Bdyn m) τ'|
        ≤ b₃ * |τ - τ'| ^ α) := by
  have hmb' : ∀ s ∈ Set.Icc (0 : ℝ) S, |m s| ≤ 1 / 2 := by
    intro s hs
    exact hmb s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨L, hL, hmhL⟩ := hmh
  have hc1 : |(1 : ℝ)| = 1 := by norm_num
  have hcm1 : |(-1 : ℝ)| = 1 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ _
    rw [Avort_eq_gpow]
    exact Real.exp_pos _
  · intro τ _
    rw [Bdyn_eq_gpow]
    exact Real.exp_pos _
  · obtain ⟨a₀, a₁, ha₀, ha⟩ := gpow_bounds (m := m) (c := 1) (S := S) hc1 hm hmb'
    exact ⟨a₀, a₁, ha₀, fun τ hτ => by rw [Avort_eq_gpow]; exact ha τ hτ⟩
  · obtain ⟨b₀, b₁, hb₀, hb⟩ := gpow_bounds (m := m) (c := -1) (S := S) hcm1 hm hmb'
    exact ⟨b₀, b₁, hb₀, fun τ hτ => by rw [Bdyn_eq_gpow]; exact hb τ hτ⟩
  · intro τ hτ
    rw [Avort_eq_gpow]
    have h := gpow_hasDerivAt (m := m) (c := 1) (S := S) hm hτ
    rw [h.deriv]
    exact h
  · intro τ hτ
    rw [Bdyn_eq_gpow]
    have h := gpow_hasDerivAt (m := m) (c := -1) (S := S) hm hτ
    rw [h.deriv]
    exact h
  · exact ⟨3 / 2, fun τ hτ => by
      rw [Avort_eq_gpow]; exact gpow_deriv_bound hc1 hm hmb' hτ⟩
  · exact ⟨3 / 2, fun τ hτ => by
      rw [Bdyn_eq_gpow]; exact gpow_deriv_bound hcm1 hm hmb' hτ⟩
  · exact ⟨L + 9 / 4 * S ^ (1 - α), fun τ hτ τ' hτ' => by
      rw [Avort_eq_gpow]
      exact gpow_deriv_holder hc1 hα hα1 hL hm hmb' hmhL τ hτ τ' hτ'⟩
  · exact ⟨L + 9 / 4 * S ^ (1 - α), fun τ hτ τ' hτ' => by
      rw [Bdyn_eq_gpow]
      exact gpow_deriv_holder hcm1 hα hα1 hL hm hmb' hmhL τ hτ τ' hτ'⟩

end Work.FTS.RegPkgGal.R6
