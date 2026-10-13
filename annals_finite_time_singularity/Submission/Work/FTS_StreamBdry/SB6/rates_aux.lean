import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB6.infra
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25.oddPerS_pieces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.rates_aux` — the weight comparisons and the `oddPerS` glue

Two groups of helpers for `sb6_rates`:

* the comparisons between the weights `(1+w)^{-k}`, `(L/w)^k` and `w^{-(k+1)}` which convert the
  compact bounds (`w ≤ L`) and the far-field bounds (`L ≤ w`) into the single weight
  `(1+w)^{-k}` of the statement;
* the agreement of `Φ = oddPerS (psiP)`, extended by `0` at `w ≤ 0`, with `psiP` on the open
  quadrant, together with the rewriting of `∂_wΦ` and `∂_θΦ` as the corresponding derivatives of
  `psiP`, and the two boundary cases `w = 0` and `θ = 0`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

/-! ## §1 Weight comparisons -/

/-- For `0 ≤ w ≤ L` and `0 ≤ k`: `(1+L)^{-k} ≤ (1+w)^{-k}`. -/
lemma one_add_rpow_neg_le {w L k : ℝ} (hL : 0 < L) (hk : 0 ≤ k) (hw0 : 0 ≤ w) (hw : w ≤ L) :
    (1 + L) ^ (-k) ≤ (1 + w) ^ (-k) := by
  have h1 : (0 : ℝ) ≤ 1 + w := by linarith
  have h2 : (0 : ℝ) < 1 + L := by linarith
  rw [Real.rpow_neg h1 k, Real.rpow_neg (le_of_lt h2) k]
  have h3 : (1 + w) ^ k ≤ (1 + L) ^ k := Real.rpow_le_rpow h1 (by linarith) hk
  have h4 := one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith : (0:ℝ) < 1 + w) k) h3
  simpa only [one_div] using h4

/-- For `L ≤ w` and `0 ≤ k`: `(L/w)^k ≤ (1+L)^k (1+w)^{-k}`. -/
lemma div_rpow_le {w L k : ℝ} (hL : 0 < L) (hk : 0 ≤ k) (hw : L ≤ w) :
    (L / w) ^ k ≤ (1 + L) ^ k * (1 + w) ^ (-k) := by
  have hw0 : 0 < w := lt_of_lt_of_le hL hw
  have h1w : (0 : ℝ) < 1 + w := by linarith
  have h1L : (0 : ℝ) < 1 + L := by linarith
  have h1 : L / w ≤ (1 + L) / (1 + w) := by
    rw [div_le_iff₀ hw0]
    have he : (1 + L) / (1 + w) * w = (1 + L) * w / (1 + w) := by ring
    rw [he, le_div_iff₀ h1w]
    linarith
  have h2 : (L / w) ^ k ≤ ((1 + L) / (1 + w)) ^ k :=
    Real.rpow_le_rpow (by positivity) h1 hk
  have he : ((1 + L) / (1 + w)) ^ k = (1 + L) ^ k * (1 + w) ^ (-k) := by
    rw [Real.div_rpow (le_of_lt h1L) (le_of_lt h1w), Real.rpow_neg (le_of_lt h1w) k,
      div_eq_mul_inv]
  rwa [he] at h2

/-- For `L ≤ w` (with `L > 0`) and `0 ≤ k`: `w^{-(k+1)} ≤ (1+1/L)^{k+1} (1+w)^{-(k+1)}`. -/
lemma rpow_neg_succ_le {w L k : ℝ} (hL : 0 < L) (hk : 0 ≤ k) (hw : L ≤ w) :
    w ^ (-(k + 1)) ≤ (1 + 1 / L) ^ (k + 1) * (1 + w) ^ (-(k + 1)) := by
  have hw0 : 0 < w := lt_of_lt_of_le hL hw
  have h1w : (0 : ℝ) < 1 + w := by linarith
  have hp : (0 : ℝ) < 1 + 1 / L := by positivity
  have h3 : (1 : ℝ) ≤ w / L := by
    rw [le_div_iff₀ hL]; linarith
  have h4 : (1 + 1 / L) * w = w + w / L := by ring
  have h2 : 1 / w ≤ (1 + 1 / L) / (1 + w) := by
    rw [div_le_iff₀ hw0]
    have he : (1 + 1 / L) / (1 + w) * w = (1 + 1 / L) * w / (1 + w) := by ring
    rw [he, le_div_iff₀ h1w]
    nlinarith [h3, h4]
  have h5 : (1 / w) ^ (k + 1) ≤ ((1 + 1 / L) / (1 + w)) ^ (k + 1) :=
    Real.rpow_le_rpow (by positivity) h2 (by linarith)
  have hw1 : w ^ (-(k + 1)) = (1 / w) ^ (k + 1) := by
    rw [Real.rpow_neg (le_of_lt hw0) (k + 1), one_div,
      Real.inv_rpow (le_of_lt hw0) (k + 1)]
  have he : ((1 + 1 / L) / (1 + w)) ^ (k + 1)
      = (1 + 1 / L) ^ (k + 1) * (1 + w) ^ (-(k + 1)) := by
    rw [Real.div_rpow (le_of_lt hp) (le_of_lt h1w), Real.rpow_neg (le_of_lt h1w) (k + 1),
      div_eq_mul_inv]
  rw [hw1]
  rwa [he] at h5

/-- For `L ≤ w` (with `L > 0`) and `0 ≤ k`:
`(L/w)^k / w ≤ L^k · (1+1/L)^{k+1} · (1+w)^{-(k+1)}` — the extra inverse power `1/w` of the
`w`-derivative is absorbed into the `(1+w)^{-(k+1)}`-weight at the cost of the factor
`(1+1/L)^{k+1}`. -/
lemma div_rpow_succ_le {w L k : ℝ} (hL : 0 < L) (hk : 0 ≤ k) (hw : L ≤ w) :
    (L / w) ^ k / w ≤ L ^ k * (1 + 1 / L) ^ (k + 1) * (1 + w) ^ (-(k + 1)) := by
  have hw0 : 0 < w := lt_of_lt_of_le hL hw
  have h1 : (L / w) ^ k / w = L ^ k * w ^ (-(k + 1)) := by
    have hsplit : w ^ (k + 1) = w ^ k * w := by
      rw [Real.rpow_add hw0 k 1, Real.rpow_one]
    rw [Real.div_rpow (le_of_lt hL) (le_of_lt hw0), div_div, ← hsplit,
      Real.rpow_neg (le_of_lt hw0) (k + 1), div_eq_mul_inv]
  rw [h1, mul_assoc]
  exact mul_le_mul_of_nonneg_left (rpow_neg_succ_le hL hk hw)
    (Real.rpow_nonneg (le_of_lt hL) k)

/-! ## §2 The `oddPerS` glue -/

/-- On the open quadrant, `Φ w θ = psiP w θ` (for `w > 0`). -/
lemma Phi_eq_of_pos {P : ℝ → ℝ → ℝ} (hP : ∀ z, P z (Real.pi / 2) = 0) {w θ : ℝ}
    (hw : 0 < w) (hθ : 0 < θ) (hθ2 : θ ≤ Real.pi / 2) :
    (if 0 < w then oddPerS P w θ else 0) = P w θ := by
  rw [ite_eq_left hw]
  exact (Work.FTS_StreamBdry.SB25.oddPerS_pieces P hP).2.1 w θ hθ hθ2

/-- On the axis, `Φ w 0 = 0`. -/
lemma Phi_zero_theta {P : ℝ → ℝ → ℝ} (hP : ∀ z, P z (Real.pi / 2) = 0) {w : ℝ} :
    (if 0 < w then oddPerS P w 0 else 0) = 0 := by
  by_cases hw : 0 < w
  · rw [ite_eq_left hw]
    exact (Work.FTS_StreamBdry.SB25.oddPerS_pieces P hP).2.2.2.2 w
  · rw [ite_eq_right hw]

/-- At `w ≤ 0`, `Φ w θ = 0`. -/
lemma Phi_eq_zero_of_nonpos {P : ℝ → ℝ → ℝ} {w θ : ℝ} (hw : ¬ 0 < w) :
    (if 0 < w then oddPerS P w θ else 0) = 0 := ite_eq_right hw

/-- The `w`-derivative of `Φ` is that of `psiP` in the open quadrant. -/
lemma Phi_deriv_w {P : ℝ → ℝ → ℝ} (hP : ∀ z, P z (Real.pi / 2) = 0) {w θ : ℝ}
    (hw : 0 < w) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    deriv (fun w' : ℝ => (if 0 < w' then oddPerS P w' θ else 0)) w
      = deriv (fun w' : ℝ => P w' θ) w := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hw] with w' hw'
  exact Phi_eq_of_pos hP hw' hθ (le_of_lt hθ2)

/-- The `θ`-derivative of `Φ` is that of `psiP` in the open quadrant. -/
lemma Phi_deriv_theta {P : ℝ → ℝ → ℝ} (hP : ∀ z, P z (Real.pi / 2) = 0) {w θ : ℝ}
    (hw : 0 < w) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    deriv (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) θ
      = deriv (fun θ' : ℝ => P w θ') θ := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ, hθ2⟩] with θ' hθ'
  exact Phi_eq_of_pos hP hw hθ'.1 (le_of_lt hθ'.2)

/-- `oddPerS P w 0 = 0`. -/
lemma oddPerS_zero_theta {P : ℝ → ℝ → ℝ} (hP : ∀ z, P z (Real.pi / 2) = 0) (w : ℝ) :
    oddPerS P w 0 = 0 :=
  (Work.FTS_StreamBdry.SB25.oddPerS_pieces P hP).2.2.2.2 w

/-- **Left-vanishing pins the derivative at `0` to `0`**: if `f` is differentiable at `0` and
`f` vanishes on `(-∞, 0)`, then `deriv f 0 = 0`. -/
lemma deriv_eq_zero_of_left_eq_zero {f : ℝ → ℝ} (hd : DifferentiableAt ℝ f 0)
    (h : ∀ y, y < 0 → f y = 0) (h0 : f 0 = 0) : deriv f 0 = 0 := by
  have h2 : Filter.Tendsto (fun t : ℝ => t⁻¹ * (f (0 + t) - f 0)) (𝓝[<] (0:ℝ))
      (𝓝 (deriv f 0)) := hd.hasDerivAt.tendsto_slope_zero_left
  have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[<] (0:ℝ)]
      (fun t : ℝ => t⁻¹ * (f (0 + t) - f 0)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hft : f (0 + t) = 0 := by simpa using h t ht
    show (0 : ℝ) = t⁻¹ * (f (0 + t) - f 0)
    rw [hft, h0, sub_self, mul_zero]
  have h3 : Filter.Tendsto (fun t : ℝ => t⁻¹ * (f (0 + t) - f 0)) (𝓝[<] (0:ℝ)) (𝓝 0) :=
    Tendsto.congr' hev tendsto_const_nhds
  exact tendsto_nhds_unique h2 h3

/-- **The derivative of `Φ w ·` at `0`** is bounded by any bound on the difference quotient
`P w t / t` for `t → 0⁺`. -/
lemma deriv_theta_zero_le' {P : ℝ → ℝ → ℝ} (hP : ∀ z, P z (Real.pi / 2) = 0) {w B : ℝ}
    (hw : 0 < w)
    (hb : ∀ t, 0 < t → t < Real.pi / 2 → |P w t / t| ≤ B)
    (hd : DifferentiableAt ℝ (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0) :
    |deriv (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0| ≤ B := by
  have hslope : Filter.Tendsto (fun t : ℝ => t⁻¹ *
      ((fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) (0 + t)
        - (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (deriv (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0)) :=
    hd.hasDerivAt.tendsto_slope_zero_right
  have hlt : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < Real.pi / 2 :=
    nhdsWithin_le_nhds
      (Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2))
  have hev : (fun t : ℝ => t⁻¹ *
      ((fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) (0 + t)
        - (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0))
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun t : ℝ => P w t / t) := by
    filter_upwards [self_mem_nhdsWithin, hlt] with t ht0 htπ
    have ht0' : (0 : ℝ) < t := ht0
    have h1 : (if 0 < w then oddPerS P w (0 + t) else 0) = P w (0 + t) := by
      rw [zero_add]
      exact Phi_eq_of_pos hP hw ht0' (le_of_lt htπ)
    have h0 : (if 0 < w then oddPerS P w 0 else 0) = 0 := Phi_zero_theta hP
    rw [h1, h0, zero_add, sub_zero, div_eq_mul_inv]
    ring
  have hbd : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), |P w t / t| ≤ B := by
    filter_upwards [self_mem_nhdsWithin, hlt] with t ht0 htπ
    have ht0' : (0 : ℝ) < t := ht0
    exact hb t ht0' htπ
  exact le_of_tendsto (hslope.congr' hev).abs hbd

/-- **The derivative of `Φ w ·` at `0`**: if it exists, it is the right difference quotient
`P w t / t` at `t → 0⁺`, hence bounded by `2M` when `|P w t| ≤ M sin 2t`. -/
lemma deriv_theta_zero_le {P : ℝ → ℝ → ℝ} (hP : ∀ z, P z (Real.pi / 2) = 0) {w M : ℝ}
    (hw : 0 < w) (hM : 0 ≤ M)
    (hb : ∀ t, 0 < t → t < Real.pi / 2 → |P w t| ≤ M * Work.Construction.s2 t)
    (hd : DifferentiableAt ℝ (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0) :
    |deriv (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0| ≤ 2 * M := by
  refine deriv_theta_zero_le' hP hw ?_ hd
  intro t ht0 htπ
  have ht0' : (0 : ℝ) < t := ht0
  have h2 : Work.Construction.s2 t / t ≤ 2 := by
    rw [Work.Construction.s2_eq, Real.sin_two_mul, div_le_iff₀ ht0']
    nlinarith [Real.sin_le (le_of_lt ht0'), Real.cos_le_one t,
      Real.sin_nonneg_of_mem_Icc ⟨le_of_lt ht0', by linarith [htπ, Real.pi_pos]⟩]
  calc |P w t / t| ≤ M * Work.Construction.s2 t / t := by
        rw [abs_div]
        simp only [abs_of_pos ht0']
        exact div_le_div_of_nonneg_right (hb t ht0 htπ) (le_of_lt ht0')
    _ = M * (Work.Construction.s2 t / t) := by ring
    _ ≤ M * 2 := mul_le_mul_of_nonneg_left h2 hM
    _ = 2 * M := by ring

/-- The same with the far-field weight. -/
lemma deriv_theta_zero_le_far {P : ℝ → ℝ → ℝ} (hP : ∀ z, P z (Real.pi / 2) = 0)
    {αG L w Kf : ℝ} (hL : 0 < L) (hwL : L ≤ w) (hKf0 : 0 ≤ Kf)
    (hb : ∀ t, 0 < t → t < Real.pi / 2 →
      |P w t| ≤ Kf * Work.Construction.s2 t * (L / w) ^ (4 / αG))
    (hd : DifferentiableAt ℝ (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0) :
    |deriv (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0|
      ≤ 2 * Kf * (L / w) ^ (4 / αG) := by
  have hw : 0 < w := lt_of_lt_of_le hL hwL
  refine deriv_theta_zero_le' hP hw ?_ hd
  intro t ht0 htπ
  have ht0' : (0 : ℝ) < t := ht0
  have h2 : Work.Construction.s2 t / t ≤ 2 := by
    rw [Work.Construction.s2_eq, Real.sin_two_mul, div_le_iff₀ ht0']
    nlinarith [Real.sin_le (le_of_lt ht0'), Real.cos_le_one t,
      Real.sin_nonneg_of_mem_Icc ⟨le_of_lt ht0', by linarith [htπ, Real.pi_pos]⟩]
  calc |P w t / t| ≤ Kf * Work.Construction.s2 t * (L / w) ^ (4 / αG) / t := by
        rw [abs_div]
        simp only [abs_of_pos ht0']
        exact div_le_div_of_nonneg_right (hb t ht0 htπ) (le_of_lt ht0')
    _ = Kf * (L / w) ^ (4 / αG) * (Work.Construction.s2 t / t) := by ring
    _ ≤ Kf * (L / w) ^ (4 / αG) * 2 :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hKf0 (Real.rpow_nonneg (by positivity) _))
    _ = 2 * Kf * (L / w) ^ (4 / αG) := by ring

end Work.FTS_StreamBdry.SB6
