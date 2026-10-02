import Mathlib
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.box_lands_step
import Submission.Work.FlowerGlue2.incr_defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.box_deep_of_transient_bound`

The repaired prefix/deepening step of `L4` of the implosion design
(`NOTES_FALSE_box_deep_attr2.md`, `NOTES_FALSE_mandelbar_implosion_N2.md` §4): the design note's
`box_deep` for an abstract `AttrCompare` needs one extra hypothesis, the *uniform transient
bound*

  `(LB)  ∃ M M', A.N ≤ M ∧ ∀ z ∈ Pa, (w0 P z).re ≤ M → (φa z).re ≤ M'`,

i.e. the shallow part of the petal `Pa` carries bounded `φa`-level.  With `(LB)` the deepening
estimate follows from the deep asymptotic `AttrCompare.asymp` alone: once the level of the orbit
exceeds `M'` the orbit can no longer be shallow, hence is deep (`Re (w0 P ·) > A.N`), and on the
deep part the asymptotic

  `φa z = w0 z - κ₀ log (w0 z) + sa + O(1/Re w0 z)`

converts the level of `φa z` into a lower bound for `Re (w0 P z)` (up to a `log`), and converts
the bounded imaginary part of `φa` into the logarithmic bound on `|Im (w0 P z)|`.

The whole content is the pointwise estimate `Work.FlowerGlue2.deep_box_eventually` of §2 below,
stated for arbitrary complex data; the theorem at the end only has to combine it with the
iteration `φa (F^j y) = φa y + j` and the transient bound `(LB)`.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Filter Set Metric
open scoped Topology

namespace Work.FlowerGlue2

noncomputable section

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-! ## 1. Elementary toolbox -/

/-- The sublinear bound on the logarithm: `log x ≤ 2√x` for `x ≥ 1`. -/
theorem bdtb_log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h1 : Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  rw [Real.sqrt_eq_rpow]
  linarith

/-- `a log L ≤ L/2` as soon as `L ≥ 16 a²`: the only place where the sublinearity of `log` is
used quantitatively. -/
theorem bdtb_const_mul_log_le_half {a L : ℝ} (ha : 0 ≤ a) (hL : 1 ≤ L)
    (h : 16 * a ^ 2 ≤ L) : a * Real.log L ≤ L / 2 := by
  have hsqrt : 4 * a ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by linarith) (by linarith)]
    nlinarith
  have hlog : Real.log L ≤ 2 * Real.sqrt L := bdtb_log_le_two_sqrt hL
  have hs : Real.sqrt L * Real.sqrt L = L := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ L by linarith)]
  nlinarith [Real.sqrt_nonneg L, hs, hlog, ha]

/-- Bootstrapping an upper bound for `T`: from `T ≤ A + b·max 0 (log T)` follows a *logarithmic*
bound for `T` in terms of `log A`. -/
theorem bdtb_max_log_le_of_self_bound {T A b : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hb : 0 ≤ b)
    (h : T ≤ A + b * max 0 (Real.log T)) :
    max 0 (Real.log T) ≤ Real.log (2 * (A + 2 * b ^ 2 + 1)) := by
  have hpos2 : (0 : ℝ) < 2 * (A + 2 * b ^ 2 + 1) := by nlinarith [sq_nonneg b]
  have hlog2 : 0 ≤ Real.log (2 * (A + 2 * b ^ 2 + 1)) :=
    Real.log_nonneg (by nlinarith [sq_nonneg b])
  by_cases hT1 : T ≤ 1
  · have : Real.log T ≤ 0 := Real.log_nonpos hT hT1
    rw [max_eq_left this]; exact hlog2
  · push Not at hT1
    have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    rw [max_eq_right hlogT0] at h ⊢
    have hlog2s : Real.log T ≤ 2 * Real.sqrt T := by
      have h1 : Real.log T ≤ T ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
        Real.log_le_rpow_div hT (by norm_num)
      rw [Real.sqrt_eq_rpow]
      linarith
    set s := Real.sqrt T with hs_def
    have hs0 : 0 ≤ s := Real.sqrt_nonneg T
    have hs2 : s ^ 2 = T := Real.sq_sqrt hT
    have hbound : s ≤ b + Real.sqrt (A + b ^ 2) := by
      have h1 : s ^ 2 ≤ A + b * (2 * s) := by
        have : b * Real.log T ≤ b * (2 * s) := by
          rw [hs_def]; exact mul_le_mul_of_nonneg_left hlog2s hb
        linarith
      have h2 : (s - b) ^ 2 ≤ A + b ^ 2 := by nlinarith
      have h3 : |s - b| ≤ Real.sqrt (A + b ^ 2) := Real.abs_le_sqrt h2
      have h4 : s - b ≤ Real.sqrt (A + b ^ 2) := le_trans (le_abs_self _) h3
      linarith
    have hTsq : T ≤ (b + Real.sqrt (A + b ^ 2)) ^ 2 := by
      rw [← hs2]; exact pow_le_pow_left₀ hs0 hbound 2
    have hsq : Real.sqrt (A + b ^ 2) ^ 2 = A + b ^ 2 :=
      Real.sq_sqrt (by nlinarith [sq_nonneg b])
    have hfinal : T ≤ 2 * (A + 2 * b ^ 2 + 1) := by
      nlinarith [Real.sqrt_nonneg (A + b ^ 2), hsq]
    exact Real.log_le_log (by linarith) hfinal

/-- The real part of `κ * z` is bounded by `‖κ‖` times the `ℓ¹`-norm of the parts of `z`. -/
theorem bdtb_abs_re_mul_le (κ z : ℂ) : |(κ * z).re| ≤ ‖κ‖ * (|z.re| + |z.im|) := by
  rw [Complex.mul_re]
  have h1 : |κ.re * z.re - κ.im * z.im| ≤ |κ.re * z.re| + |κ.im * z.im| :=
    abs_sub_le_iff.mpr
      ⟨by linarith [le_abs_self (κ.re * z.re), neg_le_abs (κ.im * z.im)],
       by linarith [le_abs_self (κ.im * z.im), neg_le_abs (κ.re * z.re)]⟩
  rw [abs_mul, abs_mul] at h1
  have h4 : |κ.re| * |z.re| ≤ ‖κ‖ * |z.re| :=
    mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm κ) (abs_nonneg _)
  have h5 : |κ.im| * |z.im| ≤ ‖κ‖ * |z.im| :=
    mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm κ) (abs_nonneg _)
  linarith

/-- The imaginary part of `κ * z` is bounded by `‖κ‖` times the `ℓ¹`-norm of the parts of `z`. -/
theorem bdtb_abs_im_mul_le (κ z : ℂ) : |(κ * z).im| ≤ ‖κ‖ * (|z.re| + |z.im|) := by
  rw [Complex.mul_im]
  have h1 : |κ.re * z.im + κ.im * z.re| ≤ |κ.re * z.im| + |κ.im * z.re| :=
    abs_add_le _ _
  rw [abs_mul, abs_mul] at h1
  have h4 : |κ.re| * |z.im| ≤ ‖κ‖ * |z.im| :=
    mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm κ) (abs_nonneg _)
  have h5 : |κ.im| * |z.re| ≤ ‖κ‖ * |z.re| :=
    mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm κ) (abs_nonneg _)
  linarith

/-! ## 2. The pointwise deep estimate

`deep_box_eventually` is the analytic heart: for every `L` beyond an explicit threshold (a
function of the data `κ, sa, K, M, H, W, X` only), every point `w` of the deep region whose
`φa`-level `h` sits in the window `[L - W - 2, L - 2]` with imaginary part bounded by `H` has
real part `> X` and imaginary part bounded by `H + |Im sa| + 2‖κ‖ log L + 4`. -/

theorem deep_box_eventually {κ sa : ℂ} {K M H W X : ℝ} (hK : 0 ≤ K) (hM : 0 < M) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ w h : ℂ,
      M ≤ w.re →
      ‖h - sa - (w - κ * Complex.log w)‖ ≤ K / w.re →
      L - W - 2 ≤ h.re → h.re ≤ L - 2 → |h.im| ≤ H →
      X < w.re ∧ |w.im| ≤ H + |sa.im| + 2 * ‖κ‖ * Real.log L + 4 := by
  set a : ℝ := ‖κ‖ with ha_def
  have ha : 0 ≤ a := by rw [ha_def]; exact norm_nonneg κ
  set Δ : ℝ := K / M with hΔ_def
  have hΔ : 0 ≤ Δ := by rw [hΔ_def]; exact div_nonneg hK hM.le
  set γ : ℝ := max 0 (-(Real.log M)) with hγ_def
  have hγ : 0 ≤ γ := by rw [hγ_def]; exact le_max_left _ _
  set β₀ : ℝ := H + |sa.re| + |sa.im| + 2 * a * (γ + Real.pi / 2 + 1) + 2 * Δ + 1 with hβ₀_def
  set β₂ : ℝ := Real.log (2 * (β₀ + 8 * a ^ 2 + 2)) with hβ₂_def
  set C₀ : ℝ := W + 2 + |sa.re| + a * (β₂ + γ + Real.pi / 2) + Δ with hC₀_def
  set R' : ℝ := X + C₀ with hR'_def
  set L₀ : ℝ := max 1 (max (16 * a ^ 2) (max (4 * C₀) (max (2 * R' + 2)
      (max (Real.exp (Real.pi / 2 + β₂ + γ)) K)))) with hL₀_def
  refine ⟨L₀, ?_⟩
  intro L hL w h hu herr hre_low hre_up him
  have hH : 0 ≤ H := le_trans (abs_nonneg h.im) him
  have hβ₀_nn : 0 ≤ β₀ := by
    rw [hβ₀_def]
    nlinarith [abs_nonneg sa.re, abs_nonneg sa.im, ha, hΔ, hγ, Real.pi_pos]
  have hβ₂_nn : 0 ≤ β₂ := by
    rw [hβ₂_def]; apply Real.log_nonneg; nlinarith [sq_nonneg a]
  rw [hL₀_def] at hL
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hL16 : 16 * a ^ 2 ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hL)
  have hL4C : 4 * C₀ ≤ L := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hL))
  have hL2R : 2 * R' + 2 ≤ L := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hL)))
  have hLexp : Real.exp (Real.pi / 2 + β₂ + γ) ≤ L := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) hL))))
  have hLK : K ≤ L := le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) hL))))
  have hu_pos : 0 < w.re := lt_of_lt_of_le hM hu
  have hMT : M ≤ ‖w‖ := le_trans hu (Complex.re_le_norm w)
  have hT0 : 0 ≤ ‖w‖ := norm_nonneg w
  set ℓ : ℝ := max 0 (Real.log ‖w‖) with hℓ_def
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ_def]; exact le_max_left _ _
  have hlog_re_le : (Complex.log w).re ≤ ℓ := by
    rw [Complex.log_re, hℓ_def]; exact le_max_right _ _
  have hlog_re_abs : |(Complex.log w).re| ≤ ℓ + γ := by
    rw [Complex.log_re]
    by_cases hx : 0 ≤ Real.log ‖w‖
    · rw [abs_of_nonneg hx]
      have h2 : Real.log ‖w‖ ≤ ℓ := by rw [hℓ_def]; exact le_max_right _ _
      linarith
    · push Not at hx
      rw [abs_of_neg hx]
      have hlogMT : Real.log M ≤ Real.log ‖w‖ := Real.log_le_log hM hMT
      have h1 : -Real.log ‖w‖ ≤ γ := by
        rw [hγ_def]
        exact le_trans (by linarith) (le_max_right _ _)
      linarith
  have hlog_im_le : (Complex.log w).im ≤ Real.pi / 2 := by
    rw [Complex.log_im]
    exact Complex.arg_le_pi_div_two_iff.mpr (Or.inl hu_pos.le)
  have hlog_im_ge : -(Real.pi / 2) ≤ (Complex.log w).im := by
    rw [Complex.log_im]
    exact Complex.neg_pi_div_two_le_arg_iff.mpr (Or.inl hu_pos.le)
  have hlog_im_abs : |(Complex.log w).im| ≤ Real.pi / 2 := abs_le.mpr ⟨hlog_im_ge, hlog_im_le⟩
  have hlogsum : |(Complex.log w).re| + |(Complex.log w).im| ≤ ℓ + γ + Real.pi / 2 := by
    linarith
  have hmul_bound : ‖κ‖ * (|(Complex.log w).re| + |(Complex.log w).im|)
      ≤ a * (ℓ + γ + Real.pi / 2) := by
    rw [ha_def]
    exact mul_le_mul_of_nonneg_left hlogsum (norm_nonneg κ)
  have hmul_re_abs : |(κ * Complex.log w).re| ≤ a * (ℓ + γ + Real.pi / 2) :=
    le_trans (bdtb_abs_re_mul_le κ (Complex.log w)) hmul_bound
  have hmul_im_abs : |(κ * Complex.log w).im| ≤ a * (ℓ + γ + Real.pi / 2) :=
    le_trans (bdtb_abs_im_mul_le κ (Complex.log w)) hmul_bound
  set E : ℂ := h - sa - (w - κ * Complex.log w) with hE_def
  have hEre : |E.re| ≤ K / w.re := le_trans (Complex.abs_re_le_norm E) herr
  have hEim : |E.im| ≤ K / w.re := le_trans (Complex.abs_im_le_norm E) herr
  have hKdiv : K / w.re ≤ Δ := by
    rw [hΔ_def]
    exact div_le_div_of_nonneg_left hK hM hu
  have hwE : w = (h - sa) + κ * Complex.log w - E := by rw [hE_def]; ring
  have hre_eq : w.re = (h - sa).re + (κ * Complex.log w).re - E.re := by
    conv_lhs => rw [hwE]
    simp only [Complex.add_re, Complex.sub_re]
  have him_eq : w.im = (h - sa).im + (κ * Complex.log w).im - E.im := by
    conv_lhs => rw [hwE]
    simp only [Complex.add_im, Complex.sub_im]
  have hupper : w.re ≤ h.re + |sa.re| + a * (ℓ + γ + Real.pi / 2) + K / w.re := by
    have h1 : (h - sa).re ≤ h.re + |sa.re| := by
      rw [Complex.sub_re]; linarith [neg_le_abs sa.re]
    have h2 : (κ * Complex.log w).re ≤ a * (ℓ + γ + Real.pi / 2) :=
      le_trans (le_abs_self _) hmul_re_abs
    have h3 : -E.re ≤ K / w.re := by linarith [hEre, neg_le_abs E.re]
    linarith
  have hv_upper : |w.im| ≤ H + |sa.im| + a * (ℓ + γ + Real.pi / 2) + K / w.re := by
    have h1 : |(h - sa).im| ≤ |h.im| + |sa.im| := by
      rw [Complex.sub_im]
      exact abs_sub_le_iff.mpr
        ⟨by linarith [le_abs_self h.im, neg_le_abs sa.im],
         by linarith [le_abs_self sa.im, neg_le_abs h.im]⟩
    have h4 : |w.im| ≤ |(h - sa).im| + |(κ * Complex.log w).im| + |E.im| := by
      rw [him_eq, show (h - sa).im + (κ * Complex.log w).im - E.im
            = ((h - sa).im + (κ * Complex.log w).im) + (-E.im) by ring]
      have h1 := abs_add_le ((h - sa).im + (κ * Complex.log w).im) (-E.im)
      have h2 := abs_add_le (h - sa).im ((κ * Complex.log w).im)
      simp only [abs_neg] at h1
      linarith
    linarith
  have hT_le : ‖w‖ ≤ L + β₀ + 2 * a * ℓ := by
    have h1 : ‖w‖ ≤ w.re + |w.im| := by
      have := Complex.norm_le_abs_re_add_abs_im w
      rw [abs_of_pos hu_pos] at this
      exact this
    have h2 : w.re + |w.im|
        ≤ (L - 2) + (H + |sa.re| + |sa.im| + 2 * a * (ℓ + γ + Real.pi / 2)) + 2 * Δ := by
      linarith [hupper, hv_upper, hre_up, hKdiv]
    have h3 : (L - 2) + (H + |sa.re| + |sa.im| + 2 * a * (ℓ + γ + Real.pi / 2)) + 2 * Δ
        ≤ L + β₀ + 2 * a * ℓ := by
      rw [hβ₀_def]; nlinarith [ha, hγ, Real.pi_pos]
    linarith
  have hself : ‖w‖ ≤ (L + β₀) + 2 * a * max 0 (Real.log ‖w‖) := by
    rw [hℓ_def] at hT_le
    linarith
  have hℓ_le : ℓ ≤ Real.log L + β₂ := by
    have h1 := bdtb_max_log_le_of_self_bound (T := ‖w‖) (A := L + β₀) (b := 2 * a)
      hT0 (by linarith) (by linarith) hself
    have h2 : Real.log (2 * ((L + β₀) + 2 * (2 * a) ^ 2 + 1)) ≤ Real.log L + β₂ := by
      have hc : 0 ≤ β₀ + 8 * a ^ 2 + 1 := by nlinarith [hβ₀_nn, sq_nonneg a]
      have h3 : 2 * ((L + β₀) + 2 * (2 * a) ^ 2 + 1) ≤ L * (2 * (β₀ + 8 * a ^ 2 + 2)) := by
        nlinarith [hL1, hc, sq_nonneg a, hβ₀_nn]
      have h5 : (0 : ℝ) < 2 * ((L + β₀) + 2 * (2 * a) ^ 2 + 1) := by
        nlinarith [sq_nonneg a, hβ₀_nn]
      calc Real.log (2 * ((L + β₀) + 2 * (2 * a) ^ 2 + 1))
          ≤ Real.log (L * (2 * (β₀ + 8 * a ^ 2 + 2))) := Real.log_le_log h5 h3
        _ = Real.log L + β₂ := by
            rw [Real.log_mul (by linarith) (by nlinarith [sq_nonneg a, hβ₀_nn]), hβ₂_def]
    rw [hℓ_def]
    exact le_trans h1 h2
  have hB_le : a * (ℓ + γ + Real.pi / 2) ≤ a * (Real.log L + β₂ + γ + Real.pi / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) ha
  have hu_lower : L - a * Real.log L - C₀ ≤ w.re := by
    have h1 : h.re - |sa.re| ≤ (h - sa).re := by
      rw [Complex.sub_re]; linarith [le_abs_self sa.re]
    have h2 : -(K / w.re) ≤ -E.re := by linarith [hEre, le_abs_self E.re]
    have h3 : -(a * (ℓ + γ + Real.pi / 2)) ≤ (κ * Complex.log w).re :=
      neg_le_of_abs_le hmul_re_abs
    rw [hre_eq, hC₀_def]
    linarith [h1, h2, h3, hB_le, hre_low]
  have hF : L / 2 - C₀ ≤ w.re := by
    have h1 : a * Real.log L ≤ L / 2 := bdtb_const_mul_log_le_half ha hL1 hL16
    linarith
  have hX_lt : X < w.re := by
    have h1 : R' + 1 ≤ L / 2 := by rw [hR'_def]; linarith
    have h2 : X + C₀ + 1 ≤ L / 2 := by linarith
    linarith
  have hu_quarter : L / 4 ≤ w.re := by
    have h1 : L / 4 ≤ L / 2 - C₀ := by linarith
    linarith
  have hKdiv4 : K / w.re ≤ 4 * K / L := by
    have h1 : 0 < L / 4 := by linarith
    have h2 : K / w.re ≤ K / (L / 4) := div_le_div_of_nonneg_left hK h1 hu_quarter
    have h3 : K / (L / 4) = 4 * K / L := by field_simp
    linarith
  have hv_final : |w.im| ≤ H + |sa.im| + 2 * a * Real.log L + 4 := by
    have h1 : Real.pi / 2 + β₂ + γ ≤ Real.log L :=
      (Real.le_log_iff_exp_le (by linarith)).mpr hLexp
    have hd : a * (Real.log L + β₂ + γ + Real.pi / 2)
        = a * Real.log L + a * (β₂ + γ + Real.pi / 2) := by ring
    have h2 : a * (β₂ + γ + Real.pi / 2) ≤ a * Real.log L :=
      mul_le_mul_of_nonneg_left (by linarith) ha
    have h3 : 4 * K / L ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith [hv_upper, hB_le, hKdiv4, hd, h2, h3]
  exact ⟨hX_lt, hv_final⟩

/-! ## 3. The deepening of a windowed box, from the uniform transient bound -/

theorem box_deep_of_transient_bound {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} {Pa : Set ℂ}
    {φa : ℂ → ℂ} (P : Work.PARIMPL.ParNormal d) (A : Work.FlowerGlue2.AttrCompare P Pa φa)
    (hLB : ∃ M M' : ℝ, A.N ≤ M ∧ ∀ z ∈ Pa,
      (Work.FlowerGlue2.w0 P z).re ≤ M → (φa z).re ≤ M') (X₁ W H : ℝ) :
    ∀ X : ℝ, ∃ J : ℕ, ∀ y ∈ Pa,
      X₁ ≤ (φa y).re → (φa y).re ≤ X₁ + W → |(φa y).im| ≤ H →
        ∀ j ≥ J, X < (Work.FlowerGlue2.w0 P ((Work.PARIMPL.Ft c₀)^[j] y)).re ∧
          |(Work.FlowerGlue2.w0 P ((Work.PARIMPL.Ft c₀)^[j] y)).im|
            ≤ H + |(A.sa).im| + 2 * ‖P.κ c₀‖ * Real.log (X₁ + W + j + 2) + 4 := by
  obtain ⟨M, M', hMN, hLB'⟩ := hLB
  have hMpos : 0 < M := lt_of_lt_of_le A.N_pos hMN
  intro X
  obtain ⟨L₀, hL₀⟩ := deep_box_eventually (κ := P.κ c₀) (sa := A.sa) (K := A.K) (M := M)
    (H := H) (W := W) (X := X) A.K_nonneg hMpos
  obtain ⟨J₀, hJ₀⟩ := exists_nat_gt (M' - X₁)
  obtain ⟨J₁, hJ₁⟩ := exists_nat_gt (L₀ - X₁ - W - 2)
  refine ⟨max J₀ J₁, ?_⟩
  intro y hy hy1 hy2 hy3 j hj
  have hj0 : J₀ ≤ j := le_trans (le_max_left _ _) hj
  have hj1 : J₁ ≤ j := le_trans (le_max_right _ _) hj
  have hj0' : M' - X₁ < (j : ℝ) := lt_of_lt_of_le hJ₀ (by exact_mod_cast hj0)
  have hj1' : L₀ - X₁ - W - 2 < (j : ℝ) := lt_of_lt_of_le hJ₁ (by exact_mod_cast hj1)
  have hzmem_gen : ∀ n : ℕ, (Work.PARIMPL.Ft c₀)^[n] y ∈ Pa := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ k ih => rw [Function.iterate_succ_apply']; exact A.mapsTo_Pa ih
  set z : ℂ := (Work.PARIMPL.Ft c₀)^[j] y with hz_def
  have hzmem : z ∈ Pa := by rw [hz_def]; exact hzmem_gen j
  have hz₁ : z ≠ d.z₁ := fun h => z₁_not_mem_loc P A (h ▸ hzmem)
  have hphi : φa z = φa y + j := by
    rw [hz_def]; exact phi_iterate_loc P A hy j
  have hdeep : M < (w0 P z).re := by
    by_contra hle
    push Not at hle
    have h1 := hLB' z hzmem hle
    have h2 : X₁ + (j : ℝ) ≤ (φa z).re := by
      have hcast : ((j : ℂ)).re = (j : ℝ) := by simp
      rw [hphi, Complex.add_re, hcast]; linarith
    linarith
  have hRe : (φa z).re = (φa y).re + j := by
    have hcast : ((j : ℂ)).re = (j : ℝ) := by simp
    rw [hphi, Complex.add_re, hcast]
  have hkey := hL₀ (X₁ + W + (j : ℝ) + 2) (by linarith) (w0 P z) (φa z)
    (le_of_lt hdeep)
    (by
      have hN : A.N < (w0 P z).re := lt_of_le_of_lt hMN hdeep
      have h := A.asymp z hzmem hz₁ hN
      have heq : φa z - (Work.FatouCoord.approxCoord (P.κ c₀) (w0 P z) + A.sa)
          = φa z - A.sa - (w0 P z - P.κ c₀ * Complex.log (w0 P z)) := by
        simp only [Work.FatouCoord.approxCoord]; ring
      rw [heq] at h
      exact h)
    (by linarith)
    (by linarith)
    (by
      have hcasti : ((j : ℂ)).im = 0 := by simp
      rw [hphi, Complex.add_im, hcasti, add_zero]
      exact hy3)
  exact hkey

end

end Work.FlowerGlue2
