/-
# Bounds for `E₁₀·𝓛_S` and `(E₁₄/Δ)·𝓛_S` on the funnel `{Im z ≥ 1/3}`

This file proves the `z`-side estimates for the `K_-` kernel on the third-generation
funnel region `{Im z ≥ 1/3}`:

* `‖E₁₀(z) 𝓛_S(z)‖` is bounded,
* `‖(E₁₄/Δ)(z) 𝓛_S(z)‖ ≤ C e^{π Im z}`.

The two inputs are (i) the first-order cusp expansions of `E₄, E₆, Δ` on `{Im z ≥ 1/3}`
(`Work.Asymptotics.ZAtomsThird.first_order`, `Work.Asymptotics.delta_lower_third`), which
bound `E₄, E₆` from above and `1/Δ` from above, and (ii) the exponential bound
`‖𝓛_S(z)‖ ≤ C e^{-π Im z}` on `{Im z ≥ 1/3}`.

For (ii) one uses the explicit branch on `{Im z > 1/2}` (`Work.Residues.LogLambdaData_LS_eq_LamS`)
together with `Work.Residues.LamSExpBound` when `Im z ≥ 1`; on the bounded strip
`{1/3 ≤ Im z ≤ 1}` the function `𝓛_S` is bounded because it is continuous and anti-periodic
(`𝓛_S(z+1) = -𝓛_S(z)`), so that its absolute value is one-periodic in `Re z` and the strip is
covered by translates of a compact rectangle.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.ZAtomsThird.first_order
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.Residues.LamSExpBound
import Submission.Work.Residues.ThetaAux
import Submission.Work.Asymptotics.KMinusFunnel.LS_vadd_int_norm

namespace Work.Asymptotics

open UpperHalfPlane
open scoped Topology

noncomputable section

/-! ## The rectangle `{1/3 ≤ Im z ≤ 1, 0 ≤ Re z ≤ 1}` is compact in `ℍ` -/

/-- The compact rectangle `{1/3 ≤ Im z ≤ 1} ∩ {0 ≤ Re z ≤ 1}` of the upper half plane. -/
lemma isCompact_zStrip :
    IsCompact {z : UpperHalfPlane |
      1 / 3 ≤ z.im ∧ z.im ≤ 1 ∧ 0 ≤ (z : ℂ).re ∧ (z : ℂ).re ≤ 1} := by
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff]
  have hcoe : ((↑) : UpperHalfPlane → ℂ) ''
      {z : UpperHalfPlane | 1 / 3 ≤ z.im ∧ z.im ≤ 1 ∧ 0 ≤ (z : ℂ).re ∧ (z : ℂ).re ≤ 1}
      = {w : ℂ | 1 / 3 ≤ w.im ∧ w.im ≤ 1 ∧ 0 ≤ w.re ∧ w.re ≤ 1} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨w, by linarith⟩, ⟨h1, h2, h3, h4⟩, rfl⟩
  rw [hcoe]
  have hclosed : IsClosed {w : ℂ | 1 / 3 ≤ w.im ∧ w.im ≤ 1 ∧ 0 ≤ w.re ∧ w.re ≤ 1} := by
    have h1 : IsClosed {w : ℂ | (1 / 3 : ℝ) ≤ w.im} :=
      isClosed_le continuous_const Complex.continuous_im
    have h2 : IsClosed {w : ℂ | w.im ≤ (1 : ℝ)} :=
      isClosed_le Complex.continuous_im continuous_const
    have h3 : IsClosed {w : ℂ | (0 : ℝ) ≤ w.re} :=
      isClosed_le continuous_const Complex.continuous_re
    have h4 : IsClosed {w : ℂ | w.re ≤ (1 : ℝ)} :=
      isClosed_le Complex.continuous_re continuous_const
    rw [show {w : ℂ | 1 / 3 ≤ w.im ∧ w.im ≤ 1 ∧ 0 ≤ w.re ∧ w.re ≤ 1}
        = {w : ℂ | (1 / 3 : ℝ) ≤ w.im} ∩ {w : ℂ | w.im ≤ (1 : ℝ)}
          ∩ {w : ℂ | (0 : ℝ) ≤ w.re} ∩ {w : ℂ | w.re ≤ (1 : ℝ)} from by
      ext w
      constructor
      · intro h
        exact ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩
      · intro h
        exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩]
    exact ((h1.inter h2).inter h3).inter h4
  have hbdd : Bornology.IsBounded {w : ℂ | 1 / 3 ≤ w.im ∧ w.im ≤ 1 ∧ 0 ≤ w.re ∧ w.re ≤ 1} :=
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset (fun w hw => by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      have hre : |w.re| ≤ 1 := abs_le.mpr ⟨by linarith [hw.2.2.1], hw.2.2.2⟩
      have him : |w.im| ≤ 1 := abs_le.mpr ⟨by linarith [hw.1], hw.2.1⟩
      linarith [Complex.norm_le_abs_re_add_abs_im w])
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩

/-! ## `𝓛_S` is bounded on the strip `{1/3 ≤ Im z ≤ 1}` -/

/-- `𝓛_S` is bounded on the strip `{1/3 ≤ Im z ≤ 1}`.  The proof reduces `z` to the compact
rectangle `{0 ≤ Re z ≤ 1}` by an integer translation, under which `|𝓛_S|` is invariant. -/
lemma LS_bdd_strip (ℓ : Work.Kernels.LogLambdaData) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : UpperHalfPlane, 1 / 3 ≤ z.im → z.im ≤ 1 → ‖ℓ.L_S z‖ ≤ M := by
  obtain ⟨z₀, -, hmax⟩ := isCompact_zStrip.exists_isMaxOn
    ⟨⟨Complex.I, by simp [Complex.I_im]⟩, by
      simp only [Set.mem_ofPred_eq, UpperHalfPlane.im, Complex.I_im, UpperHalfPlane.re,
        Complex.I_re]
      norm_num⟩
    ((MDifferentiable.continuous ℓ.holo_S).norm.continuousOn)
  refine ⟨‖ℓ.L_S z₀‖, norm_nonneg _, fun z hz1 hz2 => ?_⟩
  set n : ℤ := ⌊(z : ℂ).re⌋ with hn
  have hre_im : ((-(n : ℝ)) +ᵥ z : ℂ).im = (z : ℂ).im := by
    rw [UpperHalfPlane.coe_vadd]
    simp [Complex.add_im]
  have hre_re : ((-(n : ℝ)) +ᵥ z : ℂ).re = (z : ℂ).re - (n : ℝ) := by
    rw [UpperHalfPlane.coe_vadd]
    simp only [Complex.add_re, Complex.ofReal_re]
    ring
  have hmem : ((-(n : ℝ)) +ᵥ z) ∈
      {w : UpperHalfPlane | 1 / 3 ≤ w.im ∧ w.im ≤ 1 ∧ 0 ≤ (w : ℂ).re ∧ (w : ℂ).re ≤ 1} := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← UpperHalfPlane.coe_im, hre_im, UpperHalfPlane.coe_im]
      exact hz1
    · rw [← UpperHalfPlane.coe_im, hre_im, UpperHalfPlane.coe_im]
      exact hz2
    · rw [hre_re]
      have h : (n : ℝ) ≤ (z : ℂ).re := by rw [hn]; exact Int.floor_le _
      linarith
    · rw [hre_re]
      have h : (z : ℂ).re < (n : ℝ) + 1 := by rw [hn]; exact Int.lt_floor_add_one _
      linarith
  have hnorm : ‖ℓ.L_S ((-(n : ℝ)) +ᵥ z)‖ = ‖ℓ.L_S z‖ := by
    have h := Work.Asymptotics.KMinusFunnel.LS_vadd_int_norm ℓ (-n) z
    rwa [Int.cast_neg] at h
  calc ‖ℓ.L_S z‖ = ‖ℓ.L_S ((-(n : ℝ)) +ᵥ z)‖ := hnorm.symm
    _ ≤ ‖ℓ.L_S z₀‖ := hmax hmem

/-! ## Exponential decay of `𝓛_S` on `{Im z ≥ 1/3}` -/

/-- `‖𝓛_S(z)‖ ≤ C e^{-π Im z}` for `Im z ≥ 1/3`. -/
lemma LS_exp_bound_third (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 / 3 ≤ z.im →
      ‖ℓ.L_S z‖ ≤ C * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨M, hM0, hM⟩ := LS_bdd_strip ℓ
  obtain ⟨C₁, hC₁, hC₁b⟩ := Work.Residues.LamSExpBound
  refine ⟨max (M * Real.exp Real.pi) C₁ + 1, by positivity, fun z hz => ?_⟩
  rcases le_total (1 : ℝ) z.im with h | h
  · have hW : (z : ℂ) ∈ Work.Kernels.LogLambda.W := by
      show (1 / 2 : ℝ) < (z : ℂ).im
      rw [UpperHalfPlane.coe_im]; linarith
    have hzim : 1 ≤ (z : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact h
    have h1 : ‖ℓ.L_S z‖ ≤ C₁ * Real.exp (-(Real.pi * z.im)) := by
      rw [Work.Residues.LogLambdaData_LS_eq_LamS ℓ z (by linarith)]
      simpa [UpperHalfPlane.coe_im] using hC₁b (z : ℂ) hW hzim
    have h2 : C₁ ≤ max (M * Real.exp Real.pi) C₁ + 1 := by
      linarith [le_max_right (M * Real.exp Real.pi) C₁]
    calc ‖ℓ.L_S z‖ ≤ C₁ * Real.exp (-(Real.pi * z.im)) := h1
      _ ≤ (max (M * Real.exp Real.pi) C₁ + 1) * Real.exp (-(Real.pi * z.im)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  · have him1 : z.im ≤ 1 := h
    have hfe : Real.exp Real.pi * Real.exp (-(Real.pi * z.im))
        = Real.exp (Real.pi * (1 - z.im)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hMineq : M ≤ M * Real.exp Real.pi * Real.exp (-(Real.pi * z.im)) := by
      rw [mul_assoc, hfe]
      have h1 : (1 : ℝ) ≤ Real.exp (Real.pi * (1 - z.im)) := by
        rw [Real.one_le_exp_iff]; nlinarith [Real.pi_pos, him1]
      nlinarith [hM0]
    have hCge : M * Real.exp Real.pi ≤ max (M * Real.exp Real.pi) C₁ + 1 := by
      linarith [le_max_left (M * Real.exp Real.pi) C₁]
    calc ‖ℓ.L_S z‖ ≤ M := hM z hz him1
      _ ≤ M * Real.exp Real.pi * Real.exp (-(Real.pi * z.im)) := hMineq
      _ ≤ (max (M * Real.exp Real.pi) C₁ + 1) * Real.exp (-(Real.pi * z.im)) :=
          mul_le_mul_of_nonneg_right hCge (Real.exp_pos _).le

/-! ## The target bound -/

/-- Bounds for `E₁₀·𝓛_S` and `(E₁₄/Δ)·𝓛_S` on the funnel `{Im z ≥ 1/3}`. -/
theorem KMinusFunnelZBoundsLS (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E10Fun z * ℓ.L_S z‖ ≤ C ∧
      ‖Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z * ℓ.L_S z‖ ≤ C * Real.exp (Real.pi * z.im) := by
  obtain ⟨CLS, hCLS, hLS⟩ := LS_exp_bound_third ℓ
  obtain ⟨Cfo, hCfo, -, hE4, hE6, -⟩ := ZAtomsThird.first_order
  obtain ⟨cd, hcd, hd⟩ := delta_lower_third
  set K : ℝ := 1 + Cfo / 3 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hKle : ∀ z : UpperHalfPlane, 1 / 3 ≤ z.im → ‖Work.Kernels.E4Fun z‖ ≤ K ∧
      ‖Work.Kernels.E6Fun z‖ ≤ K := by
    intro z hz
    have hq : ‖Work.Kernels.qParamFun z‖ ≤ 1 / 3 := norm_qParam_le_third hz
    have h4 : Cfo * ‖Work.Kernels.qParamFun z‖ ≤ Cfo * (1 / 3) :=
      mul_le_mul_of_nonneg_left hq hCfo.le
    have h6 : Cfo * ‖Work.Kernels.qParamFun z‖ ≤ Cfo * (1 / 3) := h4
    constructor
    · have h := hE4 z hz
      have hsplit : Work.Kernels.E4Fun z = (Work.Kernels.E4Fun z - 1) + 1 := by ring
      rw [hsplit]
      have h1 := norm_add_le (Work.Kernels.E4Fun z - 1) (1 : ℂ)
      rw [norm_one] at h1
      rw [hKdef]
      linarith
    · have h := hE6 z hz
      have hsplit : Work.Kernels.E6Fun z = (Work.Kernels.E6Fun z - 1) + 1 := by ring
      rw [hsplit]
      have h1 := norm_add_le (Work.Kernels.E6Fun z - 1) (1 : ℂ)
      rw [norm_one] at h1
      rw [hKdef]
      linarith
  refine ⟨K ^ 2 * CLS + K ^ 3 * CLS / cd + 1, ?_, fun z hz => ⟨?_, ?_⟩⟩
  · have h1 : 0 ≤ K ^ 2 * CLS := mul_nonneg (pow_nonneg hKpos.le 2) hCLS.le
    have h2 : 0 ≤ K ^ 3 * CLS / cd :=
      div_nonneg (mul_nonneg (pow_nonneg hKpos.le 3) hCLS.le) hcd.le
    linarith
  · have hE4z : ‖Work.Kernels.E4Fun z‖ ≤ K := (hKle z hz).1
    have hE6z : ‖Work.Kernels.E6Fun z‖ ≤ K := (hKle z hz).2
    have hLSz : ‖ℓ.L_S z‖ ≤ CLS * Real.exp (-(Real.pi * z.im)) := hLS z hz
    have hexp1 : Real.exp (-(Real.pi * z.im)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, z.im_pos]
    have hrepr : ‖Work.Kernels.E10Fun z * ℓ.L_S z‖
        = ‖Work.Kernels.E4Fun z‖ * ‖Work.Kernels.E6Fun z‖ * ‖ℓ.L_S z‖ := by
      rw [show Work.Kernels.E10Fun z = Work.Kernels.E4Fun z * Work.Kernels.E6Fun z from rfl,
        norm_mul, norm_mul]
    rw [hrepr]
    have hprod : ‖Work.Kernels.E4Fun z‖ * ‖Work.Kernels.E6Fun z‖ ≤ K * K :=
      mul_le_mul hE4z hE6z (norm_nonneg _) hKpos.le
    have hstep : ‖Work.Kernels.E4Fun z‖ * ‖Work.Kernels.E6Fun z‖ * ‖ℓ.L_S z‖
        ≤ K * K * (CLS * Real.exp (-(Real.pi * z.im))) :=
      mul_le_mul hprod hLSz (norm_nonneg _)
        (mul_nonneg hKpos.le hKpos.le)
    have hstep2 : K * K * (CLS * Real.exp (-(Real.pi * z.im))) ≤ K ^ 2 * CLS := by
      have h2 : K * K = K ^ 2 := by ring
      rw [h2]
      have h3 : K ^ 2 * (CLS * Real.exp (-(Real.pi * z.im))) ≤ K ^ 2 * (CLS * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp1 hCLS.le) (pow_nonneg hKpos.le 2)
      linarith [h3]
    have hstep3 : K ^ 2 * CLS ≤ K ^ 2 * CLS + K ^ 3 * CLS / cd + 1 := by
      have h : 0 ≤ K ^ 3 * CLS / cd :=
        div_nonneg (mul_nonneg (pow_nonneg hKpos.le 3) hCLS.le) hcd.le
      linarith
    linarith [hstep, hstep2, hstep3]
  · have hE4z : ‖Work.Kernels.E4Fun z‖ ≤ K := (hKle z hz).1
    have hE6z : ‖Work.Kernels.E6Fun z‖ ≤ K := (hKle z hz).2
    have hDz : cd * ‖Work.Kernels.qParamFun z‖ ≤ ‖Work.Kernels.DeltaFun z‖ := hd z hz
    have hqpos : 0 < ‖Work.Kernels.qParamFun z‖ := by
      rw [norm_qParamFun]; exact Real.exp_pos _
    have hDpos : 0 < ‖Work.Kernels.DeltaFun z‖ := lt_of_lt_of_le (mul_pos hcd hqpos) hDz
    have hinv : ‖Work.Kernels.DeltaFun z‖⁻¹ ≤ Real.exp (2 * Real.pi * z.im) / cd := by
      have h1 : ‖Work.Kernels.DeltaFun z‖⁻¹ ≤ (cd * ‖Work.Kernels.qParamFun z‖)⁻¹ :=
        (inv_le_inv₀ hDpos (mul_pos hcd hqpos)).mpr hDz
      have h2 : (cd * ‖Work.Kernels.qParamFun z‖)⁻¹
          = Real.exp (2 * Real.pi * z.im) / cd := by
        rw [norm_qParamFun, mul_inv, Real.exp_neg, inv_inv, div_eq_mul_inv]
        ring
      rwa [h2] at h1
    have hE14z : ‖Work.Kernels.E14Fun z‖ ≤ K ^ 3 := by
      rw [show Work.Kernels.E14Fun z
          = Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z from rfl, norm_mul, norm_pow]
      have h42 : ‖Work.Kernels.E4Fun z‖ ^ 2 ≤ K ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hE4z 2
      have hstep : ‖Work.Kernels.E4Fun z‖ ^ 2 * ‖Work.Kernels.E6Fun z‖ ≤ K ^ 2 * K :=
        calc ‖Work.Kernels.E4Fun z‖ ^ 2 * ‖Work.Kernels.E6Fun z‖
              ≤ K ^ 2 * ‖Work.Kernels.E6Fun z‖ :=
              mul_le_mul_of_nonneg_right h42 (norm_nonneg _)
          _ ≤ K ^ 2 * K := mul_le_mul_of_nonneg_left hE6z (pow_nonneg hKpos.le 2)
      calc ‖Work.Kernels.E4Fun z‖ ^ 2 * ‖Work.Kernels.E6Fun z‖ ≤ K ^ 2 * K := hstep
        _ = K ^ 3 := by ring
    have hrepr : ‖Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z * ℓ.L_S z‖
        = ‖Work.Kernels.E14Fun z‖ * ‖Work.Kernels.DeltaFun z‖⁻¹ * ‖ℓ.L_S z‖ := by
      rw [norm_mul, norm_div, div_eq_mul_inv]
    rw [hrepr]
    have hexp : Real.exp (2 * Real.pi * z.im) * Real.exp (-(Real.pi * z.im))
        = Real.exp (Real.pi * z.im) := by
      rw [← Real.exp_add]; congr 1; ring
    have hmain : ‖Work.Kernels.E14Fun z‖ * ‖Work.Kernels.DeltaFun z‖⁻¹ * ‖ℓ.L_S z‖
        ≤ K ^ 3 * (Real.exp (2 * Real.pi * z.im) / cd)
          * (CLS * Real.exp (-(Real.pi * z.im))) :=
      mul_le_mul
        (mul_le_mul hE14z hinv (inv_nonneg.mpr (norm_nonneg _)) (pow_nonneg hKpos.le 3))
        (hLS z hz) (norm_nonneg _)
        (mul_nonneg (pow_nonneg hKpos.le 3) (div_nonneg (Real.exp_pos _).le hcd.le))
    have heq : K ^ 3 * (Real.exp (2 * Real.pi * z.im) / cd)
          * (CLS * Real.exp (-(Real.pi * z.im)))
        = (K ^ 3 * CLS / cd) * Real.exp (Real.pi * z.im) := by
      rw [← hexp]; ring
    have hfin : (K ^ 3 * CLS / cd) * Real.exp (Real.pi * z.im)
        ≤ (K ^ 2 * CLS + K ^ 3 * CLS / cd + 1) * Real.exp (Real.pi * z.im) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have h : 0 ≤ K ^ 2 * CLS := mul_nonneg (pow_nonneg hKpos.le 2) hCLS.le
      linarith
    linarith [hmain, heq, hfin]

end

end Work.Asymptotics
