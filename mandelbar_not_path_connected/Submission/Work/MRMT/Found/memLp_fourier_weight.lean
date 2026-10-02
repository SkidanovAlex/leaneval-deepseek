import Mathlib
import Submission.Work.MRMT.Found.PrincipalAux
import Submission.Work.MRMT.Found.beurlingL2_translateL2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal FourierTransform SchwartzMap

namespace Work.MRMT.Found

/-! ## Auxiliary lemmas for `memLp_fourier_weight`

The proof of `memLp_fourier_weight` proceeds as follows.

* `mw_ofReal_norm_sq_eq_lintegral` : the `L²` norm of an `Lp`-element is the
  Lebesgue integral of its squared pointwise norm.
* `mw_transChar_eq`, `mw_transChar_ofReal_mul` : the Fourier multiplier of a
  translation is the exponential it is defined to be.
* `mw_four_mul_le_norm_exp_sub_one` : the Jordan-type chord bound, giving a lower
  bound for `‖e^{iθ} - 1‖`.
* `mw_fourier_diffOp` : the Fourier transform of `(τ_t - 1)^n f` is the pointwise
  product of `(transChar t - 1)^n` and the Fourier transform of `f`.
* `mw_lintegral_inner_sq_ne_top` : the ball argument: from the fourth-difference
  bound we get the finiteness of `∫ ‖⟪u,ξ⟫‖⁸ ‖𝓕f(ξ)‖²` for every unit vector `u`.
* `mw_lintegral_sq_ne_top_of_re_im` : the combination of the two coordinate
  directions into the finiteness of `∫ (1+‖ξ‖²)⁴ ‖𝓕f(ξ)‖²`.
-/

/-! ### 1. The `L²` norm as an integral -/

theorem mw_ofReal_norm_sq_eq_lintegral (g : Lp ℂ 2 (volume : Measure ℂ)) :
    ENNReal.ofReal (‖g‖ ^ 2) = ∫⁻ ξ, ENNReal.ofReal ‖(g : ℂ → ℂ) ξ‖ ^ 2 := by
  set a : ENNReal := ∫⁻ ξ, ENNReal.ofReal ‖(g : ℂ → ℂ) ξ‖ ^ 2 with ha
  have hgmeas : AEStronglyMeasurable (g : ℂ → ℂ) (volume : Measure ℂ) := Lp.aestronglyMeasurable g
  have h1 : eLpNorm (g : ℂ → ℂ) 2 (volume : Measure ℂ) = a ^ ((1:ℝ)/2) := by
    rw [ha]
    have h2 := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := (volume : Measure ℂ))
      (p := (2:ENNReal)) (f := (g : ℂ → ℂ)) (by norm_num) (by norm_num) hgmeas
    simpa [ofReal_norm] using h2
  have hne : a ≠ ⊤ := by
    intro hbot
    have htop := Lp.eLpNorm_ne_top g
    rw [h1, hbot] at htop
    exact htop (by simp)
  have h2 : ‖g‖ = a.toReal ^ ((1:ℝ)/2) := by
    rw [Lp.norm_def, h1, ENNReal.toReal_rpow]
  rw [h2]
  conv_rhs => rw [← ENNReal.ofReal_toReal hne]
  congr 1
  rw [← Real.rpow_natCast (a.toReal ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num

theorem mw_aemeasurable_ofReal_norm (F : ℂ → ℂ) (hF : AEStronglyMeasurable F (volume : Measure ℂ)) :
    AEMeasurable (fun ξ : ℂ => ENNReal.ofReal ‖F ξ‖) volume := by
  have h := hF.enorm
  refine h.congr ?_
  filter_upwards with ξ
  rw [ofReal_norm]

/-! ### 2. The Fourier multiplier of a translation -/

theorem mw_transChar_eq (t ξ : ℂ) :
    transChar t ξ = Complex.exp (Complex.I * ↑(2 * Real.pi * (inner ℝ (-t) ξ))) := by
  rw [transChar, Real.fourierChar_apply, mul_comm]

theorem mw_transChar_ofReal_mul (ε : ℝ) (u ξ : ℂ) :
    transChar ((ε : ℂ) * u) ξ =
      Complex.exp (Complex.I * ↑(-(2 * Real.pi * ε * (inner ℝ u ξ)))) := by
  rw [mw_transChar_eq]
  have harg : inner ℝ (-((ε : ℂ) * u)) ξ = -ε * inner ℝ u ξ := by
    rw [show -((ε : ℂ) * u) = (-ε) • u by simp, real_inner_smul_left]
  have hreal : 2 * Real.pi * (inner ℝ (-((ε : ℂ) * u)) ξ)
      = -(2 * Real.pi * ε * (inner ℝ u ξ)) := by
    rw [harg]; ring
  rw [hreal]

/-! ### 3. The chord/Jordan lower bound -/

theorem mw_pow4_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have h1 : (x + y)^2 ≤ 2*(x^2 + y^2) := by nlinarith [sq_nonneg (x - y)]
  have h2 : (x^2 + y^2)^2 ≤ 2*(x^4 + y^4) := by nlinarith [sq_nonneg (x^2 - y^2)]
  calc (x+y)^4 = ((x+y)^2)^2 := by ring
    _ ≤ (2*(x^2+y^2))^2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = 4*(x^2+y^2)^2 := by ring
    _ ≤ 4*(2*(x^4+y^4)) := by linarith [h2]
    _ = 8*(x^4+y^4) := by ring

theorem mw_weight_pointwise (ξ : ℂ) :
    (1 + ‖ξ‖ ^ 2) ^ 4 ≤ 8 + 64 * |ξ.re| ^ 8 + 64 * |ξ.im| ^ 8 := by
  have h1 : ‖ξ‖ ^ 2 = ξ.re ^ 2 + ξ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [h1]
  have hsq : ξ.re ^ 2 + ξ.im ^ 2 = |ξ.re| ^ 2 + |ξ.im| ^ 2 := by rw [sq_abs, sq_abs]
  rw [hsq]
  have h3 := mw_pow4_add_le 1 (|ξ.re| ^ 2 + |ξ.im| ^ 2) zero_le_one (by positivity)
  have h4 := mw_pow4_add_le (|ξ.re| ^ 2) (|ξ.im| ^ 2) (by positivity) (by positivity)
  nlinarith [h3, h4]

theorem mw_four_mul_le_norm_exp_sub_one (ε a : ℝ) (hε : 0 ≤ ε)
    (hπ : 2 * Real.pi * ε * |a| ≤ Real.pi) :
    4 * ε * |a| ≤ ‖Complex.exp (Complex.I * ↑(-(2 * Real.pi * ε * a))) - 1‖ := by
  have hkey : ‖Complex.exp (Complex.I * ↑(-(2 * Real.pi * ε * a))) - 1‖
      = 2 * |Real.sin (Real.pi * ε * a)| := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show -(2 * Real.pi * ε * a) / 2 = -(Real.pi * ε * a) by ring]
    simp [Real.sin_neg]
  rw [hkey]
  have hy : |Real.pi * ε * a| = Real.pi * ε * |a| := by
    rw [abs_mul, abs_mul, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg hε]
  have h1 : |Real.pi * ε * a| ≤ Real.pi / 2 := by rw [hy]; linarith
  have hb : 2 * ε * |a| ≤ |Real.sin (Real.pi * ε * a)| := by
    have h2 := Real.mul_le_sin (abs_nonneg (Real.pi * ε * a)) h1
    rw [← Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [h1, Real.pi_pos] :
      |Real.pi * ε * a| ≤ Real.pi)] at h2
    calc 2 * ε * |a| = 2 / Real.pi * |Real.pi * ε * a| := by rw [hy]; field_simp
      _ ≤ |Real.sin (Real.pi * ε * a)| := h2
  linarith [hb]

theorem mw_norm_transChar_sub_one_ge (ε : ℝ) (hε : 0 ≤ ε) (u ξ : ℂ) (hu : ‖u‖ = 1)
    (hπ : 2 * Real.pi * ε * |inner ℝ u ξ| ≤ Real.pi) :
    4 * ε * |inner ℝ u ξ| ≤ ‖transChar ((ε : ℂ) * u) ξ - 1‖ := by
  have h := mw_four_mul_le_norm_exp_sub_one ε (inner ℝ u ξ) hε hπ
  rwa [← mw_transChar_ofReal_mul] at h

/-! ### 4. The Fourier transform of a difference operator -/

theorem mw_fourier_translateL2_sub (t : ℂ) (f : Lp ℂ 2 (volume : Measure ℂ)) :
    (((Lp.fourierTransformₗᵢ ℂ ℂ) (translateL2 t f - f) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[volume] fun ξ => (transChar t ξ - 1) *
        (((Lp.fourierTransformₗᵢ ℂ ℂ) f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) ξ := by
  have hsub : (Lp.fourierTransformₗᵢ ℂ ℂ) (translateL2 t f - f)
      = (Lp.fourierTransformₗᵢ ℂ ℂ) (translateL2 t f) - (Lp.fourierTransformₗᵢ ℂ ℂ) f :=
    map_sub _ _ _
  rw [hsub]
  filter_upwards [Lp.coeFn_sub ((Lp.fourierTransformₗᵢ ℂ ℂ) (translateL2 t f))
      ((Lp.fourierTransformₗᵢ ℂ ℂ) f), fourier_translateL2 t f] with ξ h1 h2
  rw [h1]
  simp only [Pi.sub_apply, h2]
  ring

theorem mw_fourier_diffOp (t : ℂ) (n : ℕ) (f : Lp ℂ 2 (volume : Measure ℂ)) :
    (((Lp.fourierTransformₗᵢ ℂ ℂ) (diffOp t n f) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[volume] fun ξ => (transChar t ξ - 1) ^ n *
        (((Lp.fourierTransformₗᵢ ℂ ℂ) f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) ξ := by
  induction n generalizing f with
  | zero =>
      have h0 : diffOp t 0 f = f := by
        change ((translateL2 t - 1) ^ (0:ℕ)) f = f
        rw [pow_zero, ContinuousLinearMap.one_apply]
      rw [h0]
      filter_upwards with ξ
      simp
  | succ n ih =>
      have hstep : diffOp t (n + 1) f = diffOp t n (translateL2 t f - f) := by
        change ((translateL2 t - 1) ^ (n + 1)) f
          = ((translateL2 t - 1) ^ n) (translateL2 t f - f)
        rw [pow_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.one_apply]
      rw [hstep]
      have e1 : (((Lp.fourierTransformₗᵢ ℂ ℂ) (diffOp t n (translateL2 t f - f)) :
            Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
          =ᵐ[volume] fun ξ => (transChar t ξ - 1) ^ n *
            (((Lp.fourierTransformₗᵢ ℂ ℂ) (translateL2 t f - f) :
              Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) ξ := ih (translateL2 t f - f)
      have e2 := mw_fourier_translateL2_sub t f
      filter_upwards [e1, e2] with ξ g1 g2
      rw [g1, g2, pow_succ]
      ring

/-! ### 5. The ball argument -/

theorem mw_lintegral_inner_sq_ne_top {f : Lp ℂ 2 (volume : Measure ℂ)} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t : ℂ, ‖diffOp t 4 f‖ ≤ C * ‖t‖ ^ 4) (u : ℂ) (hu : ‖u‖ = 1) :
    ∫⁻ ξ : ℂ, ENNReal.ofReal ‖inner ℝ u ξ‖ ^ 8 *
      ENNReal.ofReal ‖(⇑((Lp.fourierTransformₗᵢ ℂ ℂ) f)) ξ‖ ^ 2 ≠ ⊤ := by
  set F : ℂ → ℂ := ⇑((Lp.fourierTransformₗᵢ ℂ ℂ) f) with hFdef
  set g : ℂ → ENNReal :=
    fun ξ => ENNReal.ofReal ‖inner ℝ u ξ‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2 with hgdef
  have key : ∀ t : ℂ, ∫⁻ ξ, ENNReal.ofReal ‖(transChar t ξ - 1) ^ 4 * F ξ‖ ^ 2
      ≤ ENNReal.ofReal ((C * ‖t‖ ^ 4) ^ 2) := by
    intro t
    have hfd := mw_fourier_diffOp t 4 f
    have e1 : ∫⁻ ξ, ENNReal.ofReal ‖(transChar t ξ - 1) ^ 4 * F ξ‖ ^ 2
        = ∫⁻ ξ, ENNReal.ofReal ‖(⇑((Lp.fourierTransformₗᵢ ℂ ℂ) (diffOp t 4 f))) ξ‖ ^ 2 := by
      rw [hFdef]
      apply lintegral_congr_ae
      filter_upwards [hfd] with ξ hξ
      rw [hξ]
    rw [e1]
    calc ∫⁻ ξ, ENNReal.ofReal ‖(⇑((Lp.fourierTransformₗᵢ ℂ ℂ) (diffOp t 4 f))) ξ‖ ^ 2
        = ENNReal.ofReal (‖(Lp.fourierTransformₗᵢ ℂ ℂ) (diffOp t 4 f)‖ ^ 2) :=
          (mw_ofReal_norm_sq_eq_lintegral _).symm
      _ = ENNReal.ofReal (‖diffOp t 4 f‖ ^ 2) := by
          have hnf : ‖(Lp.fourierTransformₗᵢ ℂ ℂ) (diffOp t 4 f)‖ = ‖diffOp t 4 f‖ :=
            Lp.norm_fourier_eq (diffOp t 4 f)
          rw [hnf]
      _ ≤ ENNReal.ofReal ((C * ‖t‖ ^ 4) ^ 2) :=
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (h t) 2)
  have hball : ∀ n : ℕ, ENNReal.ofReal ((2:ℝ) ^ 16) *
      (∫⁻ ξ, (Metric.closedBall (0:ℂ) ((n:ℝ)+1)).indicator g ξ) ≤ ENNReal.ofReal (C ^ 2) := by
    intro n
    set R : ℝ := (n:ℝ)+1 with hRdef
    have hRpos : 0 < R := by rw [hRdef]; positivity
    set ε : ℝ := (2*R)⁻¹ with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; positivity
    have hεnonneg : 0 ≤ ε := le_of_lt hεpos
    have ht : ‖((ε:ℂ) * u)‖ = ε := by
      rw [norm_mul, show ‖(ε:ℂ)‖ = |ε| by simp, abs_of_pos hεpos, hu, mul_one]
    have hpt : ∀ ξ : ℂ,
        ENNReal.ofReal ((2:ℝ) ^ 16) * ((Metric.closedBall (0:ℂ) R).indicator g ξ)
        ≤ ENNReal.ofReal ((ε⁻¹) ^ 8) *
          ENNReal.ofReal ‖(transChar ((ε:ℂ)*u) ξ - 1) ^ 4 * F ξ‖ ^ 2 := by
      intro ξ
      by_cases hξ : ξ ∈ Metric.closedBall (0:ℂ) R
      · rw [Set.indicator_of_mem hξ, hgdef]
        have hξR : ‖ξ‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hξ
        have hin : |inner ℝ u ξ| ≤ R := by
          calc |inner ℝ u ξ| ≤ ‖u‖ * ‖ξ‖ := abs_real_inner_le_norm u ξ
            _ = ‖ξ‖ := by rw [hu, one_mul]
            _ ≤ R := hξR
        have hπ : 2 * Real.pi * ε * |inner ℝ u ξ| ≤ Real.pi := by
          have h2 : 2 * Real.pi * ε * |inner ℝ u ξ| ≤ 2 * Real.pi * ε * R :=
            mul_le_mul_of_nonneg_left hin (by positivity)
          have h3 : 2 * Real.pi * ε * R = Real.pi := by
            rw [hεdef]; field_simp
          linarith [h2, h3.le]
        have hnorm : 4 * ε * |inner ℝ u ξ| ≤ ‖transChar ((ε:ℂ)*u) ξ - 1‖ :=
          mw_norm_transChar_sub_one_ge ε hεnonneg u ξ hu hπ
        have hnorm2 : 4 * ε * ‖inner ℝ u ξ‖ ≤ ‖transChar ((ε:ℂ)*u) ξ - 1‖ := hnorm
        have h4 : (4*ε) ^ 8 * ‖inner ℝ u ξ‖ ^ 8
            ≤ ‖transChar ((ε:ℂ)*u) ξ - 1‖ ^ 8 := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) hnorm2 8
        have h5 : ‖(transChar ((ε:ℂ)*u) ξ - 1) ^ 4 * F ξ‖ ^ 2
            = ‖transChar ((ε:ℂ)*u) ξ - 1‖ ^ 8 * ‖F ξ‖ ^ 2 := by
          rw [norm_mul, norm_pow, mul_pow]; ring
        have hreal : (2:ℝ)^16 * (‖inner ℝ u ξ‖ ^ 8 * ‖F ξ‖ ^ 2)
            ≤ (ε⁻¹) ^ 8 * ‖(transChar ((ε:ℂ)*u) ξ - 1) ^ 4 * F ξ‖ ^ 2 := by
          rw [h5]
          have h6 : (2:ℝ)^16 = (4*ε) ^ 8 * (ε⁻¹) ^ 8 := by
            rw [← mul_pow]
            have h4ε : (4*ε) * ε⁻¹ = 4 := by
              rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hεpos), mul_one]
            rw [h4ε]; norm_num
          rw [h6]
          have hFnn : (0:ℝ) ≤ ‖F ξ‖ ^ 2 := sq_nonneg _
          have heps : (0:ℝ) ≤ (ε⁻¹) ^ 8 := by positivity
          calc ((4*ε) ^ 8 * (ε⁻¹) ^ 8) * (‖inner ℝ u ξ‖ ^ 8 * ‖F ξ‖ ^ 2)
              = (ε⁻¹) ^ 8 * ((4*ε) ^ 8 * ‖inner ℝ u ξ‖ ^ 8) * ‖F ξ‖ ^ 2 := by ring
            _ ≤ (ε⁻¹) ^ 8 * ‖transChar ((ε:ℂ)*u) ξ - 1‖ ^ 8 * ‖F ξ‖ ^ 2 := by
                gcongr
            _ = (ε⁻¹) ^ 8 * (‖transChar ((ε:ℂ)*u) ξ - 1‖ ^ 8 * ‖F ξ‖ ^ 2) := by ring
        have hle := ENNReal.ofReal_le_ofReal hreal
        have hconvL : ENNReal.ofReal ((2:ℝ)^16 * (‖inner ℝ u ξ‖ ^ 8 * ‖F ξ‖ ^ 2))
            = ENNReal.ofReal ((2:ℝ) ^ 16)
              * (ENNReal.ofReal ‖inner ℝ u ξ‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]
        have hconvR : ENNReal.ofReal ((ε⁻¹) ^ 8 *
              ‖(transChar ((ε:ℂ)*u) ξ - 1) ^ 4 * F ξ‖ ^ 2)
            = ENNReal.ofReal ((ε⁻¹) ^ 8)
              * ENNReal.ofReal ‖(transChar ((ε:ℂ)*u) ξ - 1) ^ 4 * F ξ‖ ^ 2 := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _)]
        rwa [hconvL, hconvR] at hle
      · rw [Set.indicator_of_notMem hξ, mul_zero]
        exact zero_le
    calc ENNReal.ofReal ((2:ℝ)^16) * ∫⁻ ξ, (Metric.closedBall (0:ℂ) R).indicator g ξ
        = ∫⁻ ξ, ENNReal.ofReal ((2:ℝ)^16) * ((Metric.closedBall (0:ℂ) R).indicator g ξ) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne).symm
      _ ≤ ∫⁻ ξ, ENNReal.ofReal ((ε⁻¹)^8) *
            ENNReal.ofReal ‖(transChar ((ε:ℂ)*u) ξ - 1) ^ 4 * F ξ‖ ^ 2 :=
          lintegral_mono hpt
      _ = ENNReal.ofReal ((ε⁻¹)^8) *
            ∫⁻ ξ, ENNReal.ofReal ‖(transChar ((ε:ℂ)*u) ξ - 1) ^ 4 * F ξ‖ ^ 2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne
      _ ≤ ENNReal.ofReal ((ε⁻¹)^8) * ENNReal.ofReal ((C * ‖((ε:ℂ)*u)‖ ^ 4) ^ 2) := by
          gcongr
          exact key ((ε:ℂ)*u)
      _ = ENNReal.ofReal (C ^ 2) := by
          rw [ht, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have hεne : ε ≠ 0 := ne_of_gt hεpos
          field_simp
  have hmono : ∀ᵐ ξ ∂(volume : Measure ℂ), Monotone fun n : ℕ =>
      (Metric.closedBall (0:ℂ) ((n:ℝ)+1)).indicator g ξ := by
    refine Filter.Eventually.of_forall (fun ξ => ?_)
    intro n m hnm
    have hsub : Metric.closedBall (0:ℂ) ((n:ℝ)+1) ⊆ Metric.closedBall (0:ℂ) ((m:ℝ)+1) := by
      intro x hx
      simp only [Metric.mem_closedBall, dist_zero_right] at hx ⊢
      have : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hnm
      linarith
    exact Set.indicator_le_indicator_of_subset hsub zero_le ξ
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun ξ : ℂ => (Metric.closedBall (0:ℂ) ((n:ℝ)+1)).indicator g ξ) (volume : Measure ℂ) := by
    intro n
    refine AEMeasurable.indicator ?_ (Metric.isClosed_closedBall.measurableSet)
    rw [hgdef]
    have h1 : AEMeasurable (fun ξ : ℂ => ENNReal.ofReal ‖inner ℝ u ξ‖ ^ 8) volume :=
      (((continuous_const.inner continuous_id).norm).measurable.ennreal_ofReal.pow_const 8).aemeasurable
    have h2 : AEMeasurable (fun ξ : ℂ => ENNReal.ofReal ‖F ξ‖ ^ 2) volume :=
      (mw_aemeasurable_ofReal_norm F (Lp.aestronglyMeasurable _)).pow_const 2
    exact h1.mul h2
  have hsup_eq : ∀ ξ : ℂ, (⨆ n : ℕ, (Metric.closedBall (0:ℂ) ((n:ℝ)+1)).indicator g ξ) = g ξ := by
    intro ξ
    apply le_antisymm
    · refine iSup_le (fun n => ?_)
      exact Set.indicator_le_self (Metric.closedBall (0:ℂ) ((n:ℝ)+1)) g ξ
    · have hmem : ξ ∈ Metric.closedBall (0:ℂ) ((⌈‖ξ‖⌉₊ : ℝ)+1) := by
        simp only [Metric.mem_closedBall, dist_zero_right]
        have : ‖ξ‖ ≤ (⌈‖ξ‖⌉₊ : ℝ) := Nat.le_ceil ‖ξ‖
        linarith
      have h := le_iSup (fun n : ℕ => (Metric.closedBall (0:ℂ) ((n:ℝ)+1)).indicator g ξ) (⌈‖ξ‖⌉₊)
      rwa [Set.indicator_of_mem hmem] at h
  have hiSup := lintegral_iSup' hmeas hmono
  have hcongr : ∫⁻ ξ, g ξ
      = ∫⁻ ξ, (⨆ n : ℕ, (Metric.closedBall (0:ℂ) ((n:ℝ)+1)).indicator g ξ) :=
    lintegral_congr_ae (Filter.Eventually.of_forall (fun ξ => (hsup_eq ξ).symm))
  have hmain : ∫⁻ ξ, g ξ
      = ⨆ n : ℕ, ∫⁻ ξ, (Metric.closedBall (0:ℂ) ((n:ℝ)+1)).indicator g ξ := by
    rw [hcongr, hiSup]
  have hbound : ∫⁻ ξ, g ξ ≤ ENNReal.ofReal (C ^ 2) := by
    rw [hmain, iSup_le_iff]
    intro n
    have hone : (1:ENNReal) ≤ ENNReal.ofReal ((2:ℝ) ^ 16) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    have hI : (0:ENNReal) ≤ ∫⁻ ξ, (Metric.closedBall (0:ℂ) ((n:ℝ)+1)).indicator g ξ := zero_le
    calc (∫⁻ ξ, (Metric.closedBall (0:ℂ) ((n:ℝ)+1)).indicator g ξ)
        = 1 * (∫⁻ ξ, (Metric.closedBall (0:ℂ) ((n:ℝ)+1)).indicator g ξ) := (one_mul _).symm
      _ ≤ ENNReal.ofReal ((2:ℝ) ^ 16)
            * (∫⁻ ξ, (Metric.closedBall (0:ℂ) ((n:ℝ)+1)).indicator g ξ) :=
          mul_le_mul_of_nonneg_right hone hI
      _ ≤ ENNReal.ofReal (C ^ 2) := hball n
  exact ne_of_lt (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)

/-! ### 6. Combining the two coordinate directions -/

theorem mw_lintegral_sq_ne_top_of_re_im (F : ℂ → ℂ) (hF : AEStronglyMeasurable F (volume : Measure ℂ))
    (hre : ∫⁻ ξ : ℂ, ENNReal.ofReal ‖ξ.re‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2 ≠ ⊤)
    (him : ∫⁻ ξ : ℂ, ENNReal.ofReal ‖ξ.im‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2 ≠ ⊤)
    (h2 : ∫⁻ ξ : ℂ, ENNReal.ofReal ‖F ξ‖ ^ 2 ≠ ⊤) :
    ∫⁻ ξ : ℂ, ENNReal.ofReal ‖(((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * F ξ‖ ^ 2 ≠ ⊤ := by
  have hFen : AEMeasurable (fun ξ : ℂ => ENNReal.ofReal ‖F ξ‖) volume :=
    mw_aemeasurable_ofReal_norm F hF
  have hG : AEMeasurable (fun ξ : ℂ => ENNReal.ofReal ‖F ξ‖ ^ 2) volume := hFen.pow_const 2
  have hAem : AEMeasurable (fun ξ : ℂ => ENNReal.ofReal (8:ℝ) * ENNReal.ofReal ‖F ξ‖ ^ 2)
      volume := hG.const_mul _
  have hBem : AEMeasurable (fun ξ : ℂ => ENNReal.ofReal (64:ℝ)
      * (ENNReal.ofReal ‖ξ.re‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2)) volume := by
    have h1 : AEMeasurable (fun ξ : ℂ => ENNReal.ofReal ‖ξ.re‖ ^ 8) volume :=
      (((continuous_re).norm).measurable.ennreal_ofReal.pow_const 8).aemeasurable
    exact (h1.mul hG).const_mul _
  have hABem : AEMeasurable (fun ξ : ℂ => ENNReal.ofReal (8:ℝ) * ENNReal.ofReal ‖F ξ‖ ^ 2
      + ENNReal.ofReal (64:ℝ) * (ENNReal.ofReal ‖ξ.re‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2))
      volume := hAem.add hBem
  have hpt : ∀ ξ : ℂ, ENNReal.ofReal ‖(((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * F ξ‖ ^ 2
      ≤ ENNReal.ofReal (8:ℝ) * ENNReal.ofReal ‖F ξ‖ ^ 2
        + ENNReal.ofReal (64:ℝ) * (ENNReal.ofReal ‖ξ.re‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2)
        + ENNReal.ofReal (64:ℝ) * (ENNReal.ofReal ‖ξ.im‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2) := by
    intro ξ
    have ha : ‖(((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ)‖ ^ 2 = (1 + ‖ξ‖ ^ 2) ^ 4 := by
      rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
    have hsq : ENNReal.ofReal ‖(((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ)‖ ^ 2
        = ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ 4) := by
      rw [← ENNReal.ofReal_pow (norm_nonneg _), ha]
    have h1 : ENNReal.ofReal ‖(((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * F ξ‖ ^ 2
        = ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ 4) * ENNReal.ofReal ‖F ξ‖ ^ 2 := by
      rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _), mul_pow, hsq]
    rw [h1]
    have h2' : ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ 4) ≤ ENNReal.ofReal (8:ℝ)
        + ENNReal.ofReal (64:ℝ) * ENNReal.ofReal ‖ξ.re‖ ^ 8
        + ENNReal.ofReal (64:ℝ) * ENNReal.ofReal ‖ξ.im‖ ^ 8 := by
      have h := ENNReal.ofReal_le_ofReal (mw_weight_pointwise ξ)
      have he : ENNReal.ofReal (8 + 64 * |ξ.re| ^ 8 + 64 * |ξ.im| ^ 8)
          = ENNReal.ofReal (8:ℝ) + ENNReal.ofReal (64:ℝ) * ENNReal.ofReal ‖ξ.re‖ ^ 8
            + ENNReal.ofReal (64:ℝ) * ENNReal.ofReal ‖ξ.im‖ ^ 8 := by
        have hqe : (0:ℝ) ≤ 64 * |ξ.im| ^ 8 := by positivity
        have hpe : (0:ℝ) ≤ 8 + 64 * |ξ.re| ^ 8 := by positivity
        have hre' : (0:ℝ) ≤ 64 * |ξ.re| ^ 8 := by positivity
        rw [ENNReal.ofReal_add hpe hqe, ENNReal.ofReal_add (by norm_num) hre',
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_pow (abs_nonneg _), ENNReal.ofReal_pow (abs_nonneg _)]
        rfl
      rwa [he] at h
    calc ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ 4) * ENNReal.ofReal ‖F ξ‖ ^ 2
        ≤ (ENNReal.ofReal (8:ℝ) + ENNReal.ofReal (64:ℝ) * ENNReal.ofReal ‖ξ.re‖ ^ 8
            + ENNReal.ofReal (64:ℝ) * ENNReal.ofReal ‖ξ.im‖ ^ 8) * ENNReal.ofReal ‖F ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h2' zero_le
      _ = ENNReal.ofReal (8:ℝ) * ENNReal.ofReal ‖F ξ‖ ^ 2
          + ENNReal.ofReal (64:ℝ) * (ENNReal.ofReal ‖ξ.re‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2)
          + ENNReal.ofReal (64:ℝ) * (ENNReal.ofReal ‖ξ.im‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2) := by
          ring
  refine ne_of_lt ?_
  calc ∫⁻ ξ, ENNReal.ofReal ‖(((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * F ξ‖ ^ 2
      ≤ ∫⁻ ξ, (ENNReal.ofReal (8:ℝ) * ENNReal.ofReal ‖F ξ‖ ^ 2
          + ENNReal.ofReal (64:ℝ) * (ENNReal.ofReal ‖ξ.re‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2)
          + ENNReal.ofReal (64:ℝ) * (ENNReal.ofReal ‖ξ.im‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (8:ℝ) * (∫⁻ ξ, ENNReal.ofReal ‖F ξ‖ ^ 2)
        + ENNReal.ofReal (64:ℝ) * (∫⁻ ξ, ENNReal.ofReal ‖ξ.re‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2)
        + ENNReal.ofReal (64:ℝ) * (∫⁻ ξ, ENNReal.ofReal ‖ξ.im‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2) := by
        rw [lintegral_add_left' hABem, lintegral_add_left' hAem]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne,
            lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne,
            lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
    _ < ⊤ := by
        rw [ENNReal.add_lt_top, ENNReal.add_lt_top]
        exact ⟨⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Ne.lt_top h2),
                ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Ne.lt_top hre)⟩,
               ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Ne.lt_top him)⟩

/-! ### 7. The main theorem -/

theorem memLp_fourier_weight {q : ℂ → ℂ}
    (hq : MeasureTheory.MemLp q 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℂ, ‖Work.MRMT.Found.diffOp t 4 (hq.toLp q)‖ ≤ C * ‖t‖ ^ 4) :
    MeasureTheory.MemLp (fun ξ : ℂ => Work.MRMT.Found.fourierWeight ξ *
      (((MeasureTheory.Lp.fourierTransformₗᵢ ℂ ℂ) (hq.toLp q) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) ξ)
      2 (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  obtain ⟨C, hC, hCt⟩ := h
  set F : ℂ → ℂ := ⇑((Lp.fourierTransformₗᵢ ℂ ℂ) (hq.toLp q)) with hFdef
  have hFmeas : AEStronglyMeasurable F (volume : Measure ℂ) := Lp.aestronglyMeasurable _
  have hinner1 : ∀ ξ : ℂ, inner ℝ (1:ℂ) ξ = ξ.re := by
    intro ξ; rw [Complex.inner]; simp
  have hinnerI : ∀ ξ : ℂ, inner ℝ Complex.I ξ = ξ.im := by
    intro ξ; rw [Complex.inner, Complex.conj_I]; simp [Complex.mul_I_re]
  have h2 : ∫⁻ ξ : ℂ, ENNReal.ofReal ‖F ξ‖ ^ 2 ≠ ⊤ := by
    rw [hFdef, ← mw_ofReal_norm_sq_eq_lintegral ((Lp.fourierTransformₗᵢ ℂ ℂ) (hq.toLp q))]
    exact ENNReal.ofReal_lt_top.ne
  have hre0 := mw_lintegral_inner_sq_ne_top hC hCt (1:ℂ) (by norm_num)
  have hre : ∫⁻ ξ : ℂ, ENNReal.ofReal ‖ξ.re‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2 ≠ ⊤ := by
    rw [hFdef]
    calc ∫⁻ ξ : ℂ, ENNReal.ofReal ‖ξ.re‖ ^ 8
            * ENNReal.ofReal ‖(⇑((Lp.fourierTransformₗᵢ ℂ ℂ) (hq.toLp q))) ξ‖ ^ 2
        = ∫⁻ ξ : ℂ, ENNReal.ofReal ‖inner ℝ (1:ℂ) ξ‖ ^ 8
            * ENNReal.ofReal ‖(⇑((Lp.fourierTransformₗᵢ ℂ ℂ) (hq.toLp q))) ξ‖ ^ 2 := by
          apply lintegral_congr_ae
          filter_upwards with ξ
          rw [hinner1]
      _ ≠ ⊤ := hre0
  have him0 := mw_lintegral_inner_sq_ne_top hC hCt Complex.I (by norm_num)
  have him : ∫⁻ ξ : ℂ, ENNReal.ofReal ‖ξ.im‖ ^ 8 * ENNReal.ofReal ‖F ξ‖ ^ 2 ≠ ⊤ := by
    rw [hFdef]
    calc ∫⁻ ξ : ℂ, ENNReal.ofReal ‖ξ.im‖ ^ 8
            * ENNReal.ofReal ‖(⇑((Lp.fourierTransformₗᵢ ℂ ℂ) (hq.toLp q))) ξ‖ ^ 2
        = ∫⁻ ξ : ℂ, ENNReal.ofReal ‖inner ℝ Complex.I ξ‖ ^ 8
            * ENNReal.ofReal ‖(⇑((Lp.fourierTransformₗᵢ ℂ ℂ) (hq.toLp q))) ξ‖ ^ 2 := by
          apply lintegral_congr_ae
          filter_upwards with ξ
          rw [hinnerI]
      _ ≠ ⊤ := him0
  have hW := mw_lintegral_sq_ne_top_of_re_im F hFmeas hre him h2
  have hwcont : Continuous (fourierWeight : ℂ → ℂ) := by
    change Continuous (fun ξ : ℂ => (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ))
    fun_prop
  have hmeas : AEStronglyMeasurable (fun ξ : ℂ => fourierWeight ξ * F ξ) volume :=
    hwcont.aestronglyMeasurable.mul hFmeas
  show eLpNorm (fun ξ : ℂ => fourierWeight ξ * F ξ) 2 (volume : Measure ℂ) < ∞
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ENNReal)) (by norm_num) (by norm_num) hmeas]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  rw [show (fun ξ : ℂ => ‖fourierWeight ξ * F ξ‖ₑ ^ ENNReal.toReal (2:ENNReal))
      = fun ξ : ℂ => ENNReal.ofReal ‖(((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * F ξ‖ ^ 2 by
        funext ξ
        rw [ofReal_norm, fourierWeight_apply,
            show ENNReal.toReal (2:ENNReal) = ((2:ℕ):ℝ) by norm_num,
            ENNReal.rpow_natCast]]
  exact hW

end Work.MRMT.Found
