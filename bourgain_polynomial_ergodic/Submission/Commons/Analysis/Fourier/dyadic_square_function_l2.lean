import Mathlib
import Submission.Commons.Analysis.Fourier.l2_multiplier_sum_square_function
import Submission.Commons.Analysis.Fourier.bandOp_l2_multiplier_bound
import Submission.Commons.Analysis.Fourier.nested_scales_maximal_l2_real
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv
import Submission.Commons.Analysis.Fourier.lintegral_fourierInv_eq
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral

namespace Commons.Analysis.Fourier

open MeasureTheory Filter
open scoped FourierTransform ENNReal BigOperators Topology Convolution

set_option maxHeartbeats 1000000

/-! ## Young's inequality `L² ⋆ L¹ ⊆ L²` on the real line -/

/-- `x ^ (y + z) = x ^ y * x ^ z` in `ℝ≥0∞` for nonnegative exponents `y, z`. -/
private theorem ennreal_rpow_add_of_nonneg' {x : ℝ≥0∞} {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rcases hy.eq_or_lt with rfl | hy'
    · rw [zero_add, ENNReal.rpow_zero, one_mul]
    · rcases hz.eq_or_lt with rfl | hz'
      · rw [add_zero, ENNReal.rpow_zero, mul_one]
      · rw [ENNReal.zero_rpow_of_pos (by linarith), ENNReal.zero_rpow_of_pos hy',
          ENNReal.zero_rpow_of_pos hz', zero_mul]
  rcases eq_or_ne x ∞ with rfl | hxtop
  · rcases hy.eq_or_lt with rfl | hy'
    · rw [zero_add, ENNReal.rpow_zero, one_mul]
    · rcases hz.eq_or_lt with rfl | hz'
      · rw [add_zero, ENNReal.rpow_zero, mul_one]
      · rw [ENNReal.top_rpow_of_pos (by linarith), ENNReal.top_rpow_of_pos hy',
          ENNReal.top_rpow_of_pos hz', ENNReal.top_mul_top]
  · exact ENNReal.rpow_add y z hx0 hxtop

/-- Hölder's inequality for three functions, with exponents summing to one. -/
private theorem lintegral_holder_three' {f0 f1 f2 : ℝ → ℝ≥0∞} {a b c : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1) (h0 : AEMeasurable f0 volume)
    (h1 : AEMeasurable f1 volume) (h2 : AEMeasurable f2 volume) :
    ∫⁻ x, f0 x ^ a * (f1 x ^ b * f2 x ^ c) ≤
      (∫⁻ x, f0 x) ^ a * ((∫⁻ x, f1 x) ^ b * (∫⁻ x, f2 x) ^ c) := by
  have h := ENNReal.lintegral_mul_prod_norm_pow_le (s := (Finset.univ : Finset (Fin 2)))
    (g := f0) (f := ![f1, f2]) h0 (by intro i _; fin_cases i <;> assumption)
    a (p := ![b, c])
    (by simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; linarith) ha
    (by intro i _; fin_cases i <;> assumption)
  simpa [Fin.prod_univ_two] using h

/-- **Young's inequality for convolutions** on `ℝ` (in `ℝ≥0∞` form). -/
private theorem lintegral_convolution_rpow_le_lin {p q r : ℝ}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hpqr : 1 / p + 1 / r = 1 + 1 / q)
    {α : ℝ → ℝ≥0∞} (hα : AEMeasurable α volume)
    {β : ℝ → ℝ≥0∞} (hβ : Measurable β) :
    (∫⁻ x, (∫⁻ y, α y * β (x - y)) ^ q) ^ (1 / q) ≤
      (∫⁻ x, α x ^ p) ^ (1 / p) * (∫⁻ x, β x ^ r) ^ (1 / r) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq_pos : 0 < q := hp_pos.trans_le hpq
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have h_invr_eq : (1:ℝ) / r = 1 + 1 / q - 1 / p := by linarith [hpqr]
  have h_invr_pos : 0 < 1 / r := by
    rw [h_invr_eq]
    have h1 : 1 / p ≤ 1 := (div_le_one hp_pos).mpr hp
    have h2 : (0:ℝ) < 1 / q := by positivity
    linarith
  have hr_pos : 0 < r := by rwa [one_div_pos] at h_invr_pos
  have hr_ne : r ≠ 0 := hr_pos.ne'
  have hr_le_q : r ≤ q := by
    have h1 : (1:ℝ) / q ≤ 1 / r := by
      rw [h_invr_eq]
      have h2 : 1 / p ≤ 1 := (div_le_one hp_pos).mpr hp
      linarith
    simp only [one_div] at h1
    exact (inv_le_inv₀ hq_pos hr_pos).mp h1
  set θ1 : ℝ := 1 / q with hθ1def
  set θ2 : ℝ := (q - p) / (p * q) with hθ2def
  set θ3 : ℝ := (q - r) / (r * q) with hθ3def
  have hθ1 : 0 ≤ θ1 := by rw [hθ1def]; positivity
  have hθ2 : 0 ≤ θ2 := by
    rw [hθ2def]; exact div_nonneg (sub_nonneg.mpr hpq) (mul_nonneg hp_pos.le hq_pos.le)
  have hθ3 : 0 ≤ θ3 := by
    rw [hθ3def]; exact div_nonneg (sub_nonneg.mpr hr_le_q) (mul_nonneg hr_pos.le hq_pos.le)
  have h12 : θ1 + θ2 = 1 / p := by
    rw [hθ1def, hθ2def]; field_simp; ring
  have h13 : θ1 + θ3 = 1 / r := by
    rw [hθ1def, hθ3def]; field_simp; ring
  have hsum : θ1 + θ2 + θ3 = 1 := by
    have hθ3' : θ3 = 1 / r - θ1 := by linarith [h13]
    rw [h12, hθ3', hθ1def]
    linarith [hpqr]
  have hpe : p * (θ1 + θ2) = 1 := by rw [h12]; field_simp
  have hre : r * (θ1 + θ3) = 1 := by rw [h13]; field_simp
  set A : ℝ≥0∞ := ∫⁻ x, α x ^ p with hAdef
  set B : ℝ≥0∞ := ∫⁻ x, β x ^ r with hBdef
  have hA : (∫⁻ x, α x ^ p) = A := hAdef.symm
  have hB : (∫⁻ x, β x ^ r) = B := hBdef.symm
  have hβm : Measurable (fun z : ℝ × ℝ => β (z.1 - z.2)) :=
    hβ.comp (continuous_fst.sub continuous_snd).measurable
  have hprod : AEMeasurable (fun z : ℝ × ℝ => α z.2 ^ p * β (z.1 - z.2) ^ r)
      (volume.prod volume) :=
    ((hα.pow_const p).comp_snd).mul (hβm.pow_const r).aemeasurable
  have hmeas : AEMeasurable (fun x => ∫⁻ y, α y ^ p * β (x - y) ^ r) volume :=
    AEMeasurable.lintegral_prod_right hprod
  have key : ∀ x, ∫⁻ y, α y * β (x - y) ∂volume
      ≤ (∫⁻ y, α y ^ p * β (x - y) ^ r ∂volume) ^ θ1 * A ^ θ2 * B ^ θ3 := by
    intro x
    have hβsh : Measurable (fun y => β (x - y)) :=
      hβ.comp (continuous_const.sub continuous_id).measurable
    have hf0 : AEMeasurable (fun y => α y ^ p * β (x - y) ^ r) volume :=
      (hα.pow_const p).mul (hβsh.pow_const r).aemeasurable
    have hf1 : AEMeasurable (fun y => α y ^ p) volume := hα.pow_const p
    have hf2 : AEMeasurable (fun y => β (x - y) ^ r) volume := (hβsh.pow_const r).aemeasurable
    have hh := lintegral_holder_three' hθ1 hθ2 hθ3 hsum hf0 hf1 hf2
    have hident : ∀ y, (α y ^ p * β (x - y) ^ r) ^ θ1
        * ((α y ^ p) ^ θ2 * (β (x - y) ^ r) ^ θ3) = α y * β (x - y) := by
      intro y
      rw [ENNReal.mul_rpow_of_nonneg _ _ hθ1]
      rw [show (α y ^ p) ^ θ1 = α y ^ (p * θ1) from (ENNReal.rpow_mul _ _ _).symm,
          show (α y ^ p) ^ θ2 = α y ^ (p * θ2) from (ENNReal.rpow_mul _ _ _).symm,
          show (β (x - y) ^ r) ^ θ1 = β (x - y) ^ (r * θ1) from (ENNReal.rpow_mul _ _ _).symm,
          show (β (x - y) ^ r) ^ θ3 = β (x - y) ^ (r * θ3) from (ENNReal.rpow_mul _ _ _).symm]
      rw [mul_mul_mul_comm,
          ← ennreal_rpow_add_of_nonneg' (by positivity : (0:ℝ) ≤ p * θ1) (by positivity : (0:ℝ) ≤ p * θ2),
          ← ennreal_rpow_add_of_nonneg' (by positivity : (0:ℝ) ≤ r * θ1) (by positivity : (0:ℝ) ≤ r * θ3)]
      rw [show p * θ1 + p * θ2 = p * (θ1 + θ2) from by ring, hpe,
          show r * θ1 + r * θ3 = r * (θ1 + θ3) from by ring, hre,
          ENNReal.rpow_one, ENNReal.rpow_one]
    rw [lintegral_congr (fun y => hident y)] at hh
    have hf1v : (∫⁻ y, α y ^ p ∂volume) = A := hA
    have hf2v : (∫⁻ y, β (x - y) ^ r ∂volume) = B := by
      rw [show (fun y => β (x - y) ^ r) = (fun y => (fun z => β z ^ r) (x - y)) from rfl,
          lintegral_sub_left_eq_self (fun z => β z ^ r) x]
    rw [hf1v, hf2v] at hh
    rw [mul_assoc]
    exact hh
  have hTon : ∫⁻ x, (∫⁻ y, α y ^ p * β (x - y) ^ r) ∂volume = A * B := by
    have hswap := lintegral_lintegral_swap (μ := volume) (ν := volume)
      (f := fun x y => α y ^ p * β (x - y) ^ r) hprod
    rw [hswap]
    have hinner : ∀ y, (∫⁻ x, α y ^ p * β (x - y) ^ r ∂volume) = α y ^ p * B := by
      intro y
      have hf : AEMeasurable (fun x => β (x - y) ^ r) volume :=
        ((hβ.comp (continuous_id.sub continuous_const).measurable).pow_const r).aemeasurable
      rw [lintegral_const_mul'' (α y ^ p) hf]
      congr 1
      rw [show (fun x => β (x - y) ^ r) = (fun x => (fun z => β z ^ r) (x - y)) from rfl,
          lintegral_sub_right_eq_self (fun z => β z ^ r) y]
    simp only [hinner]
    rw [lintegral_mul_const'' B (hα.pow_const p)]
  have step1 : ∫⁻ x, (∫⁻ y, α y * β (x - y)) ^ q
      ≤ ∫⁻ x, (∫⁻ y, α y ^ p * β (x - y) ^ r) * A ^ (q * θ2) * B ^ (q * θ3) := by
    apply lintegral_mono; intro x
    calc (∫⁻ y, α y * β (x - y)) ^ q
        ≤ ((∫⁻ y, α y ^ p * β (x - y) ^ r) ^ θ1 * A ^ θ2 * B ^ θ3) ^ q :=
          ENNReal.rpow_le_rpow (key x) hq_pos.le
      _ = (∫⁻ y, α y ^ p * β (x - y) ^ r) ^ (θ1 * q) * A ^ (θ2 * q) * B ^ (θ3 * q) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq_pos.le, ENNReal.mul_rpow_of_nonneg _ _ hq_pos.le]
          rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      _ = (∫⁻ y, α y ^ p * β (x - y) ^ r) * A ^ (q * θ2) * B ^ (q * θ3) := by
          rw [show θ1 * q = 1 from by rw [hθ1def]; field_simp,
              show θ2 * q = q * θ2 from by ring, show θ3 * q = q * θ3 from by ring,
              ENNReal.rpow_one]
  have hmain : ∫⁻ x, (∫⁻ y, α y * β (x - y)) ^ q ≤ A ^ (q / p) * B ^ (q / r) := by
    calc ∫⁻ x, (∫⁻ y, α y * β (x - y)) ^ q
        ≤ ∫⁻ x, (∫⁻ y, α y ^ p * β (x - y) ^ r) * A ^ (q * θ2) * B ^ (q * θ3) := step1
      _ = (∫⁻ x, (∫⁻ y, α y ^ p * β (x - y) ^ r)) * (A ^ (q * θ2) * B ^ (q * θ3)) := by
          rw [show (fun x => (∫⁻ y, α y ^ p * β (x - y) ^ r) * A ^ (q * θ2) * B ^ (q * θ3))
                = (fun x => (∫⁻ y, α y ^ p * β (x - y) ^ r) * (A ^ (q * θ2) * B ^ (q * θ3)))
                from by funext x; rw [mul_assoc]]
          rw [lintegral_mul_const'' _ hmeas]
      _ = (A * B) * (A ^ (q * θ2) * B ^ (q * θ3)) := by rw [hTon]
      _ = A ^ (q / p) * B ^ (q / r) := by
          rw [mul_mul_mul_comm]
          rw [show A * A ^ (q * θ2) = A ^ (1:ℝ) * A ^ (q * θ2) from by rw [ENNReal.rpow_one],
              show B * B ^ (q * θ3) = B ^ (1:ℝ) * B ^ (q * θ3) from by rw [ENNReal.rpow_one]]
          rw [(ennreal_rpow_add_of_nonneg' (show (0:ℝ) ≤ 1 by norm_num) (by positivity)).symm,
              (ennreal_rpow_add_of_nonneg' (show (0:ℝ) ≤ 1 by norm_num) (by positivity)).symm]
          rw [show 1 + q * θ2 = q / p from by rw [hθ2def]; field_simp; ring,
              show 1 + q * θ3 = q / r from by rw [hθ3def]; field_simp; ring]
  calc (∫⁻ x, (∫⁻ y, α y * β (x - y)) ^ q) ^ (1 / q)
      ≤ (A ^ (q / p) * B ^ (q / r)) ^ (1 / q) := ENNReal.rpow_le_rpow hmain (by positivity)
    _ = A ^ (1 / p) * B ^ (1 / r) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        rw [show (q / p) * (1 / q) = 1 / p from by field_simp,
            show (q / r) * (1 / q) = 1 / r from by field_simp]
    _ = (∫⁻ x, α x ^ p) ^ (1 / p) * (∫⁻ x, β x ^ r) ^ (1 / r) := by rw [hA, hB]


/-- **Young's inequality `L² ⋆ L¹ ⊆ L²`** for measurable `ℝ≥0∞`-valued functions on `ℝ`. -/
private theorem young_l2_l1 (a b : ℝ → ℝ≥0∞) (ha : AEMeasurable a volume)
    (hb : AEMeasurable b volume) :
    ∫⁻ x, (∫⁻ y, a y * b (x - y)) ^ (2:ℝ)
      ≤ (∫⁻ y, a y ^ (2:ℝ)) * (∫⁻ y, b y) ^ (2:ℝ) := by
  have h := lintegral_convolution_rpow_le_lin (p := 2) (q := 2) (r := 1)
    (by norm_num) (by norm_num) (by norm_num) ha hb.measurable_mk
  have hconv : ∀ x, (∫⁻ y, a y * (hb.mk b) (x - y)) = (∫⁻ y, a y * b (x - y)) := by
    intro x
    refine lintegral_congr_ae ?_
    filter_upwards [(Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae_eq_comp
      hb.ae_eq_mk] with y hy
    simp only [Function.comp_apply] at hy
    rw [← hy]
  have hL : (∫⁻ x, (∫⁻ y, a y * (hb.mk b) (x - y)) ^ (2:ℝ))
      = (∫⁻ x, (∫⁻ y, a y * b (x - y)) ^ (2:ℝ)) := by
    refine lintegral_congr (fun x => ?_); rw [hconv x]
  have hB : (∫⁻ y, (hb.mk b) y ^ (1:ℝ)) = (∫⁻ y, b y) := by
    rw [show (fun y => (hb.mk b) y ^ (1:ℝ)) = (fun y => (hb.mk b) y) from by
      funext y; rw [ENNReal.rpow_one]]
    exact (lintegral_congr_ae hb.ae_eq_mk).symm
  rw [hL, hB, show (1:ℝ)/1 = 1 by norm_num, ENNReal.rpow_one] at h
  have hsq := ENNReal.rpow_le_rpow h (show (0:ℝ) ≤ 2 by norm_num)
  rw [← ENNReal.rpow_mul, show (1/2:ℝ)*2 = 1 by norm_num, ENNReal.rpow_one] at hsq
  rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0:ℝ) ≤ 2 by norm_num),
      ← ENNReal.rpow_mul, show (1/2:ℝ)*2 = 1 by norm_num, ENNReal.rpow_one] at hsq
  exact hsq

/-- **`L²` convolution bound**: for `f ∈ L²(ℝ)`, `k ∈ L¹(ℝ)`, the convolution integral
`x ↦ ∫ y, f y · k (x-y)` is square integrable with
`∫⁻ ‖f ⋆ k‖² ≤ (∫⁻ ‖f‖²)(∫⁻ ‖k‖)²`. -/
private theorem convolution_enorm_sq_le (f k : ℝ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hk : MemLp k 1 (volume : Measure ℝ)) :
    ∫⁻ x, ‖∫ y, f y * k (x - y)‖ₑ ^ (2:ℝ)
      ≤ (∫⁻ y, ‖f y‖ₑ ^ (2:ℝ)) * (∫⁻ y, ‖k y‖ₑ) ^ (2:ℝ) := by
  have hpt : ∀ x, ‖∫ y, f y * k (x - y)‖ₑ ≤ ∫⁻ y, ‖f y‖ₑ * ‖k (x - y)‖ₑ := by
    intro x
    calc ‖∫ y, f y * k (x - y)‖ₑ ≤ ∫⁻ y, ‖f y * k (x - y)‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y, ‖f y‖ₑ * ‖k (x - y)‖ₑ := by
          refine lintegral_congr (fun y => ?_); rw [enorm_mul]
  calc ∫⁻ x, ‖∫ y, f y * k (x - y)‖ₑ ^ (2:ℝ)
      ≤ ∫⁻ x, (∫⁻ y, ‖f y‖ₑ * ‖k (x - y)‖ₑ) ^ (2:ℝ) := by
        refine lintegral_mono (fun x => ?_)
        exact ENNReal.rpow_le_rpow (hpt x) (by norm_num)
    _ ≤ (∫⁻ y, ‖f y‖ₑ ^ (2:ℝ)) * (∫⁻ y, ‖k y‖ₑ) ^ (2:ℝ) :=
        young_l2_l1 _ _ hf.aemeasurable.enorm hk.aemeasurable.enorm


/-! ## Linearity and continuity of the multiplier operator -/

private lemma fourier_sub_lp (f g : Lp ℂ 2 (volume : Measure ℝ)) : 𝓕 (f - g) = 𝓕 f - 𝓕 g := by
  change (Lp.fourierTransformₗᵢ ℝ ℂ) (f - g) = (Lp.fourierTransformₗᵢ ℝ ℂ) f - (Lp.fourierTransformₗᵢ ℝ ℂ) g
  exact map_sub _ _ _

private lemma fourierInv_sub_lp (f g : Lp ℂ 2 (volume : Measure ℝ)) : 𝓕⁻ (f - g) = 𝓕⁻ f - 𝓕⁻ g := by
  change ((Lp.fourierTransformₗᵢ ℝ ℂ)).symm (f - g)
    = (Lp.fourierTransformₗᵢ ℝ ℂ).symm f - (Lp.fourierTransformₗᵢ ℝ ℂ).symm g
  exact map_sub _ _ _

private lemma mulLp_sub_fst (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    BoundaryLayer.mulLp m hm (f - g)
      = BoundaryLayer.mulLp m hm f - BoundaryLayer.mulLp m hm g := by
  apply Lp.ext
  filter_upwards [BoundaryLayer.mulLp_coe m hm (f - g), BoundaryLayer.mulLp_coe m hm f,
    BoundaryLayer.mulLp_coe m hm g, Lp.coeFn_sub f g,
    Lp.coeFn_sub (BoundaryLayer.mulLp m hm f) (BoundaryLayer.mulLp m hm g)] with x h1 h2 h3 h4 h5
  simp only [Pi.mul_apply, Pi.sub_apply] at h1 h2 h3 h4 h5 ⊢
  rw [h5, h1, h2, h3, h4]
  ring

private lemma multiplier_sub_fst (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    BoundaryLayer.multiplier m hm (f - g)
      = BoundaryLayer.multiplier m hm f - BoundaryLayer.multiplier m hm g := by
  simp only [BoundaryLayer.multiplier]
  rw [fourier_sub_lp, mulLp_sub_fst]
  exact fourierInv_sub_lp _ _

private lemma enorm_sq_eq (z : ℂ) : ‖z‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [BoundaryLayer.enorm_eq_ofReal_norm,
      show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
      ENNReal.ofReal_pow (norm_nonneg z)]

private lemma ofReal_sq_rpow (B : ℝ) (hB : 0 ≤ B) :
    (ENNReal.ofReal B) ^ (2:ℝ) = ENNReal.ofReal (B ^ 2) := by
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hB]

/-- Operator-norm bound for the multiplier: if `‖m ξ‖ ≤ B` for all `ξ`, then
`‖multiplier m hm f‖ₑ ≤ ofReal B * ‖f‖ₑ`. -/
private lemma enorm_multiplier_le (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (B : ℝ) (hBnn : 0 ≤ B) (hB : ∀ ξ, ‖m ξ‖ ≤ B) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖BoundaryLayer.multiplier m hm f‖ₑ ≤ ENNReal.ofReal B * ‖f‖ₑ := by
  have hb : ∫⁻ ξ, ‖m ξ‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal (B ^ 2) * ‖f‖ₑ ^ (2:ℝ) := by
    calc ∫⁻ ξ, ‖m ξ‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ)
        ≤ ∫⁻ ξ, ENNReal.ofReal (B ^ 2) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
          refine lintegral_mono (fun ξ => mul_le_mul' ?_ le_rfl)
          rw [enorm_sq_eq]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hB ξ) 2)
      _ = ENNReal.ofReal (B ^ 2) * ∫⁻ ξ, ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (B ^ 2) * ‖𝓕 f‖ₑ ^ (2:ℝ) := by
          rw [← BoundaryLayer.lp_enorm_sq_eq_lintegral (𝓕 f)]
      _ = ENNReal.ofReal (B ^ 2) * ‖f‖ₑ ^ (2:ℝ) := by rw [BoundaryLayer.enorm_fourier]
  have hsq : ‖BoundaryLayer.multiplier m hm f‖ₑ ^ (2:ℝ)
      ≤ (ENNReal.ofReal B * ‖f‖ₑ) ^ (2:ℝ) := by
    rw [BoundaryLayer.enorm_multiplier_sq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ofReal_sq_rpow B hBnn]
    exact hb
  have h2 := ENNReal.rpow_le_rpow hsq (show (0:ℝ) ≤ 1/2 by norm_num)
  rwa [← ENNReal.rpow_mul, show (2:ℝ)*(1/2) = 1 by norm_num, ENNReal.rpow_one,
       ← ENNReal.rpow_mul, show (2:ℝ)*(1/2) = 1 by norm_num, ENNReal.rpow_one] at h2

private lemma enorm_toReal (x : Lp ℂ 2 (volume : Measure ℝ)) : (‖x‖ₑ).toReal = ‖x‖ := by
  rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]

/-- The multiplier operator is `B`-Lipschitz on `L²`. -/
private lemma norm_multiplier_sub_le (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (B : ℝ) (hBnn : 0 ≤ B) (hB : ∀ ξ, ‖m ξ‖ ≤ B) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖BoundaryLayer.multiplier m hm f - BoundaryLayer.multiplier m hm g‖ ≤ B * ‖f - g‖ := by
  have h := enorm_multiplier_le m hm B hBnn hB (f - g)
  rw [multiplier_sub_fst] at h
  have hfin : ENNReal.ofReal B * ‖f - g‖ₑ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by rw [← ofReal_norm]; exact ENNReal.ofReal_ne_top)
  have hle := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hBnn, enorm_toReal, enorm_toReal] at hle
  exact hle


/-! ## The bridge: the multiplier is the convolution with the kernel -/

open scoped Convolution

/-- **`L¹ ∩ L²` case of the multiplier/convolution identification.**  For `f ∈ L¹ ∩ L²` and
`k ∈ L¹`, the multiplier operator with symbol `𝓕 k` is a.e. the convolution with `k`. -/
private theorem multiplier_eq_convolution_memLp (k : ℝ → ℂ) (hk : Integrable k)
    (hm : MemLp (fun ξ => 𝓕 k ξ) ⊤ (volume : Measure ℝ))
    (f : ℝ → ℂ) (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    (fun x => ∫ y : ℝ, f y * k (x - y))
      =ᵐ[volume]
    (fun x => (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm (hf2.toLp f) : ℝ → ℂ) x) := by
  set convK : ℝ → ℂ := f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k with hconvdef
  have hconvpt : convK = fun x => ∫ y : ℝ, f y * k (x - y) := by
    funext x
    rw [hconvdef]
    exact MeasureTheory.convolution_mul
  have hconv1 : Integrable convK := by
    rw [hconvdef]
    exact (memLp_one_iff_integrable.mp hf1).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hk
  have hk1 : MemLp k 1 (volume : Measure ℝ) := memLp_one_iff_integrable.mpr hk
  have hconv2 : MemLp convK 2 (volume : Measure ℝ) := by
    refine memLp_two_of_lintegral_enorm_lt_top hconv1.aestronglyMeasurable ?_
    rw [hconvpt]
    refine lt_of_le_of_lt (convolution_enorm_sq_le f k hf2 hk1) ?_
    refine ENNReal.mul_lt_top (lintegral_enorm_sq_lt_top_of_memLp hf2) ?_
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
    exact ENNReal.pow_lt_top hk.hasFiniteIntegral
  have hkey : 𝓕 (hconv2.toLp convK) = BoundaryLayer.mulLp (fun ξ => 𝓕 k ξ) hm (𝓕 (hf2.toLp f)) := by
    apply Lp.ext
    filter_upwards [fourier_toLp_ae_eq_fourier_of_memLp (memLp_one_iff_integrable.mpr hconv1) hconv2,
      BoundaryLayer.mulLp_coe (fun ξ => 𝓕 k ξ) hm (𝓕 (hf2.toLp f)),
      fourier_toLp_ae_eq_fourier_of_memLp hf1 hf2] with ξ h1 h2 h3
    simp only [Pi.mul_apply] at h2 ⊢
    rw [h1, h2, h3, hconvdef]
    rw [Real.fourier_mul_convolution_eq (memLp_one_iff_integrable.mp hf1) hk]
    ring
  have hL : hconv2.toLp convK = BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm (hf2.toLp f) := by
    rw [show BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm (hf2.toLp f)
        = 𝓕⁻ (BoundaryLayer.mulLp (fun ξ => 𝓕 k ξ) hm (𝓕 (hf2.toLp f))) from rfl]
    rw [← hkey]
    exact (FourierPair.fourierInv_fourier_eq _).symm
  have hcoe2 : (hconv2.toLp convK : ℝ → ℂ)
      =ᵐ[volume] (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm (hf2.toLp f) : ℝ → ℂ) := by
    rw [hL]
  rw [← hconvpt]
  exact hconv2.coeFn_toLp.symm.trans hcoe2


/-! ## Dilated kernels and their Fourier transforms -/

/-- Fourier transform of a dilation of a kernel: `𝓕 (z ↦ c K(c z)) ξ = 𝓕 K (ξ / c)`. -/
private lemma fourier_dilation {K : ℝ → ℂ} {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    𝓕 (fun z : ℝ => (c : ℂ) * K (c * z)) ξ = (𝓕 K) (ξ / c) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  rw [Real.fourier_eq, Real.fourier_eq]
  simp_rw [Real.inner_apply]
  have h1 : (∫ z : ℝ, Real.fourierChar (-(z * ξ)) • ((c : ℂ) * K (c * z)))
      = (c : ℂ) * ∫ z : ℝ, Real.fourierChar (-(z * ξ)) • K (c * z) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [Circle.smul_def, smul_eq_mul]
    ring
  rw [h1]
  have h2 : (∫ z : ℝ, Real.fourierChar (-(z * ξ)) • K (c * z))
      = |c⁻¹| • ∫ u : ℝ, Real.fourierChar (-((u / c) * ξ)) • K u := by
    have hsub := MeasureTheory.Measure.integral_comp_mul_left
      (fun u : ℝ => Real.fourierChar (-((u / c) * ξ)) • K u) c
    have heq : (∫ z : ℝ, Real.fourierChar (-(z * ξ)) • K (c * z))
        = ∫ z : ℝ, (fun u : ℝ => Real.fourierChar (-((u / c) * ξ)) • K u) (c * z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only []
      rw [show -(z * ξ) = -((c * z / c) * ξ) by field_simp]
    rw [heq, hsub]
  rw [h2, abs_of_pos (inv_pos.mpr hc), Complex.real_smul, ← mul_assoc, Complex.ofReal_inv,
    mul_inv_cancel₀ (by exact_mod_cast hcne), one_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  rw [show -(u / c * ξ) = -(u * (ξ / c)) by ring]

/-! ## Almost-everywhere finiteness and a.e. linearity of convolution integrals -/

/-- For `f ∈ L²` and `k ∈ L¹`, the convolution weight `∫⁻ y, ‖f y‖ₑ ‖k (x-y)‖ₑ` is finite
for almost every `x`. -/
private lemma ae_lintegral_convolution_lt_top (f k : ℝ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hk : MemLp k 1 (volume : Measure ℝ)) :
    ∀ᵐ x ∂volume, ∫⁻ y, ‖f y‖ₑ * ‖k (x - y)‖ₑ < ⊤ := by
  have hF : AEMeasurable (fun x : ℝ => ∫⁻ y, ‖f y‖ₑ * ‖k (x - y)‖ₑ) volume := by
    have hfm : Measurable (hf.aemeasurable.mk f) := hf.aemeasurable.measurable_mk
    have hkm : Measurable (hk.aemeasurable.mk k) := hk.aemeasurable.measurable_mk
    have hjoint : AEMeasurable (fun p : ℝ × ℝ =>
        ‖(hf.aemeasurable.mk f) p.2‖ₑ * ‖(hk.aemeasurable.mk k) (p.1 - p.2)‖ₑ)
        (volume.prod volume) :=
      ((hfm.enorm.comp measurable_snd).aemeasurable).mul
        (((hkm.enorm).comp (continuous_fst.sub continuous_snd).measurable).aemeasurable)
    have hF' : AEMeasurable
        (fun x : ℝ => ∫⁻ y, ‖(hf.aemeasurable.mk f) y‖ₑ * ‖(hk.aemeasurable.mk k) (x - y)‖ₑ)
        volume := hjoint.lintegral_prod_right
    rw [show (fun x : ℝ => ∫⁻ y, ‖f y‖ₑ * ‖k (x - y)‖ₑ)
        = (fun x : ℝ => ∫⁻ y, ‖(hf.aemeasurable.mk f) y‖ₑ
            * ‖(hk.aemeasurable.mk k) (x - y)‖ₑ) from ?_]
    · exact hF'
    · funext x
      have hmp : MeasurePreserving (fun y : ℝ => x - y) volume volume := by
        simpa using Measure.measurePreserving_sub_left volume x
      refine lintegral_congr_ae ?_
      filter_upwards [hf.aemeasurable.ae_eq_mk,
        hmp.quasiMeasurePreserving.ae_eq_comp hk.aemeasurable.ae_eq_mk] with y h1 h2
      simp only [Function.comp_apply] at h2
      rw [h1, h2]
  have hfin : ∫⁻ x : ℝ, (∫⁻ y, ‖f y‖ₑ * ‖k (x - y)‖ₑ) ^ (2:ℝ) < ⊤ :=
    lt_of_le_of_lt
      (young_l2_l1 (fun y => ‖f y‖ₑ) (fun y => ‖k y‖ₑ) hf.aemeasurable.enorm hk.aemeasurable.enorm)
      (by
        refine ENNReal.mul_lt_top (lintegral_enorm_sq_lt_top_of_memLp hf) ?_
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
        exact ENNReal.pow_lt_top (memLp_one_iff_integrable.mp hk).hasFiniteIntegral)
  filter_upwards [ae_lt_top' (hF.pow_const (2:ℝ)) (ne_of_lt hfin)] with x hx
  rwa [ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < 2)] at hx

/-- For `f ∈ L²`, `k ∈ L¹` and a.e. `x`, the convolution integrand `y ↦ f y * k (x-y)` is
integrable. -/
private lemma integrable_convolution_integrand_ae (f k : ℝ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hk : MemLp k 1 (volume : Measure ℝ)) :
    ∀ᵐ x ∂volume, Integrable (fun y : ℝ => f y * k (x - y)) volume := by
  filter_upwards [ae_lintegral_convolution_lt_top f k hf hk] with x hx
  have hmp : MeasurePreserving (fun y : ℝ => x - y) volume volume := by
    simpa using Measure.measurePreserving_sub_left volume x
  have hkshift : AEMeasurable (fun y : ℝ => k (x - y)) volume :=
    hk.aemeasurable.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
  refine ⟨(hf.aemeasurable.mul hkshift).aestronglyMeasurable, ?_⟩
  change ∫⁻ y, ‖f y * k (x - y)‖ₑ < ⊤
  rw [lintegral_congr (fun y => enorm_mul _ _)]
  exact hx

/-- **A.e. linearity of the convolution integral**: if `f, g ∈ L²` and `k ∈ L¹`, then for a.e. `x`,
`(f ⋆ k)(x) - (g ⋆ k)(x) = ((f - g) ⋆ k)(x)`. -/
private lemma convolution_sub_ae (f g k : ℝ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hg : MemLp g 2 (volume : Measure ℝ))
    (hk : MemLp k 1 (volume : Measure ℝ)) :
    (fun x => (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x
        - (g ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x)
      =ᵐ[volume] (fun x => ((f - g) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x) := by
  filter_upwards [integrable_convolution_integrand_ae f k hf hk,
    integrable_convolution_integrand_ae g k hg hk,
    integrable_convolution_integrand_ae (f - g) k (hf.sub hg) hk] with x hif hig hifg
  rw [MeasureTheory.convolution_mul, MeasureTheory.convolution_mul, MeasureTheory.convolution_mul,
      ← MeasureTheory.integral_sub hif hig]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.sub_apply]
  ring

/-- **`L²` bound for the difference of convolutions.**  For `f, g ∈ L²` and `k ∈ L¹`,
`∫⁻ ‖f ⋆ k - g ⋆ k‖² ≤ (∫⁻ ‖f - g‖²)(∫⁻ ‖k‖)²`. -/
private lemma convolution_sub_lintegral_le (f g k : ℝ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hg : MemLp g 2 (volume : Measure ℝ))
    (hk : MemLp k 1 (volume : Measure ℝ)) :
    ∫⁻ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x
        - (g ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ)
      ≤ (∫⁻ y, ‖f y - g y‖ₑ ^ (2:ℝ)) * (∫⁻ y, ‖k y‖ₑ) ^ (2:ℝ) := by
  calc ∫⁻ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x
        - (g ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ)
      = ∫⁻ x, ‖((f - g) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ) := by
        refine lintegral_congr_ae ?_
        filter_upwards [convolution_sub_ae f g k hf hg hk] with x hx
        exact congrArg (fun t => ‖t‖ₑ ^ (2:ℝ)) hx
    _ ≤ ∫⁻ x, (∫⁻ y, ‖f y - g y‖ₑ * ‖k (x - y)‖ₑ) ^ (2:ℝ) := by
        refine lintegral_mono (fun x => ?_)
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [MeasureTheory.convolution_mul]
        calc ‖∫ y, (f - g) y * k (x - y)‖ₑ ≤ ∫⁻ y, ‖(f - g) y * k (x - y)‖ₑ :=
              enorm_integral_le_lintegral_enorm _
          _ = ∫⁻ y, ‖(f - g) y‖ₑ * ‖k (x - y)‖ₑ :=
              lintegral_congr (fun y => enorm_mul _ _)
    _ ≤ (∫⁻ y, ‖f y - g y‖ₑ ^ (2:ℝ)) * (∫⁻ y, ‖k y‖ₑ) ^ (2:ℝ) :=
        young_l2_l1 _ _ (hf.sub hg).aemeasurable.enorm hk.aemeasurable.enorm

private lemma add_sq_le_four (u v : ℝ≥0∞) :
    (u + v) ^ (2:ℝ) ≤ 4 * (u ^ (2:ℝ) + v ^ (2:ℝ)) := by
  have h1 : u + v ≤ 2 * max u v := by
    calc u + v ≤ max u v + max u v := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * max u v := by ring
  have h2 : (max u v) ^ (2:ℝ) ≤ u ^ (2:ℝ) + v ^ (2:ℝ) := by
    rcases max_cases u v with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact le_add_right le_rfl
    · rw [h]; exact le_add_left le_rfl
  calc (u + v) ^ (2:ℝ) ≤ (2 * max u v) ^ (2:ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = 4 * (max u v) ^ (2:ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
    _ ≤ 4 * (u ^ (2:ℝ) + v ^ (2:ℝ)) := by gcongr

/-- `L²`-norm bound for the multiplier with bounded symbol (squared form). -/
private lemma enorm_multiplier_sq_le (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (B : ℝ) (hBnn : 0 ≤ B) (hB : ∀ ξ, ‖m ξ‖ ≤ B) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖BoundaryLayer.multiplier m hm f‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal (B ^ 2) * ‖f‖ₑ ^ (2:ℝ) := by
  rw [BoundaryLayer.enorm_multiplier_sq]
  calc ∫⁻ ξ, ‖m ξ‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ)
      ≤ ∫⁻ ξ, ENNReal.ofReal (B ^ 2) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
        refine lintegral_mono (fun ξ => mul_le_mul' ?_ le_rfl)
        rw [enorm_sq_eq]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hB ξ) 2)
    _ = ENNReal.ofReal (B ^ 2) * ∫⁻ ξ, ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (B ^ 2) * ‖f‖ₑ ^ (2:ℝ) := by
        rw [← BoundaryLayer.lp_enorm_sq_eq_lintegral (𝓕 f), BoundaryLayer.enorm_fourier]

/-- The convolution integral `x ↦ ∫ y, f y * k (x - y)` is a.e. strongly measurable. -/
private lemma bfun_aeStronglyMeasurable (f k : ℝ → ℂ) (hk : Integrable k)
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    AEStronglyMeasurable (fun x : ℝ => ∫ y, f y * k (x - y)) volume := by
  have hfm : Measurable (hf.aemeasurable.mk f) := hf.aemeasurable.measurable_mk
  have hkm : Measurable (hk.aemeasurable.mk k) := hk.aemeasurable.measurable_mk
  have hjoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (hf.aemeasurable.mk f) p.2 * (hk.aemeasurable.mk k) (p.1 - p.2))
      (volume.prod volume) :=
    ((hfm.comp measurable_snd).mul
      (hkm.comp (continuous_fst.sub continuous_snd).measurable)).aestronglyMeasurable
  have hres : AEStronglyMeasurable
      (fun x : ℝ => ∫ y, (hf.aemeasurable.mk f) y * (hk.aemeasurable.mk k) (x - y)) volume :=
    hjoint.integral_prod_right'
  rw [show (fun x : ℝ => ∫ y, f y * k (x - y))
      = (fun x : ℝ => ∫ y, (hf.aemeasurable.mk f) y * (hk.aemeasurable.mk k) (x - y)) from ?_]
  exact hres
  funext x
  have hmp : MeasurePreserving (fun y : ℝ => x - y) volume volume := by
    simpa using Measure.measurePreserving_sub_left volume x
  refine integral_congr_ae ?_
  filter_upwards [hf.aemeasurable.ae_eq_mk,
    hmp.quasiMeasurePreserving.ae_eq_comp hk.aemeasurable.ae_eq_mk] with y h1 h2
  simp only [Function.comp_apply] at h2
  rw [h1, h2]

/-- **General bridge: the multiplier with symbol `𝓕 k` is a.e. the convolution with `k`.** -/
private theorem multiplier_eq_convolution_ae (k : ℝ → ℂ) (hk : Integrable k)
    (hm : MemLp (fun ξ => 𝓕 k ξ) ⊤ (volume : Measure ℝ))
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (fun x => ∫ y : ℝ, (f : ℝ → ℂ) y * k (x - y))
      =ᵐ[volume]
    (fun x => (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x) := by
  set Bc : ℝ := ∫ x : ℝ, ‖k x‖ with hBcdef
  have hBnn : 0 ≤ Bc := integral_nonneg (fun x => norm_nonneg _)
  have hBbound : ∀ ξ : ℝ, ‖𝓕 k ξ‖ ≤ Bc := fun ξ => by
    rw [hBcdef]; exact norm_fourier_le k ξ
  have hk1 : MemLp k 1 (volume : Measure ℝ) := memLp_one_iff_integrable.mpr hk
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  choose ψ hψ using fun n : ℕ =>
    (Metric.denseRange_iff.mp hdense f (1 / ((n:ℝ) + 1)) (by positivity))
  have hψ' : ∀ n : ℕ, dist f ((ψ n).toLp 2 (volume : Measure ℝ)) < 1 / ((n:ℝ) + 1) := by
    intro n; simpa using hψ n
  have htend : Tendsto (fun n : ℕ => ((ψ n).toLp 2 (volume : Measure ℝ) : Lp ℂ 2 (volume : Measure ℝ)))
      atTop (𝓝 f) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_comm]; exact le_of_lt (hψ' n)
  have hbridge : ∀ n : ℕ, ((ψ n : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k)
      =ᵐ[volume] (fun x => (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm
        ((ψ n).toLp 2 (volume : Measure ℝ)) : ℝ → ℂ) x) := by
    intro n
    have h := multiplier_eq_convolution_memLp k hk hm (ψ n : ℝ → ℂ)
      ((ψ n).memLp 1 volume) ((ψ n).memLp 2 volume)
    rw [show (fun x : ℝ => ∫ y : ℝ, (ψ n : ℝ → ℂ) y * k (x - y))
        = ((ψ n : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) from by
      funext x; rw [MeasureTheory.convolution_mul]] at h
    exact h
  let D : ℕ → Lp ℂ 2 (volume : Measure ℝ) :=
    fun n => ((ψ n).toLp 2 (volume : Measure ℝ) : Lp ℂ 2 (volume : Measure ℝ)) - f
  have hDtend : Tendsto D atTop (𝓝 0) := by
    have := htend.sub_const f
    simpa only [D, sub_self] using this
  have hDnorm : Tendsto (fun n : ℕ => ‖D n‖ₑ ^ (2:ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ‖D n‖ ^ 2) atTop (𝓝 0) := by
      have h := (hDtend.norm).pow 2
      simpa using h
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (‖D n‖ ^ 2)) atTop (𝓝 0) := by
      have hc := (ENNReal.continuous_ofReal.tendsto 0).comp h1
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using hc
    have heq : ∀ n : ℕ, ENNReal.ofReal (‖D n‖ ^ 2) = ‖D n‖ₑ ^ (2:ℝ) := by
      intro n
      rw [← ofReal_norm, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
          ENNReal.ofReal_pow (norm_nonneg _)]
    have hgoal : (fun n : ℕ => ENNReal.ofReal (‖D n‖ ^ 2)) = (fun n : ℕ => ‖D n‖ₑ ^ (2:ℝ)) := by
      funext n; exact heq n
    rw [hgoal] at h2; exact h2
  have hDint : Tendsto (fun n : ℕ => ∫⁻ y : ℝ,
      ‖(ψ n : ℝ → ℂ) y - (f : ℝ → ℂ) y‖ₑ ^ (2:ℝ)) atTop (𝓝 0) := by
    have heq : ∀ n : ℕ, (∫⁻ y : ℝ, ‖(ψ n : ℝ → ℂ) y - (f : ℝ → ℂ) y‖ₑ ^ (2:ℝ))
        = ‖D n‖ₑ ^ (2:ℝ) := by
      intro n
      rw [BoundaryLayer.lp_enorm_sq_eq_lintegral (D n)]
      refine lintegral_congr_ae ?_
      have hcoe : (D n : ℝ → ℂ) =ᵐ[volume]
          (fun y => (ψ n : ℝ → ℂ) y - (f : ℝ → ℂ) y) := by
        filter_upwards [Lp.coeFn_sub ((ψ n).toLp 2 (volume : Measure ℝ)) f,
          (ψ n).coeFn_toLp 2 (volume : Measure ℝ)] with y h1 h2
        simp only [D]
        simp only [Pi.sub_apply] at h1 ⊢
        rw [h1, h2]
      filter_upwards [hcoe] with y hy
      rw [hy]
    simpa only [heq] using hDnorm
  -- the pointwise bound, for each `n`
  have hbound : ∀ n : ℕ, ∫⁻ x, ‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
        - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ)
      ≤ 4 * (ENNReal.ofReal (Bc ^ 2) * ‖D n‖ₑ ^ (2:ℝ)
          + (∫⁻ y, ‖(ψ n : ℝ → ℂ) y - (f : ℝ → ℂ) y‖ₑ ^ (2:ℝ)) * (∫⁻ y, ‖k y‖ₑ) ^ (2:ℝ)) := by
    intro n
    have hAmeas : AEMeasurable (fun x : ℝ =>
        ‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
          - (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm ((ψ n).toLp 2 (volume : Measure ℝ))
              : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) volume := by
      refine (AEMeasurable.congr (f := fun x : ℝ => ‖(((BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f
            - BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm ((ψ n).toLp 2 (volume : Measure ℝ))
            ) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) ?_ ?_)
      · exact (Lp.aestronglyMeasurable _).aemeasurable.enorm.pow_const (2:ℝ)
      · filter_upwards [Lp.coeFn_sub (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f)
          (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm ((ψ n).toLp 2 (volume : Measure ℝ)))] with x hx
        simp only [Pi.sub_apply] at hx ⊢
        rw [hx]
    have hpt : (fun x : ℝ => ‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
          - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ))
        ≤ᵐ[volume]
        (fun x : ℝ => 4 * (‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
              - (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm ((ψ n).toLp 2 (volume : Measure ℝ))
                  : ℝ → ℂ) x‖ₑ ^ (2:ℝ)
            + ‖(((ψ n : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x
              - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ))) := by
      filter_upwards [hbridge n] with x hx
      calc ‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
            - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ)
          = ‖((BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
              - (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm ((ψ n).toLp 2 (volume : Measure ℝ))
                  : ℝ → ℂ) x)
            + ((((ψ n : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x
              - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x)‖ₑ ^ (2:ℝ) := by
              rw [← hx]; ring_nf
        _ ≤ (‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
              - (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm ((ψ n).toLp 2 (volume : Measure ℝ))
                  : ℝ → ℂ) x‖ₑ
            + ‖(((ψ n : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x
              - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ) ^ (2:ℝ) :=
              ENNReal.rpow_le_rpow (enorm_add_le _ _) (by norm_num)
        _ ≤ 4 * (‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
              - (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm ((ψ n).toLp 2 (volume : Measure ℝ))
                  : ℝ → ℂ) x‖ₑ ^ (2:ℝ)
            + ‖(((ψ n : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x
              - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ)) :=
              add_sq_le_four _ _
    have hAbound : (∫⁻ x, ‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
          - (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm ((ψ n).toLp 2 (volume : Measure ℝ))
              : ℝ → ℂ) x‖ₑ ^ (2:ℝ))
        ≤ ENNReal.ofReal (Bc ^ 2) * ‖D n‖ₑ ^ (2:ℝ) := by
      have hE : (∫⁻ x, ‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
          - (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm ((ψ n).toLp 2 (volume : Measure ℝ))
              : ℝ → ℂ) x‖ₑ ^ (2:ℝ))
          = ‖BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f
              - BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm ((ψ n).toLp 2 (volume : Measure ℝ))‖ₑ ^ (2:ℝ) := by
        rw [BoundaryLayer.lp_enorm_sq_eq_lintegral (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f
          - BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm ((ψ n).toLp 2 (volume : Measure ℝ)))]
        refine lintegral_congr_ae ?_
        filter_upwards [Lp.coeFn_sub (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f)
          (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm ((ψ n).toLp 2 (volume : Measure ℝ)))] with x hx
        simp only [Pi.sub_apply] at hx
        rw [hx]
      rw [hE, ← multiplier_sub_fst]
      refine (enorm_multiplier_sq_le (fun ξ => 𝓕 k ξ) hm Bc hBnn hBbound
        (f - (ψ n).toLp 2 (volume : Measure ℝ))).trans ?_
      have hneg : f - (ψ n).toLp 2 (volume : Measure ℝ) = -(D n) := by
        rw [show D n = ((ψ n).toLp 2 (volume : Measure ℝ)) - f from rfl, neg_sub]
      rw [hneg, enorm_neg]
    have hBbound' : (∫⁻ x, ‖(((ψ n : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x
          - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ))
        ≤ (∫⁻ y, ‖(ψ n : ℝ → ℂ) y - (f : ℝ → ℂ) y‖ₑ ^ (2:ℝ)) * (∫⁻ y, ‖k y‖ₑ) ^ (2:ℝ) :=
      convolution_sub_lintegral_le (ψ n : ℝ → ℂ) (f : ℝ → ℂ) k
        ((ψ n).memLp 2 (volume : Measure ℝ)) (Lp.memLp f) hk1
    calc ∫⁻ x, ‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
          - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ)
        ≤ ∫⁻ x, 4 * (‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
              - (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm ((ψ n).toLp 2 (volume : Measure ℝ))
                  : ℝ → ℂ) x‖ₑ ^ (2:ℝ)
            + ‖(((ψ n : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x
              - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ)) :=
          lintegral_mono_ae hpt
      _ = 4 * ((∫⁻ x, ‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
              - (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm ((ψ n).toLp 2 (volume : Measure ℝ))
                  : ℝ → ℂ) x‖ₑ ^ (2:ℝ))
            + (∫⁻ x, ‖(((ψ n : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x
              - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ))) := by
          rw [lintegral_const_mul' 4 _ (by norm_num),
              lintegral_add_left' hAmeas]
      _ ≤ 4 * (ENNReal.ofReal (Bc ^ 2) * ‖D n‖ₑ ^ (2:ℝ)
          + (∫⁻ y, ‖(ψ n : ℝ → ℂ) y - (f : ℝ → ℂ) y‖ₑ ^ (2:ℝ)) * (∫⁻ y, ‖k y‖ₑ) ^ (2:ℝ)) := by
          refine mul_le_mul' le_rfl (add_le_add hAbound hBbound')
  have hsum : Tendsto (fun n : ℕ => 4 * (ENNReal.ofReal (Bc ^ 2) * ‖D n‖ₑ ^ (2:ℝ)
      + (∫⁻ y, ‖(ψ n : ℝ → ℂ) y - (f : ℝ → ℂ) y‖ₑ ^ (2:ℝ)) * (∫⁻ y, ‖k y‖ₑ) ^ (2:ℝ)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (Bc ^ 2) * ‖D n‖ₑ ^ (2:ℝ)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Bc ^ 2)) hDnorm
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using this
    have h2 : Tendsto (fun n : ℕ => (∫⁻ y, ‖(ψ n : ℝ → ℂ) y - (f : ℝ → ℂ) y‖ₑ ^ (2:ℝ))
        * (∫⁻ y, ‖k y‖ₑ) ^ (2:ℝ)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const (b := (∫⁻ y, ‖k y‖ₑ) ^ (2:ℝ)) hDint
        (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          (ne_of_lt (memLp_one_iff_integrable.mp hk1).hasFiniteIntegral)))
      simpa using this
    have h3 := (h1.add h2)
    have := ENNReal.Tendsto.const_mul (a := (4:ℝ≥0∞)) h3 (Or.inr (by norm_num))
    simpa using this
  have hkey : ∫⁻ x, ‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
      - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ) = 0 :=
    le_antisymm (ge_of_tendsto hsum (Filter.Eventually.of_forall hbound)) bot_le
  have hmeas : AEMeasurable (fun x : ℝ => ‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
      - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ)) volume :=
    (AEMeasurable.enorm (AEMeasurable.sub ((Lp.aestronglyMeasurable (BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f)).aemeasurable)
      (AEStronglyMeasurable.aemeasurable (bfun_aeStronglyMeasurable (f : ℝ → ℂ) k hk (Lp.memLp f)))
      )).pow_const (2:ℝ)
  have hae : (fun x : ℝ => ‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
      - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ)) =ᵐ[volume] 0 :=
    (lintegral_eq_zero_iff' hmeas).mp hkey
  rw [show (fun x : ℝ => ∫ y : ℝ, (f : ℝ → ℂ) y * k (x - y))
      = ((f : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) from by
    funext x; rw [MeasureTheory.convolution_mul]]
  filter_upwards [hae] with x hx
  have hx1 : ‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
      - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ ^ (2:ℝ) = 0 := by
    simpa only [Pi.zero_apply] using hx
  have hx2 : ‖(BoundaryLayer.multiplier (fun ξ => 𝓕 k ξ) hm f : ℝ → ℂ) x
      - (((f : ℝ → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) x‖ₑ = 0 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast] at hx1
    exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hx1
  rw [enorm_eq_zero, sub_eq_zero] at hx2
  exact hx2.symm


/-- **Uniform summability of the squared dyadic dilates of `𝓕 K`.** -/
private lemma norm_exp_ofReal_mul_I_sub_one_le (t : ℝ) :
    ‖Complex.exp (↑t * Complex.I) - 1‖ ≤ 2 * |t| := by
  by_cases h : |t| ≤ 1
  · have hx : ‖(↑t : ℂ) * Complex.I‖ ≤ 1 := by
      rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact h
    have := Complex.norm_exp_sub_one_le hx
    rwa [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
  · have h1 : ‖Complex.exp (↑t * Complex.I) - 1‖ ≤ 2 := by
      calc ‖Complex.exp (↑t * Complex.I) - 1‖ ≤ ‖Complex.exp (↑t * Complex.I)‖ + ‖(1:ℂ)‖ :=
            norm_sub_le _ _
        _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
    linarith [not_le.mp h]

private theorem fourier_lin_bound (K : ℝ → ℂ) (hK1 : Integrable K (volume : Measure ℝ))
    (hKx : Integrable (fun x : ℝ => x • K x) (volume : Measure ℝ))
    (hK0 : (∫ x : ℝ, K x) = 0) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ η : ℝ, ‖𝓕 K η‖ ≤ C₁ * |η| := by
  set D : ℝ := ∫ x : ℝ, ‖x • K x‖ with hDdef
  have hDnn : 0 ≤ D := integral_nonneg (fun x => norm_nonneg _)
  refine ⟨4 * Real.pi * D + 1, by positivity, fun η => ?_⟩
  suffices h : ‖𝓕 K η‖ ≤ 4 * Real.pi * D * |η| by
    have hη : 0 ≤ |η| := abs_nonneg η
    nlinarith [h, hDnn, Real.pi_pos, hη]
  have h0 : 𝓕 K 0 = 0 := by
    rw [Real.fourier_eq']
    simp only [Real.inner_apply, mul_zero, neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      one_smul]
    exact hK0
  have ht : ∀ v : ℝ, ‖Complex.exp (↑(-2 * Real.pi * inner ℝ v η) * Complex.I) - 1‖
      ≤ 4 * Real.pi * |η| * |v| := by
    intro v
    simp only [Real.inner_apply]
    have h1 := norm_exp_ofReal_mul_I_sub_one_le (-2 * Real.pi * (v * η))
    have h2 : |(-2 * Real.pi * (v * η))| = 2 * Real.pi * |v| * |η| := by
      rw [show (-2 * Real.pi * (v * η)) = (-(2 * Real.pi)) * (v * η) by ring, abs_mul, abs_neg,
          abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi), abs_mul]
      ring
    rw [h2] at h1
    have h3 : 2 * (2 * Real.pi * |v| * |η|) = 4 * Real.pi * |η| * |v| := by ring
    linarith [h1, h3]
  have hintSmul : Integrable (fun v : ℝ =>
      Complex.exp (↑(-2 * Real.pi * inner ℝ v η) * Complex.I) • K v) := by
    refine (hK1.norm).mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact (show Continuous (fun v : ℝ =>
          Complex.exp (↑(-2 * Real.pi * inner ℝ v η) * Complex.I)) by fun_prop).aestronglyMeasurable.smul
        hK1.aestronglyMeasurable
    · rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hsub : 𝓕 K η - 𝓕 K 0
      = ∫ v : ℝ, (Complex.exp (↑(-2 * Real.pi * inner ℝ v η) * Complex.I) - 1) • K v := by
    rw [Real.fourier_eq', Real.fourier_eq']
    have hzero : (∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * inner ℝ v 0) * Complex.I) • K v) = 0 := by
      simp only [Real.inner_apply, mul_zero, neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
        one_smul]
      exact hK0
    rw [hzero, sub_zero]
    rw [show (∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * inner ℝ v η) * Complex.I) • K v)
        = (∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * inner ℝ v η) * Complex.I) • K v)
          - (∫ v : ℝ, K v) from by rw [hK0, sub_zero]]
    rw [← integral_sub hintSmul hK1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only []
    rw [sub_smul, one_smul]
  have hdiff := hsub
  rw [h0, sub_zero] at hdiff
  calc ‖𝓕 K η‖
      = ‖∫ v : ℝ, (Complex.exp (↑(-2 * Real.pi * inner ℝ v η) * Complex.I) - 1) • K v‖ := by
        rw [hdiff]
    _ ≤ ∫ v : ℝ, ‖(Complex.exp (↑(-2 * Real.pi * inner ℝ v η) * Complex.I) - 1) • K v‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ v : ℝ, ‖Complex.exp (↑(-2 * Real.pi * inner ℝ v η) * Complex.I) - 1‖ * ‖K v‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        simp only []
        rw [norm_smul]
    _ ≤ ∫ v : ℝ, (4 * Real.pi * |η|) * ‖v • K v‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => by positivity) ?_ ?_
        · exact (hKx.norm).const_mul _
        · refine Filter.Eventually.of_forall fun v => ?_
          have hsm : ‖v • K v‖ = |v| * ‖K v‖ := by rw [norm_smul, Real.norm_eq_abs]
          calc ‖Complex.exp (↑(-2 * Real.pi * inner ℝ v η) * Complex.I) - 1‖ * ‖K v‖
              ≤ (4 * Real.pi * |η| * |v|) * ‖K v‖ :=
                mul_le_mul_of_nonneg_right (ht v) (norm_nonneg _)
            _ = (4 * Real.pi * |η|) * ‖v • K v‖ := by rw [hsm]; ring
    _ = 4 * Real.pi * D * |η| := by
        rw [hDdef, integral_const_mul]; ring

private lemma range_zpow_le_geom (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i ≤ (1 - r)⁻¹ := by
  rw [← tsum_geometric_of_lt_one hr0 hr1]
  exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _
    (fun i _ => pow_nonneg hr0 i)

private lemma finset_zpow_lower_le (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (L : ℤ) (t : Finset ℤ)
    (h : ∀ l ∈ t, L ≤ l) : ∑ l ∈ t, r ^ l ≤ r ^ L * (1 - r)⁻¹ := by
  have hinj : Set.InjOn (fun l : ℤ => (l - L).toNat) ↑t := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    simp only [] at hab
    have h1 : ((a - L).toNat : ℤ) = a - L := Int.toNat_of_nonneg (by have := h a ha; omega)
    have h2 : ((b - L).toNat : ℤ) = b - L := Int.toNat_of_nonneg (by have := h b hb; omega)
    have hab' : ((a - L).toNat : ℤ) = ((b - L).toNat : ℤ) := by exact_mod_cast hab
    rw [h1, h2] at hab'
    omega
  have hterm : ∀ l ∈ t, r ^ l = r ^ L * r ^ ((l - L).toNat) := by
    intro l hl
    have hl' : L ≤ l := h l hl
    have h1 : r ^ l = r ^ L * r ^ (l - L) := by
      rw [← zpow_add₀ (ne_of_gt hr0)]; congr 1; ring
    have h2 : r ^ (l - L) = r ^ ((l - L).toNat) := by
      rw [← zpow_natCast]
      congr 1
      exact (Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ l - L)).symm
    rw [h1, h2]
  have hsplit : ∑ l ∈ t, r ^ l = r ^ L * ∑ l ∈ t, r ^ ((l - L).toNat) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  rw [hsplit, ← Finset.sum_image hinj]
  refine mul_le_mul_of_nonneg_left ?_ (zpow_nonneg hr0.le L)
  set t' : Finset ℕ := t.image (fun l : ℤ => (l - L).toNat)
  have hsub : t' ⊆ Finset.range (t'.sup id + 1) := by
    intro m hm
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => pow_nonneg hr0.le i))
    (range_zpow_le_geom r hr0.le hr1 _)

private lemma finset_zpow_upper_le (r : ℝ) (hr1 : 1 < r) (L : ℤ) (t : Finset ℤ)
    (h : ∀ l ∈ t, l < L) : ∑ l ∈ t, r ^ l ≤ r ^ (L - 1) * (1 - r⁻¹)⁻¹ := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  have hr'0 : 0 < r⁻¹ := inv_pos.mpr hr0
  have hr'1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
  have hinj : Set.InjOn (fun l : ℤ => (L - 1 - l).toNat) ↑t := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    simp only [] at hab
    have h1 : ((L - 1 - a).toNat : ℤ) = L - 1 - a := Int.toNat_of_nonneg (by have := h a ha; omega)
    have h2 : ((L - 1 - b).toNat : ℤ) = L - 1 - b := Int.toNat_of_nonneg (by have := h b hb; omega)
    have hab' : ((L - 1 - a).toNat : ℤ) = ((L - 1 - b).toNat : ℤ) := by exact_mod_cast hab
    rw [h1, h2] at hab'
    omega
  have hterm : ∀ l ∈ t, r ^ l = r ^ (L - 1) * (r⁻¹) ^ ((L - 1 - l).toNat) := by
    intro l hl
    have hl' : l < L := h l hl
    have h1 : r ^ l = r ^ (L - 1) * r ^ (l - (L - 1)) := by
      rw [← zpow_add₀ (ne_of_gt hr0)]; congr 1; ring
    have h2 : r ^ (l - (L - 1)) = (r⁻¹) ^ ((L - 1 - l).toNat) := by
      rw [show l - (L - 1) = -((L - 1) - l) by ring, zpow_neg, ← inv_zpow, ← zpow_natCast]
      congr 1
      exact (Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ L - 1 - l)).symm
    rw [h1, h2]
  have hsplit : ∑ l ∈ t, r ^ l = r ^ (L - 1) * ∑ l ∈ t, (r⁻¹) ^ ((L - 1 - l).toNat) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  rw [hsplit, ← Finset.sum_image hinj]
  refine mul_le_mul_of_nonneg_left ?_ (zpow_nonneg hr0.le (L - 1))
  set t' : Finset ℕ := t.image (fun l : ℤ => (L - 1 - l).toNat)
  have hsub : t' ⊆ Finset.range (t'.sup id + 1) := by
    intro m hm
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => pow_nonneg hr'0.le i))
    (range_zpow_le_geom r⁻¹ hr'0.le hr'1 _)

private lemma finset_zpow_rev_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (L : ℤ) (t : Finset ℤ)
    (h : ∀ l ∈ t, l < L) : ∑ l ∈ t, r ^ ((L - 1 - l).toNat) ≤ (1 - r)⁻¹ := by
  have hinj : Set.InjOn (fun l : ℤ => (L - 1 - l).toNat) ↑t := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    simp only [] at hab
    have h1 : ((L - 1 - a).toNat : ℤ) = L - 1 - a := Int.toNat_of_nonneg (by have := h a ha; omega)
    have h2 : ((L - 1 - b).toNat : ℤ) = L - 1 - b := Int.toNat_of_nonneg (by have := h b hb; omega)
    have hab' : ((L - 1 - a).toNat : ℤ) = ((L - 1 - b).toNat : ℤ) := by exact_mod_cast hab
    rw [h1, h2] at hab'
    omega
  rw [← Finset.sum_image hinj]
  set t' : Finset ℕ := t.image (fun l : ℤ => (L - 1 - l).toNat)
  have hsub : t' ⊆ Finset.range (t'.sup id + 1) := by
    intro m hm
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => pow_nonneg hr0 i))
    (range_zpow_le_geom r hr0 hr1 _)

private lemma dyadic_finite_sum_bound (K : ℝ → ℂ) (C₁ C N : ℝ) (hC₁ : 0 ≤ C₁)
    (hlin : ∀ η : ℝ, ‖𝓕 K η‖ ≤ C₁ * |η|)
    (hC : 0 < C) (hN : 0 < N) (hdec' : ∀ ξ : ℝ, ‖𝓕 K ξ‖ ≤ C * (1 + |ξ|) ^ (-N)) :
    ∀ (ξ : ℝ) (s : Finset ℤ),
      ∑ l ∈ s, ‖𝓕 K (ξ / (2:ℝ)^l)‖ ^ 2 ≤ (4/3) * C₁^2 + C^2 * (1 - (2:ℝ)^(-N))⁻¹ + 1 := by
  intro ξ s
  set S : ℝ := |ξ| with hSdef
  rcases eq_or_lt_of_le (abs_nonneg ξ) with hS0 | hSpos
  · have hξ : ξ = 0 := abs_eq_zero.mp hS0.symm
    have hz : ∀ l : ℤ, ‖𝓕 K (ξ / (2:ℝ)^l)‖ ^ 2 = 0 := by
      intro l
      rw [hξ, zero_div]
      have h := hlin 0
      rw [abs_zero, mul_zero] at h
      rw [le_antisymm h (norm_nonneg _)]; norm_num
    rw [Finset.sum_congr rfl (fun l _ => hz l), Finset.sum_const_zero]
    have hρ1 : (2:ℝ)^(-N) < 1 := by
      rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0:ℝ) < 2)]
      left; exact ⟨by norm_num, by linarith⟩
    have : (0:ℝ) < 1 - (2:ℝ)^(-N) := by linarith
    positivity
  · set L : ℤ := ⌈Real.logb 2 S⌉ with hLdef
    have hc1 : (⌈Real.logb 2 S⌉ : ℝ) - 1 < Real.logb 2 S := (Int.ceil_eq_iff.mp rfl).1
    have hc2 : Real.logb 2 S ≤ (⌈Real.logb 2 S⌉ : ℝ) := (Int.ceil_eq_iff.mp rfl).2
    rw [← hLdef] at hc1 hc2
    have hlog : (2:ℝ) ^ Real.logb 2 S = S :=
      Real.rpow_logb (by norm_num) (by norm_num) hSpos
    have hL1 : (2:ℝ)^(L - 1) < S := by
      rw [← hlog]
      have hcast : (((L - 1 : ℤ)) : ℝ) < Real.logb 2 S := by
        rw [show (((L - 1 : ℤ)) : ℝ) = (L:ℝ) - 1 from by push_cast; ring]; exact hc1
      rw [show ((2:ℝ)^(L-1)) = (2:ℝ)^((((L-1):ℤ)):ℝ) from (Real.rpow_intCast 2 (L-1)).symm]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hcast
    have hL2 : S ≤ (2:ℝ)^L := by
      rw [← hlog]
      have hcast : Real.logb 2 S ≤ (((L : ℤ)) : ℝ) := by push_cast; exact hc2
      rw [show ((2:ℝ)^L) = (2:ℝ)^((((L:ℤ))):ℝ) from (Real.rpow_intCast 2 L).symm]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hcast
    have hsplit := Finset.sum_filter_add_sum_filter_not s (fun l : ℤ => L ≤ l)
      (fun l : ℤ => ‖𝓕 K (ξ / (2:ℝ)^l)‖ ^ 2)
    rw [← hsplit]
    have h1 : ∑ l ∈ s.filter (fun l : ℤ => L ≤ l), ‖𝓕 K (ξ / (2:ℝ)^l)‖ ^ 2 ≤ (4/3) * C₁^2 := by
      have hterm : ∀ l ∈ s.filter (fun l : ℤ => L ≤ l),
          ‖𝓕 K (ξ / (2:ℝ)^l)‖ ^ 2 ≤ C₁^2 * S^2 * (1/4:ℝ)^l := by
        intro l hl
        have habs : |ξ / (2:ℝ)^l| = S * ((1/2:ℝ)^l) := by
          rw [abs_div, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) l), ← hSdef,
              show ((1/2:ℝ)^l) = (((2:ℝ)^l))⁻¹ from by rw [one_div, inv_zpow], div_eq_mul_inv]
        have hsq : ((((1/2:ℝ)^l)))^2 = (1/4:ℝ)^l := by
          rw [pow_two, ← zpow_add₀ (by norm_num : ((1/2:ℝ)) ≠ 0),
              show l + l = 2 * l from by ring, zpow_mul]
          norm_num
        calc ‖𝓕 K (ξ / (2:ℝ)^l)‖ ^ 2 ≤ (C₁ * |ξ / (2:ℝ)^l|) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (hlin _) 2
          _ = C₁^2 * S^2 * (1/4:ℝ)^l := by
              rw [habs]
              rw [show (C₁ * (S * ((1/2:ℝ)^l))) ^ 2 = C₁^2 * S^2 * ((((1/2:ℝ)^l))^2) from by
                ring, hsq]
      calc ∑ l ∈ s.filter (fun l : ℤ => L ≤ l), ‖𝓕 K (ξ / (2:ℝ)^l)‖ ^ 2
          ≤ ∑ l ∈ s.filter (fun l : ℤ => L ≤ l), C₁^2 * S^2 * (1/4:ℝ)^l :=
            Finset.sum_le_sum hterm
        _ = C₁^2 * S^2 * ∑ l ∈ s.filter (fun l : ℤ => L ≤ l), (1/4:ℝ)^l := by
            rw [Finset.mul_sum]
        _ ≤ C₁^2 * S^2 * ((1/4:ℝ)^L * (1 - (1/4:ℝ))⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact finset_zpow_lower_le (1/4) (by norm_num) (by norm_num) L _
              (fun l hl => (Finset.mem_filter.mp hl).2)
        _ ≤ (4/3) * C₁^2 := by
            have hS2 : S^2 * (1/4:ℝ)^L ≤ 1 := by
              have hpos : (0:ℝ) < (2:ℝ)^L := zpow_pos (by norm_num) L
              have hle : S / (2:ℝ)^L ≤ 1 := (div_le_one hpos).mpr hL2
              have hsq4 : ((((2:ℝ)^L)))^2 = (4:ℝ)^L := by
                rw [pow_two, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
                    show L + L = 2 * L from by ring, zpow_mul]
                norm_num
              have hinv4 : ((1/4:ℝ)^L) = (((4:ℝ)^L))⁻¹ := by rw [one_div, inv_zpow]
              have hkey : ((1/4:ℝ)^L) = ((((2:ℝ)^L))⁻¹)^2 := by
                rw [inv_pow, hsq4, ← hinv4]
              have heq : S^2 * (1/4:ℝ)^L = (S / (2:ℝ)^L)^2 := by
                rw [hkey, div_eq_mul_inv, mul_pow]
              rw [heq]
              simpa using pow_le_pow_left₀ (by positivity) hle 2
            have hrw : (1 - (1/4:ℝ))⁻¹ = 4/3 := by norm_num
            rw [hrw]
            have := mul_le_mul_of_nonneg_left hS2 (by positivity : (0:ℝ) ≤ (4/3) * C₁^2)
            nlinarith [this]
    have h2 : ∑ l ∈ s.filter (fun l : ℤ => ¬ (L ≤ l)), ‖𝓕 K (ξ / (2:ℝ)^l)‖ ^ 2
        ≤ C^2 * (1 - (2:ℝ)^(-N))⁻¹ := by
      have hρ0 : (0:ℝ) ≤ (2:ℝ)^(-N) := Real.rpow_nonneg (by norm_num) _
      have hρ1 : (2:ℝ)^(-N) < 1 := by
        rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0:ℝ) < 2)]
        left; exact ⟨by norm_num, by linarith⟩
      have hterm : ∀ l ∈ s.filter (fun l : ℤ => ¬ (L ≤ l)),
          ‖𝓕 K (ξ / (2:ℝ)^l)‖ ^ 2 ≤ C^2 * ((2:ℝ)^(-N)) ^ ((L-1-l).toNat) := by
        intro l hl
        have hl' : l < L := lt_of_not_ge (Finset.mem_filter.mp hl).2
        have hposl : (0:ℝ) < (2:ℝ)^l := zpow_pos (by norm_num) l
        have hlt : (2:ℝ)^l < S := by
          rw [show ((2:ℝ)^l) = (2:ℝ)^((l:ℤ):ℝ) from (Real.rpow_intCast 2 l).symm,
              show ((2:ℝ)^(L-1)) = (2:ℝ)^(((L-1:ℤ)):ℝ) from (Real.rpow_intCast 2 (L-1)).symm] at *
          calc (2:ℝ)^((l:ℤ):ℝ) ≤ (2:ℝ)^(((L-1:ℤ)):ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num)
                  (by exact_mod_cast (show l ≤ L - 1 from by omega))
            _ < S := hL1
        have hu : 1 < |ξ / (2:ℝ)^l| := by
          rw [abs_div, abs_of_pos hposl, ← hSdef, one_lt_div hposl]
          exact hlt
        have hu0 : 0 < |ξ / (2:ℝ)^l| := lt_trans zero_lt_one hu
        have hui : |ξ / (2:ℝ)^l| = S / (2:ℝ)^l := by
          rw [abs_div, abs_of_pos hposl, ← hSdef]
        have hkey : |ξ / (2:ℝ)^l| ^ (-N) = (((2:ℝ)^l) / S) ^ N := by
          rw [hui, div_eq_mul_inv]
          rw [Real.mul_rpow (by positivity) (by positivity)]
          have hS1 : S^(-N) = ((S⁻¹)) ^ N := by
            rw [show -N = -(N) from rfl, Real.rpow_neg hSpos.le]
            exact (Real.inv_rpow hSpos.le N).symm
          have h21 : (((((2:ℝ)^l))⁻¹)) ^ (-N) = ((2:ℝ)^l)^N := by
            rw [Real.inv_rpow (by positivity) (-N), ← Real.rpow_neg (by positivity : (0:ℝ) ≤ ((2:ℝ)^l)), neg_neg]
          rw [hS1, h21, ← Real.mul_rpow (by positivity) (by positivity),
              show S⁻¹ * ((2:ℝ)^l) = ((2:ℝ)^l) / S from by rw [div_eq_mul_inv, mul_comm]]
        have hratio : ((2:ℝ)^l) / S ≤ (2:ℝ)^(l - (L-1)) := by
          have h1 : ((2:ℝ)^l) / S < (2:ℝ)^(l - (L-1)) := by
            rw [div_lt_iff₀ hSpos]
            have he : ((2:ℝ)^(l - (L-1))) * S > (2:ℝ)^(l - (L-1)) * (2:ℝ)^(L-1) :=
              mul_lt_mul_of_pos_left hL1 (zpow_pos (by norm_num) _)
            rwa [show ((2:ℝ)^(l - (L-1))) * (2:ℝ)^(L-1) = (2:ℝ)^l from by
              rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]; congr 1; ring] at he
          exact le_of_lt h1
        have huN : |ξ / (2:ℝ)^l| ^ (-N) ≤ ((2:ℝ)^(-N)) ^ ((L-1-l).toNat) := by
          rw [hkey]
          calc (((2:ℝ)^l) / S) ^ N ≤ ((2:ℝ)^(l - (L-1))) ^ N :=
                Real.rpow_le_rpow (by positivity) hratio hN.le
            _ = ((2:ℝ)^(-N)) ^ ((L-1-l).toNat) := by
                have h1 : ((2:ℝ)^(l - (L-1))) ^ N = (2:ℝ)^(((l - (L-1) : ℤ) : ℝ) * N) := by
                  rw [show ((2:ℝ)^(l - (L-1))) = (2:ℝ)^(((l - (L-1) : ℤ)):ℝ) from
                        (Real.rpow_intCast 2 (l - (L-1))).symm,
                      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
                have h2 : ((2:ℝ)^(-N)) ^ ((L-1-l).toNat)
                    = (2:ℝ)^((-N) * ((L-1-l).toNat : ℝ)) := by
                  rw [← Real.rpow_natCast (x := (2:ℝ)^(-N)) (n := (L-1-l).toNat),
                      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
                rw [h1, h2]
                congr 1
                have hm : ((l - (L-1) : ℤ) : ℝ) = -(((L-1-l).toNat : ℕ) : ℝ) := by
                  have hZ : (l - (L-1) : ℤ) = -(((L-1-l).toNat : ℕ) : ℤ) := by
                    rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ L-1-l)]; ring
                  rw [hZ]; push_cast; ring
                rw [hm]
                ring
        calc ‖𝓕 K (ξ / (2:ℝ)^l)‖ ^ 2 ≤ (C * (1 + |ξ / (2:ℝ)^l|) ^ (-N)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (hdec' _) 2
          _ ≤ (C * ((2:ℝ)^(-N)) ^ ((L-1-l).toNat)) ^ 2 := by
              refine pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left ?_ hC.le) 2
              exact le_trans (Real.rpow_le_rpow_of_nonpos hu0 (by linarith) (by linarith)) huN
          _ ≤ C^2 * ((2:ℝ)^(-N)) ^ ((L-1-l).toNat) := by
              rw [mul_pow]
              refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg C)
              rw [pow_two]
              exact mul_le_of_le_one_right (pow_nonneg hρ0 _) (pow_le_one₀ hρ0 hρ1.le)
      calc ∑ l ∈ s.filter (fun l : ℤ => ¬ (L ≤ l)), ‖𝓕 K (ξ / (2:ℝ)^l)‖ ^ 2
          ≤ ∑ l ∈ s.filter (fun l : ℤ => ¬ (L ≤ l)),
              C^2 * ((2:ℝ)^(-N)) ^ ((L-1-l).toNat) := Finset.sum_le_sum hterm
        _ = C^2 * ∑ l ∈ s.filter (fun l : ℤ => ¬ (L ≤ l)), ((2:ℝ)^(-N)) ^ ((L-1-l).toNat) := by
            rw [Finset.mul_sum]
        _ ≤ C^2 * (1 - (2:ℝ)^(-N))⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg C)
            exact finset_zpow_rev_le _ hρ0 hρ1 L _
              (fun l hl => lt_of_not_ge (Finset.mem_filter.mp hl).2)
    linarith [h1, h2]

private theorem fourier_decay_sum_sq_dyadic (K : ℝ → ℂ)
    (hK1 : Integrable K (volume : Measure ℝ))
    (hKx : Integrable (fun x : ℝ => x • K x) (volume : Measure ℝ))
    (hK0 : (∫ x : ℝ, K x) = 0)
    (hdec : ∃ C N : ℝ, 0 < C ∧ 0 < N ∧ ∀ ξ : ℝ,
      ‖𝓕 K ξ‖ ≤ C * (1 + |ξ|) ^ (-N)) :
    ∃ A : ℝ, 0 < A ∧ ∀ ξ : ℝ,
      (∑' l : ℤ, ‖𝓕 K (ξ / (2:ℝ)^l)‖ₑ ^ (2:ℝ)) ≤ ENNReal.ofReal (A^2) := by
  obtain ⟨C₁, hC₁pos, hlin⟩ := fourier_lin_bound K hK1 hKx hK0
  obtain ⟨C, N, hCpos, hNpos, hdec'⟩ := hdec
  have hρ1 : (2:ℝ)^(-N) < 1 := by
    rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0:ℝ) < 2)]
    left; exact ⟨by norm_num, by linarith⟩
  have hden : (0:ℝ) < 1 - (2:ℝ)^(-N) := by linarith
  refine ⟨Real.sqrt ((4/3) * C₁^2 + C^2 * (1 - (2:ℝ)^(-N))⁻¹ + 1), ?_, fun ξ => ?_⟩
  · refine Real.sqrt_pos.mpr ?_
    have := inv_pos.mpr hden
    nlinarith [sq_nonneg C₁, sq_nonneg C]
  · rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (4/3) * C₁^2 + C^2 * (1 - (2:ℝ)^(-N))⁻¹ + 1)]
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le (fun s => ?_)
    have hsum : (∑ l ∈ s, ‖𝓕 K (ξ / (2:ℝ)^l)‖ₑ ^ (2:ℝ))
        = ENNReal.ofReal (∑ l ∈ s, ‖𝓕 K (ξ / (2:ℝ)^l)‖ ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => sq_nonneg _)]
      exact Finset.sum_congr rfl (fun l _ => by
        rw [← ofReal_norm, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
            ENNReal.ofReal_pow (norm_nonneg _)])
    rw [hsum]
    exact ENNReal.ofReal_le_ofReal
      (dyadic_finite_sum_bound K C₁ C N hC₁pos.le hlin hCpos hNpos hdec' ξ s)


theorem dyadic_square_function_l2 (K : ℝ → ℂ)
    (hK1 : MeasureTheory.Integrable K (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hKx : MeasureTheory.Integrable (fun x : ℝ => x • K x) (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hK0 : (∫ x : ℝ, K x) = 0)
    (hdec : ∃ C N : ℝ, 0 < C ∧ 0 < N ∧ ∀ ξ : ℝ,
      ‖FourierTransform.fourier K ξ‖ ≤ C * (1 + |ξ|) ^ (-N)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (g : ℝ → ℂ),
      MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      ∫⁻ x : ℝ, (∑' l : ℤ,
          ‖(∫ y : ℝ, g y * ((2:ℝ)^l * K ((x - y) * (2:ℝ)^l)))‖ₑ ^ (2 : ℝ))
        ≤ ENNReal.ofReal C' * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖ ^ 2) := by
  obtain ⟨A, hApos, hA⟩ := fourier_decay_sum_sq_dyadic K hK1 hKx hK0 hdec
  refine ⟨A ^ 2, by positivity, fun g hg => ?_⟩
  set c : ℤ → ℝ := fun l => (2:ℝ)^l with hcdef
  have hcpos : ∀ l : ℤ, 0 < c l := fun l => by rw [hcdef]; exact zpow_pos (by norm_num) l
  set kl : ℤ → ℝ → ℂ := fun l z => (c l : ℂ) * K (c l * z) with hkldef
  have hkl : ∀ l : ℤ, Integrable (kl l) := fun l => by
    rw [hkldef]
    exact (hK1.comp_smul (hcpos l).ne').const_mul (c l : ℂ)
  have hFkl : ∀ l : ℤ, (𝓕 (kl l)) = fun ξ => 𝓕 K (ξ / c l) := fun l => by
    simp only [hkldef]
    funext ξ
    exact fourier_dilation (K := K) (hcpos l) ξ
  set m : ℤ → ℝ → ℂ := fun l ξ => 𝓕 (kl l) ξ with hmdef
  have hmm : ∀ l : ℤ, m l = fun ξ => 𝓕 K (ξ / c l) := fun l => by
    rw [hmdef]; exact hFkl l
  have hm : ∀ l : ℤ, MemLp (m l) ⊤ (volume : Measure ℝ) := fun l => by
    exact memLp_top_of_bound (continuous_fourier_of_integrable (kl l) (hkl l)).aestronglyMeasurable
      (∫ x, ‖kl l x‖) (Filter.Eventually.of_forall (fun ξ => norm_fourier_le (kl l) ξ))
  have hA' : ∀ ξ : ℝ, (∑' l : ℤ, ‖m l ξ‖ₑ ^ (2:ℝ)) ≤ ENNReal.ofReal (A ^ 2) := fun ξ => by
    refine le_trans (le_of_eq ?_) (hA ξ)
    refine tsum_congr (fun l => ?_)
    rw [hmm l, hcdef]
  have hbridge : ∀ l : ℤ, (fun x => ∫ y : ℝ, g y * ((2:ℝ)^l * K ((x - y) * (2:ℝ)^l)))
      =ᵐ[volume] (fun x => (BoundaryLayer.multiplier (m l) (hm l) (hg.toLp g) : ℝ → ℂ) x) := by
    intro l
    have h := multiplier_eq_convolution_ae (kl l) (hkl l) (hm l) (hg.toLp g)
    have hL : (fun x => ∫ y : ℝ, (hg.toLp g : ℝ → ℂ) y * kl l (x - y))
        = (fun x => ∫ y : ℝ, g y * ((2:ℝ)^l * K ((x - y) * (2:ℝ)^l))) := by
      funext x
      refine integral_congr_ae ?_
      filter_upwards [hg.coeFn_toLp] with y hy
      rw [hy, hkldef, hcdef]
      simp only [mul_comm ((2:ℝ)^l) (x - y)]
      push_cast
      ring
    rw [hL] at h
    simpa only [hmdef] using h
  have hper : (fun x => ∑' l : ℤ, ‖∫ y : ℝ, g y * ((2:ℝ)^l * K ((x - y) * (2:ℝ)^l))‖ₑ ^ (2:ℝ))
      =ᵐ[volume] (fun x => ∑' l : ℤ,
        ‖(BoundaryLayer.multiplier (m l) (hm l) (hg.toLp g) : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) := by
    filter_upwards [MeasureTheory.ae_all_iff.mpr hbridge] with x hx
    exact tsum_congr (fun l => by rw [hx l])
  calc ∫⁻ x : ℝ, (∑' l : ℤ, ‖∫ y : ℝ, g y * ((2:ℝ)^l * K ((x - y) * (2:ℝ)^l))‖ₑ ^ (2:ℝ))
      = ∫⁻ x : ℝ, (∑' l : ℤ,
          ‖(BoundaryLayer.multiplier (m l) (hm l) (hg.toLp g) : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) :=
        lintegral_congr_ae hper
    _ ≤ ENNReal.ofReal (A ^ 2) * ‖hg.toLp g‖ₑ ^ (2:ℝ) :=
        l2_multiplier_sum_square_function m hm (hg.toLp g) A hA'
    _ = ENNReal.ofReal (A ^ 2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖ ^ 2) := by
        rw [BoundaryLayer.lp_enorm_sq_eq_lintegral]
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [hg.coeFn_toLp] with x hx
        rw [hx, ← ofReal_norm, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
            ENNReal.ofReal_pow (norm_nonneg _)]
