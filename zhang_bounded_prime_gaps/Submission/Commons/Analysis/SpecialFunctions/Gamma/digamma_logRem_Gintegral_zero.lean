import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open scoped Real Topology BigOperators
open Filter MeasureTheory Set Complex

noncomputable section

namespace GintDev

/-- `e^{a·t}` with complex `a`, real `t` -/
def expc (a : ℂ) (t : ℝ) : ℂ := Complex.exp (a * (t : ℂ))

lemma expc_add (a b : ℂ) (t : ℝ) : expc (a + b) t = expc a t * expc b t := by
  unfold expc
  rw [← Complex.exp_add]
  congr 1
  ring

lemma expc_zero (t : ℝ) : expc 0 t = 1 := by simp [expc]

lemma expc_ofReal (a : ℝ) (t : ℝ) : expc (a : ℂ) t = ((Real.exp (a * t) : ℝ) : ℂ) := by
  unfold expc
  rw [← Complex.ofReal_mul]
  exact (Complex.ofReal_exp (a * t)).symm

lemma expc_neg_one_real (t : ℝ) : expc (-(1 : ℂ)) t = ((Real.exp (-t) : ℝ) : ℂ) := by
  simpa using expc_ofReal (-1) t

lemma expc_neg_nat_real (m : ℕ) (t : ℝ) : expc (-((m : ℕ) : ℂ)) t = ((Real.exp (-(m : ℝ) * t) : ℝ) : ℂ) := by
  simpa using expc_ofReal (-(m : ℝ)) t

lemma expc_ne_zero (a : ℂ) (t : ℝ) : expc a t ≠ 0 := by
  unfold expc
  exact Complex.exp_ne_zero _

lemma norm_expc (a : ℂ) (t : ℝ) : ‖expc a t‖ = Real.exp (a.re * t) := by
  unfold expc
  rw [Complex.norm_exp]
  congr 1
  rw [Complex.mul_re]
  simp

lemma expc_neg_one_ne_one {t : ℝ} (ht : 0 < t) : expc (-(1 : ℂ)) t ≠ 1 := by
  have hv := expc_neg_one_real t
  rw [hv]
  intro h
  have hre : Real.exp (-t) = 1 := (Complex.ofReal_eq_one.mp h)
  have hgt : Real.exp t > 1 := (Real.one_lt_exp_iff).2 ht
  have hprod : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hmain : Real.exp t = 1 := by
    calc
      Real.exp t = Real.exp t * Real.exp (-t) := by rw [hre]; ring
      _ = 1 := hprod
  exact (ne_of_gt hgt) hmain

lemma exp_sub_one_le_mul_self (t : ℝ) : Real.exp t - 1 ≤ t * Real.exp t := by
  have h := Real.one_sub_le_exp_neg t
  have hpos : 0 ≤ Real.exp t := (Real.exp_pos t).le
  have hmul : (1 - t) * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
    mul_le_mul_of_nonneg_right h hpos
  have h1 : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    norm_num
  have h2 : (1 - t) * Real.exp t = Real.exp t - t * Real.exp t := by ring
  nlinarith

lemma exp_ge_add (t : ℝ) : 1 + t ≤ Real.exp t := by
  simpa [add_comm] using (Real.add_one_le_exp t : t + 1 ≤ Real.exp t)

lemma exp_sub_one_ge (t : ℝ) : t ≤ Real.exp t - 1 := by
  have h := exp_ge_add t
  linarith

lemma exp_sub_one_pos (t : ℝ) (ht : 0 < t) : 0 < Real.exp t - 1 := by
  have hle := exp_ge_add t
  have hlt : 1 < 1 + t := by linarith
  exact sub_pos.mpr (lt_of_lt_of_le hlt hle)

/-- 1 - exp(-t) ≥ t/(1+t) for t ≥ 0 -/
lemma one_sub_exp_neg_ge_div {t : ℝ} (ht : 0 ≤ t) : t / (1 + t) ≤ 1 - Real.exp (-t) := by
  have h := exp_ge_add t  -- 1 + t ≤ exp t
  have he : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have h1pt : 0 < 1 + t := by linarith
  -- from (1+t) ≤ e^t, multiply by e^{-t}: (1+t) e^{-t} ≤ 1
  have hmul : (1 + t) * Real.exp (-t) ≤ 1 := by
    calc
      (1 + t) * Real.exp (-t) ≤ Real.exp t * Real.exp (-t) := by
        exact mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-t))
      _ = 1 := by
        rw [← Real.exp_add]
        norm_num
  -- so e^{-t} ≤ 1/(1+t), hence 1 - e^{-t} ≥ 1 - 1/(1+t) = t/(1+t)
  have he' : Real.exp (-t) ≤ 1 / (1 + t) := by
    rw [le_div_iff₀ h1pt]
    simpa [mul_comm] using hmul
  have hterm : 1 - 1 / (1 + t) = t / (1 + t) := by
    field_simp [h1pt.ne']
    ring
  have hgoal : 1 - 1 / (1 + t) ≤ 1 - Real.exp (-t) := by linarith
  rwa [hterm] at hgoal

/-- 1 - exp(-t) ≥ t/2 for 0 ≤ t ≤ 1 -/
lemma one_sub_exp_neg_ge_half {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t / 2 ≤ 1 - Real.exp (-t) := by
  have h := one_sub_exp_neg_ge_div ht0
  have hdiv : t / 2 ≤ t / (1 + t) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    -- t/2 ≤ t/(1+t): t·(1+t) ≤ 2t
    nlinarith
  linarith

/-- |t - 1 + exp(-t)| ≤ t^2 for 0 ≤ t ≤ 1 -/
lemma abs_sub_one_add_exp_neg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |t - 1 + Real.exp (-t)| ≤ t ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := -t) (by
    rw [abs_neg]
    rw [abs_of_nonneg ht0]
    linarith)
  -- |exp(-t) - 1 - (-t)| ≤ (-t)^2, i.e. |exp(-t) - 1 + t| ≤ t^2
  convert h using 1 <;> ring_nf

/-- ‖expc a t − 1‖ ≤ ‖a‖ · t when a.re ≤ 0 and t ≥ 0 (via MVT) -/
lemma norm_expc_sub_one_le_of_re_nonpos {a : ℂ} (ha : a.re ≤ 0) {t : ℝ} (ht0 : 0 ≤ t) :
    ‖expc a t - 1‖ ≤ ‖a‖ * t := by
  let f : ℝ → ℂ := fun u => expc a u
  have hder : ∀ u : ℝ, HasDerivAt (fun v : ℝ => expc a v) (a * expc a u) u := by
    intro u
    unfold expc
    have hlin : HasDerivAt (fun v : ℝ => a * (v : ℂ)) a u := by
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id' u).smul_const (a : ℂ))
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlin.cexp
  have hf_diff : ∀ x ∈ Icc 0 t, HasDerivWithinAt f (a * expc a x) (Icc 0 t) x := by
    intro x hx
    exact (hder x).hasDerivWithinAt
  have hbnd : ∀ x ∈ Ico 0 t, ‖a * expc a x‖ ≤ ‖a‖ := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    calc
      ‖a * expc a x‖ = ‖a‖ * ‖expc a x‖ := by rw [norm_mul]
      _ ≤ ‖a‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg a)
        rw [norm_expc]
        have : a.re * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha hx0
        exact (Real.exp_le_one_iff).2 this
      _ = ‖a‖ := by rw [mul_one]
  have hres := norm_image_sub_le_of_norm_deriv_le_segment' (f := f)
    (f' := fun u : ℝ => a * expc a u) (a := 0) (b := t) (C := ‖a‖) hf_diff hbnd t
    (right_mem_Icc.mpr ht0)
  simpa [f, expc] using hres

lemma tendsto_expc_neg_nat (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => expc (-((n : ℕ) : ℂ)) t) atTop (𝓝 (0 : ℂ)) := by
  have heq : (fun n : ℕ => expc (-((n : ℕ) : ℂ)) t) =
      fun n : ℕ => ((Real.exp (-(n : ℝ) * t) : ℝ) : ℂ) := by
    funext n
    rw [expc_neg_nat_real]
  rw [heq]
  have harg : Tendsto (fun n : ℕ => -(n : ℝ) * t) atTop atBot := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) * t) atTop atTop := by
      simpa [mul_comm] using (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const ht
    have hneg : Tendsto (fun n : ℕ => -(↑n * t)) atTop atBot := tendsto_neg_atTop_atBot.comp h1
    convert hneg using 1
    funext n
    ring
  have hrexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  have hlift : Tendsto (fun n : ℕ => ((Real.exp (-(n : ℝ) * t) : ℝ) : ℂ))
      atTop (𝓝 ((0 : ℝ) : ℂ)) := by
    exact (Complex.continuous_ofReal.tendsto 0).comp hrexp
  simpa using hlift

/- The inner function and its bounds -/

/-- J z t = e^{-(z+1)t}/(1-e^{-t}) - 1/t (complex, t real) -/
def J (z : ℂ) (t : ℝ) : ℂ :=
  expc (-(z + 1 : ℂ)) t * (1 - expc (-(1 : ℂ)) t)⁻¹ - (t : ℂ)⁻¹

/-- numerator of J over common denominator -/
def N (z : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) * expc (-(z + 1 : ℂ)) t - (1 - expc (-(1 : ℂ)) t)

/-- common denominator -/
def D (t : ℝ) : ℂ := (t : ℂ) * (1 - expc (-(1 : ℂ)) t)

lemma D_ne_zero {t : ℝ} (ht : 0 < t) : D t ≠ 0 := by
  unfold D
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  have hq : 1 - expc (-(1 : ℂ)) t ≠ 0 := sub_ne_zero.mpr (expc_neg_one_ne_one ht).symm
  exact mul_ne_zero ht0 hq

lemma J_eq_div (z : ℂ) {t : ℝ} (ht : 0 < t) : J z t = N z t / D t := by
  unfold J N D
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  have hq : expc (-(1 : ℂ)) t ≠ 1 := expc_neg_one_ne_one ht
  field_simp [ht0, hq]

/-- ‖1 - exp(-t)‖ as complex = 1 - exp(-t) (a positive real) -/
lemma norm_one_sub_expc_neg (t : ℝ) (ht : 0 < t) :
    ‖(1 - expc (-(1 : ℂ)) t : ℂ)‖ = 1 - Real.exp (-t) := by
  have hv := expc_neg_one_real t
  rw [hv]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
  rw [Complex.norm_real]
  have h1 : 1 - Real.exp (-t) ≥ 0 := by
    have : Real.exp (-t) ≤ 1 := (Real.exp_le_one_iff).2 (neg_nonpos.mpr (le_of_lt ht))
    linarith
  exact abs_of_nonneg h1

/-- ‖D t‖ = t·(1 - e^{-t}) for t > 0 -/
lemma norm_D (t : ℝ) (ht : 0 < t) : ‖D t‖ = t * (1 - Real.exp (-t)) := by
  unfold D
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ht)]
  rw [norm_one_sub_expc_neg t ht]
/- bounds on N and D on (0,1] -/
lemma norm_expc_sub_one_neg_z1 (z : ℂ) (hz : 0 < z.re) {t : ℝ} (ht0 : 0 ≤ t) :
    ‖expc (-(z + 1)) t - 1‖ ≤ ‖z + 1‖ * t := by
  have hre : (-(z + 1)).re ≤ 0 := by
    rw [Complex.neg_re, Complex.add_re]
    have : ((1 : ℂ).re) = 1 := by norm_num
    rw [this]
    linarith
  have h := norm_expc_sub_one_le_of_re_nonpos (a := -(z + 1)) hre ht0
  calc
    ‖expc (-(z + 1)) t - 1‖ ≤ ‖-(z + 1)‖ * t := h
    _ = ‖z + 1‖ * t := by rw [norm_neg]


lemma norm_N_le (z : ℂ) (hz : 0 < z.re) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖N z t‖ ≤ (‖z + 1‖ + 1) * t ^ 2 := by
  have hz' : 0 ≤ z.re + 1 := by linarith
  have hN_expand : N z t = (t : ℂ) * (expc (-(z + 1)) t - 1) + ((t : ℂ) - 1 + expc (-(1 : ℂ)) t) := by
    unfold N
    ring
  have h1 : ‖(t : ℂ) * (expc (-(z + 1)) t - 1)‖ ≤ ‖z + 1‖ * t ^ 2 := by
    calc
      ‖(t : ℂ) * (expc (-(z + 1)) t - 1)‖ = ‖(t : ℂ)‖ * ‖expc (-(z + 1)) t - 1‖ := by
        rw [norm_mul]
      _ = t * ‖expc (-(z + 1)) t - 1‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      _ ≤ t * (‖z + 1‖ * t) := by
        apply mul_le_mul_of_nonneg_left _ ht0
        exact norm_expc_sub_one_neg_z1 z hz ht0
      _ = ‖z + 1‖ * t ^ 2 := by ring
  have h2 : ‖(t : ℂ) - 1 + expc (-(1 : ℂ)) t‖ ≤ t ^ 2 := by
    have hv : (t : ℂ) - 1 + expc (-(1 : ℂ)) t = ((t - 1 + Real.exp (-t) : ℝ) : ℂ) := by
      rw [expc_neg_one_real]
      norm_num
    rw [hv]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_sub_one_add_exp_neg ht0 ht1
  calc
    ‖N z t‖ ≤ ‖(t : ℂ) * (expc (-(z + 1)) t - 1)‖ + ‖(t : ℂ) - 1 + expc (-(1 : ℂ)) t‖ := by
      rw [hN_expand]
      exact norm_add_le _ _
    _ ≤ ‖z + 1‖ * t ^ 2 + t ^ 2 := add_le_add h1 h2
    _ = (‖z + 1‖ + 1) * t ^ 2 := by ring

lemma norm_D_lower {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) : t ^ 2 / 2 ≤ ‖D t‖ := by
  rw [norm_D t ht0]
  have h := one_sub_exp_neg_ge_half (le_of_lt ht0) ht1  -- t/2 ≤ 1 - e^{-t}
  have hmul : t * (t / 2) ≤ t * (1 - Real.exp (-t)) := by
    exact mul_le_mul_of_nonneg_left h (le_of_lt ht0)
  have hcalc : t ^ 2 / 2 = t * (t / 2) := by ring
  rwa [hcalc]

lemma norm_J_le_small (z : ℂ) (hz : 0 < z.re) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖J z t‖ ≤ 2 * (‖z + 1‖ + 1) := by
  have hN : ‖N z t‖ ≤ (‖z + 1‖ + 1) * t ^ 2 := norm_N_le z hz (le_of_lt ht0) ht1
  have hD : t ^ 2 / 2 ≤ ‖D t‖ := norm_D_lower ht0 ht1
  have hBpos : 0 < ‖D t‖ := norm_pos_iff.mpr (D_ne_zero ht0)
  have hc0 : 0 ≤ 2 * (‖z + 1‖ + 1) := by positivity
  have hMain : ‖N z t‖ ≤ (2 * (‖z + 1‖ + 1)) * ‖D t‖ := by
    calc
      ‖N z t‖ ≤ (‖z + 1‖ + 1) * t ^ 2 := hN
      _ = (2 * (‖z + 1‖ + 1)) * (t ^ 2 / 2) := by ring
      _ ≤ (2 * (‖z + 1‖ + 1)) * ‖D t‖ := mul_le_mul_of_nonneg_left hD hc0
  have hJ : ‖J z t‖ ≤ ‖N z t‖ / ‖D t‖ := by
    rw [J_eq_div z ht0]
    calc
      ‖N z t / D t‖ = ‖N z t * (D t)⁻¹‖ := by rw [div_eq_mul_inv]
      _ ≤ ‖N z t‖ * ‖(D t)⁻¹‖ := norm_mul_le _ _
      _ = ‖N z t‖ / ‖D t‖ := by rw [norm_inv, div_eq_mul_inv]
  calc
    ‖J z t‖ ≤ ‖N z t‖ / ‖D t‖ := hJ
    _ ≤ 2 * (‖z + 1‖ + 1) := (div_le_iff₀ hBpos).2 hMain

/- bounds for t ≥ 1 -/

/-- ‖J z t‖ ≤ Clarge z for t ≥ 1 -/
def Clarge (z : ℂ) : ℝ := Real.exp (-(z.re + 1)) * (1 - Real.exp (-1))⁻¹ + 1

lemma norm_expc_neg_z1_le (z : ℂ) (hz : 0 < z.re) {t : ℝ} (ht1 : 1 ≤ t) :
    ‖expc (-(z + 1)) t‖ ≤ Real.exp (-(z.re + 1)) := by
  rw [norm_expc, Real.exp_le_exp]
  have hre : (-(z + 1)).re = -(z.re + 1) := by
    rw [Complex.neg_re, Complex.add_re]
    norm_num
  rw [hre]
  have hzp : 0 ≤ z.re + 1 := by linarith
  have htmp : z.re + 1 ≤ (z.re + 1) * t := by
    simpa using (mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ t) hzp)
  linarith

lemma exp_neg_le_exp_neg_one_of_ge_one {t : ℝ} (ht1 : 1 ≤ t) : Real.exp (-t) ≤ Real.exp (-1) := by
  rw [Real.exp_le_exp]
  linarith

lemma exp_neg_one_lt_one : Real.exp (-1) < 1 := by
  rw [← Real.exp_zero]
  exact (Real.exp_lt_exp).mpr (by norm_num)

lemma one_sub_exp_neg_one_pos : 0 < 1 - Real.exp (-1) := by
  linarith [exp_neg_one_lt_one]

lemma norm_J_le_large (z : ℂ) (hz : 0 < z.re) {t : ℝ} (ht1 : 1 ≤ t) :
    ‖J z t‖ ≤ Clarge z := by
  have ht0 : 0 < t := by linarith
  unfold J Clarge
  have hA : ‖expc (-(z + 1)) t‖ ≤ Real.exp (-(z.re + 1)) := norm_expc_neg_z1_le z hz ht1
  have hinv : ‖(1 - expc (-(1 : ℂ)) t)⁻¹‖ = (1 - Real.exp (-t))⁻¹ := by
    rw [norm_inv]
    rw [norm_one_sub_expc_neg t ht0]
  have hden1 : 0 < 1 - Real.exp (-1) := one_sub_exp_neg_one_pos
  have hden : 0 < 1 - Real.exp (-t) := by
    have he : Real.exp (-t) < 1 := by
      have hle : Real.exp (-t) ≤ Real.exp (-1) := exp_neg_le_exp_neg_one_of_ge_one ht1
      linarith [exp_neg_one_lt_one, hle]
    linarith
  have hsuble : 1 - Real.exp (-1) ≤ 1 - Real.exp (-t) := by
    have he : Real.exp (-t) ≤ Real.exp (-1) := exp_neg_le_exp_neg_one_of_ge_one ht1
    linarith
  have hinv_le : (1 - Real.exp (-t))⁻¹ ≤ (1 - Real.exp (-1))⁻¹ := by
    -- one_div version
    have h := one_div_le_one_div_of_le hden1 hsuble
    -- 1/x = x⁻¹ in ℝ
    simpa using h
  have hA0 : 0 ≤ Real.exp (-(z.re + 1)) := (Real.exp_pos _).le
  have hInv0 : 0 ≤ (1 - Real.exp (-1))⁻¹ := inv_nonneg.mpr (le_of_lt hden1)
  have hC : ‖expc (-(z + 1)) t‖ * ‖(1 - expc (-(1 : ℂ)) t)⁻¹‖ ≤
      Real.exp (-(z.re + 1)) * (1 - Real.exp (-1))⁻¹ := by
    calc
      ‖expc (-(z + 1)) t‖ * ‖(1 - expc (-(1 : ℂ)) t)⁻¹‖
          ≤ ‖expc (-(z + 1)) t‖ * (1 - Real.exp (-1))⁻¹ := by
            apply mul_le_mul_of_nonneg_left (by
              rw [hinv]
              exact hinv_le) (norm_nonneg _)
      _ ≤ Real.exp (-(z.re + 1)) * (1 - Real.exp (-1))⁻¹ := by
            exact mul_le_mul_of_nonneg_right hA hInv0
  have htinv : ‖(t : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith : 0 ≤ t)]
    have : 1 / t ≤ 1 := by
      rw [div_le_iff₀ (by linarith : 0 < t)]
      linarith
    simpa using this
  calc
    ‖expc (-(z + 1)) t * (1 - expc (-(1 : ℂ)) t)⁻¹ - (t : ℂ)⁻¹‖
        ≤ ‖expc (-(z + 1)) t * (1 - expc (-(1 : ℂ)) t)⁻¹‖ + ‖(t : ℂ)⁻¹‖ := norm_sub_le _ _
    _ ≤ ‖expc (-(z + 1)) t‖ * ‖(1 - expc (-(1 : ℂ)) t)⁻¹‖ + ‖(t : ℂ)⁻¹‖ := by
        exact add_le_add_left (norm_mul_le _ _) _
    _ ≤ Real.exp (-(z.re + 1)) * (1 - Real.exp (-1))⁻¹ + 1 := add_le_add hC htinv

/- global domination and the full integrand -/

def Csmall (z : ℂ) : ℝ := 2 * (‖z + 1‖ + 1)

def Cbound (z : ℂ) : ℝ := max (Csmall z) (Clarge z)

/-- full integrand: e^{-(n+1)t} · J z t -/
def Fseq (n : ℕ) (z : ℂ) (t : ℝ) : ℂ := expc (-((n + 1 : ℕ) : ℂ)) t * J z t

lemma Cbound_nonneg (z : ℂ) : 0 ≤ Cbound z := by
  unfold Cbound
  have h1 : 0 ≤ Csmall z := by
    unfold Csmall
    positivity
  exact le_max_of_le_left h1

lemma Csmall_le_Cbound (z : ℂ) : Csmall z ≤ Cbound z := by
  exact le_max_left _ _

lemma Clarge_le_Cbound (z : ℂ) : Clarge z ≤ Cbound z := by
  exact le_max_right _ _

lemma norm_expc_neg_natp1 (n : ℕ) (t : ℝ) :
    ‖expc (-((n + 1 : ℕ) : ℂ)) t‖ = Real.exp (-((n + 1 : ℝ) * t)) := by
  rw [norm_expc]
  congr 1
  have hre : (-((n + 1 : ℕ) : ℂ)).re = -((n + 1 : ℝ)) := by
    rw [Complex.neg_re]
    norm_num
  rw [hre]
  ring

lemma norm_expc_neg_natp1_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖expc (-((n + 1 : ℕ) : ℂ)) t‖ ≤ Real.exp (-t) := by
  rw [norm_expc_neg_natp1]
  rw [Real.exp_le_exp]
  have hn : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hm : (1 : ℝ) * t ≤ ((n + 1 : ℝ)) * t := mul_le_mul_of_nonneg_right hn ht
  have hm' : t ≤ (n + 1 : ℝ) * t := by simpa using hm
  linarith

/-- ‖Fseq n z t‖ ≤ Cbound z · e^{-t} for t > 0 -/
lemma norm_Fseq_le (z : ℂ) (hz : 0 < z.re) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖Fseq n z t‖ ≤ Cbound z * Real.exp (-t) := by
  unfold Fseq
  have ht0 : 0 ≤ t := le_of_lt ht
  have hA : ‖expc (-((n + 1 : ℕ) : ℂ)) t‖ ≤ Real.exp (-t) := norm_expc_neg_natp1_le n ht0
  by_cases ht1 : t ≤ 1
  · -- small t: use Csmall
    have hJ : ‖J z t‖ ≤ Csmall z := by
      unfold Csmall
      simpa using norm_J_le_small z hz ht ht1
    have hprod : ‖expc (-((n + 1 : ℕ) : ℂ)) t‖ * ‖J z t‖ ≤ Real.exp (-t) * Csmall z := by
      exact mul_le_mul hA hJ (norm_nonneg _) (Real.exp_nonneg (-t))
    have hfin : Real.exp (-t) * Csmall z ≤ Real.exp (-t) * Cbound z := by
      exact mul_le_mul_of_nonneg_left (Csmall_le_Cbound z) (Real.exp_nonneg (-t))
    calc
      ‖expc (-((n + 1 : ℕ) : ℂ)) t * J z t‖ = ‖expc (-((n + 1 : ℕ) : ℂ)) t‖ * ‖J z t‖ := by
        rw [norm_mul]
      _ ≤ Real.exp (-t) * Csmall z := hprod
      _ ≤ Real.exp (-t) * Cbound z := hfin
      _ = Cbound z * Real.exp (-t) := by rw [mul_comm]
  · -- large t
    have ht1' : 1 ≤ t := by linarith
    have hJ : ‖J z t‖ ≤ Clarge z := norm_J_le_large z hz ht1'
    have hprod : ‖expc (-((n + 1 : ℕ) : ℂ)) t‖ * ‖J z t‖ ≤ Real.exp (-t) * Clarge z := by
      exact mul_le_mul hA hJ (norm_nonneg _) (Real.exp_nonneg (-t))
    have hfin : Real.exp (-t) * Clarge z ≤ Real.exp (-t) * Cbound z := by
      exact mul_le_mul_of_nonneg_left (Clarge_le_Cbound z) (Real.exp_nonneg (-t))
    calc
      ‖expc (-((n + 1 : ℕ) : ℂ)) t * J z t‖ = ‖expc (-((n + 1 : ℕ) : ℂ)) t‖ * ‖J z t‖ := by
        rw [norm_mul]
      _ ≤ Real.exp (-t) * Clarge z := hprod
      _ ≤ Real.exp (-t) * Cbound z := hfin
      _ = Cbound z * Real.exp (-t) := by rw [mul_comm]

lemma integrable_bound (z : ℂ) :
    MeasureTheory.Integrable (fun t : ℝ => Cbound z * Real.exp (-t))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have h := integrableOn_exp_neg_Ioi (0 : ℝ)
  exact MeasureTheory.Integrable.const_mul (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) h (Cbound z)

lemma tendsto_expc_neg_natp1 (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => expc (-((n + 1 : ℕ) : ℂ)) t) atTop (𝓝 (0 : ℂ)) := by
  have h₁ : Tendsto (fun m : ℕ => expc (-((m : ℕ) : ℂ)) t) atTop (𝓝 (0 : ℂ)) :=
    tendsto_expc_neg_nat t ht
  have h₂ : Tendsto (fun n : ℕ => (fun m : ℕ => expc (-((m : ℕ) : ℂ)) t) (n + 1)) atTop (𝓝 (0 : ℂ)) := by
    exact h₁.comp (tendsto_add_atTop_nat 1)
  simpa using h₂

lemma tendsto_Fseq (z : ℂ) (_hz : 0 < z.re) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => Fseq n z t) atTop (𝓝 (0 : ℂ)) := by
  unfold Fseq
  have hA : Tendsto (fun n : ℕ => expc (-((n + 1 : ℕ) : ℂ)) t) atTop (𝓝 (0 : ℂ)) :=
    tendsto_expc_neg_natp1 t ht
  have hJ : Tendsto (fun _ : ℕ => J z t) atTop (𝓝 (J z t)) := tendsto_const_nhds
  have h := hA.mul hJ
  simpa using h

lemma continuous_expc (a : ℂ) : Continuous fun t : ℝ => expc a t := by
  unfold expc
  fun_prop

lemma measurable_Fseq (z : ℂ) (_hz : 0 < z.re) (n : ℕ) :
    MeasureTheory.AEStronglyMeasurable (fun t : ℝ => Fseq n z t)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  apply ContinuousOn.aestronglyMeasurable
  · unfold Fseq J
    have hcA : ContinuousOn (fun t : ℝ => expc (-((n + 1 : ℕ) : ℂ)) t) (Set.Ioi (0 : ℝ)) :=
      (continuous_expc _).continuousOn
    have hcB : ContinuousOn (fun t : ℝ => expc (-(z + 1)) t) (Set.Ioi (0 : ℝ)) :=
      (continuous_expc _).continuousOn
    have hcC : ContinuousOn (fun t : ℝ => (1 - expc (-(1 : ℂ)) t)⁻¹) (Set.Ioi (0 : ℝ)) := by
      have hc0 : Continuous (fun t : ℝ => 1 - expc (-(1 : ℂ)) t) := by
        exact continuous_const.sub (continuous_expc (-(1 : ℂ)))
      have hc : ContinuousOn (fun t : ℝ => 1 - expc (-(1 : ℂ)) t) (Set.Ioi (0 : ℝ)) :=
        hc0.continuousOn
      refine hc.inv₀ ?_
      intro t ht
      exact sub_ne_zero.mpr (expc_neg_one_ne_one ht).symm
    have hcid : ContinuousOn (fun t : ℝ => (t : ℂ)) (Set.Ioi (0 : ℝ)) :=
      Complex.continuous_ofReal.continuousOn
    have hcinv : ContinuousOn (fun t : ℝ => (t : ℂ)⁻¹) (Set.Ioi (0 : ℝ)) := by
      refine hcid.inv₀ ?_
      intro t ht
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    exact hcA.mul ((hcB.mul hcC).sub hcinv)
  · exact measurableSet_Ioi



/- identity between Fseq and the raw integrand of the statement -/
lemma Fseq_eq_raw (z : ℂ) (n : ℕ) (t : ℝ) :
    Fseq n z t =
      Complex.exp (-(((n + 1 : ℕ) : ℂ) * (t : ℂ))) *
        (Complex.exp (-((z + 1 : ℂ) * (t : ℂ))) * (1 - Complex.exp (-(t : ℂ)))⁻¹ -
          (t : ℂ)⁻¹) := by
  unfold Fseq J expc
  have h1 : (-(((n + 1 : ℕ) : ℂ)) * (t : ℂ)) = -(((n + 1 : ℕ) : ℂ) * (t : ℂ)) := by ring
  have h2 : (-((z + 1 : ℂ)) * (t : ℂ)) = -((z + 1 : ℂ) * (t : ℂ)) := by ring
  have h3 : (-(1 : ℂ)) * (t : ℂ) = -(t : ℂ) := by ring
  rw [h1, h2, h3]

end GintDev

namespace Commons.Analysis.SpecialFunctions.Gamma

open GintDev

theorem digamma_logRem_Gintegral_zero (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
        Complex.exp (-(((n + 1 : ℕ) : ℂ) * (t : ℂ))) *
          (Complex.exp (-((z + 1 : ℂ) * (t : ℂ))) * (1 - Complex.exp (-(t : ℂ)))⁻¹ -
            (t : ℂ)⁻¹))
      atTop (𝓝 (0 : ℂ)) := by
  let bound : ℝ → ℝ := fun t => Cbound z * Real.exp (-t)
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have hDCT : Tendsto (fun n : ℕ =>
      ∫ t : ℝ, Fseq n z t ∂μ) atTop
      (𝓝 (∫ t : ℝ, (0 : ℂ) ∂μ)) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n t => Fseq n z t) (f := fun _ : ℝ => (0 : ℂ)) bound
    · intro n
      exact measurable_Fseq z hz n
    · dsimp [μ]
      exact integrable_bound z
    · intro n
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      apply Filter.Eventually.of_forall
      intro t ht
      exact norm_Fseq_le z hz n ht
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      apply Filter.Eventually.of_forall
      intro t ht
      exact tendsto_Fseq z hz ht
  have hDCT' : Tendsto (fun n : ℕ => ∫ t : ℝ in Set.Ioi (0 : ℝ), Fseq n z t)
      atTop (𝓝 (0 : ℂ)) := by
    dsimp [μ] at hDCT
    simpa using hDCT
  have hFunEq : (fun n : ℕ => ∫ t : ℝ in Set.Ioi (0 : ℝ), Fseq n z t) =
      fun n : ℕ => ∫ t : ℝ in Set.Ioi (0 : ℝ),
        Complex.exp (-(((n + 1 : ℕ) : ℂ) * (t : ℂ))) *
          (Complex.exp (-((z + 1 : ℂ) * (t : ℂ))) * (1 - Complex.exp (-(t : ℂ)))⁻¹ -
            (t : ℂ)⁻¹) := by
    funext n
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact Fseq_eq_raw z n t
  simpa [hFunEq] using hDCT'

end Commons.Analysis.SpecialFunctions.Gamma