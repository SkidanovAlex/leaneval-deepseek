import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Real Set Complex Filter intervalIntegral MeasureTheory
open scoped Topology Real

namespace Commons.Analysis.Fourier

/-!
# Oscillatory tail bound for the truncated Perron kernel with parameter σ

`perronKernelSigma_oscTail`: for real `0 < σ`, `α ≠ 0`, `1 ≤ T ≤ R`,

    ‖∫_T^R e^{iαt} / (σ + i t) dt‖ ≤ 3 / (|α| · T)

This is the σ-generalisation of `PerronKernel.osc_tail_bound` (already proven in
`Submission.Commons.Analysis.Fourier.perron_kernel_bound` for σ = 1).  The
proof is identical: write the integrand as `u'(t)·v(t)` with
`u(t) = e^{iαt}/(iα)` and `v(t) = (σ + i t)⁻¹`, integrate by parts and use
`‖σ + i t‖ ≥ t` (which holds for every real σ) and
`∫_T^R (σ² + t²)⁻¹ dt ≤ ∫_T^R t⁻² dt ≤ 1/T`.
-/

namespace PerronSigma

/-- derivative of `s ↦ e^{I·α·s}/(I·α)`, equal to `e^{I·α·s}`. -/
lemma deriv_cexp_div (α : ℝ) (hα : α ≠ 0) : ∀ t : ℝ,
    HasDerivAt (fun s : ℝ => cexp (I * (α : ℂ) * (s : ℂ)) / (I * (α : ℂ)))
      (cexp (I * (α : ℂ) * (t : ℂ))) t := by
  intro t
  have hlin : HasDerivAt (fun w : ℂ => (I * (α : ℂ)) * w) (I * (α : ℂ)) (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).const_mul (I * (α : ℂ))
  have hcomp : HasDerivAt (fun s : ℝ => (I * (α : ℂ)) * (s : ℂ)) (I * (α : ℂ)) t :=
    hlin.comp_ofReal
  have hcexp := HasDerivAt.cexp hcomp
  have h2 := hcexp.div_const (I * (α : ℂ))
  refine h2.congr_deriv ?_
  have hnz : (I * (α : ℂ)) ≠ 0 := by
    intro hz
    apply hα
    have hz' := congrArg Complex.im hz
    simpa using hz'
  have hα' : ((α : ℂ)) ≠ 0 := by exact_mod_cast hα
  field_simp [hnz, hα']

/-- `σ + i t ≠ 0` for `σ ≠ 0`. -/
lemma sigma_add_I_ne_zero (σ t : ℝ) (hσ : σ ≠ 0) : ((σ : ℂ) + I * (t : ℂ)) ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  have : σ = 0 := by simpa using hre
  exact hσ this

/-- derivative of `s ↦ (σ + I·s)⁻¹`. -/
lemma deriv_sigma_add_I_inv (σ : ℝ) (hσ : σ ≠ 0) : ∀ t : ℝ,
    HasDerivAt (fun s : ℝ => ((σ : ℂ) + I * (s : ℂ))⁻¹)
      (-(I : ℂ) * (((σ : ℂ) + I * (t : ℂ))⁻¹) ^ 2) t := by
  intro t
  have hg : HasDerivAt (fun s : ℝ => ((σ : ℂ) + I * (s : ℂ) : ℂ)) I t := by
    have hlin : HasDerivAt (fun w : ℂ => I * w) I (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).const_mul I
    have hcomp : HasDerivAt (fun s : ℝ => I * (s : ℂ)) I t := hlin.comp_ofReal
    simpa using hcomp.const_add (σ : ℂ)
  have hne : ((σ : ℂ) + I * (t : ℂ) : ℂ) ≠ 0 := sigma_add_I_ne_zero σ t hσ
  have hinv := hasDerivAt_inv hne
  have h := hinv.comp t hg
  refine h.congr_deriv ?_
  have hx2 : (((σ : ℂ) + I * (t : ℂ)) ^ 2)⁻¹ = (((σ : ℂ) + I * (t : ℂ))⁻¹) ^ 2 := by
    exact (inv_pow (a := ((σ : ℂ) + I * (t : ℂ))) 2).symm
  calc
    (-(((σ : ℂ) + I * (t : ℂ)) ^ 2)⁻¹) * I = -(I * (((σ : ℂ) + I * (t : ℂ)) ^ 2)⁻¹) := by ring
    _ = -I * (((σ : ℂ) + I * (t : ℂ)) ^ 2)⁻¹ := by ring
    _ = -(I : ℂ) * (((σ : ℂ) + I * (t : ℂ))⁻¹) ^ 2 := by rw [hx2]

def oscUp (α : ℝ) (s : ℝ) : ℂ := cexp (I * (α : ℂ) * (s : ℂ))
def oscU (α : ℝ) (s : ℝ) : ℂ := oscUp α s / (I * (α : ℂ))
def oscV (σ : ℝ) (s : ℝ) : ℂ := (((σ : ℂ) + I * (s : ℂ))⁻¹)
def oscW (α σ : ℝ) (s : ℝ) : ℂ := oscU α s * oscV σ s
def oscR (α σ : ℝ) (s : ℝ) : ℂ := oscU α s * (-(I : ℂ) * (oscV σ s) ^ 2)
def oscG (α σ : ℝ) (s : ℝ) : ℂ := cexp (I * ((α : ℂ) * (s : ℂ))) / ((σ : ℂ) + I * (s : ℂ))

lemma phase_arg (α t : ℝ) : I * (α : ℂ) * (t : ℂ) = I * ((α * t : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul]; ring

lemma oscG_eq (α σ x : ℝ) : oscG α σ x = oscUp α x * oscV σ x := by
  unfold oscG oscUp oscV
  rw [div_eq_mul_inv]
  congr 1
  congr 1
  ring

lemma norm_phase_exp (α t : ℝ) : ‖cexp (I * (α : ℂ) * (t : ℂ))‖ = 1 := by
  rw [phase_arg]
  simpa [mul_comm, mul_left_comm, mul_assoc] using Complex.norm_exp_ofReal_mul_I (α * t)

lemma norm_I_mul_ofReal (α : ℝ) : ‖I * (α : ℂ)‖ = |α| := by simp

lemma sigma_add_I_norm_sq (σ t : ℝ) : ‖((σ : ℂ) + I * (t : ℂ) : ℂ)‖ ^ 2 = σ ^ 2 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [sq]

lemma sigma_add_I_norm_ge (σ t : ℝ) (ht : 0 ≤ t) : t ≤ ‖((σ : ℂ) + I * (t : ℂ) : ℂ)‖ := by
  have hsq : t ^ 2 ≤ ‖((σ : ℂ) + I * (t : ℂ) : ℂ)‖ ^ 2 := by
    rw [sigma_add_I_norm_sq]; nlinarith [sq_nonneg σ]
  have hs := (sq_le_sq.mp hsq)
  simpa [abs_of_nonneg ht, abs_of_nonneg (norm_nonneg _)] using hs

lemma oscV_norm_le (σ t : ℝ) (hσ : σ ≠ 0) (ht : 1 ≤ t) : ‖oscV σ t‖ ≤ t⁻¹ := by
  unfold oscV
  rw [norm_inv]
  have ht0 : 0 < t := by linarith
  have hz0 : 0 < ‖((σ : ℂ) + I * (t : ℂ) : ℂ)‖ := norm_pos_iff.mpr (sigma_add_I_ne_zero σ t hσ)
  exact (inv_le_inv₀ hz0 ht0).mpr (sigma_add_I_norm_ge σ t (by linarith))

lemma oscV_norm_sq (σ t : ℝ) : ‖oscV σ t‖ ^ 2 = (σ ^ 2 + t ^ 2)⁻¹ := by
  unfold oscV
  rw [norm_inv, inv_pow, sigma_add_I_norm_sq]

lemma oscU_norm (α t : ℝ) : ‖oscU α t‖ = (|α|)⁻¹ := by
  unfold oscU oscUp
  calc
    ‖cexp (I * (α : ℂ) * (t : ℂ)) / (I * (α : ℂ))‖ = ‖cexp (I * (α : ℂ) * (t : ℂ))‖ / ‖I * (α : ℂ)‖ := by rw [norm_div]
    _ = 1 / |α| := by
      rw [norm_phase_exp, norm_I_mul_ofReal]
    _ = (|α|)⁻¹ := by simp

lemma oscR_norm_le (α σ t : ℝ) : ‖oscR α σ t‖ ≤ (|α|)⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ := by
  unfold oscR
  calc
    ‖oscU α t * (-(I : ℂ) * (oscV σ t) ^ 2)‖ ≤ ‖oscU α t‖ * ‖-(I : ℂ) * (oscV σ t) ^ 2‖ := norm_mul_le _ _
    _ = (|α|)⁻¹ * ‖(oscV σ t) ^ 2‖ := by
      have hnorm : ‖-(I : ℂ) * (oscV σ t) ^ 2‖ = ‖(oscV σ t) ^ 2‖ := by
        rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
      rw [oscU_norm, hnorm]
    _ = (|α|)⁻¹ * ((σ ^ 2 + t ^ 2)⁻¹) := by rw [norm_pow, oscV_norm_sq]

lemma oscW_norm_le (α σ t : ℝ) (hσ : σ ≠ 0) (ht : 1 ≤ t) : ‖oscW α σ t‖ ≤ (|α| * t)⁻¹ := by
  unfold oscW
  calc
    ‖oscU α t * oscV σ t‖ ≤ ‖oscU α t‖ * ‖oscV σ t‖ := norm_mul_le _ _
    _ = (|α|)⁻¹ * ‖oscV σ t‖ := by rw [oscU_norm]
    _ ≤ (|α|)⁻¹ * t⁻¹ := mul_le_mul_of_nonneg_left (oscV_norm_le σ t hσ ht) (inv_nonneg.mpr (abs_nonneg α))
    _ = (|α| * t)⁻¹ := by rw [← mul_inv]

lemma oscW_norm_bound (α σ t T : ℝ) (hα : α ≠ 0) (hσ : σ ≠ 0) (htT : T ≤ t) (hT : 1 ≤ T) :
    ‖oscW α σ t‖ ≤ (|α| * T)⁻¹ := by
  have h1 := oscW_norm_le α σ t hσ (le_trans hT htT)
  refine le_trans h1 ?_
  have hle : |α| * T ≤ |α| * t := mul_le_mul_of_nonneg_left htT (abs_nonneg α)
  have hbpos : 0 < |α| * t := mul_pos (abs_pos.mpr hα) (lt_of_lt_of_le zero_lt_one (le_trans hT htT))
  have hapos : 0 < |α| * T := mul_pos (abs_pos.mpr hα) (lt_of_lt_of_le zero_lt_one hT)
  exact (inv_le_inv₀ hbpos hapos).mpr hle

lemma cont_oscUp (α : ℝ) : Continuous (oscUp α) := by unfold oscUp; fun_prop
lemma cont_oscV (σ : ℝ) (hσ : σ ≠ 0) : Continuous (oscV σ) := by
  unfold oscV
  exact (by fun_prop : Continuous fun s : ℝ => ((σ : ℂ) + I * (s : ℂ) : ℂ)).inv₀ (fun s => sigma_add_I_ne_zero σ s hσ)
lemma cont_oscU (α : ℝ) : Continuous (oscU α) := by unfold oscU; exact (cont_oscUp α).div_const (I * (α : ℂ))
lemma cont_oscR (α σ : ℝ) (hσ : σ ≠ 0) : Continuous (oscR α σ) := by
  unfold oscR
  exact (cont_oscU α).mul ((continuous_const.mul ((cont_oscV σ hσ).pow 2)))
lemma hasDerivAt_oscU (α : ℝ) (hα : α ≠ 0) : ∀ t, HasDerivAt (oscU α) (oscUp α t) t := by
  intro t; unfold oscU oscUp; simpa using deriv_cexp_div α hα t
lemma hasDerivAt_oscV (σ : ℝ) (hσ : σ ≠ 0) : ∀ t, HasDerivAt (oscV σ) (-(I : ℂ) * (oscV σ t) ^ 2) t := by
  intro t; unfold oscV; simpa using deriv_sigma_add_I_inv σ hσ t
lemma hasDerivAt_oscW (α σ : ℝ) (hα : α ≠ 0) (hσ : σ ≠ 0) : ∀ t,
    HasDerivAt (oscU α * oscV σ) (oscUp α t * oscV σ t + oscU α t * (-(I : ℂ) * (oscV σ t) ^ 2)) t := by
  intro t
  exact (hasDerivAt_oscU α hα t).mul (hasDerivAt_oscV σ hσ t)

lemma integral_osc_main (α σ T R : ℝ) (hα : α ≠ 0) (hσ : σ ≠ 0) :
    (∫ t in T..R, (oscUp α t * oscV σ t + oscU α t * (-(I : ℂ) * (oscV σ t) ^ 2)))
      = (oscU α * oscV σ) R - (oscU α * oscV σ) T := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := oscU α * oscV σ)
    (f' := fun t => oscUp α t * oscV σ t + oscU α t * (-(I : ℂ) * (oscV σ t) ^ 2))
  · intro x hx
    exact hasDerivAt_oscW α σ hα hσ x
  · exact (((cont_oscUp α).mul (cont_oscV σ hσ)).add (cont_oscR α σ hσ)).intervalIntegrable T R

lemma osc_integral_identity (α σ T R : ℝ) (hα : α ≠ 0) (hσ : σ ≠ 0) :
    (∫ t in T..R, oscG α σ t) = (oscW α σ R - oscW α σ T) - ∫ t in T..R, oscR α σ t := by
  have hFTC := integral_osc_main α σ T R hα hσ
  have hsplit :
      (∫ t in T..R, (oscUp α t * oscV σ t + oscU α t * (-(I : ℂ) * (oscV σ t) ^ 2)))
        = (∫ t in T..R, oscUp α t * oscV σ t) + ∫ t in T..R, oscU α t * (-(I : ℂ) * (oscV σ t) ^ 2) := by
    exact intervalIntegral.integral_add (μ := volume)
      (((cont_oscUp α).mul (cont_oscV σ hσ)).intervalIntegrable T R)
      ((cont_oscR α σ hσ).intervalIntegrable T R)
  have hrewrite : (∫ t in T..R, oscUp α t * oscV σ t) = ∫ t in T..R, oscG α σ t := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact (oscG_eq α σ x).symm
  rw [hsplit, hrewrite] at hFTC
  change (∫ t in T..R, oscG α σ t) + ∫ t in T..R, oscR α σ t = oscW α σ R - oscW α σ T at hFTC
  rw [eq_sub_iff_add_eq]
  exact hFTC

lemma inv_sigma_add_sq_le_inv_sq (σ t : ℝ) (ht : 1 ≤ t) : (σ ^ 2 + t ^ 2)⁻¹ ≤ (t ^ 2)⁻¹ := by
  have ht0 : 0 < t := by linarith
  have hle : t ^ 2 ≤ σ ^ 2 + t ^ 2 := by nlinarith [sq_nonneg σ]
  have hpos1 : 0 < σ ^ 2 + t ^ 2 := by nlinarith [sq_nonneg σ]
  have hpos2 : 0 < t ^ 2 := sq_pos_of_pos ht0
  exact (inv_le_inv₀ hpos1 hpos2).mpr hle

lemma continuous_inv_sigma_add_sq (σ : ℝ) (hσ : σ ≠ 0) : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ := by
  refine Continuous.inv₀ ?hf ?h0
  · fun_prop
  · intro t
    have hpos : 0 < σ ^ 2 + t ^ 2 := by
      have h1 : 0 < σ ^ 2 := sq_pos_of_ne_zero hσ
      nlinarith
    exact ne_of_gt hpos

lemma integral_inv_sq_of_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in a..b, (t ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hint : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ ?hf ?h0
    · exact (by fun_prop : Continuous fun t : ℝ => (t : ℝ) ^ 2).continuousOn
    · intro x hx
      have hmin : min a b ≤ x := hx.1
      have hpos : 0 < min a b := lt_min ha hb
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hpos hmin))
  have hintN : IntervalIntegrable (fun t : ℝ => -(t ^ 2)⁻¹) volume a b := by
    exact IntervalIntegrable.neg hint
  have hFTC : (∫ t in a..b, -(t ^ 2)⁻¹) = (fun x : ℝ => x⁻¹) b - (fun x : ℝ => x⁻¹) a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => x⁻¹)
      (f' := fun t : ℝ => -(t ^ 2)⁻¹)
      (by
        intro x hx
        have hx0 : x ≠ 0 := by
          have hmin : min a b ≤ x := hx.1
          have hpos : 0 < min a b := lt_min ha hb
          exact ne_of_gt (lt_of_lt_of_le hpos hmin)
        exact hasDerivAt_inv hx0)
      hintN
  have hneg : (∫ t in a..b, -(t ^ 2)⁻¹) = -(∫ t in a..b, (t ^ 2)⁻¹) := by
    rw [intervalIntegral.integral_neg]
  rw [hneg] at hFTC
  linarith

lemma integrable_inv_sq_Icc (T R : ℝ) (hT : 0 < T) (hTR : T ≤ R) :
    IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume T R := by
  refine ContinuousOn.intervalIntegrable_of_Icc hTR ?_
  refine ContinuousOn.inv₀ ?hf ?h0
  · exact (by fun_prop : Continuous fun t : ℝ => (t : ℝ) ^ 2).continuousOn
  · intro x hx
    have hT0 : 0 < x := lt_of_lt_of_le hT hx.1
    exact pow_ne_zero 2 (ne_of_gt hT0)

lemma integral_inv_sigma_add_sq_le (σ T R : ℝ) (hσ : σ ≠ 0) (hT : 1 ≤ T) (hTR : T ≤ R) :
    (∫ t in T..R, (σ ^ 2 + t ^ 2)⁻¹) ≤ T⁻¹ := by
  have hmono : (∫ t in T..R, (σ ^ 2 + t ^ 2)⁻¹) ≤ ∫ t in T..R, (t ^ 2)⁻¹ := by
    refine intervalIntegral.integral_mono_on hTR ?hf ?hg ?h
    · exact (continuous_inv_sigma_add_sq σ hσ).intervalIntegrable T R
    · exact integrable_inv_sq_Icc T R (by linarith) hTR
    · intro x hx
      exact inv_sigma_add_sq_le_inv_sq σ x (le_trans hT hx.1)
  have hval : (∫ t in T..R, (t ^ 2)⁻¹) = T⁻¹ - R⁻¹ :=
    integral_inv_sq_of_pos T R (by linarith) (by linarith)
  rw [hval] at hmono
  have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr (by linarith)
  linarith

lemma oscR_integral_norm_le (α σ T R : ℝ) (hσ : σ ≠ 0) (hT : 1 ≤ T) (hTR : T ≤ R) :
    ‖∫ t in T..R, oscR α σ t‖ ≤ (|α|)⁻¹ * T⁻¹ := by
  calc
    ‖∫ t in T..R, oscR α σ t‖ ≤ ∫ t in T..R, ‖oscR α σ t‖ := intervalIntegral.norm_integral_le_integral_norm hTR
    _ ≤ ∫ t in T..R, (|α|)⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ := by
      exact intervalIntegral.integral_mono_on hTR
        (((cont_oscR α σ hσ).norm).intervalIntegrable T R)
        (((continuous_const.mul (continuous_inv_sigma_add_sq σ hσ))).intervalIntegrable T R)
        (fun x hx => oscR_norm_le α σ x)
    _ = (|α|)⁻¹ * (∫ t in T..R, (σ ^ 2 + t ^ 2)⁻¹) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (|α|)⁻¹ * T⁻¹ := mul_le_mul_of_nonneg_left (integral_inv_sigma_add_sq_le σ T R hσ hT hTR)
        (inv_nonneg.mpr (abs_nonneg α))

end PerronSigma

/-! The oscillatory tail bound with general `0 < σ`. -/
theorem perronKernelSigma_oscTail (σ T R α : ℝ) (hσ : 0 < σ) (hα : α ≠ 0) (hT : 1 ≤ T) (hTR : T ≤ R) :
    ‖(∫ (t : ℝ) in T..R, Complex.exp (Complex.I * (↑α * ↑t)) / ((σ : ℂ) + Complex.I * ↑t))‖ ≤
      3 / (|α| * T) := by
  have hσnz : σ ≠ 0 := ne_of_gt hσ
  have hconv : (∫ t in T..R, Complex.exp (Complex.I * (↑α * ↑t)) / ((σ : ℂ) + Complex.I * ↑t))
      = ∫ t in T..R, PerronSigma.oscG α σ t := by
    apply intervalIntegral.integral_congr
    intro x hx
    rfl
  rw [hconv]
  have hbound : ‖PerronSigma.oscW α σ R - PerronSigma.oscW α σ T‖ ≤ 2 * (|α| * T)⁻¹ := by
    calc
      ‖PerronSigma.oscW α σ R - PerronSigma.oscW α σ T‖ ≤ ‖PerronSigma.oscW α σ R‖ + ‖PerronSigma.oscW α σ T‖ := norm_sub_le _ _
      _ ≤ 2 * (|α| * T)⁻¹ := by
        have h1 := PerronSigma.oscW_norm_bound α σ R T hα hσnz hTR hT
        have h2 := PerronSigma.oscW_norm_bound α σ T T hα hσnz le_rfl hT
        nlinarith
  have hint : ‖∫ t in T..R, PerronSigma.oscR α σ t‖ ≤ (|α| * T)⁻¹ := by
    have h := PerronSigma.oscR_integral_norm_le α σ T R hσnz hT hTR
    rwa [← mul_inv] at h
  have hmain : ‖∫ t in T..R, PerronSigma.oscG α σ t‖ ≤ 3 * (|α| * T)⁻¹ := by
    calc
      ‖∫ t in T..R, PerronSigma.oscG α σ t‖ = ‖(PerronSigma.oscW α σ R - PerronSigma.oscW α σ T)
          - ∫ t in T..R, PerronSigma.oscR α σ t‖ := by
          rw [PerronSigma.osc_integral_identity α σ T R hα hσnz]
      _ ≤ ‖PerronSigma.oscW α σ R - PerronSigma.oscW α σ T‖ + ‖∫ t in T..R, PerronSigma.oscR α σ t‖ := norm_sub_le _ _
      _ ≤ 2 * (|α| * T)⁻¹ + (|α| * T)⁻¹ := add_le_add hbound hint
      _ = 3 * (|α| * T)⁻¹ := by ring
  rw [div_eq_mul_inv]
  exact hmain

end Commons.Analysis.Fourier