import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.r2_setup
import Submission.Work.Deep.Nibble.log_one_sub_bound

/-!
# Numerical helper lemmas for `r2_num_basic`

Elementary real-analysis estimates used to prove the asymptotic side conditions
`Work.Deep.Nibble.r2_num_basic`: exponential/quadratic bounds, a reciprocal form
of `exp (-x) ≤ ...`, and the lower bound on the residual level `Dlev`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Deep.Nibble

/-- `x ≤ exp x` for `x ≥ 0`. -/
lemma r2nb_exp_ge_self {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.exp x := by
  have := Real.add_one_le_exp x
  linarith

/-- `x ^ 2 / 4 ≤ exp x` for `x ≥ 0`. -/
lemma r2nb_exp_ge_sq {x : ℝ} (hx : 0 ≤ x) : x^2/4 ≤ Real.exp x := by
  have hhalf : 0 ≤ x/2 := by linarith
  have h2 : x/2 ≤ Real.exp (x/2) := by
    have := Real.add_one_le_exp (x/2)
    linarith
  have h3 : (x/2)*(x/2) ≤ Real.exp (x/2) * Real.exp (x/2) := mul_self_le_mul_self hhalf h2
  have h4 : Real.exp (x/2) * Real.exp (x/2) = Real.exp x := by
    rw [← Real.exp_add]; ring_nf
  have hkey : x^2/4 = (x/2)*(x/2) := by ring
  rw [hkey]
  calc (x/2)*(x/2) ≤ Real.exp (x/2) * Real.exp (x/2) := h3
    _ = Real.exp x := h4

/-- `x ^ 4 / 256 ≤ exp x` for `x ≥ 0`. -/
lemma r2nb_exp_ge_biquad {x : ℝ} (hx : 0 ≤ x) : x^4/256 ≤ Real.exp x := by
  have h := r2nb_exp_ge_sq (x := x/2) (by linarith)
  have hnn : 0 ≤ (x/2)^2/4 := by positivity
  have h2 : ((x/2)^2/4) * ((x/2)^2/4) ≤ Real.exp (x/2) * Real.exp (x/2) :=
    mul_self_le_mul_self hnn h
  have hexp : Real.exp (x/2) * Real.exp (x/2) = Real.exp x := by
    rw [← Real.exp_add]; ring_nf
  have hkey : ((x/2)^2/4) * ((x/2)^2/4) = x^4/256 := by ring
  rw [hkey, hexp] at h2
  exact h2

/-- If `0 < Y ≤ exp x` then `exp (-x) ≤ 1 / Y`. -/
lemma r2nb_exp_neg_le_inv {x Y : ℝ} (hY : 0 < Y) (h : Y ≤ Real.exp x) :
    Real.exp (-x) ≤ 1/Y := by
  have hE : 0 < Real.exp x := Real.exp_pos x
  have h1 : 1 ≤ Y⁻¹ * Real.exp x := by
    have h2 := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hY.le)
    rwa [inv_mul_cancel₀ hY.ne'] at h2
  rw [Real.exp_neg, one_div, inv_le_iff_one_le_mul₀ hE]
  exact h1

/-- The residual level `Dlev r θ D` is at least `D * exp (-(2 θ r))`. -/
lemma r2nb_dlev_ge {r : ℕ} {θ : ℝ} (hr : 1 ≤ r) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1/2)
    {D : ℕ} (hD : 1 ≤ D) :
    (D:ℝ) * Real.exp (-(2*θ*(r:ℝ))) ≤ Dlev r θ D := by
  rw [Dlev]
  have hr1R : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  have hD1R : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hx0 : 0 ≤ θ/(D:ℝ) := by positivity
  have hx1 : θ/(D:ℝ) ≤ 1/2 := by
    have h : θ/(D:ℝ) ≤ θ := div_le_self hθ0.le hD1R
    linarith
  have hbase : 0 < 1 - θ/(D:ℝ) := by linarith
  have hlog : -2 * (θ/(D:ℝ)) ≤ Real.log (1 - θ/(D:ℝ)) := log_one_sub_bound hx0 hx1
  have hncast : (((r-1)*(D-1) : ℕ) : ℝ) = ((r:ℝ)-1)*((D:ℝ)-1) := by
    rw [Nat.cast_mul, Nat.cast_sub hr, Nat.cast_sub hD]
    norm_num
  have hn0 : (0:ℝ) ≤ (((r-1)*(D-1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hlog hn0
  have hDn : ((r:ℝ)-1) * ((D:ℝ)-1) / (D:ℝ) ≤ (r:ℝ) := by
    have h1 : ((D:ℝ)-1)/(D:ℝ) ≤ 1 := by
      rw [div_le_one hDpos]; linarith
    have hrm1 : 0 ≤ (r:ℝ)-1 := by linarith
    calc ((r:ℝ)-1) * ((D:ℝ)-1) / (D:ℝ) = ((r:ℝ)-1) * (((D:ℝ)-1)/(D:ℝ)) := by ring
      _ ≤ ((r:ℝ)-1) * 1 := mul_le_mul_of_nonneg_left h1 hrm1
      _ ≤ (r:ℝ) := by linarith
  have hstep : -(2*θ*(r:ℝ)) ≤ (((r-1)*(D-1) : ℕ) : ℝ) * (-2*(θ/(D:ℝ))) := by
    rw [hncast]
    have hrew : ((r:ℝ)-1) * ((D:ℝ)-1) * (-2*(θ/(D:ℝ))) =
        -(2*θ) * (((r:ℝ)-1) * ((D:ℝ)-1) / (D:ℝ)) := by ring_nf
    rw [hrew]
    have hmono := mul_le_mul_of_nonneg_left hDn (by positivity : (0:ℝ) ≤ 2*θ)
    linarith
  have hcomb : -(2*θ*(r:ℝ)) ≤ (((r-1)*(D-1) : ℕ) : ℝ) * Real.log (1 - θ/(D:ℝ)) :=
    le_trans hstep hmul
  have hlogp : (((r-1)*(D-1) : ℕ) : ℝ) * Real.log (1 - θ/(D:ℝ)) =
      Real.log ((1 - θ/(D:ℝ)) ^ ((r-1)*(D-1))) := by
    rw [Real.log_pow]
  have hexp : Real.exp (-(2*θ*(r:ℝ))) ≤ (1 - θ/(D:ℝ)) ^ ((r-1)*(D-1)) := by
    calc Real.exp (-(2*θ*(r:ℝ)))
        ≤ Real.exp ((((r-1)*(D-1) : ℕ) : ℝ) * Real.log (1 - θ/(D:ℝ))) :=
          Real.exp_le_exp.mpr hcomb
      _ = Real.exp (Real.log ((1 - θ/(D:ℝ)) ^ ((r-1)*(D-1)))) := by rw [hlogp]
      _ = (1 - θ/(D:ℝ)) ^ ((r-1)*(D-1)) := Real.exp_log (pow_pos hbase _)
  calc (D:ℝ) * Real.exp (-(2*θ*(r:ℝ)))
      ≤ (D:ℝ) * (1 - θ/(D:ℝ)) ^ ((r-1)*(D-1)) := mul_le_mul_of_nonneg_left hexp hDpos.le

/-- If `0 < Y ≤ exp x` then `Y * exp (-x) ≤ 1`. -/
lemma r2nb_mul_exp_neg_le_one {x Y : ℝ} (hY : 0 < Y) (h : Y ≤ Real.exp x) :
    Y * Real.exp (-x) ≤ 1 := by
  have h2 : Y * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) :=
    mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  have h3 : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  linarith

end Work.Deep.Nibble
