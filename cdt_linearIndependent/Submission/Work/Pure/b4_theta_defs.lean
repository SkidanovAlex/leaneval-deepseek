import Mathlib
import Submission.Work.Pure.b4_defs
import Submission.Work.Pure.b4_B2_ode

/-!
# Shared `x`-side data for the `Θ`-bridge of the pure function `B₄`

Calegari--Dimitrov--Tang, arXiv:2408.15403, §`sec:lindep`.  All series here are power series
in `x` (`PowerSeries ℚ`); the symmetrization coordinate is `y = x²/(x-1) = sympY`, the
involutive Möbius map is `φ = x/(x-1) = sympPhi`, and `w = x - φ = sympW`.

Contents (all proved, no axioms):

* the unit `b4Unit = (x-1)⁻¹` and its basic identities (in particular `derivative b4Unit = -b4Unit²`);
* the symmetrization data: `sympPhi = X·b4Unit`, `sympY = X²·b4Unit`,
  `sympW = X(X-2)·b4Unit` (hence nonzero), the derivatives
  `sympY' = sympW·b4Unit`, `sympPhi' = -b4Unit²`, and the algebraic identities
  `sympY(4-sympY) = -sympW²`, `sympW(2-X) = X(4-sympY)`, `(X-1)(1-sympPhi') = -(2-sympY)`;
* `Ψ = Li₂(x) - Li₂(φ)` (so that `b4Theta = sympW·Ψ`), and the first-order identities
  `(1-X)·b4L' = -1`, `X·b4Li₂' = -b4L` (coefficientwise), and the chain-rule consequence
  `b4L.subst sympPhi = -b4L` (via `derivative_subst`).
-/

namespace Work.Pure

open PowerSeries

noncomputable section

/-- `u = (x-1)⁻¹`, the unit of `ℚ⟦x⟧` in which the symmetrization `x ↦ x/(x-1)` is written. -/
def b4Unit : PowerSeries ℚ := ((X : PowerSeries ℚ) - 1)⁻¹

/-- `Ψ = Li₂(x) - Li₂(φ(x))`, the second factor of `b4Theta = (x - φ)·Ψ`. -/
def b4Psi : PowerSeries ℚ := b4Li2 - b4Li2.subst Submission.CDT.sympPhi

/-- `b4Theta = sympW · Ψ` (definitional). -/
lemma b4Theta_eq : b4Theta = Submission.CDT.sympW * b4Psi := rfl

/-! ## The unit `u = (x-1)⁻¹` -/

lemma b4Unit_mul : b4Unit * ((X : PowerSeries ℚ) - 1) = 1 :=
  PowerSeries.inv_mul_cancel _ (by simp)

lemma mul_b4Unit : ((X : PowerSeries ℚ) - 1) * b4Unit = 1 :=
  PowerSeries.mul_inv_cancel _ (by simp)

lemma b4Unit_ne_zero : b4Unit ≠ 0 := by
  intro h
  have hh := b4Unit_mul
  rw [h, zero_mul] at hh
  exact one_ne_zero hh.symm

lemma sub_one_ne_zero : ((X : PowerSeries ℚ) - 1) ≠ 0 := by
  intro h
  have h0 : PowerSeries.constantCoeff ((X : PowerSeries ℚ) - 1) = 0 := by rw [h]; simp
  rw [map_sub, PowerSeries.constantCoeff_X, map_one] at h0
  norm_num at h0

lemma X_sub_two_ne_zero : ((X : PowerSeries ℚ) - 2) ≠ 0 := by
  intro h
  have h0 : PowerSeries.constantCoeff ((X : PowerSeries ℚ) - 2) = 0 := by rw [h]; simp
  rw [map_sub, PowerSeries.constantCoeff_X, map_ofNat] at h0
  norm_num at h0

lemma derivative_b4Unit : (PowerSeries.derivative (R := ℚ)) b4Unit = -(b4Unit ^ 2) := by
  rw [b4Unit, PowerSeries.derivative_inv']
  simp

/-- Leibniz rule for the (formal) derivative of `ℚ⟦x⟧`. -/
lemma b4_deriv_mul (f g : PowerSeries ℚ) :
    (PowerSeries.derivative (R := ℚ)) (f * g)
      = f * (PowerSeries.derivative (R := ℚ)) g + (PowerSeries.derivative (R := ℚ)) f * g := by
  rw [Derivation.leibniz]
  simp [smul_eq_mul, mul_comm]

/-! ## The symmetrization data -/

lemma sympPhi_eq_mul : Submission.CDT.sympPhi = (X : PowerSeries ℚ) * b4Unit := rfl

lemma sympY_eq_Xsq : Submission.CDT.sympY = (X : PowerSeries ℚ) ^ 2 * b4Unit := by
  rw [show Submission.CDT.sympY = (X : PowerSeries ℚ) * Submission.CDT.sympPhi from rfl,
      sympPhi_eq_mul]
  ring

lemma sympW_eq : Submission.CDT.sympW = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * b4Unit := by
  rw [show Submission.CDT.sympW = (X : PowerSeries ℚ) - Submission.CDT.sympPhi from rfl,
      sympPhi_eq_mul]
  linear_combination (-(X)) * mul_b4Unit

lemma sympW_ne_zero : Submission.CDT.sympW ≠ 0 := by
  rw [sympW_eq]
  exact mul_ne_zero (mul_ne_zero PowerSeries.X_ne_zero X_sub_two_ne_zero) b4Unit_ne_zero

lemma derivative_sympPhi : (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi = -(b4Unit ^ 2) := by
  rw [sympPhi_eq_mul, b4_deriv_mul, PowerSeries.derivative_X, derivative_b4Unit]
  linear_combination (-b4Unit) * mul_b4Unit

lemma derivative_sympY : (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympY
    = Submission.CDT.sympW * b4Unit := by
  rw [show Submission.CDT.sympY = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) * b4Unit) by
        rw [show Submission.CDT.sympY = (X : PowerSeries ℚ) * Submission.CDT.sympPhi from rfl,
            sympPhi_eq_mul]]
  rw [b4_deriv_mul, b4_deriv_mul, PowerSeries.derivative_X, derivative_b4Unit]
  rw [show Submission.CDT.sympW = (X : PowerSeries ℚ) - (X : PowerSeries ℚ) * b4Unit by
        rw [show Submission.CDT.sympW = (X : PowerSeries ℚ) - Submission.CDT.sympPhi from rfl,
            sympPhi_eq_mul]]
  linear_combination (-(X * b4Unit)) * mul_b4Unit

lemma sympY_mul_four_sub : Submission.CDT.sympY * (4 - Submission.CDT.sympY)
    = -(Submission.CDT.sympW ^ 2) := by
  rw [Submission.CDT.symp_w_sq]; ring

lemma sympW_mul_two_sub_X : Submission.CDT.sympW * (2 - X)
    = (X : PowerSeries ℚ) * (4 - Submission.CDT.sympY) := by
  rw [sympW_eq, sympY_eq_Xsq]
  linear_combination (4 * X) * mul_b4Unit

lemma derivative_one_sub_sympPhi :
    ((X : PowerSeries ℚ) - 1) * (1 - (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi)
      = -(2 - Submission.CDT.sympY) := by
  rw [derivative_sympPhi, sympY_eq_Xsq]
  linear_combination (b4Unit - (X + 1)) * mul_b4Unit

/-! ## Substitution of `u` and of `b4L` along `φ` -/

lemma subst_one_sympPhi : PowerSeries.subst Submission.CDT.sympPhi (1 : PowerSeries ℚ) = 1 := by
  rw [show (1 : PowerSeries ℚ) = PowerSeries.C 1 from rfl,
      Submission.CDT.C_subst_eq ℚ 1 Submission.CDT.sympPhi Submission.CDT.sympPhi_hasSubst]

lemma subst_b4Unit : PowerSeries.subst Submission.CDT.sympPhi b4Unit = (X : PowerSeries ℚ) - 1 := by
  have hφ := Submission.CDT.sympPhi_hasSubst
  have h0 : (Submission.CDT.sympPhi - 1) * PowerSeries.subst Submission.CDT.sympPhi b4Unit = 1 := by
    have h1 : (Submission.CDT.sympPhi - 1)
        = PowerSeries.subst Submission.CDT.sympPhi ((X : PowerSeries ℚ) - 1) := by
      rw [PowerSeries.subst_sub hφ, PowerSeries.subst_X hφ, subst_one_sympPhi]
    rw [h1, ← PowerSeries.subst_mul hφ, mul_b4Unit]
    exact subst_one_sympPhi
  have h2 : (Submission.CDT.sympPhi - 1) * ((X : PowerSeries ℚ) - 1) = 1 := by
    have h := Submission.CDT.sympPhi_mul_sub_one
    rw [show (Submission.CDT.sympPhi - 1) * ((X : PowerSeries ℚ) - 1)
        = Submission.CDT.sympPhi * ((X : PowerSeries ℚ) - 1) - ((X : PowerSeries ℚ) - 1) by ring, h]
    ring
  have hne : Submission.CDT.sympPhi - 1 ≠ 0 := by
    intro h
    have h0 : PowerSeries.constantCoeff (Submission.CDT.sympPhi - 1) = 0 := by rw [h]; simp
    rw [map_sub, map_one] at h0
    have h1 : PowerSeries.constantCoeff Submission.CDT.sympPhi = 0 := by
      show PowerSeries.constantCoeff ((X : PowerSeries ℚ) * b4Unit) = 0
      rw [map_mul, PowerSeries.constantCoeff_X, zero_mul]
    rw [h1] at h0
    norm_num at h0
  exact mul_left_cancel₀ hne (h0.trans h2.symm)

/-! ## The two coefficient identities for `b4L` and `b4Li2` -/

theorem b4L_deriv : ((1 : PowerSeries ℚ) - PowerSeries.X) * PowerSeries.derivative (R := ℚ) b4L = -1 := by
  ext n
  rw [show ((1 : PowerSeries ℚ) - PowerSeries.X) * (PowerSeries.derivative (R := ℚ)) b4L
        = (PowerSeries.derivative (R := ℚ)) b4L
          - PowerSeries.X * (PowerSeries.derivative (R := ℚ)) b4L by ring]
  rw [map_sub, PowerSeries.coeff_derivative]
  rcases n with _ | k
  · rw [PowerSeries.coeff_zero_X_mul, coeff_b4L, map_neg, PowerSeries.coeff_one]
    norm_num
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, coeff_b4L, coeff_b4L,
        map_neg, PowerSeries.coeff_one]
    push_cast
    field_simp
    ring

theorem b4Li2_deriv : (PowerSeries.X : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) b4Li2 = -b4L := by
  ext n
  rcases n with _ | k
  · rw [PowerSeries.coeff_zero_X_mul, map_neg, coeff_b4L]
    norm_num
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, coeff_b4Li2, map_neg,
        coeff_b4L]
    push_cast
    field_simp

/-- `b4L' = u`, the form in which the two coefficient identities are used. -/
lemma deriv_b4L : (PowerSeries.derivative (R := ℚ)) b4L = b4Unit := by
  have h : ((X : PowerSeries ℚ) - 1) * (PowerSeries.derivative (R := ℚ)) b4L = 1 := by
    have h2 := b4L_deriv
    rw [show ((X : PowerSeries ℚ) - 1) = -((1 : PowerSeries ℚ) - X) by ring, neg_mul, h2]
    ring
  calc (PowerSeries.derivative (R := ℚ)) b4L
      = b4Unit * (((X : PowerSeries ℚ) - 1) * (PowerSeries.derivative (R := ℚ)) b4L) := by
          rw [← mul_assoc, b4Unit_mul, one_mul]
    _ = b4Unit := by rw [h, mul_one]

lemma constantCoeff_sympPhi_eq_zero : PowerSeries.constantCoeff Submission.CDT.sympPhi = 0 := by
  show PowerSeries.constantCoeff ((X : PowerSeries ℚ) * b4Unit) = 0
  rw [map_mul, PowerSeries.constantCoeff_X, zero_mul]

lemma constantCoeff_subst_b4L :
    PowerSeries.constantCoeff (PowerSeries.subst Submission.CDT.sympPhi b4L) = 0 := by
  rw [PowerSeries.constantCoeff_eq]
  exact PowerSeries.constantCoeff_subst_eq_zero (a := Submission.CDT.sympPhi)
    (by
      show PowerSeries.constantCoeff Submission.CDT.sympPhi = 0
      exact constantCoeff_sympPhi_eq_zero)
    b4L (by simp [b4L])

/-- **`log(1-x)` is anti-invariant under `x ↦ x/(x-1)`**: `b4L∘φ = -b4L`.

Proof.  Let `F = b4L∘φ + b4L`.  Differentiating (`derivative_subst`) and using
`b4L' = u`, `(u∘φ) = X-1`, `φ' = -u²` gives `F' = (X-1)·(-u²) + u = -u + u = 0`;
and `F` has zero constant term, so `F = 0` by `PowerSeries.derivative.ext`. -/
theorem b4L_subst_sympPhi : b4L.subst Submission.CDT.sympPhi = -b4L := by
  have hdF : (PowerSeries.derivative (R := ℚ)) (b4L.subst Submission.CDT.sympPhi + b4L) = 0 := by
    rw [map_add, PowerSeries.derivative_subst Submission.CDT.sympPhi_hasSubst, deriv_b4L,
        derivative_sympPhi, subst_b4Unit]
    linear_combination (-b4Unit) * mul_b4Unit
  have hcF : PowerSeries.constantCoeff (b4L.subst Submission.CDT.sympPhi + b4L) = 0 := by
    rw [map_add, constantCoeff_subst_b4L]
    simp [b4L]
  have hF : b4L.subst Submission.CDT.sympPhi + b4L = 0 := by
    apply PowerSeries.derivative.ext (g := 0)
    · rw [hdF]; simp
    · rw [hcF, PowerSeries.constantCoeff_zero]
  exact eq_neg_of_add_eq_zero_left hF

end

end Work.Pure
