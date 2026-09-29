import Mathlib
import Submission.Work.Pure.b4_aux
import Submission.Work.Pure.b4_W_sq
import Submission.Work.Pure.b4_B2_ode
import Submission.Work.Pure.b4_Fser_eq
import Submission.Work.Pure.b4_eq_prod
import Submission.Work.Pure.b4_Fser_ode

/-!
# The first-order differential relation satisfied by `B₄`

CDT arXiv:2408.15403, §`sec:lindep`, eq. `(diffformulas)`:

  `y(4−y)·B₄'(y) = (2−y)·B₄(y) + (4−y)·B₂(y) − 2y(4−y)`.

Strategy.  Write `B₄ = 4·y·Fser·fG` (the double-binomial coefficient of `B₄` is the
`k`-convolution of `Fser = Σ C(2k,k)yᵏ/((2k-1)16ᵏ)` and `fG = Σ C(2k,k)yᵏ/((2k+1)²16ᵏ)`),
and `B₂ = 2y + 2y·Fser·fA` with `fA = Σ C(2k,k)yᵏ/((2k+1)16ᵏ)`.  The two closed forms of `B₂`
are identified through the (unique) power-series solution of the inhomogeneous equation
`X(4−X)g' = (2−X)g + X²`, which `B₂` satisfies (`b4_B2_ode`).  The relation itself then
reduces to the three elementary identities `2(4−X)Fser' + Fser = 0`, `fA = fG + 2X fG'`,
`(4−X)W² = 4` (hence `Fser·W = −1`).
-/

namespace Work.Pure

open Submission.CDTPlan
open PowerSeries
open scoped BigOperators

noncomputable section

/-- `fA = Σ_n C(2n,n) yⁿ/((2n+1)·16ⁿ)`, the series of `arcsin(√y/2)/(√y/2)`. -/
def fA : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Nat.centralBinom n : ℚ) / ((2 * (n : ℚ) + 1) * 16 ^ n)

@[simp] lemma coeff_fA (n : ℕ) :
    PowerSeries.coeff n fA = (Nat.centralBinom n : ℚ) / ((2 * (n : ℚ) + 1) * 16 ^ n) := by
  simp [fA]

/-! ## Coefficient shifts -/

lemma rcoeff_X_mul (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (X * f) = if 1 ≤ m then PowerSeries.coeff (m - 1) f else 0 := by
  simpa using PowerSeries.coeff_X_pow_mul' f 1 m

lemma rcoeff_X_sq_mul (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (X ^ 2 * f) = if 2 ≤ m then PowerSeries.coeff (m - 2) f else 0 :=
  PowerSeries.coeff_X_pow_mul' f 2 m

lemma rcoeff_deriv (k : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff k ((PowerSeries.derivative (R := ℚ)) f) =
      ((k : ℚ) + 1) * PowerSeries.coeff (k + 1) f := by
  rw [PowerSeries.coeff_derivative]; ring

/-! ## The two auxiliary coefficient identities -/

lemma rfG_rel : fA = fG + 2 * (X : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) fG := by
  apply PowerSeries.ext
  intro m
  rw [map_add]
  rw [show (2 : PowerSeries ℚ) * (X : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) fG
        = PowerSeries.C (2:ℚ) * (X * (PowerSeries.derivative (R := ℚ)) fG) by
      rw [show (2 : PowerSeries ℚ) = PowerSeries.C (2:ℚ) from rfl]; ring]
  rw [PowerSeries.coeff_C_mul, rcoeff_X_mul]
  by_cases hm : 1 ≤ m
  · rw [if_pos hm, rcoeff_deriv, show m - 1 + 1 = m from by omega]
    have hmc : ((m - 1 : ℕ) : ℚ) + 1 = (m : ℚ) := by rw [Nat.cast_sub hm]; ring
    rw [hmc, coeff_fA, coeff_fG]
    have h2m1 : (2*(m:ℚ)+1) ≠ 0 := by positivity
    have hp : (16:ℚ)^m ≠ 0 := pow_ne_zero m (by norm_num)
    field_simp
    ring
  · have hm0 : m = 0 := by omega
    subst hm0
    rw [if_neg (by omega : ¬ (1:ℕ) ≤ 0), coeff_fA, coeff_fG]
    norm_num [Nat.centralBinom]

lemma rfA_rel : 2 * (X : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) fA = W - fA := by
  apply PowerSeries.ext
  intro m
  rw [show (2 : PowerSeries ℚ) * (X : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) fA
        = PowerSeries.C (2:ℚ) * (X * (PowerSeries.derivative (R := ℚ)) fA) by
      rw [show (2 : PowerSeries ℚ) = PowerSeries.C (2:ℚ) from rfl]; ring]
  rw [PowerSeries.coeff_C_mul, rcoeff_X_mul, map_sub]
  by_cases hm : 1 ≤ m
  · rw [if_pos hm, rcoeff_deriv, show m - 1 + 1 = m from by omega]
    have hmc : ((m - 1 : ℕ) : ℚ) + 1 = (m : ℚ) := by rw [Nat.cast_sub hm]; ring
    rw [hmc, coeff_fA, W, PowerSeries.coeff_mk]
    have h2m1 : (2*(m:ℚ)+1) ≠ 0 := by positivity
    have hp : (16:ℚ)^m ≠ 0 := pow_ne_zero m (by norm_num)
    field_simp
    ring
  · have hm0 : m = 0 := by omega
    subst hm0
    rw [if_neg (by omega : ¬ (1:ℕ) ≤ 0), coeff_fA, W, PowerSeries.coeff_mk]
    norm_num [Nat.centralBinom]

/-! ## Uniqueness of the power-series solution of `X(4−X)g' = (2−X)g + X²` -/

lemma rcoeff_ode_lhs (n : ℕ) (h : PowerSeries ℚ) :
    PowerSeries.coeff n (X * ((4:PowerSeries ℚ) - X) * (PowerSeries.derivative (R := ℚ)) h)
      = 4 * ((n:ℚ) * PowerSeries.coeff n h) - ((n-1:ℕ):ℚ) * PowerSeries.coeff (n-1) h := by
  rw [show X * ((4:PowerSeries ℚ) - X) * (PowerSeries.derivative (R := ℚ)) h
        = (4:PowerSeries ℚ) * (X * (PowerSeries.derivative (R := ℚ)) h)
          - X^2 * (PowerSeries.derivative (R := ℚ)) h by ring]
  rw [show (4:PowerSeries ℚ) = PowerSeries.C 4 from rfl]
  rw [map_sub, PowerSeries.coeff_C_mul, rcoeff_X_mul, rcoeff_X_sq_mul]
  by_cases hn : 1 ≤ n
  · rw [if_pos hn, rcoeff_deriv, show n - 1 + 1 = n from by omega]
    have hmc : ((n-1:ℕ):ℚ) + 1 = (n:ℚ) := by rw [Nat.cast_sub hn]; ring
    rw [hmc]
    by_cases h2 : 2 ≤ n
    · rw [if_pos h2, rcoeff_deriv, show n - 2 + 1 = n - 1 from by omega]
      have hmc2 : ((n-2:ℕ):ℚ) + 1 = ((n-1:ℕ):ℚ) := by
        rw [Nat.cast_sub (by omega: 2 ≤ n), Nat.cast_sub hn]; ring
      rw [hmc2]
    · rw [if_neg h2]
      have hn1 : n = 1 := by omega
      subst hn1; norm_num
  · have hn0 : n = 0 := by omega
    subst hn0; norm_num

lemma rcoeff_ode_rhs (n : ℕ) (h : PowerSeries ℚ) :
    PowerSeries.coeff n ((2 - X) * h)
      = 2 * PowerSeries.coeff n h - (if 1≤n then PowerSeries.coeff (n-1) h else 0) := by
  rw [show (2 - X) * h = (2:PowerSeries ℚ) * h - X * h by ring]
  rw [show (2:PowerSeries ℚ) = PowerSeries.C 2 from rfl]
  rw [map_sub, PowerSeries.coeff_C_mul, rcoeff_X_mul]

lemma rhomogeneous_vanishes (h : PowerSeries ℚ)
    (hh : X * ((4:PowerSeries ℚ) - X) * (PowerSeries.derivative (R := ℚ)) h = (2 - X) * h) : h = 0 := by
  have hrec : ∀ n : ℕ, 1 ≤ n →
      (4*(n:ℚ) - 2) * PowerSeries.coeff n h = ((n:ℚ) - 2) * PowerSeries.coeff (n-1) h := by
    intro n hn
    have hc := congrArg (fun f : PowerSeries ℚ => PowerSeries.coeff n f) hh
    rw [rcoeff_ode_lhs n h, rcoeff_ode_rhs n h, if_pos hn] at hc
    have hnc : ((n-1:ℕ):ℚ) = (n:ℚ) - 1 := by rw [Nat.cast_sub hn]; ring
    rw [hnc] at hc
    linear_combination hc
  have hcoeff : ∀ n, PowerSeries.coeff n h = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        have hc := congrArg (fun f : PowerSeries ℚ => PowerSeries.coeff 0 f) hh
        have hL : PowerSeries.coeff 0 (X * ((4:PowerSeries ℚ) - X) * (PowerSeries.derivative (R := ℚ)) h) = 0 := by
          rw [show X * ((4:PowerSeries ℚ) - X) * (PowerSeries.derivative (R := ℚ)) h
                = X * (((4:PowerSeries ℚ) - X) * (PowerSeries.derivative (R := ℚ)) h) by ring]
          exact PowerSeries.coeff_zero_X_mul _
        have hR : PowerSeries.coeff 0 ((2 - X) * h) = 2 * PowerSeries.coeff 0 h := by
          rw [show (2 - X) * h = (2:PowerSeries ℚ) * h - X * h by ring]
          rw [show (2:PowerSeries ℚ) = PowerSeries.C 2 from rfl]
          rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul]
          ring
        rw [hL, hR] at hc
        exact (mul_eq_zero.mp hc.symm).resolve_left (by norm_num)
      · have hn : 1 ≤ n := hnpos
        have hrv := hrec n hn
        rw [ih (n-1) (by omega), mul_zero] at hrv
        have hne : (4*(n:ℚ) - 2) ≠ 0 := by
          have : (1:ℚ) ≤ n := by exact_mod_cast hn
          linarith
        exact (mul_eq_zero.mp hrv).resolve_left hne
  apply PowerSeries.ext
  intro n
  simp [hcoeff n]

lemma req_of_same_ode {g1 g2 : PowerSeries ℚ}
    (h1 : X * ((4:PowerSeries ℚ) - X) * (PowerSeries.derivative (R := ℚ)) g1 = (2 - X) * g1 + X^2)
    (h2 : X * ((4:PowerSeries ℚ) - X) * (PowerSeries.derivative (R := ℚ)) g2 = (2 - X) * g2 + X^2) :
    g1 = g2 := by
  have hh : X * ((4:PowerSeries ℚ) - X) * (PowerSeries.derivative (R := ℚ)) (g1 - g2)
      = (2 - X) * (g1 - g2) := by
    rw [map_sub]
    rw [show X * ((4:PowerSeries ℚ) - X) * ((PowerSeries.derivative (R := ℚ)) g1 - (PowerSeries.derivative (R := ℚ)) g2)
          = X * ((4:PowerSeries ℚ) - X) * (PowerSeries.derivative (R := ℚ)) g1
            - X * ((4:PowerSeries ℚ) - X) * (PowerSeries.derivative (R := ℚ)) g2 by ring]
    rw [h1, h2]; ring
  have := rhomogeneous_vanishes (g1 - g2) hh
  rwa [sub_eq_zero] at this

/-! ## The ODE satisfied by `2X(1 + Fser·fA)` -/

lemma rDmul (u v : PowerSeries ℚ) :
    (PowerSeries.derivative (R := ℚ)) (u * v) = u * (PowerSeries.derivative (R := ℚ)) v
      + (PowerSeries.derivative (R := ℚ)) u * v := by
  rw [Derivation.leibniz]; simp [smul_eq_mul, mul_comm]

lemma rD4mul (Y : PowerSeries ℚ) :
    (PowerSeries.derivative (R := ℚ)) (4 * Y) = 4 * (PowerSeries.derivative (R := ℚ)) Y := by
  rw [show (4:PowerSeries ℚ) = PowerSeries.C (4:ℚ) from rfl, Derivation.leibniz]
  simp

lemma rD2mul (Y : PowerSeries ℚ) :
    (PowerSeries.derivative (R := ℚ)) (2 * Y) = 2 * (PowerSeries.derivative (R := ℚ)) Y := by
  rw [show (2:PowerSeries ℚ) = PowerSeries.C (2:ℚ) from rfl, Derivation.leibniz]
  simp

lemma rD1 : (PowerSeries.derivative (R := ℚ)) (1 : PowerSeries ℚ) = 0 := by simp
lemma rDX : (PowerSeries.derivative (R := ℚ)) (X : PowerSeries ℚ) = 1 := by simp

theorem rbeta_ode (F A W : PowerSeries ℚ)
    (hF : 2 * ((4:PowerSeries ℚ) - X) * (PowerSeries.derivative (R := ℚ)) F + F = 0)
    (hA : 2 * X * (PowerSeries.derivative (R := ℚ)) A = W - A)
    (hFW : F * W = -1) :
    X * ((4:PowerSeries ℚ) - X) * (PowerSeries.derivative (R := ℚ)) (2 * X * (1 + F * A))
      = (2 - X) * (2 * X * (1 + F * A)) + X ^ 2 := by
  have hD : (PowerSeries.derivative (R := ℚ)) (2 * X * (1 + F * A))
      = 2 * (1 + F * A)
        + 2 * X * (F * (PowerSeries.derivative (R := ℚ)) A + (PowerSeries.derivative (R := ℚ)) F * A) := by
    rw [show (2:PowerSeries ℚ) * X * (1 + F * A) = 2 * (X * (1 + F * A)) by ring, rD2mul,
      rDmul X (1 + F * A), map_add, rD1, rDmul F A, rDX]
    ring
  rw [hD]
  linear_combination (X^2 * A) * hF + (X * (4 - X) * F) * hA + (X * (4 - X)) * hFW

/-! ## The closed form of `B₂` -/

lemma rFser_mul_W : Fser * W = -1 := by
  have h := b4_Fser_eq
  have h2 : (4:PowerSeries ℚ) * (Fser * W) = -((4 - X) * W * W) := by
    calc (4:PowerSeries ℚ) * (Fser * W) = (4 * Fser) * W := by ring
      _ = (-(4 - X) * W) * W := by rw [h]
      _ = -((4 - X) * W * W) := by ring
  rw [b4_W_sq] at h2
  have h4 : (4:PowerSeries ℚ) ≠ 0 := by
    intro hzero
    have hc := congrArg (fun z : PowerSeries ℚ => PowerSeries.constantCoeff z) hzero
    rw [show (4:PowerSeries ℚ) = PowerSeries.C (4:ℚ) from rfl, PowerSeries.constantCoeff_C,
        PowerSeries.constantCoeff_zero] at hc
    norm_num at hc
  have h3 : (4:PowerSeries ℚ) * (Fser * W) = 4 * (-1) := by rw [h2]; ring
  exact (mul_eq_mul_left_iff.mp h3).resolve_right h4

lemma rB2_form : B2 = 2 * (X : PowerSeries ℚ) + 2 * X * Fser * fA := by
  have hbeta := rbeta_ode Fser fA W b4_Fser_ode rfA_rel rFser_mul_W
  have h := req_of_same_ode hbeta b4_B2_ode
  rw [← h]; ring

/-! ## The differential relation of `B₄` -/

theorem b4_rel :
    (X : PowerSeries ℚ) * (4 - X) * (PowerSeries.derivative (R := ℚ)) B4
      = (2 - X) * B4 + (4 - X) * B2 - 2 * X * (4 - X) := by
  rw [b4_eq_prod, rB2_form]
  have hD4 : (PowerSeries.derivative (R := ℚ)) (4 * X * Fser * fG)
      = 4 * (X * (Fser * (PowerSeries.derivative (R := ℚ)) fG
          + (PowerSeries.derivative (R := ℚ)) Fser * fG) + Fser * fG) := by
    rw [show (4:PowerSeries ℚ) * X * Fser * fG = 4 * (X * (Fser * fG)) by ring, rD4mul,
      rDmul X (Fser * fG), rDmul Fser fG, rDX]
    ring
  rw [hD4]
  have hGr : fA - fG - 2 * X * (PowerSeries.derivative (R := ℚ)) fG = 0 := by rw [rfG_rel]; ring
  linear_combination (2 * X^2 * fG) * b4_Fser_ode + (-2 * X * (4 - X) * Fser) * hGr

end

end Work.Pure
