import Mathlib
import Submission.CDTPlan.InterfacesC
import Submission.CDT.SympH
import Submission.CDT.DerivOrderAt
import Submission.CDT.RatFuncConstants

/-!
# Area C7 — the x-side of Lemma `seven`

Definitions for the pullback of the seven pure functions `B₁,…,B₇` along `y = x²/(x-1)`
(`Submission.CDT.sympY`), together with the transcendence functions occurring in the x-side proof
of their `ℚ(y)`-linear independence:

* `Lps = log(1-x)`, `Li2ps = Li₂(x)`, `Jps = x·₃F₂(1/2,1,1;3/2,3/2;y/4)`  (the "fifth function"),
* `g i = B i ∘ y` for `i = 1,…,7`.
-/

noncomputable section

namespace Work.C7

open PowerSeries

/-- `y = x²/(x-1)`, as a power series. -/
abbrev yps : PowerSeries ℚ := Submission.CDT.sympY

/-- `log(1-x) = -Σ xⁿ/n`. -/
def Lps : PowerSeries ℚ := PowerSeries.mk fun n => if n = 0 then 0 else -((n : ℚ))⁻¹

/-- `Li₂(x) = Σ xⁿ/n²`. -/
def Li2ps : PowerSeries ℚ := PowerSeries.mk fun n => if n = 0 then 0 else (((n : ℚ)) ^ 2)⁻¹

/-- The series `K` with `B₅ = X·K`. -/
def K5 : PowerSeries ℚ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) Submission.CDTPlan.B5

/-- `J(x) = x·₃F₂(1/2,1,1;3/2,3/2; y/4) = x·(K ∘ y)`. -/
def Jps : PowerSeries ℚ := X * K5.subst yps

/-- The pullbacks `Bᵢ ∘ y`. -/
def g (i : Fin 7) : PowerSeries ℚ := (Submission.CDTPlan.pureB i).subst yps

/-- `c(x) = x(x-2)/(x-1)`, the rational function with `B₂∘y = 2y - c·L`. -/
def cfun : PowerSeries ℚ := X * (X - 2) * (X - 1)⁻¹

lemma coeff_Lps (n : ℕ) : PowerSeries.coeff n Lps = if n = 0 then 0 else -((n : ℚ))⁻¹ := by
  rw [Lps, PowerSeries.coeff_mk]

lemma coeff_Li2ps (n : ℕ) :
    PowerSeries.coeff n Li2ps = if n = 0 then 0 else (((n : ℚ)) ^ 2)⁻¹ := by
  rw [Li2ps, PowerSeries.coeff_mk]

lemma coeff_zero_Lps : PowerSeries.coeff 0 Lps = 0 := by rw [coeff_Lps]; simp
lemma coeff_one_Lps : PowerSeries.coeff 1 Lps = -1 := by rw [coeff_Lps]; norm_num
lemma coeff_zero_Li2ps : PowerSeries.coeff 0 Li2ps = 0 := by rw [coeff_Li2ps]; simp
lemma Lps_ne_zero : Lps ≠ 0 := by
  intro h
  have := congrArg (PowerSeries.coeff 1) h
  rw [coeff_one_Lps] at this
  norm_num at this

/-- The derivative of `Lps = log(1-x)` is the constant series `-1`. -/
lemma coeff_deriv_Lps (m : ℕ) :
    PowerSeries.coeff m (PowerSeries.derivative (R := ℚ) Lps) = -1 := by
  rw [PowerSeries.coeff_derivative, coeff_Lps, if_neg (by omega : ¬ (m + 1 = 0))]
  push_cast
  field_simp

/-- `(1 - x)·L' = -1`. -/
theorem deriv_Lps : (1 - X) * PowerSeries.derivative (R := ℚ) Lps = -1 := by
  apply PowerSeries.ext
  intro n
  have hsplit : (1 - X) * PowerSeries.derivative (R := ℚ) Lps =
      PowerSeries.derivative (R := ℚ) Lps - X ^ 1 * PowerSeries.derivative (R := ℚ) Lps := by
    rw [pow_one]; ring
  rw [hsplit, map_sub, PowerSeries.coeff_X_pow_mul', coeff_deriv_Lps, map_neg]
  rcases n with _ | n
  · rw [if_neg (by omega : ¬ (1 : ℕ) ≤ 0), PowerSeries.coeff_one]
    norm_num
  · rw [if_pos (by omega : (1 : ℕ) ≤ n + 1), show (n + 1 - 1) = n by omega, coeff_deriv_Lps,
      PowerSeries.coeff_one, if_neg (by omega : ¬ (n + 1 = 0))]
    norm_num

/-- The coefficient of `Li₂'` is `1/(m+1)`. -/
lemma coeff_deriv_Li2ps (m : ℕ) :
    PowerSeries.coeff m (PowerSeries.derivative (R := ℚ) Li2ps) = (((m + 1 : ℕ) : ℚ))⁻¹ := by
  rw [PowerSeries.coeff_derivative, coeff_Li2ps, if_neg (by omega : ¬ (m + 1 = 0))]
  push_cast
  field_simp

/-- `x·Li₂' = -L`. -/
theorem deriv_Li2ps : X * PowerSeries.derivative (R := ℚ) Li2ps = -Lps := by
  apply PowerSeries.ext
  intro n
  have hsplit : (X : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) Li2ps =
      X ^ 1 * PowerSeries.derivative (R := ℚ) Li2ps := by rw [pow_one]
  rw [hsplit, PowerSeries.coeff_X_pow_mul', map_neg]
  rcases n with _ | n
  · rw [if_neg (by omega : ¬ (1 : ℕ) ≤ 0), coeff_Lps]
    simp
  · rw [if_pos (by omega : (1 : ℕ) ≤ n + 1), show (n + 1 - 1) = n by omega, coeff_deriv_Li2ps,
      coeff_Lps, if_neg (by omega : ¬ (n + 1 = 0))]
    push_cast
    ring

end Work.C7
