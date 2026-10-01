import Mathlib
import Submission.Work.LinnikAreas.Density4.box_divisor_identity
import Submission.Work.LinnikAreas.Density4.inner_indicator_le_one
import Submission.Work.LinnikAreas.Density4.sum_inv_mul_sqrt_le

namespace Work.LinnikAreas.Density4

open Finset

/-- **Block sum bound.**  For every real `X > 0`,
`Σ_{⌊X⌋ < δ ≤ ⌊2X⌋} μ(δ)²/δ · Σ_{d ∣ δ} d^{-1/2} ≤ 6`.

Only squarefree `δ` contribute.  Bounding `μ(δ)² ≤ 1`, pulling `1/δ` into the
divisor sum and substituting `e = δ/d` turns the sum into the "hyperbola" sum
`Σ_{(d,e) : de ∈ (⌊X⌋,⌊2X⌋]} (d√d·e)^{-1}`.  For fixed `d` the inner harmonic sum over
`e ∈ (X/d, 2X/d]` is at most `1` (the interval has ratio `2`), and
`Σ_d (d√d)^{-1} ≤ 6`. -/
theorem block_sum_bound (X : ℝ) (hX : 0 < X) :
    (∑ δ ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2 * X)),
        ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (δ : ℝ) *
          (∑ d ∈ δ.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) ≤ 6 := by
  have hμ : ∀ δ : ℕ, ((ArithmeticFunction.moebius δ : ℝ))^2 ≤ 1 := by
    intro δ; rcases ArithmeticFunction.moebius_eq_or δ with h|h|h <;> (rw [h]; norm_num)
  have hinner_nonneg : ∀ δ : ℕ, 0 ≤ ∑ d ∈ δ.divisors, (1:ℝ)/Real.sqrt (d:ℝ) := by
    intro δ; apply Finset.sum_nonneg; intro d hd; positivity
  have hstep1 : (∑ δ ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2 * X)),
        ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (δ : ℝ) *
          (∑ d ∈ δ.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
      ≤ ∑ δ ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2 * X)),
          (1/(δ:ℝ)) * (∑ d ∈ δ.divisors, (1:ℝ)/Real.sqrt (d:ℝ)) := by
    apply Finset.sum_le_sum
    intro δ hδ
    have hδ1 : 1 ≤ δ := by
      have := (Finset.mem_Ioc.mp hδ).1; omega
    have hδpos : (0:ℝ) < (δ:ℝ) := by
      have : (1:ℝ) ≤ (δ:ℝ) := by exact_mod_cast hδ1
      linarith
    have hle : ((ArithmeticFunction.moebius δ : ℝ))^2 / (δ:ℝ) ≤ (1:ℝ)/(δ:ℝ) :=
      div_le_div_of_nonneg_right (hμ δ) hδpos.le
    exact mul_le_mul_of_nonneg_right hle (hinner_nonneg δ)
  have hLHS_eq : (∑ δ ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2 * X)),
          (1/(δ:ℝ)) * (∑ d ∈ δ.divisors, (1:ℝ)/Real.sqrt (d:ℝ)))
      = ∑ δ ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2 * X)),
          ∑ d ∈ δ.divisors,
            (1/((d:ℝ)*Real.sqrt (d:ℝ))) * (1/((δ/d:ℕ):ℝ)) := by
    apply Finset.sum_congr rfl
    intro δ hδ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hdvd : d ∣ δ := Nat.dvd_of_mem_divisors hd
    have hdne : (d:ℝ) ≠ 0 := by
      have : 0 < d := Nat.pos_of_mem_divisors hd
      positivity
    have hδne : (δ:ℝ) ≠ 0 := by
      have : δ ≠ 0 := Nat.ne_zero_of_mem_divisors hd
      positivity
    have hcast : ((δ/d:ℕ):ℝ) = (δ:ℝ)/(d:ℝ) := Nat.cast_div hdvd hdne
    rw [hcast, one_div_div]
    field_simp
  have hbox := box_divisor_identity (Finset.Ioc (Nat.floor X) (Nat.floor (2 * X)))
      (Nat.floor (2 * X))
      (fun δ hδ => (Finset.mem_Ioc.mp hδ).2)
      (fun d e => (1/((d:ℝ)*Real.sqrt (d:ℝ))) * (1/(e:ℝ)))
  have hfact : (∑ d ∈ Finset.Icc 1 (Nat.floor (2*X)), ∑ e ∈ Finset.Icc 1 (Nat.floor (2*X)),
        (if d*e ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2*X)) then
          (1/((d:ℝ)*Real.sqrt (d:ℝ)))*(1/(e:ℝ)) else 0))
      = ∑ d ∈ Finset.Icc 1 (Nat.floor (2*X)),
          (1/((d:ℝ)*Real.sqrt (d:ℝ))) *
            (∑ e ∈ Finset.Icc 1 (Nat.floor (2*X)),
              (if d*e ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2*X)) then (1:ℝ)/e else 0)) := by
    apply Finset.sum_congr rfl; intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro e he
    by_cases h : d*e ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2*X)) <;> simp [h]
  have hbnd : (∑ d ∈ Finset.Icc 1 (Nat.floor (2*X)),
          (1/((d:ℝ)*Real.sqrt (d:ℝ))) *
            (∑ e ∈ Finset.Icc 1 (Nat.floor (2*X)),
              (if d*e ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2*X)) then (1:ℝ)/e else 0)))
      ≤ ∑ d ∈ Finset.Icc 1 (Nat.floor (2*X)), (1/((d:ℝ)*Real.sqrt (d:ℝ))) * 1 := by
    apply Finset.sum_le_sum; intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdpos : (0:ℝ) < (d:ℝ) := by
      have : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
      linarith
    have hw : 0 ≤ (1:ℝ)/((d:ℝ)*Real.sqrt (d:ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left (inner_indicator_le_one X hX d hd1) hw
  have hfin : (∑ d ∈ Finset.Icc 1 (Nat.floor (2*X)), (1/((d:ℝ)*Real.sqrt (d:ℝ))) * 1) ≤ 6 := by
    have := sum_inv_mul_sqrt_le (Nat.floor (2*X))
    simpa using this
  calc (∑ δ ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2 * X)),
        ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (δ : ℝ) *
          (∑ d ∈ δ.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
      ≤ ∑ δ ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2 * X)),
          (1/(δ:ℝ)) * (∑ d ∈ δ.divisors, (1:ℝ)/Real.sqrt (d:ℝ)) := hstep1
    _ = ∑ δ ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2 * X)),
          ∑ d ∈ δ.divisors, (1/((d:ℝ)*Real.sqrt (d:ℝ))) * (1/((δ/d:ℕ):ℝ)) := hLHS_eq
    _ = ∑ d ∈ Finset.Icc 1 (Nat.floor (2*X)), ∑ e ∈ Finset.Icc 1 (Nat.floor (2*X)),
        (if d*e ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2*X)) then
          (1/((d:ℝ)*Real.sqrt (d:ℝ)))*(1/(e:ℝ)) else 0) := hbox
    _ = ∑ d ∈ Finset.Icc 1 (Nat.floor (2*X)),
          (1/((d:ℝ)*Real.sqrt (d:ℝ))) *
            (∑ e ∈ Finset.Icc 1 (Nat.floor (2*X)),
              (if d*e ∈ Finset.Ioc (Nat.floor X) (Nat.floor (2*X)) then (1:ℝ)/e else 0)) := hfact
    _ ≤ ∑ d ∈ Finset.Icc 1 (Nat.floor (2*X)), (1/((d:ℝ)*Real.sqrt (d:ℝ))) * 1 := hbnd
    _ ≤ 6 := hfin

end Work.LinnikAreas.Density4
