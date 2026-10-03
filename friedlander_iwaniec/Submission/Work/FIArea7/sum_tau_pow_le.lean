import Mathlib
import Submission.Work.FIArea7.psiTauMul
import Submission.Work.FIArea7.sum_Icc_divisors_swap_left
import Submission.Work.FIArea7.sum_inv_Icc_le_one_add_log
import Submission.Work.FIArea7.tau_pow_mul_le
import Submission.Work.FIArea7.sum_Icc_divisors_swap_all
import Submission.Work.FIArea7.tau_pow_succ_eq_sum_divisors

namespace Work.FIArea7

open Finset

/-! ## The two summatory functions -/

/-- `∑_{n ≤ y} τ(n)^j`. -/
noncomputable def ppow (j y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 y, (((n.divisors.card : ℕ) : ℝ)) ^ j

/-- `∑_{n ≤ y} τ(n)^j / n`. -/
noncomputable def pdiv (j y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 y, (((n.divisors.card : ℕ) : ℝ)) ^ j / (n : ℝ)

private lemma sum_div_const {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c : ℝ) :
    (∑ d ∈ s, f d) / c = ∑ d ∈ s, f d / c := by
  calc (∑ d ∈ s, f d) / c = (∑ d ∈ s, f d) * c⁻¹ := div_eq_mul_inv ..
    _ = ∑ d ∈ s, f d * c⁻¹ := Finset.sum_mul ..
    _ = ∑ d ∈ s, f d / c := Finset.sum_congr rfl (fun d _ => (div_eq_mul_inv ..).symm)

private lemma ppow_zero (y : ℕ) : ppow 0 y = y := by
  rw [ppow]
  simp only [pow_zero]
  rw [Finset.sum_const, Nat.card_Icc]
  simp

private lemma pdiv_zero (y : ℕ) : pdiv 0 y ≤ 1 + Real.log y := by
  simpa [pdiv] using sum_inv_Icc_le_one_add_log y

/-- `pdiv` is a sum of nonnegative terms. -/
private lemma pdiv_nonneg (j y : ℕ) : 0 ≤ pdiv j y := by
  rw [pdiv]
  exact Finset.sum_nonneg (fun n _ => by positivity)

/-- Monotonicity of `pdiv` in the upper endpoint. -/
private lemma pdiv_mono (j : ℕ) {a b : ℕ} (h : a ≤ b) : pdiv j a ≤ pdiv j b := by
  rw [pdiv, pdiv]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h) ?_
  intro x _ _
  positivity

/-- The `τ^{j+1}` moment is bounded by the `j`-th moment twisted by `1/n`. -/
private lemma ppow_succ (j y : ℕ)
    (h : ∀ x, ppow j x ≤ (x : ℝ) * (1 + Real.log x) ^ (2 ^ j - 1)) :
    ppow (j + 1) y ≤ (y : ℝ) * (1 + Real.log y) ^ (2 ^ j - 1) * pdiv j y := by
  have hstep1 : ppow (j + 1) y
      = ∑ n ∈ Finset.Icc 1 y, ∑ d ∈ n.divisors, (((n.divisors.card : ℕ) : ℝ)) ^ j := by
    rw [ppow]
    exact Finset.sum_congr rfl (fun n _ => tau_pow_succ_eq_sum_divisors j n)
  have hstep2 : (∑ n ∈ Finset.Icc 1 y, ∑ d ∈ n.divisors, (((n.divisors.card : ℕ) : ℝ)) ^ j)
      = ∑ d ∈ Finset.Icc 1 y, ∑ m ∈ Finset.Icc 1 (y / d),
          ((((d * m).divisors.card : ℕ) : ℝ)) ^ j :=
    sum_Icc_divisors_swap_all y y le_rfl (fun d n => (((n.divisors.card : ℕ) : ℝ)) ^ j)
  calc ppow (j + 1) y
      = _ := hstep1
    _ = _ := hstep2
    _ ≤ ∑ d ∈ Finset.Icc 1 y, ∑ m ∈ Finset.Icc 1 (y / d),
          ((((d.divisors.card : ℕ) : ℝ)) ^ j) * ((((m.divisors.card : ℕ) : ℝ)) ^ j) := by
        refine Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun m _ => ?_))
        exact tau_pow_mul_le j d m
    _ = ∑ d ∈ Finset.Icc 1 y, ((((d.divisors.card : ℕ) : ℝ)) ^ j) * ppow j (y / d) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [ppow, Finset.mul_sum]
    _ ≤ ∑ d ∈ Finset.Icc 1 y, ((((d.divisors.card : ℕ) : ℝ)) ^ j)
          * (((y : ℝ) / d) * (1 + Real.log (y : ℝ)) ^ (2 ^ j - 1)) := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hdle : d ≤ y := (Finset.mem_Icc.mp hd).2
        have hpos : 0 < d := by omega
        have hyd1 : 1 ≤ y / d := (Nat.one_le_div_iff hpos).mpr hdle
        have hlog : Real.log ((y / d : ℕ)) ≤ Real.log (y : ℝ) :=
          Real.log_le_log (by exact_mod_cast hyd1) (by exact_mod_cast Nat.div_le_self y d)
        have hbase : 1 + Real.log ((y / d : ℕ)) ≤ 1 + Real.log (y : ℝ) := by linarith
        have hbase0 : 0 ≤ 1 + Real.log ((y / d : ℕ)) := by
          have := Real.log_natCast_nonneg (y / d); linarith
        have hpow : (1 + Real.log ((y / d : ℕ))) ^ (2 ^ j - 1)
            ≤ (1 + Real.log (y : ℝ)) ^ (2 ^ j - 1) :=
          pow_le_pow_left₀ hbase0 hbase _
        have hcast : ((y / d : ℕ) : ℝ) ≤ (y : ℝ) / d := Nat.cast_div_le
        have hBC : ((y / d : ℕ) : ℝ) * (1 + Real.log ((y / d : ℕ))) ^ (2 ^ j - 1)
            ≤ ((y : ℝ) / d) * (1 + Real.log (y : ℝ)) ^ (2 ^ j - 1) :=
          mul_le_mul hcast hpow (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (le_trans (h (y / d)) hBC) (by positivity)
    _ = (∑ d ∈ Finset.Icc 1 y, ((((d.divisors.card : ℕ) : ℝ)) ^ j) * ((y : ℝ) / d))
          * (1 + Real.log y) ^ (2 ^ j - 1) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun d _ => by ring)
    _ = ((y : ℝ) * pdiv j y) * (1 + Real.log y) ^ (2 ^ j - 1) := by
        congr 1
        rw [pdiv, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
    _ = (y : ℝ) * (1 + Real.log y) ^ (2 ^ j - 1) * pdiv j y := by ring

/-- The `(j+1)`-th twisted moment is at most the square of the `j`-th one. -/
private lemma pdiv_succ (j y : ℕ) :
    pdiv (j + 1) y ≤ pdiv j y * pdiv j y := by
  have hstep1 : pdiv (j + 1) y
      = ∑ n ∈ Finset.Icc 1 y, ∑ d ∈ n.divisors, (((n.divisors.card : ℕ) : ℝ)) ^ j / (n : ℝ) := by
    rw [pdiv]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [tau_pow_succ_eq_sum_divisors j n]
    exact sum_div_const _ _ _
  have hstep2 : (∑ n ∈ Finset.Icc 1 y, ∑ d ∈ n.divisors,
        (((n.divisors.card : ℕ) : ℝ)) ^ j / (n : ℝ))
      = ∑ d ∈ Finset.Icc 1 y, ∑ m ∈ Finset.Icc 1 (y / d),
          ((((d * m).divisors.card : ℕ) : ℝ)) ^ j / ((d * m : ℕ) : ℝ) :=
    sum_Icc_divisors_swap_all y y le_rfl
      (fun d n => (((n.divisors.card : ℕ) : ℝ)) ^ j / (n : ℝ))
  calc pdiv (j + 1) y
      = _ := hstep1
    _ = _ := hstep2
    _ ≤ ∑ d ∈ Finset.Icc 1 y, ∑ m ∈ Finset.Icc 1 (y / d),
          ((((d.divisors.card : ℕ) : ℝ)) ^ j / (d : ℝ))
            * ((((m.divisors.card : ℕ) : ℝ)) ^ j / (m : ℝ)) := by
        refine Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun m _ => ?_))
        have hdm : (((d * m).divisors.card : ℕ) : ℝ)
            ≤ ((d.divisors.card : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
          have h : (((d * m).divisors.card : ℕ) : ℝ)
              ≤ (((d.divisors.card * m.divisors.card : ℕ)) : ℝ) :=
            Nat.cast_le.mpr (psiTauMul d m)
          simpa using h
        have hp : ((((d * m).divisors.card : ℕ) : ℝ)) ^ j
            ≤ ((((d.divisors.card : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ))) ^ j :=
          pow_le_pow_left₀ (by positivity) hdm j
        have hcast : (((d * m : ℕ) : ℝ)) = (d : ℝ) * (m : ℝ) := by push_cast; ring
        rw [hcast]
        calc ((((d * m).divisors.card : ℕ) : ℝ)) ^ j / ((d : ℝ) * (m : ℝ))
            ≤ ((((d.divisors.card : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ)) ^ j)
                / ((d : ℝ) * (m : ℝ)) :=
              div_le_div_of_nonneg_right hp (by positivity)
          _ = ((((d.divisors.card : ℕ) : ℝ)) ^ j / (d : ℝ))
                * ((((m.divisors.card : ℕ) : ℝ)) ^ j / (m : ℝ)) := by
              rw [div_mul_div_comm, mul_pow]
    _ = ∑ d ∈ Finset.Icc 1 y, ((((d.divisors.card : ℕ) : ℝ)) ^ j / (d : ℝ))
          * pdiv j (y / d) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [pdiv, Finset.mul_sum]
    _ ≤ ∑ d ∈ Finset.Icc 1 y, ((((d.divisors.card : ℕ) : ℝ)) ^ j / (d : ℝ)) * pdiv j y := by
        refine Finset.sum_le_sum (fun d _ => ?_)
        exact mul_le_mul_of_nonneg_left (pdiv_mono j (Nat.div_le_self y d)) (by positivity)
    _ = pdiv j y * pdiv j y := by
        rw [← Finset.sum_mul, ← pdiv]

/-- The simultaneous induction: the sharp moment bound for `ppow`, and the companion
bound for the twisted moment `pdiv`. -/
private lemma main_induction (j : ℕ) :
    (∀ y, ppow j y ≤ (y : ℝ) * (1 + Real.log y) ^ (2 ^ j - 1)) ∧
    (∀ y, pdiv j y ≤ (1 + Real.log y) ^ (2 ^ j)) := by
  induction j with
  | zero =>
      refine ⟨fun y => ?_, fun y => ?_⟩
      · rw [ppow_zero]
        simp
      · simpa using pdiv_zero y
  | succ j ih =>
      obtain ⟨ihA, ihB⟩ := ih
      have hexp : (2 ^ j - 1) + 2 ^ j = 2 ^ (j + 1) - 1 := by
        have h1 : 0 < 2 ^ j := by positivity
        rw [pow_succ]
        omega
      have hexp2 : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by
        rw [pow_succ]; ring
      refine ⟨fun y => ?_, fun y => ?_⟩
      · calc ppow (j + 1) y
            ≤ (y : ℝ) * (1 + Real.log y) ^ (2 ^ j - 1) * pdiv j y := ppow_succ j y ihA
          _ ≤ (y : ℝ) * (1 + Real.log y) ^ (2 ^ j - 1) * (1 + Real.log y) ^ (2 ^ j) := by
              refine mul_le_mul_of_nonneg_left (ihB y) ?_
              refine mul_nonneg (by positivity) (pow_nonneg ?_ _)
              linarith [Real.log_natCast_nonneg y]
          _ = (y : ℝ) * (1 + Real.log y) ^ (2 ^ (j + 1) - 1) := by
              rw [mul_assoc, ← pow_add, hexp]
      · calc pdiv (j + 1) y
            ≤ pdiv j y * pdiv j y := pdiv_succ j y
          _ ≤ (1 + Real.log y) ^ (2 ^ j) * (1 + Real.log y) ^ (2 ^ j) := by
              exact mul_le_mul (ihB y) (ihB y) (pdiv_nonneg j y)
                (pow_nonneg (by linarith [Real.log_natCast_nonneg y]) _)
          _ = (1 + Real.log y) ^ (2 ^ (j + 1)) := by
              rw [← pow_add, hexp2]

/-- **A3a: the divisor-sum moment bound.**  For every `j : ℕ` and `y : ℕ`,

  `Σ_{n ≤ y} τ(n)^j ≤ y·(1 + log y)^{2^j − 1}`.

Proof: `τ(n)^j = Σ_{d|n} τ(d)^{j−1}·τ(n/d)^{j−1}` (from `τ(n) = Σ_{d|n} 1` and
`τ(n) ≤ τ(d)τ(n/d)`), then `Σ_{n≤y} f*f ≤ y(1+log y)^c·Σ_{d≤y} f(d)/d`, giving
`c_j = 2c_{j−1}+1`, `c_0 = 0`; carry the companion bound `Σ_{d≤y} f(d)/d ≤ (1+log y)^{c_j+1}` in the
same induction.  Used by `deltaTau_mass_le` and `sum_convPow_sq_le`. -/
theorem sum_tau_pow_le (j : ℕ) (y : ℕ) :
    ∑ n ∈ Finset.Icc 1 y, (((n.divisors.card : ℕ) : ℝ)) ^ j
      ≤ y * (1 + Real.log y) ^ (2 ^ j - 1) := by
  simpa [ppow] using (main_induction j).1 y

end Work.FIArea7
