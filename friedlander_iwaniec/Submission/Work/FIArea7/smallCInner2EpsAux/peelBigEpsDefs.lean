import Mathlib
import Submission.Work.FIArea7.smallCInner2EpsAux.defs
import Submission.Work.FIArea7.prop172defs

set_option autoImplicit false

namespace Work.FIArea7.smallCInner2EpsAux

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `⌊u/(z+1)⌋`: the common range of the two variables of the peeled big part. -/
def peelBigM (u z : ℕ) : ℕ := u / (z + 1)

/-- The `p`-coefficient `μ(p)·nspInd(p)·[c ⊥ p]` of the peeled bilinear form, supported on the
primes `p > z`. -/
def peelA (Pa : Work.FITop.Params) (c z : ℕ) (m : ℕ) : ℂ :=
  if m.Prime ∧ z < m then
    (ArithmeticFunction.moebius m : ℂ) * Work.FIArea7.nspInd Pa m
      * (if Nat.Coprime c m then (1 : ℂ) else 0)
  else 0

/-- The `q`-coefficient `μ(q)·nspInd(q)·[c ⊥ q]·(1+ν(q,z))^{-1}` of the peeled bilinear form,
supported on `q > z`. -/
def peelB (Pa : Work.FITop.Params) (c u z : ℕ) (n : ℕ) : ℂ :=
  if z < n then
    (ArithmeticFunction.moebius n : ℂ) * Work.FIArea7.nspInd Pa n
      * (if Nat.Coprime c n then (1 : ℂ) else 0)
      * (((1 + Work.FIArea7.largePrimeCount u z n : ℕ) : ℂ))⁻¹
  else 0

/-- The summand of the peeled bilinear form. -/
def peelT (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k : ℤ) (c u z : ℕ)
    (P : ℝ → ℝ) (m n : ℕ) : ℂ :=
  if m * n ≤ u then
    peelA Pa c z m * peelB Pa c u z n
      * ((P ((c : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)
      * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (m * n))
  else 0

/-- The peeled bilinear form: the double sum of `peelT` over `[1, M0]²` with `M0 = ⌊u/(z+1)⌋`. -/
def peelBilinSum (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k : ℤ) (c u z : ℕ)
    (P : ℝ → ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (peelBigM u z), ∑ n ∈ Finset.Icc 1 (peelBigM u z),
    peelT Pa chi k c u z P m n

/-- The diagonal correction: the part of the bilinear form with `m ∣ n`. -/
def peelDiagSum (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k : ℤ) (c u z : ℕ)
    (P : ℝ → ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (peelBigM u z),
    ∑ n ∈ (Finset.Icc 1 (peelBigM u z)).filter (fun n => m ∣ n), peelT Pa chi k c u z P m n

/-- `‖μ(m)‖ ≤ 1` in `ℂ`. -/
lemma norm_moebius_cast_le (m : ℕ) : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or m with h | h | h <;> rw [h] <;> norm_num

/-- The `p`-coefficient has norm at most `1`. -/
lemma norm_peelA_le (Pa : Work.FITop.Params) (c z : ℕ) (m : ℕ) : ‖peelA Pa c z m‖ ≤ 1 := by
  unfold peelA
  split
  · have h1 : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := norm_moebius_cast_le m
    have h2 : ‖Work.FIArea7.nspInd Pa m‖ ≤ 1 := Work.FIArea7.norm_nspInd_le_one Pa m
    have h3 : ‖(if Nat.Coprime c m then (1 : ℂ) else 0)‖ ≤ 1 := by split <;> simp
    calc ‖(ArithmeticFunction.moebius m : ℂ) * Work.FIArea7.nspInd Pa m
            * (if Nat.Coprime c m then (1 : ℂ) else 0)‖
        ≤ ‖(ArithmeticFunction.moebius m : ℂ) * Work.FIArea7.nspInd Pa m‖
            * ‖(if Nat.Coprime c m then (1 : ℂ) else 0)‖ := le_of_eq (norm_mul _ _)
      _ ≤ 1 * 1 := by
          refine mul_le_mul ?_ h3 (norm_nonneg _) (by norm_num)
          calc ‖(ArithmeticFunction.moebius m : ℂ) * Work.FIArea7.nspInd Pa m‖
              ≤ ‖(ArithmeticFunction.moebius m : ℂ)‖ * ‖Work.FIArea7.nspInd Pa m‖ := le_of_eq (norm_mul _ _)
            _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
            _ ≤ 1 := by norm_num
      _ ≤ 1 := by norm_num
  · simp

/-- The `q`-coefficient has norm at most `1`. -/
lemma norm_peelB_le (Pa : Work.FITop.Params) (c u z : ℕ) (n : ℕ) : ‖peelB Pa c u z n‖ ≤ 1 := by
  unfold peelB
  split
  · set μ : ℂ := (ArithmeticFunction.moebius n : ℂ) * Work.FIArea7.nspInd Pa n
        * (if Nat.Coprime c n then (1 : ℂ) else 0) with hμ
    have h1 : ‖μ‖ ≤ 1 := by
      rw [hμ]
      calc ‖(ArithmeticFunction.moebius n : ℂ) * Work.FIArea7.nspInd Pa n
              * (if Nat.Coprime c n then (1 : ℂ) else 0)‖
          ≤ ‖(ArithmeticFunction.moebius n : ℂ) * Work.FIArea7.nspInd Pa n‖
              * ‖(if Nat.Coprime c n then (1 : ℂ) else 0)‖ := le_of_eq (norm_mul _ _)
        _ ≤ 1 * 1 := by
            refine mul_le_mul ?_ (by split <;> simp) (norm_nonneg _) (by norm_num)
            calc ‖(ArithmeticFunction.moebius n : ℂ) * Work.FIArea7.nspInd Pa n‖
                ≤ ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖Work.FIArea7.nspInd Pa n‖ := le_of_eq (norm_mul _ _)
              _ ≤ 1 * 1 := mul_le_mul (norm_moebius_cast_le n)
                  (Work.FIArea7.norm_nspInd_le_one Pa n) (norm_nonneg _) (by norm_num)
              _ ≤ 1 := by norm_num
        _ ≤ 1 := by norm_num
    have h2 : ‖(((1 + Work.FIArea7.largePrimeCount u z n : ℕ) : ℂ))⁻¹‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_natCast]
      have h3 : (1 : ℝ) ≤ ((1 + Work.FIArea7.largePrimeCount u z n : ℕ) : ℝ) := by
        have : 1 ≤ 1 + Work.FIArea7.largePrimeCount u z n := Nat.le_add_right _ _
        exact_mod_cast this
      rw [inv_le_one₀ (by linarith)]
      exact h3
    calc ‖μ * (((1 + Work.FIArea7.largePrimeCount u z n : ℕ) : ℂ))⁻¹‖
        = ‖μ‖ * ‖(((1 + Work.FIArea7.largePrimeCount u z n : ℕ) : ℂ))⁻¹‖ := norm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ ≤ 1 := by norm_num
  · simp

end

end Work.FIArea7.smallCInner2EpsAux
