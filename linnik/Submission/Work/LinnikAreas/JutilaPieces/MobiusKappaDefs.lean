import Mathlib
import Submission.Work.LinnikAreas.Density4.KappaDefs
import Submission.Work.LinnikAreas.Density4.selTheta_asymptotic
import Submission.Commons.NumberTheory.Moebius.moebius_abs_le_one

/-!
# Auxiliary definitions for the `1/κ`-weighted Möbius sum

`κ(n) = n·∏_{p | n} (1 + 1/p)` (`Work.LinnikAreas.Density4.kappaR`) is the reciprocal weight
of An's (Graham's) lemmas 11/12.  Here we collect

* `mobKappaW d = μ(d)²/(d·κ(d))`, the weight of the Selberg-diagonalised expansion
  `kappaLogSum z r = Σ_{d} mobKappaW d · selTheta (z/d) (d*r)` (`KappaSum.kappaLogSum_expansion`);
* elementary pointwise bounds for `κ`, which are used to control the auxiliary sums.
-/

open Finset
open scoped BigOperators

namespace Work.LinnikAreas.JutilaPieces

noncomputable section

/-- The Selberg weight `μ(d)²/(d·κ(d))` of the `κ`-sum expansion. -/
def mobKappaW (d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℝ)) ^ 2 / ((d : ℝ) * Work.LinnikAreas.Density4.kappaR d)

/-- `1 ≤ ∏_{p | n} (1 + 1/p)`. -/
lemma one_le_prod_one_add_inv (n : ℕ) :
    1 ≤ ∏ p ∈ n.primeFactors, (1 + (1 : ℝ) / (p : ℝ)) := by
  apply Finset.one_le_prod₀
  intro p hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    have := (Nat.mem_primeFactors.mp hp).1
    exact_mod_cast this.two_le
  have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  linarith

/-- `κ(n) = n · ∏_{p | n}(1 + 1/p)`. -/
lemma kappaR_eq (n : ℕ) :
    Work.LinnikAreas.Density4.kappaR n
      = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 + (1 : ℝ) / (p : ℝ)) := rfl

/-- `κ(n) ≥ 0` for every `n`. -/
lemma kappaR_nonneg' (n : ℕ) : 0 ≤ Work.LinnikAreas.Density4.kappaR n := by
  rw [kappaR_eq]
  exact mul_nonneg (Nat.cast_nonneg n) (by linarith [one_le_prod_one_add_inv n])

/-- `κ(n) > 0` for `n ≥ 1`. -/
lemma kappaR_pos' {n : ℕ} (hn : 1 ≤ n) : 0 < Work.LinnikAreas.Density4.kappaR n := by
  rw [kappaR_eq]
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  exact mul_pos hn' (by linarith [one_le_prod_one_add_inv n])

/-- `n ≤ κ(n)`. -/
lemma kappaR_ge_self' {n : ℕ} (hn : 1 ≤ n) : (n : ℝ) ≤ Work.LinnikAreas.Density4.kappaR n := by
  rw [kappaR_eq]
  have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc (n : ℝ) = (n : ℝ) * 1 := (mul_one _).symm
    _ ≤ (n : ℝ) * ∏ p ∈ n.primeFactors, (1 + (1 : ℝ) / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left (one_le_prod_one_add_inv n) hn'
    _ = Work.LinnikAreas.Density4.kappaR n := by rw [kappaR_eq]

/-- `1/κ(n) ≤ 1/n` for `n ≥ 1`. -/
lemma one_div_kappaR_le_inv' {n : ℕ} (hn : 1 ≤ n) :
    1 / Work.LinnikAreas.Density4.kappaR n ≤ 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  exact one_div_le_one_div_of_le hn' (kappaR_ge_self' hn)

/-- The Selberg weight is nonnegative. -/
lemma mobKappaW_nonneg (d : ℕ) : 0 ≤ mobKappaW d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp [mobKappaW]
  · rw [mobKappaW]
    exact div_nonneg (sq_nonneg _)
      (le_of_lt (mul_pos (by exact_mod_cast h) (kappaR_pos' h)))

/-- `mobKappaW d ≤ 1/d²` for `d ≥ 1`. -/
lemma mobKappaW_le_inv_sq {d : ℕ} (hd : 1 ≤ d) :
    mobKappaW d ≤ 1 / ((d : ℝ) ^ 2) := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hk : (d : ℝ) ≤ Work.LinnikAreas.Density4.kappaR d := kappaR_ge_self' hd
  have hmu : ((ArithmeticFunction.moebius d : ℝ)) ^ 2 ≤ 1 := by
    have h := Commons.NumberTheory.Moebius.moebius_abs_le_one d
    nlinarith [abs_nonneg (ArithmeticFunction.moebius d : ℝ), sq_abs (ArithmeticFunction.moebius d : ℝ)]
  rw [mobKappaW, div_le_div_iff₀ (mul_pos hd' (lt_of_lt_of_le hd' hk)) (by positivity)]
  nlinarith [hmu, hk, hd']

end

end Work.LinnikAreas.JutilaPieces
