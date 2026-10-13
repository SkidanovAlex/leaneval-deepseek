/-
# `gC_eq_famTrig` — the trigonometric form of the Gegenbauer polynomials

`gC n = C_n^{(3/2)}` is the Gegenbauer polynomial of order `3/2`, defined by the classical
three-term recurrence `(n+2) C_{n+2} = (2n+5) x C_{n+1} - (n+3) C_n` with `C_0 = 1`,
`C_1 = 3x` (`Submission/Work/FTS/PhiStar/Gegenbauer/Defs.lean`), and

`famTrig n ψ = Σ_{j ≤ n} famC j · famC (n - j) · cos ((2j - n) ψ)`,   `famC k = (3/2)_k / k!`

is its trigonometric form.  This file proves the classical identity

`gC n (cos ψ) = famTrig n ψ`.

The proof is the standard one.  `famTrig` satisfies the same three-term recurrence as `gC`:

`(n+2) · famTrig (n+2) ψ = (2n+5) · cos ψ · famTrig (n+1) ψ - (n+3) · famTrig n ψ`   (`gtrig_rec`),

obtained by expanding `cos ψ · cos ((2j-(n+1))ψ)` with the product-to-sum formula, shifting
the three summation ranges so that they all run over `j ∈ {0, …, n+2}` (the boundary terms
vanish because `famC k = 0` for `k < 0`), and cancelling the coefficients with the
contiguity relation for `famC` (`famC_coeff_int`).  Two-step induction on `n`, using the base
cases `famTrig 0 ψ = 1`, `famTrig 1 ψ = 3 cos ψ` and `gC`'s recurrence `gC_rec`, gives the
result.
-/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Computability.Reduce
import Mathlib.Tactic.LinearCombination
import Submission.Work.FTS.PhiStar.FamLopAux.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.FTS.PhiStar.FlatWAux.famC_coeff_int
import Submission.Work.FTS.PhiStar.FlatWAux.famTrig_cos_step
import Submission.Work.FTS.PhiStar.FlatWAux.famTrig_shift

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped BigOperators

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-! ## The values of `famC` at `0` and `1` -/

/-- `famC` of a natural number, in product form. -/
private lemma gtrig_famC_nat (n : ℕ) :
    famC (((n : ℕ)) : ℤ)
      = (∏ i ∈ Finset.range n, ((3 : ℝ) / 2 + (i : ℝ))) / (((n.factorial : ℕ)) : ℝ) := by
  rw [show famC (((n : ℕ)) : ℤ)
      = (if (0 : ℤ) ≤ (((n : ℕ)) : ℤ) then
          (∏ i ∈ Finset.range (((n : ℕ)) : ℤ).toNat, ((3 : ℝ) / 2 + i))
            / (((Nat.factorial (((n : ℕ)) : ℤ).toNat : ℕ)) : ℝ)
        else 0) from rfl,
    if_pos (Int.natCast_nonneg n), Int.toNat_natCast]

private lemma gtrig_famC_zero : famC (0 : ℤ) = 1 := by
  have h := gtrig_famC_nat 0
  simpa [Finset.prod_range_zero] using h

private lemma gtrig_famC_one : famC (1 : ℤ) = 3 / 2 := by
  have h := gtrig_famC_nat 1
  simpa [Finset.prod_range_one] using h

/-! ## The two base cases -/

private lemma gtrig_famTrig_zero (ψ : ℝ) : famTrig 0 ψ = 1 := by
  unfold famTrig
  rw [Finset.sum_range_one]
  simp [gtrig_famC_zero]

private lemma gtrig_famTrig_one (ψ : ℝ) : famTrig 1 ψ = 3 * Real.cos ψ := by
  have h : famTrig 1 ψ = (3 : ℝ) / 2 * Real.cos ψ + (3 : ℝ) / 2 * Real.cos ψ := by
    unfold famTrig
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [gtrig_famC_zero, gtrig_famC_one]
    norm_num
  rw [h]
  ring

/-! ## The recurrence satisfied by `famTrig` -/

/-- The pointwise contiguity relation of `famC` in the index form used below. -/
private lemma gtrig_coeff_nat (n j : ℕ) (hj : j ≤ n + 2) :
    ((n : ℝ) + 2) * famC (j : ℤ) * famC ((n : ℤ) + 2 - (j : ℤ))
      - ((2 * (n : ℝ) + 5) / 2) * (famC (j : ℤ) * famC ((n : ℤ) + 1 - (j : ℤ))
          + famC ((j : ℤ) - 1) * famC ((n : ℤ) + 2 - (j : ℤ)))
      + ((n : ℝ) + 3) * famC ((j : ℤ) - 1) * famC ((n : ℤ) + 1 - (j : ℤ)) = 0 := by
  have hc := famC_coeff_int n (j : ℤ) ((n : ℤ) + 2 - (j : ℤ)) (Int.natCast_nonneg j)
    (by omega) (by ring)
  rw [show ((n : ℤ) + 2 - (j : ℤ)) - 1 = (n : ℤ) + 1 - (j : ℤ) from by ring] at hc
  exact hc

/-- The termwise identity behind the recurrence. -/
private lemma gtrig_rec_term (n j : ℕ) (ψ : ℝ) (hj : j ≤ n + 2) :
    ((n : ℝ) + 2)
        * (famC (j : ℤ) * famC ((n : ℤ) + 2 - (j : ℤ))
            * Real.cos ((2 * (j : ℝ) - ((n : ℝ) + 2)) * ψ))
      + ((n : ℝ) + 3)
        * (famC ((j : ℤ) - 1) * famC ((n : ℤ) + 1 - (j : ℤ))
            * Real.cos ((2 * (j : ℝ) - ((n : ℝ) + 2)) * ψ))
      - (2 * (n : ℝ) + 5)
        * ((famC (j : ℤ) * famC ((n : ℤ) + 1 - (j : ℤ))
              + famC ((j : ℤ) - 1) * famC ((n : ℤ) + 2 - (j : ℤ)))
            * Real.cos ((2 * (j : ℝ) - ((n : ℝ) + 2)) * ψ) / 2) = 0 := by
  have hc := gtrig_coeff_nat n j hj
  linear_combination hc * Real.cos ((2 * (j : ℝ) - ((n : ℝ) + 2)) * ψ)

/-- The three-term recurrence of the trigonometric Gegenbauer family. -/
private lemma gtrig_rec (n : ℕ) (ψ : ℝ) :
    ((n : ℝ) + 2) * famTrig (n + 2) ψ
      = (2 * (n : ℝ) + 5) * Real.cos ψ * famTrig (n + 1) ψ
        - ((n : ℝ) + 3) * famTrig n ψ := by
  have hD : famTrig (n + 2) ψ
      = ∑ j ∈ Finset.range (n + 3), famC (j : ℤ) * famC ((n : ℤ) + 2 - (j : ℤ))
          * Real.cos ((2 * (j : ℝ) - ((n : ℝ) + 2)) * ψ) := by
    simp only [famTrig]
    refine Finset.sum_congr ?_ (fun j _ => ?_)
    · exact congrArg Finset.range (by omega)
    · push_cast
      ring
  have h0 : ((n : ℝ) + 2) * famTrig (n + 2) ψ + ((n : ℝ) + 3) * famTrig n ψ
      - (2 * (n : ℝ) + 5) * Real.cos ψ * famTrig (n + 1) ψ = 0 := by
    rw [hD, famTrig_shift n ψ]
    rw [show (2 * (n : ℝ) + 5) * Real.cos ψ * famTrig (n + 1) ψ
          = (2 * (n : ℝ) + 5) * (Real.cos ψ * famTrig (n + 1) ψ) from by ring,
      famTrig_cos_step n ψ]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro j hj
    have hjle : j ≤ n + 2 := by
      have : j < n + 3 := Finset.mem_range.mp hj
      omega
    exact gtrig_rec_term n j ψ hjle
  linear_combination h0

/-! ## The main theorem -/

theorem gC_eq_famTrig (n : ℕ) (ψ : ℝ) :
    Work.FTS.PhiStar.Gegenbauer.gC n (Real.cos ψ) = Work.FTS.PhiStar.famTrig n ψ := by
  induction n using Nat.twoStepInduction with
  | zero => exact (gtrig_famTrig_zero ψ).symm
  | one => exact (gtrig_famTrig_one ψ).symm
  | more n ih1 ih2 =>
    have hmain : ((n : ℝ) + 2) * Work.FTS.PhiStar.Gegenbauer.gC (n + 2) (Real.cos ψ)
        = ((n : ℝ) + 2) * famTrig (n + 2) ψ := by
      rw [Work.FTS.PhiStar.Gegenbauer.gC_rec n (Real.cos ψ), ih1, ih2, gtrig_rec n ψ]
    exact mul_left_cancel₀ (by positivity : ((n : ℝ) + 2) ≠ 0) hmain

end Work.FTS.PhiStar.FlatWAux
