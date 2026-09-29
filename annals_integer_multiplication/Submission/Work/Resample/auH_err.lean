import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.fxPotSucc
import Submission.Work.Fx.expRec
import Submission.Work.Fx.expStepErr

/-!
# Error of the fixed-point Horner recursion for the Gaussian weights (paper Lemma 4.9)

`auH p Z j` is the fixed-point Horner recursion of *scale* `2^P` (`P = auPrec p`)
computing the truncated exponential `Σ_{k ≤ j} (−y)^k / k!`:

`Q₀ = 2^P`, `Q_{j+1} = 2^P + ⌊⌊Z·Q_j / 2^P⌋ / (M − j)⌋`   (`M = auNstep p = 2P`),

and `Work.Fx.pot y d i = Σ_{k<i} y^k · d!/(d+k)!` is the matching "error potential"
(so `pot y (M−j) (j+1)` is the exact partial sum computed at stage `j`).

This file proves the truncation-error estimate `auH_err`: for every `j ≤ M`,

`|auH p Z j / 2^P − pot (Z/2^P) (M−j) (j+1)| ≤ (2/2^P) · exp|Z/2^P|`.

The proof is the standard two-step analysis: each Horner stage performs two truncated
divisions, each of error `< 1`, which contributes `≤ 2/2^P` at the working scale, and the
error recursion `E_{j+1} = (y/d)·E_j + ε` with `|ε| ≤ 2/2^P` unrolls into the potential
recursion, whose values are dominated by `exp |y|`.
-/

set_option autoImplicit false

namespace Work.Resample

open Work.Fx

/-- `pot Z d 1 = 1`. -/
lemma pot_one (Z : ℝ) (d : ℕ) : Work.Fx.pot Z d 1 = 1 := by
  rw [Work.Fx.pot, Finset.sum_range_one, pow_zero, Nat.add_zero, one_mul]
  exact div_self (by exact_mod_cast Nat.factorial_ne_zero d)

/-- One-step error of the fixed-point Horner recursion `auH`: at the working scale `2^P`
the two truncated divisions of one step introduce an error of at most `2/2^P`. -/
lemma auH_step_err (p : ℕ) (Z Q : ℤ) (d : ℕ) (hd : 1 ≤ d) :
    |(((Int.tdiv (Int.tdiv (Z * Q) ((2:ℤ)^(auPrec p))) (d:ℤ)) : ℤ) : ℝ) / (2:ℝ)^(auPrec p)
      - ((Z:ℝ)/(2:ℝ)^(auPrec p)) / (d:ℝ) * ((Q:ℝ)/(2:ℝ)^(auPrec p))|
      ≤ 2 / (2:ℝ)^(auPrec p) := by
  have h2P : (0:ℝ) < (2:ℝ)^(auPrec p) := by positivity
  have hp : (0:ℤ) < (2:ℤ)^(auPrec p) := by positivity
  have hdz : (0:ℤ) < (d:ℤ) := by omega
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hdz
  have key := Work.Fx.tdiv_tdiv_abs_le_two (Z*Q) ((2:ℤ)^(auPrec p)) (d:ℤ) hp hdz
  have key' : |((Int.tdiv (Int.tdiv (Z*Q) ((2:ℤ)^(auPrec p))) (d:ℤ) : ℤ) : ℝ)
      - (Z:ℝ)*(Q:ℝ)/((2:ℝ)^(auPrec p)*(d:ℝ))| ≤ 2 := by
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] using key
  have hW : ((Int.tdiv (Int.tdiv (Z*Q) ((2:ℤ)^(auPrec p))) (d:ℤ) : ℤ) : ℝ) / (2:ℝ)^(auPrec p)
      - ((Z:ℝ)/(2:ℝ)^(auPrec p)) / (d:ℝ) * ((Q:ℝ)/(2:ℝ)^(auPrec p))
      = (((Int.tdiv (Int.tdiv (Z*Q) ((2:ℤ)^(auPrec p))) (d:ℤ) : ℤ) : ℝ)
          - (Z:ℝ)*(Q:ℝ)/((2:ℝ)^(auPrec p)*(d:ℝ))) / (2:ℝ)^(auPrec p) := by
    field_simp
  rw [hW, abs_div, abs_of_pos h2P]
  exact div_le_div_of_nonneg_right key' (le_of_lt h2P)

/-- **Truncation error of the weight recursion.**  For every stage `j ≤ auNstep p` the
fixed-point Horner value `auH p Z j`, read at the working scale `2^{auPrec p}`, differs from
the exact partial sum `pot (Z/2^P) (auNstep p − j) (j+1)` by at most `(2/2^P)·exp|Z/2^P|`. -/
theorem auH_err (p : ℕ) (Z : ℤ) (j : ℕ) (hj : j ≤ auNstep p) :
    |(auH p Z j : ℝ) / (2:ℝ)^(auPrec p) - Work.Fx.pot ((Z:ℝ)/(2:ℝ)^(auPrec p)) (auNstep p - j) (j + 1)|
      ≤ (2 / (2:ℝ)^(auPrec p)) * Real.exp |(Z:ℝ)/(2:ℝ)^(auPrec p)| := by
  have h2P : (0:ℝ) < (2:ℝ)^(auPrec p) := by positivity
  -- `P j`: the error at stage `j` is bounded by `(2/2^P)·pot |y| (M−j) (j+1)`.
  have main : ∀ j, j ≤ auNstep p →
      |(auH p Z j : ℝ) / (2:ℝ)^(auPrec p)
        - Work.Fx.pot ((Z:ℝ)/(2:ℝ)^(auPrec p)) (auNstep p - j) (j + 1)|
      ≤ (2 / (2:ℝ)^(auPrec p))
        * Work.Fx.pot |(Z:ℝ)/(2:ℝ)^(auPrec p)| (auNstep p - j) (j + 1) := by
    intro j
    induction j with
    | zero =>
      intro _
      have h0 : (auH p Z 0 : ℝ) / (2:ℝ)^(auPrec p) = 1 := by
        rw [show auH p Z 0 = (2:ℤ)^(auPrec p) from rfl]
        push_cast
        exact div_self (ne_of_gt h2P)
      have h1 : Work.Fx.pot ((Z:ℝ)/(2:ℝ)^(auPrec p)) (auNstep p - 0) (0+1) = 1 := by
        simpa using pot_one ((Z:ℝ)/(2:ℝ)^(auPrec p)) (auNstep p)
      have h2 : Work.Fx.pot |(Z:ℝ)/(2:ℝ)^(auPrec p)| (auNstep p - 0) (0+1) = 1 := by
        simpa using pot_one |(Z:ℝ)/(2:ℝ)^(auPrec p)| (auNstep p)
      rw [h0, h1, h2]
      have hpos : (0:ℝ) ≤ 2 / (2:ℝ)^(auPrec p) := by positivity
      simpa using hpos
    | succ j ih =>
      intro hj1
      have hj : j ≤ auNstep p := by omega
      have hrec := ih hj
      -- shorten the notation
      set d : ℕ := auNstep p - j with hddef
      set y : ℝ := (Z:ℝ)/(2:ℝ)^(auPrec p) with hydef
      set Q : ℤ := auH p Z j with hQdef
      have hd1 : 1 ≤ d := by rw [hddef]; omega
      have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : (0:ℤ) < (d:ℤ))
      have hdcast : (auNstep p : ℤ) - (j:ℤ) = (d:ℤ) := by rw [hddef]; omega
      -- the numerator of the next Horner value
      set Tr : ℝ := ((Int.tdiv (Int.tdiv (Z * Q) ((2:ℤ)^(auPrec p))) ((d:ℤ)) : ℤ) : ℝ)
        with hTrdef
      -- unfold one Horner step
      have hAuH : (auH p Z (j+1) : ℝ) / (2:ℝ)^(auPrec p) = 1 + Tr / (2:ℝ)^(auPrec p) := by
        have h : (auH p Z (j+1) : ℝ) = (2:ℝ)^(auPrec p) + Tr := by
          rw [show auH p Z (j+1) = (2:ℤ)^(auPrec p)
                + Int.tdiv (Int.tdiv (Z * auH p Z j) ((2:ℤ)^(auPrec p)))
                    ((auNstep p : ℤ) - (j:ℤ)) from rfl,
              hdcast, show Z * auH p Z j = Z * Q from by rw [hQdef]]
          push_cast
          rfl
        rw [h, add_div, div_self (ne_of_gt h2P)]
      -- the matching potential recursion (both for `y` and for `|y|`)
      have hPot : Work.Fx.pot y (auNstep p - (j+1)) (j+1+1)
          = 1 + (y / (d:ℝ)) * Work.Fx.pot y d (j+1) := by
        have h := fxPotSucc y d (j+1) hd1
        rw [show auNstep p - (j+1) = d - 1 by rw [hddef]; omega]
        exact h
      have hPotAbs : Work.Fx.pot |y| (auNstep p - (j+1)) (j+1+1)
          = 1 + (|y| / (d:ℝ)) * Work.Fx.pot |y| d (j+1) := by
        have h := fxPotSucc |y| d (j+1) hd1
        rw [show auNstep p - (j+1) = d - 1 by rw [hddef]; omega]
        exact h
      -- reduce the goal to the error recursion
      have hdiff : (auH p Z (j+1) : ℝ) / (2:ℝ)^(auPrec p)
            - Work.Fx.pot y (auNstep p - (j+1)) (j+1+1)
          = Tr / (2:ℝ)^(auPrec p) - (y / (d:ℝ)) * Work.Fx.pot y d (j+1) := by
        rw [hAuH, hPot]; ring
      rw [hdiff]
      have htrunc : |Tr / (2:ℝ)^(auPrec p) - (y / (d:ℝ)) * ((Q:ℝ)/(2:ℝ)^(auPrec p))|
          ≤ 2 / (2:ℝ)^(auPrec p) := auH_step_err p Z Q d hd1
      have hnonneg : (0:ℝ) ≤ |y| / (d:ℝ) := div_nonneg (abs_nonneg y) (le_of_lt hdR)
      have hsplit : Tr / (2:ℝ)^(auPrec p) - (y / (d:ℝ)) * Work.Fx.pot y d (j+1)
          = (y / (d:ℝ)) * ((Q:ℝ)/(2:ℝ)^(auPrec p) - Work.Fx.pot y d (j+1))
            + (Tr / (2:ℝ)^(auPrec p) - (y / (d:ℝ)) * ((Q:ℝ)/(2:ℝ)^(auPrec p))) := by ring
      calc |Tr / (2:ℝ)^(auPrec p) - (y / (d:ℝ)) * Work.Fx.pot y d (j+1)|
          = |(y / (d:ℝ)) * ((Q:ℝ)/(2:ℝ)^(auPrec p) - Work.Fx.pot y d (j+1))
              + (Tr / (2:ℝ)^(auPrec p)
                  - (y / (d:ℝ)) * ((Q:ℝ)/(2:ℝ)^(auPrec p)))| := by rw [hsplit]
        _ ≤ |(y / (d:ℝ)) * ((Q:ℝ)/(2:ℝ)^(auPrec p) - Work.Fx.pot y d (j+1))|
              + |Tr / (2:ℝ)^(auPrec p)
                  - (y / (d:ℝ)) * ((Q:ℝ)/(2:ℝ)^(auPrec p))| := abs_add_le _ _
        _ ≤ (|y| / (d:ℝ)) * ((2 / (2:ℝ)^(auPrec p)) * Work.Fx.pot |y| d (j+1))
              + 2 / (2:ℝ)^(auPrec p) := by
            apply add_le_add
            · rw [abs_mul, abs_div, abs_of_pos hdR]
              exact mul_le_mul_of_nonneg_left hrec hnonneg
            · exact htrunc
        _ = (2 / (2:ℝ)^(auPrec p))
              * Work.Fx.pot |y| (auNstep p - (j+1)) (j+1+1) := by
            rw [hPotAbs]; ring
  calc |(auH p Z j : ℝ) / (2:ℝ)^(auPrec p)
        - Work.Fx.pot ((Z:ℝ)/(2:ℝ)^(auPrec p)) (auNstep p - j) (j + 1)|
      ≤ (2 / (2:ℝ)^(auPrec p))
        * Work.Fx.pot |(Z:ℝ)/(2:ℝ)^(auPrec p)| (auNstep p - j) (j + 1) := main j hj
    _ ≤ (2 / (2:ℝ)^(auPrec p)) * Real.exp |(Z:ℝ)/(2:ℝ)^(auPrec p)| :=
        mul_le_mul_of_nonneg_left
          (Work.Fx.expRec.2.2.1 |(Z:ℝ)/(2:ℝ)^(auPrec p)| (abs_nonneg _) (auNstep p - j) (j+1))
          (by positivity)

end Work.Resample
