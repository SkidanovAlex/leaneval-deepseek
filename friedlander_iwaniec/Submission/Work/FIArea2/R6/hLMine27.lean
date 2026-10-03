import Mathlib
import Submission.Work.FIArea2.R6.KCap
import Submission.Work.FIArea2.R6.ubox_bound3
import Submission.Work.FIArea2.R6.hbox6_of_ubox3
import Submission.Work.FIArea2.R6.hL_of_box
import Submission.Work.FIArea2.R6.LD_lossy
import Submission.Work.FIArea2.R6.WC_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `FIArea2/R6/hLMine27` — the §9 lacunarity input at the raised cap `2^27`

Chains, all sorry-free,

  `R6/ubox_bound3` (exponent `2^26`, from `R6/uboxSum_le_dsum3` + `R6/WC_cube` instantiated with
  `R6/LD_lossy` and `R6/WC_basic` + `sum_tau_pow_div_le 26`)
  → `R6/hbox6_of_ubox3` (exponent `2^26 + 200`)
  → `R6/hL_of_box` (the dyadic `h`-tsum exchange),

producing `LacPropK (2^26 + 200)`: the §9 lacunarity input with exponent cap `2^26 + 200 ≤ 2^27`, which
`R6/KCap` and `R6/A27.area2_6e_A27` consume.  `R6/Inputs6.LacProp` (cap `2^10`) is left untouched.
-/

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `R6/LD_lossy`, with the `[NeZero]` instance made explicit for use as a hypothesis. -/
private lemma hLDinst : ∀ (c X S : ℕ) [NeZero c],
    (∑ h1 ∈ zPz X, ∑ v1 ∈ zPz S, ∑ v2 ∈ zPz S,
        (((Finset.univ : Finset (ZMod c)).filter
            (fun z => (v2 : ZMod c) * z ^ 2 = (v1 : ZMod c) * ((h1 : ZMod c)) ^ 2)).card : ℝ)
          / ((max v1.natAbs v2.natAbs : ℕ) : ℝ))
      ≤ 64 * (X : ℝ) * (S : ℝ) * ((c.divisors.card : ℝ)) ^ 5 := by
  intro c X S
  exact Work.FIArea2.R6.LD_lossy c X S

/-- **The §9 lacunarity input at the raised cap `2^26 + 200`.** -/
theorem hLMine27 : Work.FIArea2.R6.LacPropK (2 ^ 26 + 200) := by
  obtain ⟨CU, hCU, hU⟩ := ubox_bound3 hLDinst Work.FIArea2.R6.WC_basic
  obtain ⟨C1, hC1, hbox⟩ := hbox6_of_ubox3 ⟨CU, hCU, hU⟩
  have hbox' : ∀ (R : ℕ), 1 ≤ R → ∀ (X : ℕ), 1 ≤ X → ∀ (Y : ℕ), 1 ≤ Y →
      (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
          (∑ h1 ∈ Finset.Icc (-(X : ℤ)) (X : ℤ), ∑ h2 ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ),
            (((u1 * h1 ^ 2 - u2 * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)))
        ≤ (C1 * (2 : ℝ) ^ ((2 : ℕ) ^ (26 : ℕ) + 200)) * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
          * (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2))
              ^ ((2 : ℕ) ^ (26 : ℕ) + 200) := by
    intro R hR X hX Y hY
    have h := hbox R X Y hR hX hY
    have hboxun : (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
          (∑ h1 ∈ Finset.Icc (-(X : ℤ)) (X : ℤ), ∑ h2 ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ),
            (((u1 * h1 ^ 2 - u2 * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)))
        = Work.FIArea2.R6.boxSum6 R X Y := by
      rw [Work.FIArea2.R6.boxSum6]
    rw [hboxun]
    have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    have hge : (5 : ℝ) ≤ (R : ℝ) + (X : ℝ) + (Y : ℝ) + 2 := by linarith
    have hlog1 : (1 : ℝ) ≤ Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) := by
      have h5 : (1 : ℝ) ≤ Real.log 5 := by
        have hh := Real.log_le_log (Real.exp_pos 1)
          (by linarith [Real.exp_one_lt_three] : Real.exp 1 ≤ 5)
        rwa [Real.log_exp] at hh
      exact le_trans h5 (Real.log_le_log (by norm_num) hge)
    have hbase : (0 : ℝ) ≤ 1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) := by linarith
    have hle : 1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)
        ≤ 2 * Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2) := by linarith
    calc Work.FIArea2.R6.boxSum6 R X Y
        ≤ C1 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
            * (1 + Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2))
                ^ ((2 : ℕ) ^ (26 : ℕ) + 200) := h
      _ ≤ C1 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
            * (2 * Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2))
                ^ ((2 : ℕ) ^ (26 : ℕ) + 200) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ hbase hle _
      _ = (C1 * (2 : ℝ) ^ ((2 : ℕ) ^ (26 : ℕ) + 200)) * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
            * (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2))
                ^ ((2 : ℕ) ^ (26 : ℕ) + 200) := by
          rw [mul_pow]
          simp only [mul_assoc, mul_comm, mul_left_comm]
  obtain ⟨C2, hC2, hfin⟩ := hL_of_box (C1 * (2 : ℝ) ^ ((2 : ℕ) ^ (26 : ℕ) + 200))
    (by positivity) ((2 : ℕ) ^ (26 : ℕ) + 200) hbox'
  exact ⟨C2, hC2, (2 : ℕ) ^ (26 : ℕ) + 200, by norm_num, hfin⟩

end

end Work.FIArea2.R6
