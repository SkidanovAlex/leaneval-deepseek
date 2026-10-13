/-
Copyright: work module for the Elgindi finite-time singularity project.

# The multiplier estimate for the `ℋᵏ`-integrand: the algebraic core

The pieces of `Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le` that do not mention the
`SmoothOpen` smoothness of the datum:

* `zmulConst k = ((k+1)³ + (k+1)⁵)·4ᵏ + 1`, the explicit constant of the estimate;
* `contDiffOn_nat_of_smoothOrder`: a `C^∞` function on a set is `C^n` there;
* `smoothOpen_zmul`: the product of a `z`-only `C^∞` factor with a function `C^∞` on the
  open quadrant is `C^∞` on the open quadrant;
* `zmul_pt`: **the algebraic core**.  Given, at a fixed point `(z,θ)`, the two Leibniz
  expansions of `D_z^i (φ·g)` and `D_z^jD_θ^i (φ·g)`, it proves
  `HkIntegrand α k (φ·g) z θ ≤ zmulConst k·(1+K)²·HkIntegrand α k g z θ`
  from the bounds `|Zop^b φ z| ≤ K` (`b ≤ k`).  The proof is the binomial Cauchy–Schwarz
  `Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le` applied to each summand of the two blocks
  of the integrand, the `y`-sums being partial sums of the blocks of `HkIntegrand α k g z θ`
  (`sq_le_HkIntegrand_z` / `sq_le_HkIntegrand_mixed`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Stability.Cutoff
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option maxHeartbeats 1600000

/-! ## The constant -/

/-- The constant of the multiplier estimate: `((k+1)³ + (k+1)⁵)·4ᵏ + 1`.  It is explicit and
does not depend on `α`, `φ`, `K` or `g`. -/
def zmulConst (k : ℕ) : ℝ :=
  (((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2 + 1

theorem zmulConst_pos (k : ℕ) : 0 < zmulConst k := by
  have h1 : (0 : ℝ) < ((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5 := by positivity
  have h2 : (0 : ℝ) ≤ ((2 : ℝ) ^ k) ^ 2 := sq_nonneg _
  have h3 : (0 : ℝ) ≤ (((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2 :=
    mul_nonneg h1.le h2
  simp only [zmulConst]
  linarith

/-! ## Elementary helpers -/

/-- A function of one variable which is `C^∞` on a set is `C^n` there, for every finite `n`. -/
theorem contDiffOn_nat_of_smoothOrder {φ : ℝ → ℝ} {V : Set ℝ} (n : ℕ)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder φ V) : ContDiffOn ℝ n φ V :=
  h.of_le (by simp [Work.Stability.smoothOrder])

/-- The product of a `z`-only `C^∞` factor with a function `C^∞` on the *open* quadrant is
again `C^∞` on the open quadrant. -/
theorem smoothOpen_zmul {φ : ℝ → ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1)))
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => φ z * g z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen]
  have hfst : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => φ p.1)
      Work.FTS.EllipticEst.Q0 :=
    hsm.comp contDiffOn_fst (fun p hp => by
      have hp1 : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      exact Set.mem_Ioi.mpr (by linarith))
  exact hfst.mul hg

/-! ## The pointwise algebraic core -/

/-- **The algebraic core of the multiplier estimate.**  If at the point `(z,θ)` the two
Leibniz expansions of `D_z^i (φ·g)` and `D_z^jD_θ^i (φ·g)` hold (with the `z`-only multiplier
`φ`) and the iterated `Zop`-derivatives of `φ` at `z` are bounded by `K`, then the
`ℋᵏ`-integrand of `φ·g` is bounded by `zmulConst k·(1+K)²` times that of `g`. -/
theorem zmul_pt (α : ℝ) (k : ℕ) (φ : ℝ → ℝ) (g : ℝ → ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    {z θ : ℝ} (hB : ∀ b ≤ k, |Work.Spaces.Zop^[b] φ z| ≤ K)
    (hexpZ : ∀ i ≤ k, Work.Spaces.DzIter i (fun z θ => φ z * g z θ) z θ =
      ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
        (Work.Spaces.Zop^[b] φ z * Work.Spaces.DzIter (i - b) g z θ))
    (hexpM : ∀ j i, 1 ≤ i → i + j ≤ k →
      Work.Spaces.mixed j i (fun z θ => φ z * g z θ) z θ =
      ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
        (Work.Spaces.Zop^[b] φ z * Work.Spaces.mixed (j - b) i g z θ)) :
    Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ
      ≤ zmulConst k * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ := by
  have hQnn : 0 ≤ Work.Spaces.HkIntegrand α k g z θ :=
    Work.Spaces.HkIntegrand_nonneg α k g z θ
  have hchoose : ∀ (m b : ℕ), m ≤ k → |((m.choose b : ℕ) : ℝ)| ≤ (2 : ℝ) ^ k := by
    intro m b hmk
    calc |((m.choose b : ℕ) : ℝ)| = ((m.choose b : ℕ) : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
      _ ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast Nat.choose_le_two_pow m b
      _ = (2 : ℝ) ^ m := by push_cast; ring
      _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hmk
  -- a partial sum of the radial block is bounded by the whole integrand
  have hzsum : ∀ i : ℕ, i ≤ k →
      (∑ m ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter m g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ Work.Spaces.HkIntegrand α k g z θ := by
    intro i hik
    rw [Work.Spaces.HkIntegrand]
    have hsub : (∑ m ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter m g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (∑ m ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter m g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro m hm
          exact Finset.mem_range.mpr (by
            have := Finset.mem_range.mp hm
            omega))
        (fun m _ _ => sq_nonneg _)
    exact le_trans hsub (le_add_of_nonneg_right (Work.Spaces.hkMixedSum_nonneg α k g z θ))
  -- a partial sum of a row of the mixed block is bounded by `(j+1)` integrands
  have hmsum : ∀ i j : ℕ, 1 ≤ i → i + j ≤ k →
      (∑ m ∈ Finset.range (j + 1),
        (Work.Spaces.mixed m i g z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ((j : ℝ) + 1) * Work.Spaces.HkIntegrand α k g z θ := by
    intro i j hi1 hij
    calc (∑ m ∈ Finset.range (j + 1),
          (Work.Spaces.mixed m i g z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∑ _m ∈ Finset.range (j + 1), Work.Spaces.HkIntegrand α k g z θ :=
          Finset.sum_le_sum fun m hm => by
            have hmj : m ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
            exact Work.Spaces.sq_le_HkIntegrand_mixed α k g z θ i m hi1 (by omega)
      _ = ((j : ℝ) + 1) * Work.Spaces.HkIntegrand α k g z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- ### the radial block of the product
  have hZi : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => φ z * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ (((k : ℝ) + 1) * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
          * Work.Spaces.HkIntegrand α k g z θ := by
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => φ z * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
            * Work.Spaces.HkIntegrand α k g z θ := by
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      -- multiply the Leibniz expansion by the weight, then Cauchy–Schwarz
      have hmul : Work.Spaces.DzIter i (fun z θ => φ z * g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.Zop^[b] φ z * (Work.Spaces.DzIter (i - b) g z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by
        rw [hexpZ i hik, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [hmul]
      have hbin := Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le (i := i) (D := (2 : ℝ) ^ k)
        (K := K) hK (x := fun b => Work.Spaces.Zop^[b] φ z)
        (y := fun m => Work.Spaces.DzIter m g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        (fun b hb => hB b (le_trans hb hik))
        (fun b hb => hchoose i b hik)
      have hbin' : (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Spaces.Zop^[b] φ z * (Work.Spaces.DzIter (i - b) g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
          ≤ (((i : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
              * (∑ m ∈ Finset.range (i + 1),
                  (Work.Spaces.DzIter m g z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hbin
      refine le_trans hbin' ?_
      have hconst : (((i : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
          ≤ (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2 := by
        have hbase : ((i : ℝ) + 1) * (2 : ℝ) ^ k ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right
            (by
              have : (i : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hik
              linarith)
            (by positivity)
        have hle : ((i : ℝ) + 1) * (2 : ℝ) ^ k * K ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ k * K :=
          mul_le_mul_of_nonneg_right hbase hK
        exact pow_le_pow_left₀ (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK)
          hle 2
      exact mul_le_mul hconst (hzsum i hik) (Finset.sum_nonneg fun m _ => sq_nonneg _)
        (by positivity)
    calc (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => φ z * g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (k + 1), ((((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
            * Work.Spaces.HkIntegrand α k g z θ) := Finset.sum_le_sum hterm
      _ = (((k : ℝ) + 1) * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
            * Work.Spaces.HkIntegrand α k g z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- ### the mixed block of the product
  have hMi : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => φ z * g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ (((k : ℝ) + 1) ^ 3 * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
          * Work.Spaces.HkIntegrand α k g z θ := by
    have hsummand : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => φ z * g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ (((k : ℝ) + 1) * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
            * Work.Spaces.HkIntegrand α k g z θ := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc]
        obtain ⟨hi1, hij⟩ := hc
        have hjn : j ≤ k := by omega
        have hmul : Work.Spaces.mixed j i (fun z θ => φ z * g z θ) z θ
              * Work.Spaces.Wt α z θ
            = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Spaces.Zop^[b] φ z
                    * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ)) := by
          rw [hexpM j i hi1 hij, Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
        rw [hmul]
        have hbin := Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le (i := j) (D := (2 : ℝ) ^ k)
          (K := K) hK (x := fun b => Work.Spaces.Zop^[b] φ z)
          (y := fun m => Work.Spaces.mixed m i g z θ * Work.Spaces.Wt α z θ)
          (fun b hb => hB b (le_trans hb hjn))
          (fun b hb => hchoose j b hjn)
        have hbin' : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Spaces.Zop^[b] φ z * (Work.Spaces.mixed (j - b) i g z θ
                  * Work.Spaces.Wt α z θ))) ^ 2
            ≤ (((j : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
                * (∑ m ∈ Finset.range (j + 1),
                    (Work.Spaces.mixed m i g z θ * Work.Spaces.Wt α z θ) ^ 2) := by
          simpa only [Nat.cast_add, Nat.cast_one] using hbin
        refine le_trans hbin' ?_
        have hconst : (((j : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
            ≤ (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2 := by
          have hbase : ((j : ℝ) + 1) * (2 : ℝ) ^ k ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right
              (by
                have : (j : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hjn
                linarith)
              (by positivity)
          have hle : ((j : ℝ) + 1) * (2 : ℝ) ^ k * K ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ k * K :=
            mul_le_mul_of_nonneg_right hbase hK
          exact pow_le_pow_left₀ (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK)
            hle 2
        have hA : (j : ℝ) + 1 ≤ (k : ℝ) + 1 := by
          have : (j : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hjn
          linarith
        have hAZ : 0 ≤ (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2 := by positivity
        calc (((j : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
              * (∑ m ∈ Finset.range (j + 1),
                  (Work.Spaces.mixed m i g z θ * Work.Spaces.Wt α z θ) ^ 2)
            ≤ (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
                * (((j : ℝ) + 1) * Work.Spaces.HkIntegrand α k g z θ) :=
              mul_le_mul hconst (hmsum i j hi1 hij)
                (Finset.sum_nonneg fun m _ => sq_nonneg _) hAZ
          _ ≤ (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
                * (((k : ℝ) + 1) * Work.Spaces.HkIntegrand α k g z θ) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hQnn) hAZ
          _ = (((k : ℝ) + 1) * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
                * Work.Spaces.HkIntegrand α k g z θ := by ring
      · rw [if_neg hc]
        exact mul_nonneg (by positivity) hQnn
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (fun z θ => φ z * g z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
            ((((k : ℝ) + 1) * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
              * Work.Spaces.HkIntegrand α k g z θ) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hsummand i hi j hj
      _ = (((k : ℝ) + 1) ^ 3 * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
            * Work.Spaces.HkIntegrand α k g z θ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- ### add the two blocks and absorb `K² ≤ (1+K)²` together with the `+1`
  conv_lhs => rw [Work.Spaces.HkIntegrand]
  refine le_trans (add_le_add hZi hMi) ?_
  have hKsq : K ^ 2 ≤ (1 + K) ^ 2 := by nlinarith [hK]
  have hkey : (((k : ℝ) + 1) * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
        * Work.Spaces.HkIntegrand α k g z θ
      + (((k : ℝ) + 1) ^ 3 * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
        * Work.Spaces.HkIntegrand α k g z θ
      = ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2) * K ^ 2
        * Work.Spaces.HkIntegrand α k g z θ := by ring
  rw [hkey]
  have h0 : 0 ≤ ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2) := by positivity
  have hstep1 : ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2) * K ^ 2
        * Work.Spaces.HkIntegrand α k g z θ
      ≤ ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2) * (1 + K) ^ 2
        * Work.Spaces.HkIntegrand α k g z θ := by
    calc ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2) * K ^ 2
          * Work.Spaces.HkIntegrand α k g z θ
        = ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2)
            * (K ^ 2 * Work.Spaces.HkIntegrand α k g z θ) := by ring
      _ ≤ ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2)
            * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKsq hQnn) h0
      _ = ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2) * (1 + K) ^ 2
            * Work.Spaces.HkIntegrand α k g z θ := by ring
  refine le_trans hstep1 ?_
  have h1 : 0 ≤ (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ :=
    mul_nonneg (by positivity) hQnn
  calc ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2) * (1 + K) ^ 2
        * Work.Spaces.HkIntegrand α k g z θ
      = ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2)
          * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ) := by ring
    _ ≤ ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2 + 1)
          * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ) :=
        mul_le_mul_of_nonneg_right (by linarith) h1
    _ = zmulConst k * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ := by
        simp only [zmulConst]
        ring

end Work.FTS.StrongPersist.L3Aux
