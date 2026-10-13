/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `α`-free `ℋⁿ`-integrand bound for a `z`-only multiplier, open class

Support module for `EpsE4Thr/E2hat_HkSq_le_uniform_O.lean`.  This is the `SmoothOpen` port of
`CoercivityFix.E2Bound.HkIntegrand_zmul_le`: for `ψ` of class `C^∞` on `(0,∞)` whose
`Zop`-iterates up to order `n` are bounded by `K ≥ 0`, and `f` of class `SmoothOpen`,

`HkIntegrand α n (ψ·f) z θ ≤ zmulC n · (1+K)² · HkIntegrand α n f z θ`

at every point of the open quadrant, with a constant depending only on `n` (in particular not
on `α`).  The binomial convolution of each slot is estimated by `E2Bound.binom_sum_sq_le`, and
the resulting `y`-sums are partial sums of the two blocks of `HkIntegrand α n f z θ` — the
angular weight `Wt α` factors out of the mixed block, so no `α`-dependence enters the
constant.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.OpenLeibniz
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E2hatOAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The explicit `n`-only constant of the `z`-multiplier estimate. -/
def zmulC (n : ℕ) : ℝ :=
  (((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2 + 1

lemma zmulC_pos (n : ℕ) : 0 < zmulC n := by
  unfold zmulC; positivity

/-- **The `ℋⁿ`-integrand of a product with a `z`-only multiplier**, with a constant
independent of `α`: for `ψ` of class `C^∞` on `(0,∞)` whose `Zop`-iterates up to order `n`
are bounded by `K ≥ 0`, and `f` of class `SmoothOpen`,

`HkIntegrand α n (ψ·f) z θ ≤ zmulC n ·(1+K)²·HkIntegrand α n f z θ`

at every point of the open quadrant. -/
theorem HkIntegrand_zmul_SO (α : ℝ) (n : ℕ) :
    ∀ (ψ : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ b ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] ψ z| ≤ K) →
      (∀ m : ℕ, ContDiffOn ℝ m ψ (Set.Ioi 0)) →
      ∀ f : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α n (fun z θ => ψ z * f z θ) z θ
          ≤ zmulC n * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ := by
  intro ψ K hK hKψ hψ f hf z hz θ hθ
  -- basic facts at the point `(z,θ)`
  have hzpos : 0 < z := hz
  have hQnn : 0 ≤ Work.Spaces.HkIntegrand α n f z θ :=
    Work.Spaces.HkIntegrand_nonneg α n f z θ
  -- the binomial coefficients are bounded by `2^n`
  have hchoose : ∀ (m b : ℕ), m ≤ n → |((m.choose b : ℕ) : ℝ)| ≤ (2 : ℝ) ^ n := by
    intro m b hmn
    calc |((m.choose b : ℕ) : ℝ)| = ((m.choose b : ℕ) : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
      _ ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast Nat.choose_le_two_pow m b
      _ = (2 : ℝ) ^ m := by push_cast; ring
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hmn
  -- a partial sum of the first (radial) block is bounded by the whole integrand
  have hzsum : ∀ i : ℕ, i ≤ n →
      (∑ m ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ Work.Spaces.HkIntegrand α n f z θ := by
    intro i hin
    rw [Work.Spaces.HkIntegrand]
    have hsub : (∑ m ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (∑ m ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro m hm
          have hm' : m < i + 1 := Finset.mem_range.mp hm
          exact Finset.mem_range.mpr (by omega))
        (fun m _ _ => sq_nonneg _)
    exact le_trans hsub (le_add_of_nonneg_right (Work.Spaces.hkMixedSum_nonneg α n f z θ))
  -- a partial sum of the second (mixed) block is bounded by `(j+1)` integrands
  have hmsum : ∀ i j : ℕ, 1 ≤ i → i + j ≤ n →
      (∑ m ∈ Finset.range (j + 1),
        (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ((j : ℝ) + 1) * Work.Spaces.HkIntegrand α n f z θ := by
    intro i j hi1 hij
    calc (∑ m ∈ Finset.range (j + 1),
          (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∑ _m ∈ Finset.range (j + 1), Work.Spaces.HkIntegrand α n f z θ :=
          Finset.sum_le_sum fun m hm => by
            have hmj : m ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
            exact Work.Spaces.sq_le_HkIntegrand_mixed α n f z θ i m hi1 (by omega)
      _ = ((j : ℝ) + 1) * Work.Spaces.HkIntegrand α n f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- the two blocks of the left-hand side are handled separately
  have hZi : (∑ i ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter i (fun z θ => ψ z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
          * Work.Spaces.HkIntegrand α n f z θ := by
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter i (fun z θ => ψ z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
            * Work.Spaces.HkIntegrand α n f z θ := by
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      -- Leibniz for `D_z^i (ψ · f)`
      have hleib : Work.Spaces.DzIter i (fun z θ => ψ z * f z θ) z θ
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.Zop^[b] ψ z * Work.Spaces.DzIter (i - b) f z θ) :=
        DzIter_zmul_SO i ψ f hψ hf hzpos hθ
      -- multiply by the weight and distribute
      have hmul : Work.Spaces.DzIter i (fun z θ => ψ z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.Zop^[b] ψ z * (Work.Spaces.DzIter (i - b) f z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by
        rw [hleib, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [hmul]
      -- Cauchy–Schwarz on the binomial convolution
      have hbin := Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le
        (i := i) (D := (2 : ℝ) ^ n) (K := K) hK
        (x := fun b => Work.Spaces.Zop^[b] ψ z)
        (y := fun m => Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        (fun b hb => hKψ b (le_trans hb hin) z hz)
        (fun b hb => hchoose i b hin)
      have hbin' : (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Spaces.Zop^[b] ψ z * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
          ≤ (((i : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
              * (∑ m ∈ Finset.range (i + 1),
                  (Work.Spaces.DzIter m f z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ))
                        ^ (Work.Spaces.eta / 2))) ^ 2) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hbin
      refine le_trans hbin' ?_
      have hconst : (((i : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
          ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2 := by
        have hbase : ((i : ℝ) + 1) * (2 : ℝ) ^ n ≤ ((n : ℝ) + 1) * (2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right
            (by
              have : (i : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hin
              linarith)
            (by positivity)
        have hle : ((i : ℝ) + 1) * (2 : ℝ) ^ n * K ≤ ((n : ℝ) + 1) * (2 : ℝ) ^ n * K :=
          mul_le_mul_of_nonneg_right hbase hK
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK) hle 2
      exact mul_le_mul hconst (hzsum i hin) (Finset.sum_nonneg fun m _ => sq_nonneg _)
        (by positivity)
    calc (∑ i ∈ Finset.range (n + 1),
          (Work.Spaces.DzIter i (fun z θ => ψ z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (n + 1), ((((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
            * Work.Spaces.HkIntegrand α n f z θ) := Finset.sum_le_sum hterm
      _ = (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
            * Work.Spaces.HkIntegrand α n f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hMi : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        if 1 ≤ i ∧ i + j ≤ n
          then (Work.Spaces.mixed j i (fun z θ => ψ z * f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ (((n : ℝ) + 1) ^ 3 * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
          * Work.Spaces.HkIntegrand α n f z θ := by
    have hsummand : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
        (if 1 ≤ i ∧ i + j ≤ n
          then (Work.Spaces.mixed j i (fun z θ => ψ z * f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
            * Work.Spaces.HkIntegrand α n f z θ := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ n
      · rw [if_pos hc]
        obtain ⟨hi1, hij⟩ := hc
        have hin : i ≤ n := by omega
        have hjn : j ≤ n := by omega
        -- Leibniz for `D_z^j D_θ^i (ψ · f)`
        have hexp : Work.Spaces.mixed j i (fun z θ => ψ z * f z θ) z θ
            = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Spaces.Zop^[b] ψ z * Work.Spaces.mixed (j - b) i f z θ) :=
          mixed_zmul_SO j i ψ f hψ hf hzpos hθ
        have hmul : Work.Spaces.mixed j i (fun z θ => ψ z * f z θ) z θ
              * Work.Spaces.Wt α z θ
            = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Spaces.Zop^[b] ψ z
                    * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ)) := by
          rw [hexp, Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
        rw [hmul]
        have hbin := Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le
          (i := j) (D := (2 : ℝ) ^ n) (K := K) hK
          (x := fun b => Work.Spaces.Zop^[b] ψ z)
          (y := fun m => Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ)
          (fun b hb => hKψ b (le_trans hb hjn) z hz)
          (fun b hb => hchoose j b hjn)
        have hbin' : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Spaces.Zop^[b] ψ z * (Work.Spaces.mixed (j - b) i f z θ
                  * Work.Spaces.Wt α z θ))) ^ 2
            ≤ (((j : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
                * (∑ m ∈ Finset.range (j + 1),
                    (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
          simpa only [Nat.cast_add, Nat.cast_one] using hbin
        refine le_trans hbin' ?_
        have hconst : (((j : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
            ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2 := by
          have hbase : ((j : ℝ) + 1) * (2 : ℝ) ^ n ≤ ((n : ℝ) + 1) * (2 : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right
              (by
                have : (j : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hjn
                linarith)
              (by positivity)
          have hle : ((j : ℝ) + 1) * (2 : ℝ) ^ n * K ≤ ((n : ℝ) + 1) * (2 : ℝ) ^ n * K :=
            mul_le_mul_of_nonneg_right hbase hK
          exact pow_le_pow_left₀
            (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK) hle 2
        have hA : (j : ℝ) + 1 ≤ (n : ℝ) + 1 := by
          have : (j : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hjn
          linarith
        have hAZ : 0 ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2 := by positivity
        calc (((j : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
              * (∑ m ∈ Finset.range (j + 1),
                  (Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ) ^ 2)
            ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
                * (((j : ℝ) + 1) * Work.Spaces.HkIntegrand α n f z θ) :=
              mul_le_mul hconst (hmsum i j hi1 hij)
                (Finset.sum_nonneg fun m _ => sq_nonneg _) hAZ
          _ ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
                * (((n : ℝ) + 1) * Work.Spaces.HkIntegrand α n f z θ) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hQnn) hAZ
          _ = (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
                * Work.Spaces.HkIntegrand α n f z θ := by ring
      · rw [if_neg hc]
        exact mul_nonneg (by positivity) hQnn
    calc (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if 1 ≤ i ∧ i + j ≤ n
            then (Work.Spaces.mixed j i (fun z θ => ψ z * f z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ∑ _i ∈ Finset.range (n + 1), ∑ _j ∈ Finset.range (n + 1),
            ((((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
              * Work.Spaces.HkIntegrand α n f z θ) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hsummand i hi j hj
      _ = (((n : ℝ) + 1) ^ 3 * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
            * Work.Spaces.HkIntegrand α n f z θ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- add the two blocks
  conv_lhs => rw [Work.Spaces.HkIntegrand]
  refine le_trans (add_le_add hZi hMi) ?_
  have hKsq : K ^ 2 ≤ (1 + K) ^ 2 := by nlinarith [hK]
  have hkey : (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
        * Work.Spaces.HkIntegrand α n f z θ
      + (((n : ℝ) + 1) ^ 3 * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
        * Work.Spaces.HkIntegrand α n f z θ
      = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * K ^ 2
        * Work.Spaces.HkIntegrand α n f z θ := by ring
  rw [hkey]
  have h0 : 0 ≤ ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) := by
    positivity
  have hstep1 : ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * K ^ 2
        * Work.Spaces.HkIntegrand α n f z θ
      ≤ ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * (1 + K) ^ 2
        * Work.Spaces.HkIntegrand α n f z θ := by
    calc ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * K ^ 2
          * Work.Spaces.HkIntegrand α n f z θ
        = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2)
            * (K ^ 2 * Work.Spaces.HkIntegrand α n f z θ) := by ring
      _ ≤ ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2)
            * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKsq hQnn) h0
      _ = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * (1 + K) ^ 2
            * Work.Spaces.HkIntegrand α n f z θ := by ring
  refine le_trans hstep1 ?_
  have h1 : 0 ≤ (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ :=
    mul_nonneg (by positivity) hQnn
  rw [zmulC]
  calc ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * (1 + K) ^ 2
        * Work.Spaces.HkIntegrand α n f z θ
      = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2)
          * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ) := by ring
    _ ≤ ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2 + 1)
          * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ) :=
        mul_le_mul_of_nonneg_right (by linarith) h1
    _ = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2 + 1) * (1 + K) ^ 2
          * Work.Spaces.HkIntegrand α n f z θ := by ring

end Work.FTS.StrongEps.EpsE4Thr.E2hatOAux
