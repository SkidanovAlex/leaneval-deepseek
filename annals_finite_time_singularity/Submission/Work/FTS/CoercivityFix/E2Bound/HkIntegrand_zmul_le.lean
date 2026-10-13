/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `ℋⁿ`-integrand of a product with a function of `z` alone

`HkIntegrand_zmul_le`: for every `n` there is a constant `C > 0` with

`HkIntegrand α n (fun z θ => a z * f z θ) z θ ≤ C · (1+K)² · HkIntegrand α n f z θ`

for all `z > 0`, `θ ∈ (0,π/2)`, every `a : ℝ → ℝ` whose `Zop`-iterates
`Zop^[b] a = (z ∂_z)^b a` are bounded by `K ≥ 0` on `(0,∞)` for `b ≤ n`, every `C^∞`
`a` (as a function of `z` alone) and every `C^∞` (on the open quadrant) `f`.

## The argument

`HkIntegrand α n g z θ` is the sum of the squares of the weighted derivatives of `g`:
`∑_{i≤n} (D_z^i g · w/sin(2θ)^{η/2})² + ∑_{1≤i, i+j≤n} (D_z^j D_θ^i g · W)²`.
Both families of operators satisfy the binomial (Leibniz) rule on the open quadrant:

* `D_z^i (a·f) = ∑_{b≤i} binom(i,b)·(Zop^b a)·(D_z^{i-b} f)`
  (`Work.FTS.LocData.DzIter_mul_smoothQuad`, with `D_z^b (fun z θ => a z) = Zop^b a`
  by `Work.FTS.LocData.Zop_iterate_slice`);
* `D_z^j D_θ^i (a·f) = ∑_{b≤j} binom(j,b)·(Zop^b a)·(D_z^{j-b} D_θ^i f)` for `i ≥ 1`
  (`Work.FTS.CoercivityFix.E2Bound.mixed_zmul`: `D_θ` commutes with the `z`-only factor).

Hence every summand of `HkIntegrand α n (a·f) z θ` is a binomial convolution
`∑_b ↑(i.choose b)·(x_b · y_{i-b})` with `|x_b| ≤ K` and `|↑(i.choose b)| ≤ 2^n`; the numerical
Cauchy–Schwarz step `Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le` bounds its square by
`((i+1)·2^n·K)²·∑_b y_b²`. The `y`-sums are partial sums of the two blocks of
`HkIntegrand α n f z θ`, which is where `Work.Spaces.sq_le_HkIntegrand_z` /
`Work.Spaces.sq_le_HkIntegrand_mixed` enter. Summing over the (at most `(n+1)²`) indices gives
the stated bound with the explicit constant `C = ((n+1)³ + (n+1)⁵)·4ⁿ + 1`; the factor
`(1+K)²` absorbs `K²` because `K ≥ 0`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.H2.WPQ.Leibniz
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.FTS.CoercivityFix.E2Bound.mixed_zmul
import Submission.Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.E2Bound

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

theorem HkIntegrand_zmul_le (α : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ b ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] a z| ≤ K) →
      Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => a z) →
      ∀ f : ℝ → ℝ → ℝ, Work.FTS.LocData.SmoothQuad f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α n (fun z θ => a z * f z θ) z θ
          ≤ C * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ := by
  refine ⟨(((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2 + 1,
    by positivity, ?_⟩
  intro a K hK hKa ha f hf z hz θ hθ
  -- basic facts at the point `(z,θ)`
  have hzpos : 0 < z := hz
  have hzIoi : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]
    linarith
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
        (Work.Spaces.DzIter i (fun z θ => a z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
          * Work.Spaces.HkIntegrand α n f z θ := by
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter i (fun z θ => a z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2
            * Work.Spaces.HkIntegrand α n f z θ := by
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      -- Leibniz for `D_z^i (a · f)`
      have hleib : Work.Spaces.DzIter i (fun z θ => a z * f z θ) z θ
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.Zop^[b] a z * Work.Spaces.DzIter (i - b) f z θ) := by
        have h := Work.FTS.LocData.DzIter_mul_smoothQuad i (fun z θ : ℝ => a z) f
          (z := z) (θ := θ) hzIz (ha.curry_z hθ) (hf.curry_z hθ)
        rw [h]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [congrFun (Work.FTS.LocData.Zop_iterate_slice b (fun z θ : ℝ => a z) θ) z]
      -- multiply by the weight and distribute
      have hmul : Work.Spaces.DzIter i (fun z θ => a z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.Zop^[b] a z * (Work.Spaces.DzIter (i - b) f z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by
        rw [hleib, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [hmul]
      -- Cauchy–Schwarz on the binomial convolution
      have hbin := binom_sum_sq_le (i := i) (D := (2 : ℝ) ^ n) (K := K) hK
        (x := fun b => Work.Spaces.Zop^[b] a z)
        (y := fun m => Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        (fun b hb => hKa b (le_trans hb hin) z hz)
        (fun b hb => hchoose i b hin)
      have hbin' : (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Spaces.Zop^[b] a z * (Work.Spaces.DzIter (i - b) f z θ
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
          (Work.Spaces.DzIter i (fun z θ => a z * f z θ) z θ
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
          then (Work.Spaces.mixed j i (fun z θ => a z * f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ (((n : ℝ) + 1) ^ 3 * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
          * Work.Spaces.HkIntegrand α n f z θ := by
    have hsummand : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
        (if 1 ≤ i ∧ i + j ≤ n
          then (Work.Spaces.mixed j i (fun z θ => a z * f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ (((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 : ℝ) ^ n * K) ^ 2)
            * Work.Spaces.HkIntegrand α n f z θ := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ n
      · rw [if_pos hc]
        obtain ⟨hi1, hij⟩ := hc
        have hin : i ≤ n := by omega
        have hjn : j ≤ n := by omega
        -- Leibniz for `D_z^j D_θ^i (a · f)`
        have hexp : Work.Spaces.mixed j i (fun z θ => a z * f z θ) z θ
            = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Spaces.Zop^[b] a z * Work.Spaces.mixed (j - b) i f z θ) :=
          mixed_zmul j i a f hzIoi hθ ha hf
        have hmul : Work.Spaces.mixed j i (fun z θ => a z * f z θ) z θ
              * Work.Spaces.Wt α z θ
            = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Spaces.Zop^[b] a z
                    * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ)) := by
          rw [hexp, Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
        rw [hmul]
        have hbin := binom_sum_sq_le (i := j) (D := (2 : ℝ) ^ n) (K := K) hK
          (x := fun b => Work.Spaces.Zop^[b] a z)
          (y := fun m => Work.Spaces.mixed m i f z θ * Work.Spaces.Wt α z θ)
          (fun b hb => hKa b (le_trans hb hjn) z hz)
          (fun b hb => hchoose j b hjn)
        have hbin' : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Spaces.Zop^[b] a z * (Work.Spaces.mixed (j - b) i f z θ
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
            then (Work.Spaces.mixed j i (fun z θ => a z * f z θ) z θ
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
  calc ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2) * (1 + K) ^ 2
        * Work.Spaces.HkIntegrand α n f z θ
      = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2)
          * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ) := by ring
    _ ≤ ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2 + 1)
          * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ) :=
        mul_le_mul_of_nonneg_right (by linarith) h1
    _ = ((((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ n) ^ 2 + 1) * (1 + K) ^ 2
          * Work.Spaces.HkIntegrand α n f z θ := by ring

end Work.FTS.CoercivityFix.E2Bound
