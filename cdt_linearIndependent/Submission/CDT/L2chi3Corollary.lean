import Mathlib
import Submission.CDT.L2chi3Real
import Submission.CDT.TheoremA_leaf

/-!
# Sub-leaf (3) of CDT Theorem A: the trigamma / residue-class corollary

The paper (Corollary after Theorem `mainA`) displays four classical
*series identities* over residue classes:

```lean
∑ₖ 1/(3k+1)² = L(2,χ₋₃)/2 + 2π²/27        ∑ₖ 1/(3k+2)² = −L(2,χ₋₃)/2 + 2π²/27
∑ₖ 1/(6k+1)² = 5L(2,χ₋₃)/8 + π²/18        ∑ₖ 1/(6k+5)² = −5L(2,χ₋₃)/8 + π²/18
```

(equivalently the trigamma evaluations `ψ₁(n/6) = 36·Σₖ 1/(6k+n)² ∈
ℚ + ℚ·L(2,χ₋₃) + ℚ·π²`), and notes that the four numbers displayed are
irrational — an immediate consequence of Theorem A (`1, π², L(2,χ₋₃)`
ℚ-linearly independent, in the reduced form `theoremA_leaf`).

**Method (no digamma theory needed).**  Split the real `p`-series
`zeta2Real = Σₙ 1/n²` into residue classes mod `3` (generic
period-splitting lemma `tsum_period_split` on the index set `ℕ`):
`zeta2Real = Σₖ1/(3k)² + Σₖ1/(3k+1)² + Σₖ1/(3k+2)² = zeta2Real/9 + A + B`,
so `A + B = 8/9·zeta2Real`; and `A − B = L2chi3Real` (the paired-term
regrouping `L2chi3Real_eq_pair_tsum` of the previous module).  Splitting
`A = Σₖ 1/(3k+1)²` by parity of `k` (`tsum_period_split` with period `2`)
gives `A = Σₖ1/(6k+1)² + Σₖ1/(6k+4)² = C + (1/4)B`, hence
`C = A − B/4`, and similarly `B = D + A/4`.  The constant `zeta2Real`
equals `π²/6` (Mathlib `riemannZeta_two` + `zeta_nat_eq_tsum_of_gt_one`,
pulled back from `ℂ` by `Complex.ofReal_tsum`), and `L2chi3Real` is the
real part of the analytic `L`-value (`LFunction_chi3_two_eq_L2chi3Real`).

The four irrationality claims are stated *conditionally* on
`theoremA_leaf` (which is exactly Theorem A in reduced form, proved
equivalent to the full statement in `TheoremA_leaf.theoremA_iff_leaf`):
each displayed series is `(1/2, 2/27)`, `(−1/2, 2/27)`, `(5/8, 1/18)`,
`(−5/8, 1/18)` times `(L(2,χ₋₃), π²)`, and a rational value would give
`L(2,χ₋₃) = a + b·π²` with `a,b ∈ ℚ`, contradicting the leaf.  Since
`riemannZeta 2 = π²/6`, `π² = 6·riemannZeta 2`, so rational combinations
of `1, π²` correspond exactly to rational combinations of `1, ζ(2)`
(see `theoremA_leaf_real` below).

**Main statements.**  `res31_eq_paper` … `res65_eq_paper` are the four
series identities in the paper's displayed form; `corollary_irrational :
theoremA_leaf → Irrational sum3_1 ∧ … ∧ Irrational sum6_5` is the paper's
irrationality claim, proved through the real leaf `theoremA_leaf_real`
(`L(2,χ₋₃) ∉ ℚ + ℚ·π²`, equivalent to `theoremA_leaf`).  A final section
records the trigamma reading: with the classical series definition
`psi₁ x = Σₘ 1/(x+m)²`, the identities `psi₁(1/6) = 36·sum6_1`,
`psi₁(1/3) = 9·sum3_1`, `psi₁(2/3) = 9·sum3_2`, `psi₁(5/6) = 36·sum6_5`,
`psi₁(1/2) = π²/2`, `psi₁(1) = π²/6` hold, and `trigamma_irrational :
theoremA_leaf → …` gives the irrationality of `ψ₁(n/6)` for `n = 1,…,5`.

Everything here is fully proved (no axioms, no `sorry`).
-/

open scoped BigOperators
open scoped Topology
open Filter

noncomputable section

namespace Submission.CDT

open Submission.Helpers


/-! ## The generic period-splitting lemma (`tsum_period_split`) -/

/-- Finite version of the period splitting: `Σₙ₌₀^(qM−1) a n` equals
`Σ_{r<q} Σ_{k<M} a (qk+r)` (division of `n` by `q` is a bijection). -/
lemma sum_range_period (a : ℕ → ℝ) (q M : ℕ) :
    (∑ n ∈ Finset.range (q * M), a n) =
      ∑ r ∈ Finset.range q, ∑ k ∈ Finset.range M, a (q * k + r) := by
  classical
  by_cases hq0 : q = 0
  · simp [hq0]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    rw [← Finset.sum_product (Finset.range q) (Finset.range M)
      (fun rk : ℕ × ℕ => a (q * rk.2 + rk.1))]
    -- goal: (∑ n ∈ range(qM), a n) = ∑ x ∈ (range q).product (range M), a (q * x.2 + x.1)
    refine Finset.sum_bij (fun n _ => (n % q, n / q)) ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_range] at hn
      rw [Finset.mem_product]
      constructor
      · exact Finset.mem_range.mpr (Nat.mod_lt n hqpos)
      · exact Finset.mem_range.mpr (by
          rw [Nat.div_lt_iff_lt_mul hqpos]
          rw [Nat.mul_comm] at hn
          exact hn)
    · -- injectivity
      intro n₁ hn₁ n₂ hn₂ hpair
      have h₁ : n₁ = q * (n₁ / q) + n₁ % q := by rw [Nat.div_add_mod]
      have h₂ : n₂ = q * (n₂ / q) + n₂ % q := by rw [Nat.div_add_mod]
      -- extract component equalities
      have heq_r : n₁ % q = n₂ % q := congrArg Prod.fst hpair
      have heq_k : n₁ / q = n₂ / q := congrArg Prod.snd hpair
      rw [heq_r, heq_k] at h₁
      exact h₁.trans h₂.symm
    · -- surjectivity
      intro x hx
      rw [Finset.mem_product] at hx
      rcases hx with ⟨hr, hk⟩
      rw [Finset.mem_range] at hr hk
      refine ⟨q * x.2 + x.1, ?_, ?_⟩
      · rw [Finset.mem_range]
        calc
          q * x.2 + x.1 < q * x.2 + q := by omega
          _ = q * (x.2 + 1) := by ring
          _ ≤ q * M := Nat.mul_le_mul_left q (by omega)
      · apply Prod.ext
        · -- (qk+r) % q = r
          have hmod : (q * x.2 + x.1) % q = x.1 := by
            rw [Nat.add_comm]
            rw [Nat.add_mul_mod_self_left]
            exact Nat.mod_eq_of_lt hr
          simp [hmod]
        · -- (qk+r) / q = k
          have hdiv : (q * x.2 + x.1) / q = x.2 := by
            rw [Nat.add_comm]
            rw [Nat.add_mul_div_left _ _ hqpos]
            rw [Nat.div_eq_of_lt hr]
            simp
          simp [hdiv]
    · intro n hn
      rw [Nat.div_add_mod]

/-- **Period splitting.**  For a summable `a : ℕ → ℝ`, the total sum equals
the sum over residue classes mod `q` of the subseries:
`Σ'ₙ a n = Σ_{r<q} Σ'ₖ a(qk+r)`. -/
lemma tsum_period_split (a : ℕ → ℝ) (q : ℕ) (hq : q ≠ 0) (ha : Summable a) :
    (∑' n : ℕ, a n) = ∑ r ∈ Finset.range q, ∑' k : ℕ, a (q * k + r) := by
  classical
  -- each subseries is summable
  have hsub : ∀ r ∈ Finset.range q, Summable (fun k : ℕ => a (q * k + r)) := by
    intro r hr
    refine Summable.comp_injective ha ?_
    intro k₁ k₂ hk
    have hq0 : q ≠ 0 := by
      have hrlt : r < q := Finset.mem_range.mp hr
      omega
    have hk' : q * k₁ = q * k₂ := by
      have hsub_eq := congrArg (fun t : ℕ => t - r) hk
      simpa using hsub_eq
    exact Nat.mul_left_cancel (by omega : 0 < q) hk'
  -- partial sums of the full series (at N = qM) converge to ∑' a
  have hpt : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (q * M), a n) atTop (𝓝 (∑' n, a n)) := by
    have hpt1 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, a n) atTop (𝓝 (∑' n, a n)) := by
      exact HasSum.tendsto_sum_nat (Summable.hasSum ha)
    have hmul : Tendsto (fun M : ℕ => q * M) atTop atTop := by
      refine Filter.tendsto_atTop_atTop.mpr ?_
      intro b
      refine ⟨b + 1, ?_⟩
      intro a0 ha0
      have hq' : 0 < q := Nat.pos_of_ne_zero hq
      have hq1 : 1 ≤ q := Nat.succ_le_of_lt hq'
      have hle : a0 ≤ q * a0 := by
        calc a0 = 1 * a0 := by simp
          _ ≤ q * a0 := Nat.mul_le_mul_right a0 hq1
      omega
    exact hpt1.comp hmul
  -- partial sums of the RHS converge to the sum of the subseries sums
  have hpt2 : Tendsto
      (fun M : ℕ => ∑ r ∈ Finset.range q, ∑ k ∈ Finset.range M, a (q * k + r))
      atTop (𝓝 (∑ r ∈ Finset.range q, ∑' k : ℕ, a (q * k + r))) := by
    -- for each r the inner partial sums converge; sum over the finite range q
    exact tendsto_finsetSum (s := Finset.range q)
      (f := fun r M : ℕ => ∑ k ∈ Finset.range M, a (q * k + r))
      (a := fun r : ℕ => ∑' k : ℕ, a (q * k + r))
      (x := atTop)
      (fun r hr => HasSum.tendsto_sum_nat (Summable.hasSum (hsub r hr)))
  -- pointwise equality of the two partial-sum families
  have hcong : (fun M : ℕ => ∑ r ∈ Finset.range q, ∑ k ∈ Finset.range M, a (q * k + r))
      =ᶠ[atTop] (fun M : ℕ => ∑ n ∈ Finset.range (q * M), a n) := by
    exact Eventually.of_forall (fun M => by
      dsimp
      rw [sum_range_period a q M])
  -- hence both limits agree
  exact tendsto_nhds_unique hpt (hpt2.congr' hcong)

/-! ## The four residue-class series and `zeta2Real` -/

/-- `ζ(2) = Σₙ 1/n²` as a real `p`-series (the `n = 0` summand vanishes). -/
def zeta2Real : ℝ := ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2

/-- `Σₖ 1/(3k+1)²`: sum of reciprocal squares of `n ≡ 1 (mod 3)`. -/
def sum3_1 : ℝ := ∑' k : ℕ, (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2)

/-- `Σₖ 1/(3k+2)²`: sum of reciprocal squares of `n ≡ 2 (mod 3)`. -/
def sum3_2 : ℝ := ∑' k : ℕ, (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2)

/-- `Σₖ 1/(6k+1)²`: sum of reciprocal squares of `n ≡ 1 (mod 6)`. -/
def sum6_1 : ℝ := ∑' k : ℕ, (1 : ℝ) / (((6 * k + 1 : ℕ) : ℝ) ^ 2)

/-- `Σₖ 1/(6k+5)²`: sum of reciprocal squares of `n ≡ 5 (mod 6)`. -/
def sum6_5 : ℝ := ∑' k : ℕ, (1 : ℝ) / (((6 * k + 5 : ℕ) : ℝ) ^ 2)

/-- the reciprocal-square `p`-series over `ℕ` is summable -/
lemma zeta2_summable : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
  (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)

/-- any subseries of the reciprocal-square series along an arithmetic
progression `k ↦ qk + r` is summable (needed only for `r ≥ 1`); the
`k = 0` summand is included (finite). -/
lemma sq_subseries_summable (q r : ℕ) (hq1 : 1 ≤ q) (hr1 : 1 ≤ r) :
    Summable (fun k : ℕ => (1 : ℝ) / (((q * k + r : ℕ) : ℝ) ^ 2)) := by
  have hg : Summable (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
    exact (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (k := 1)).mpr zeta2_summable
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hg
  · -- summand nonnegative: denominator is a square
    have hdenpos : 0 < ((q * k + r : ℕ) : ℝ) ^ 2 := by
      have h0 : 0 < (q * k + r : ℕ) := by omega
      exact sq_pos_of_pos (by exact_mod_cast h0)
    exact div_nonneg zero_le_one (le_of_lt hdenpos)
  · -- denominator comparison: (k+1) ≤ qk+r
    have hden : ((k + 1 : ℕ) : ℝ) ≤ ((q * k + r : ℕ) : ℝ) := by
      exact_mod_cast (by
        have hkq : k ≤ q * k := by
          calc k = 1 * k := by simp
            _ ≤ q * k := Nat.mul_le_mul_right k hq1
        omega)
    have hpos0 : 0 < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k + 1)
    have hsq_le : ((k + 1 : ℕ) : ℝ) ^ 2 ≤ ((q * k + r : ℕ) : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ (le_of_lt hpos0) hden 2
    have hpos' : 0 < ((k + 1 : ℕ) : ℝ) ^ 2 := sq_pos_of_pos hpos0
    exact one_div_le_one_div_of_le hpos' hsq_le

lemma sum3_1_summable : Summable (fun k : ℕ => (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2)) := by
  simpa using sq_subseries_summable 3 1 (by norm_num) (by norm_num)

lemma sum3_2_summable : Summable (fun k : ℕ => (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2)) := by
  simpa using sq_subseries_summable 3 2 (by norm_num) (by norm_num)

lemma sum6_1_summable : Summable (fun k : ℕ => (1 : ℝ) / (((6 * k + 1 : ℕ) : ℝ) ^ 2)) := by
  simpa using sq_subseries_summable 6 1 (by norm_num) (by norm_num)

lemma sum6_5_summable : Summable (fun k : ℕ => (1 : ℝ) / (((6 * k + 5 : ℕ) : ℝ) ^ 2)) := by
  simpa using sq_subseries_summable 6 5 (by norm_num) (by norm_num)

/-- the `0 (mod q)` residue subseries of the reciprocal-square series:
`Σₖ 1/(qk)² = ζ(2)/q²` (for `q ≠ 0`) -/
lemma residue_zero_subseries (q : ℕ) (hq : q ≠ 0) :
    (∑' k : ℕ, (1 : ℝ) / (((q * k : ℕ) : ℝ) ^ 2)) = zeta2Real / (q : ℝ) ^ 2 := by
  -- termwise: 1/(qk)² = (1/q²)·(1/k²)
  have hterm : ∀ k : ℕ, (1 : ℝ) / (((q * k : ℕ) : ℝ) ^ 2)
      = (1 : ℝ) / (q : ℝ) ^ 2 * ((1 : ℝ) / (k : ℝ) ^ 2) := by
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · have hqk : ((q * k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_ne_zero hq hk)
      have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      have hcast : (((q * k : ℕ) : ℝ)) = (q : ℝ) * (k : ℝ) := by norm_num
      rw [hcast]
      field_simp [hqk, hkℝ]
  calc
    (∑' k : ℕ, (1 : ℝ) / (((q * k : ℕ) : ℝ) ^ 2))
        = ∑' k : ℕ, (1 : ℝ) / (q : ℝ) ^ 2 * ((1 : ℝ) / (k : ℝ) ^ 2) := by
          exact tsum_congr hterm
    _ = ((1 : ℝ) / (q : ℝ) ^ 2) * ∑' k : ℕ, (1 : ℝ) / (k : ℝ) ^ 2 := by
          rw [tsum_mul_left]
    _ = zeta2Real / (q : ℝ) ^ 2 := by
          unfold zeta2Real
          ring

/-- **Mod-3 decomposition of `ζ(2)`**: `ζ(2) = A + B + ζ(2)/9` where
`A = Σₖ1/(3k+1)²`, `B = Σₖ1/(3k+2)²`. -/
lemma zeta2_eq_sum3_add : zeta2Real = sum3_1 + sum3_2 + zeta2Real / 9 := by
  have h0 : (∑' k : ℕ, (1 : ℝ) / (((3 * k : ℕ) : ℝ) ^ 2)) = zeta2Real / 9 := by
    have hres := residue_zero_subseries 3 (by norm_num : 3 ≠ 0)
    rw [hres]
    norm_num
  have hsplit := tsum_period_split (a := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (q := 3)
    (by norm_num : 3 ≠ 0) zeta2_summable
  -- hsplit : (∑' n, 1/(n:ℝ)^2) = ∑ r ∈ range 3, ∑' k, 1/((3k+r)²)
  calc
    zeta2Real = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by rfl
    _ = ∑ r ∈ Finset.range 3, ∑' k : ℕ, (1 : ℝ) / (((3 * k + r : ℕ) : ℝ) ^ 2) := hsplit
    _ = sum3_1 + sum3_2 + zeta2Real / 9 := by
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero]
          rw [h0]
          rw [show (∑' k : ℕ, (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2)) = sum3_1 by rfl]
          rw [show (∑' k : ℕ, (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2)) = sum3_2 by rfl]
          ring

/-- `A + B = 8/9·ζ(2)`. -/
lemma sum3_add_sum3 : sum3_1 + sum3_2 = (8 : ℝ) * zeta2Real / 9 := by
  have h := zeta2_eq_sum3_add
  nlinarith [h]

/-- `A − B = L(2,χ₋₃)` (the paired-sum regrouping). -/
lemma sum3_sub_sum3 : sum3_1 - sum3_2 = L2chi3Real := by
  have hx : Summable (fun k : ℕ => (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2)) := sum3_1_summable
  have hy : Summable (fun k : ℕ => (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2)) := sum3_2_summable
  have hsub : HasSum (fun k : ℕ => (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2)
      - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))
      ((∑' k : ℕ, (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2))
        - (∑' k : ℕ, (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) :=
    (Summable.hasSum hx).sub (Summable.hasSum hy)
  calc
    sum3_1 - sum3_2
        = (∑' k : ℕ, (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2))
          - (∑' k : ℕ, (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2)) := by rfl
    _ = ∑' k : ℕ, ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2)
        - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2)) := hsub.tsum_eq.symm
    _ = ∑' k : ℕ, pairSum k := by
          exact (tsum_congr (fun k => (pairSum_eq k).symm))
    _ = L2chi3Real := (L2chi3Real_eq_pair_tsum).symm

/-- `A = L(2,χ₋₃)/2 + (4/9)·ζ(2)` (from `A ± B`). -/
lemma sum3_1_eq : sum3_1 = L2chi3Real / 2 + (4 : ℝ) * zeta2Real / 9 := by
  have hadd := sum3_add_sum3
  have hsub := sum3_sub_sum3
  calc
    sum3_1 = ((sum3_1 + sum3_2) + (sum3_1 - sum3_2)) / 2 := by ring
    _ = (((8 : ℝ) * zeta2Real / 9) + L2chi3Real) / 2 := by rw [hadd, hsub]
    _ = L2chi3Real / 2 + (4 : ℝ) * zeta2Real / 9 := by ring

/-- `B = −L(2,χ₋₃)/2 + (4/9)·ζ(2)`. -/
lemma sum3_2_eq : sum3_2 = -L2chi3Real / 2 + (4 : ℝ) * zeta2Real / 9 := by
  have hadd := sum3_add_sum3
  have hsub := sum3_sub_sum3
  calc
    sum3_2 = ((sum3_1 + sum3_2) - (sum3_1 - sum3_2)) / 2 := by ring
    _ = (((8 : ℝ) * zeta2Real / 9) - L2chi3Real) / 2 := by rw [hadd, hsub]
    _ = -L2chi3Real / 2 + (4 : ℝ) * zeta2Real / 9 := by ring

/-! ## The mod-6 residue classes (parity split of `A` and `B`) -/

/-- parity split of `A = Σₖ 1/(3k+1)²` into the even and odd index sums -/
lemma sum3_1_parity : sum3_1 =
    (∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k) + 1 : ℕ) : ℝ) ^ 2))
      + (∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k + 1) + 1 : ℕ) : ℝ) ^ 2)) := by
  have hsplit := tsum_period_split (a := fun k : ℕ => (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2))
    (q := 2) (by norm_num : 2 ≠ 0) sum3_1_summable
  calc
    sum3_1 = ∑' k : ℕ, (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) := by rfl
    _ = ∑ r ∈ Finset.range 2, ∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k + r) + 1 : ℕ) : ℝ) ^ 2) := hsplit
    _ = (∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k) + 1 : ℕ) : ℝ) ^ 2))
        + (∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k + 1) + 1 : ℕ) : ℝ) ^ 2)) := by
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero]

/-- the even-index part of `A` is `C = Σₖ 1/(6k+1)²` -/
lemma even_part_eq_sum6_1 :
    (∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k) + 1 : ℕ) : ℝ) ^ 2)) = sum6_1 := by
  unfold sum6_1
  exact tsum_congr (fun k => by
    have hn : (3 * (2 * k) + 1 : ℕ) = (6 * k + 1 : ℕ) := by ring
    rw [hn])

/-- the odd-index part of `A` is `B/4` (termwise `1/(6k+4)² = (1/4)·1/(3k+2)²`) -/
lemma odd_part_eq_quarter :
    (∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k + 1) + 1 : ℕ) : ℝ) ^ 2)) = sum3_2 / 4 := by
  have hterm : ∀ k : ℕ, (1 : ℝ) / (((3 * (2 * k + 1) + 1 : ℕ) : ℝ) ^ 2)
      = (1 : ℝ) / 4 * ((1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2)) := by
    intro k
    have hn : (3 * (2 * k + 1) + 1 : ℕ) = 2 * (3 * k + 2 : ℕ) := by ring
    have hd : ((3 * k + 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : 3 * k + 2 ≠ 0)
    rw [hn]
    rw [Nat.cast_mul]
    norm_num
    field_simp [hd]
    norm_num
  calc
    (∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k + 1) + 1 : ℕ) : ℝ) ^ 2))
        = ∑' k : ℕ, (1 : ℝ) / 4 * ((1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2)) := by
          exact tsum_congr hterm
    _ = ((1 : ℝ) / 4) * ∑' k : ℕ, (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2) := by
          rw [tsum_mul_left]
    _ = sum3_2 / 4 := by
          unfold sum3_2
          ring

/-- `A = C + B/4`. -/
lemma sum3_1_eq_sum6_1_add_quarter : sum3_1 = sum6_1 + sum3_2 / 4 := by
  rw [sum3_1_parity, even_part_eq_sum6_1, odd_part_eq_quarter]

/-- parity split of `B = Σₖ 1/(3k+2)²` -/
lemma sum3_2_parity : sum3_2 =
    (∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k) + 2 : ℕ) : ℝ) ^ 2))
      + (∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k + 1) + 2 : ℕ) : ℝ) ^ 2)) := by
  have hsplit := tsum_period_split (a := fun k : ℕ => (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))
    (q := 2) (by norm_num : 2 ≠ 0) sum3_2_summable
  calc
    sum3_2 = ∑' k : ℕ, (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2) := by rfl
    _ = ∑ r ∈ Finset.range 2, ∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k + r) + 2 : ℕ) : ℝ) ^ 2) := hsplit
    _ = (∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k) + 2 : ℕ) : ℝ) ^ 2))
        + (∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k + 1) + 2 : ℕ) : ℝ) ^ 2)) := by
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero]

/-- the even-index part of `B` is `A/4` (`1/(6k+2)² = (1/4)·1/(3k+1)²`) -/
lemma even_part_B_eq_quarter :
    (∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k) + 2 : ℕ) : ℝ) ^ 2)) = sum3_1 / 4 := by
  have hterm : ∀ k : ℕ, (1 : ℝ) / (((3 * (2 * k) + 2 : ℕ) : ℝ) ^ 2)
      = (1 : ℝ) / 4 * ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2)) := by
    intro k
    have hn : (3 * (2 * k) + 2 : ℕ) = 2 * (3 * k + 1 : ℕ) := by ring
    have hd : ((3 * k + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : 3 * k + 1 ≠ 0)
    rw [hn]
    rw [Nat.cast_mul]
    norm_num
    field_simp [hd]
    norm_num
  calc
    (∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k) + 2 : ℕ) : ℝ) ^ 2))
        = ∑' k : ℕ, (1 : ℝ) / 4 * ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2)) := by
          exact tsum_congr hterm
    _ = ((1 : ℝ) / 4) * ∑' k : ℕ, (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) := by
          rw [tsum_mul_left]
    _ = sum3_1 / 4 := by
          unfold sum3_1
          ring

/-- the odd-index part of `B` is `D = Σₖ 1/(6k+5)²` -/
lemma odd_part_B_eq_sum6_5 :
    (∑' k : ℕ, (1 : ℝ) / (((3 * (2 * k + 1) + 2 : ℕ) : ℝ) ^ 2)) = sum6_5 := by
  unfold sum6_5
  exact tsum_congr (fun k => by
    have hn : (3 * (2 * k + 1) + 2 : ℕ) = (6 * k + 5 : ℕ) := by ring
    rw [hn])

/-- `B = A/4 + D`. -/
lemma sum3_2_eq_quarter_add_sum6_5 : sum3_2 = sum3_1 / 4 + sum6_5 := by
  rw [sum3_2_parity, even_part_B_eq_quarter, odd_part_B_eq_sum6_5]

/-- `C = Σₖ1/(6k+1)² = A − B/4`. -/
lemma sum6_1_eq : sum6_1 = sum3_1 - sum3_2 / 4 := by
  have h := sum3_1_eq_sum6_1_add_quarter
  nlinarith

/-- `D = Σₖ1/(6k+5)² = B − A/4`. -/
lemma sum6_5_eq : sum6_5 = sum3_2 - sum3_1 / 4 := by
  have h := sum3_2_eq_quarter_add_sum6_5
  nlinarith

/-! ## `zeta2Real = π²/6` (bridge to Mathlib's `riemannZeta`) -/

/-- `ζ(2) = π²/6` for the real `p`-series `zeta2Real` -/
lemma zeta2Real_eq_pi : zeta2Real = (Real.pi : ℝ) ^ 2 / 6 := by
  let f : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ) ^ 2
  have hterm : ∀ n : ℕ, (f n : ℂ) = (1 : ℂ) / (n : ℂ) ^ 2 := by
    intro n
    by_cases hn : n = 0
    · subst n; simp [f]
    · simp [f]
  have hcast : (zeta2Real : ℂ) = riemannZeta 2 := by
    calc
      (zeta2Real : ℂ) = ∑' n : ℕ, (f n : ℂ) := by
        rw [zeta2Real]
        dsimp [f]
        exact Complex.ofReal_tsum f
      _ = ∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ 2 := by
        exact tsum_congr hterm
      _ = riemannZeta 2 := by
        exact (zeta_nat_eq_tsum_of_gt_one (k := 2) (by norm_num)).symm
  have hpi : riemannZeta 2 = ((((Real.pi : ℝ) ^ 2 / 6 : ℝ) : ℂ)) := by
    rw [riemannZeta_two]
    norm_num
  exact Complex.ofReal_inj.mp (by
    calc
      (zeta2Real : ℂ) = riemannZeta 2 := hcast
      _ = ((((Real.pi : ℝ) ^ 2 / 6 : ℝ) : ℂ)) := hpi)

/-! ## The four series in their paper form (rational combinations of `L` and `π²`) -/

/-- the paper's first display: `Σₖ1/(3k+1)² = L(2,χ₋₃)/2 + 2π²/27` -/
theorem res31_eq_paper : sum3_1 = L2chi3Real / 2 + (2 : ℝ) * (Real.pi : ℝ) ^ 2 / 27 := by
  rw [sum3_1_eq, zeta2Real_eq_pi]
  ring

/-- the paper's second display: `Σₖ1/(3k+2)² = −L(2,χ₋₃)/2 + 2π²/27` -/
theorem res32_eq_paper : sum3_2 = -L2chi3Real / 2 + (2 : ℝ) * (Real.pi : ℝ) ^ 2 / 27 := by
  rw [sum3_2_eq, zeta2Real_eq_pi]
  ring

/-- the paper's third display: `Σₖ1/(6k+1)² = 5L(2,χ₋₃)/8 + π²/18` -/
theorem res61_eq_paper : sum6_1 = (5 : ℝ) * L2chi3Real / 8 + (Real.pi : ℝ) ^ 2 / 18 := by
  rw [sum6_1_eq, res31_eq_paper, res32_eq_paper]
  ring

/-- the paper's fourth display: `Σₖ1/(6k+5)² = −5L(2,χ₋₃)/8 + π²/18` -/
theorem res65_eq_paper : sum6_5 = -(5 : ℝ) * L2chi3Real / 8 + (Real.pi : ℝ) ^ 2 / 18 := by
  rw [sum6_5_eq, res32_eq_paper, res31_eq_paper]
  ring

/-! ## Irrationality, conditional on Theorem A (`theoremA_leaf`) -/

/-- Theorem A (`theoremA_leaf`) in real form: `L(2,χ₋₃) ∉ ℚ + ℚ·π²`
(as real numbers). -/
def theoremA_leaf_real : Prop :=
  ∀ a b : ℚ, L2chi3Real ≠ (a : ℝ) + (b : ℝ) * (Real.pi : ℝ) ^ 2

/-- the complex leaf implies the real leaf (cast through the `L`-bridge and
`riemannZeta_two = (π:ℂ)²/6`). -/
lemma leaf_real_of_leaf (hleaf : theoremA_leaf) : theoremA_leaf_real := by
  intro a b h
  have hchi3 : ZMod.LFunction (Submission.CDT.chi3) 2 = ZMod.LFunction (Submission.Helpers.chi3) 2 := by
    rfl
  have hpi : (Real.pi : ℂ) ^ 2 = (6 : ℂ) * riemannZeta 2 := by
    rw [riemannZeta_two]
    ring
  apply hleaf a (6 * b)
  rw [hchi3]
  rw [Submission.CDT.LFunction_chi3_two_eq_L2chi3Real]
  calc
    (L2chi3Real : ℂ) = (a : ℂ) + (b : ℂ) * (Real.pi : ℂ) ^ 2 := by
      rw [h]
      norm_num
    _ = (a : ℂ) + (b : ℂ) * ((6 : ℂ) * riemannZeta 2) := by rw [hpi]
    _ = (a : ℂ) + (((6 * b : ℚ) : ℂ)) * riemannZeta 2 := by
          norm_num
          ring

/-- the first displayed number of the paper corollary is irrational under
Theorem A: `Σₖ1/(3k+1)² = L/2 + 2π²/27 ∉ ℚ`. -/
lemma irr_res31 (hl : theoremA_leaf_real) : Irrational sum3_1 := by
  rw [Irrational]
  rintro ⟨r, hr⟩
  apply hl (2 * r) (-(4 : ℚ) / 27)
  have hbase : (r : ℝ) = L2chi3Real / 2 + (2 : ℝ) * (Real.pi : ℝ) ^ 2 / 27 := hr.trans res31_eq_paper
  have hcastA : (((2 * r : ℚ) : ℝ)) = (2 : ℝ) * (r : ℝ) := by norm_num
  have hcastB : (((-(4 : ℚ) / 27 : ℚ) : ℝ)) = -(4 : ℝ) / 27 := by norm_num
  rw [hcastA, hcastB]
  nlinarith

/-- the second displayed number of the paper corollary is irrational under
Theorem A: `Σₖ1/(3k+2)² = −L/2 + 2π²/27 ∉ ℚ`. -/
lemma irr_res32 (hl : theoremA_leaf_real) : Irrational sum3_2 := by
  rw [Irrational]
  rintro ⟨r, hr⟩
  apply hl ((-2) * r) (4 / 27 : ℚ)
  have hbase : (r : ℝ) = -L2chi3Real / 2 + (2 : ℝ) * (Real.pi : ℝ) ^ 2 / 27 := hr.trans res32_eq_paper
  have hcastA : ((((-2 * r : ℚ) : ℝ)) = -(2 : ℝ) * (r : ℝ)) := by norm_num
  have hcastB : (((4 / 27 : ℚ) : ℝ)) = (4 : ℝ) / 27 := by norm_num
  rw [hcastA, hcastB]
  nlinarith

/-- the third displayed number of the paper corollary is irrational under
Theorem A: `Σₖ1/(6k+1)² = 5L/8 + π²/18 ∉ ℚ`. -/
lemma irr_res61 (hl : theoremA_leaf_real) : Irrational sum6_1 := by
  rw [Irrational]
  rintro ⟨r, hr⟩
  apply hl ((8 : ℚ) / 5 * r) (-(4 : ℚ) / 45)
  have hbase : (r : ℝ) = (5 : ℝ) * L2chi3Real / 8 + (Real.pi : ℝ) ^ 2 / 18 := hr.trans res61_eq_paper
  have hcastA : ((((8 : ℚ) / 5 * r : ℚ) : ℝ)) = (8 : ℝ) / 5 * (r : ℝ) := by norm_num
  have hcastB : (((-(4 : ℚ) / 45 : ℚ) : ℝ)) = -(4 : ℝ) / 45 := by norm_num
  rw [hcastA, hcastB]
  nlinarith

/-- the fourth displayed number of the paper corollary is irrational under
Theorem A: `Σₖ1/(6k+5)² = −5L/8 + π²/18 ∉ ℚ`. -/
lemma irr_res65 (hl : theoremA_leaf_real) : Irrational sum6_5 := by
  rw [Irrational]
  rintro ⟨r, hr⟩
  apply hl ((-8 : ℚ) / 5 * r) (4 / 45 : ℚ)
  have hbase : (r : ℝ) = -(5 : ℝ) * L2chi3Real / 8 + (Real.pi : ℝ) ^ 2 / 18 := hr.trans res65_eq_paper
  have hcastA : ((((-8 : ℚ) / 5 * r : ℚ) : ℝ)) = -(8 : ℝ) / 5 * (r : ℝ) := by norm_num
  have hcastB : (((4 / 45 : ℚ) : ℝ)) = (4 : ℝ) / 45 := by norm_num
  rw [hcastA, hcastB]
  nlinarith

/-- **The paper's trigamma corollary, conditional on Theorem A.**  Each of
the four displayed numbers is irrational — an immediate consequence of
`theoremA_leaf` (Theorem A reduced) and the four classical identities above.
Equivalently each of `ψ₁(n/6)` (`n = 1,…,5`) is irrational. -/
theorem corollary_irrational (hleaf : theoremA_leaf) :
    Irrational sum3_1 ∧ Irrational sum3_2 ∧ Irrational sum6_1 ∧ Irrational sum6_5 := by
  have hl : theoremA_leaf_real := leaf_real_of_leaf hleaf
  exact ⟨irr_res31 hl, irr_res32 hl, irr_res61 hl, irr_res65 hl⟩

/-! ## The trigamma values `ψ₁(n/6)` (series definition, `n = 1,…,5`) -/

/-- the trigamma function at `0 < x`, defined by its classical series
`ψ₁(x) = Σₘ 1/(x+m)²` (only used at the rational points `x = n/6`, where the
series converges). -/
def psi₁ (x : ℝ) : ℝ := ∑' m : ℕ, (1 : ℝ) / ((x + (m : ℝ)) ^ 2)

/-- termwise: `1/(x+m)² = c·1/(qk+r)²` for `x = r/q` with `qk + r = q(x+m)`.
Instances below: `ψ₁(1/6) = 36·sum6_1` etc. -/
lemma psi₁_sixth : psi₁ ((1 : ℝ) / 6) = 36 * sum6_1 := by
  -- termwise: (m + 1/6) = (6m+1)/6
  have hterm : ∀ m : ℕ, (1 : ℝ) / (((1 : ℝ) / 6 + (m : ℝ)) ^ 2)
      = (36 : ℝ) * ((1 : ℝ) / (((6 * m + 1 : ℕ) : ℝ) ^ 2)) := by
    intro m
    have hm : ((1 : ℝ) / 6 + (m : ℝ)) = ((6 * m + 1 : ℕ) : ℝ) / 6 := by
      have hcast : ((6 * m + 1 : ℕ) : ℝ) = (6 : ℝ) * (m : ℝ) + 1 := by norm_num
      rw [hcast]
      field_simp
      ring
    rw [hm]
    field_simp
    ring
  calc
    psi₁ ((1 : ℝ) / 6) = ∑' m : ℕ, (36 : ℝ) * ((1 : ℝ) / (((6 * m + 1 : ℕ) : ℝ) ^ 2)) := by
          unfold psi₁
          exact tsum_congr hterm
    _ = (36 : ℝ) * ∑' m : ℕ, (1 : ℝ) / (((6 * m + 1 : ℕ) : ℝ) ^ 2) := by
          rw [tsum_mul_left]
    _ = 36 * sum6_1 := by rfl

lemma psi₁_third : psi₁ ((1 : ℝ) / 3) = 9 * sum3_1 := by
  have hterm : ∀ m : ℕ, (1 : ℝ) / (((1 : ℝ) / 3 + (m : ℝ)) ^ 2)
      = (9 : ℝ) * ((1 : ℝ) / (((3 * m + 1 : ℕ) : ℝ) ^ 2)) := by
    intro m
    have hm : ((1 : ℝ) / 3 + (m : ℝ)) = ((3 * m + 1 : ℕ) : ℝ) / 3 := by
      have hcast : ((3 * m + 1 : ℕ) : ℝ) = (3 : ℝ) * (m : ℝ) + 1 := by norm_num
      rw [hcast]
      field_simp
      ring
    rw [hm]
    field_simp
    ring
  calc
    psi₁ ((1 : ℝ) / 3) = ∑' m : ℕ, (9 : ℝ) * ((1 : ℝ) / (((3 * m + 1 : ℕ) : ℝ) ^ 2)) := by
          unfold psi₁
          exact tsum_congr hterm
    _ = (9 : ℝ) * ∑' m : ℕ, (1 : ℝ) / (((3 * m + 1 : ℕ) : ℝ) ^ 2) := by
          rw [tsum_mul_left]
    _ = 9 * sum3_1 := by rfl

lemma psi₁_two_thirds : psi₁ ((2 : ℝ) / 3) = 9 * sum3_2 := by
  have hterm : ∀ m : ℕ, (1 : ℝ) / (((2 : ℝ) / 3 + (m : ℝ)) ^ 2)
      = (9 : ℝ) * ((1 : ℝ) / (((3 * m + 2 : ℕ) : ℝ) ^ 2)) := by
    intro m
    have hm : ((2 : ℝ) / 3 + (m : ℝ)) = ((3 * m + 2 : ℕ) : ℝ) / 3 := by
      have hcast : ((3 * m + 2 : ℕ) : ℝ) = (3 : ℝ) * (m : ℝ) + 2 := by norm_num
      rw [hcast]
      field_simp
      ring
    rw [hm]
    field_simp
    ring
  calc
    psi₁ ((2 : ℝ) / 3) = ∑' m : ℕ, (9 : ℝ) * ((1 : ℝ) / (((3 * m + 2 : ℕ) : ℝ) ^ 2)) := by
          unfold psi₁
          exact tsum_congr hterm
    _ = (9 : ℝ) * ∑' m : ℕ, (1 : ℝ) / (((3 * m + 2 : ℕ) : ℝ) ^ 2) := by
          rw [tsum_mul_left]
    _ = 9 * sum3_2 := by rfl

lemma psi₁_five_sixths : psi₁ ((5 : ℝ) / 6) = 36 * sum6_5 := by
  have hterm : ∀ m : ℕ, (1 : ℝ) / (((5 : ℝ) / 6 + (m : ℝ)) ^ 2)
      = (36 : ℝ) * ((1 : ℝ) / (((6 * m + 5 : ℕ) : ℝ) ^ 2)) := by
    intro m
    have hm : ((5 : ℝ) / 6 + (m : ℝ)) = ((6 * m + 5 : ℕ) : ℝ) / 6 := by
      have hcast : ((6 * m + 5 : ℕ) : ℝ) = (6 : ℝ) * (m : ℝ) + 5 := by norm_num
      rw [hcast]
      field_simp
      ring
    rw [hm]
    field_simp
    ring
  calc
    psi₁ ((5 : ℝ) / 6) = ∑' m : ℕ, (36 : ℝ) * ((1 : ℝ) / (((6 * m + 5 : ℕ) : ℝ) ^ 2)) := by
          unfold psi₁
          exact tsum_congr hterm
    _ = (36 : ℝ) * ∑' m : ℕ, (1 : ℝ) / (((6 * m + 5 : ℕ) : ℝ) ^ 2) := by
          rw [tsum_mul_left]
    _ = 36 * sum6_5 := by rfl

/-- `ψ₁(1/2) = π²/2`: from `ψ₁(1/2) = 4·Σₘ1/(2m+1)² = 4·(3ζ(2)/4)`. -/
lemma psi₁_half : psi₁ ((1 : ℝ) / 2) = (Real.pi : ℝ) ^ 2 / 2 := by
  -- ψ₁(1/2) = Σₘ 1/(m+1/2)² = 4·Σₘ1/(2m+1)²
  have hsplit := tsum_period_split (a := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (q := 2)
    (by norm_num : 2 ≠ 0) zeta2_summable
  -- zeta2 = Σₖ1/(2k)² + Σₖ1/(2k+1)²  = zeta2/4 + odd
  have hodd : (∑' k : ℕ, (1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) = 3 * zeta2Real / 4 := by
    have hzero : (∑' k : ℕ, (1 : ℝ) / (((2 * k : ℕ) : ℝ) ^ 2)) = zeta2Real / 4 := by
      have hres := residue_zero_subseries 2 (by norm_num : 2 ≠ 0)
      rw [hres]
      norm_num
    have hmain : zeta2Real =
        (∑' k : ℕ, (1 : ℝ) / (((2 * k : ℕ) : ℝ) ^ 2))
          + (∑' k : ℕ, (1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
      calc
        zeta2Real = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by rfl
        _ = ∑ r ∈ Finset.range 2, ∑' k : ℕ, (1 : ℝ) / (((2 * k + r : ℕ) : ℝ) ^ 2) := hsplit
        _ = (∑' k : ℕ, (1 : ℝ) / (((2 * k : ℕ) : ℝ) ^ 2))
            + (∑' k : ℕ, (1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
              simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero]
    rw [hzero] at hmain
    nlinarith
  -- ψ₁(1/2) = 4·odd
  have hterm : ∀ m : ℕ, (1 : ℝ) / (((1 : ℝ) / 2 + (m : ℝ)) ^ 2)
      = (4 : ℝ) * ((1 : ℝ) / (((2 * m + 1 : ℕ) : ℝ) ^ 2)) := by
    intro m
    have hm : ((1 : ℝ) / 2 + (m : ℝ)) = ((2 * m + 1 : ℕ) : ℝ) / 2 := by
      have hcast : ((2 * m + 1 : ℕ) : ℝ) = (2 : ℝ) * (m : ℝ) + 1 := by norm_num
      rw [hcast]
      field_simp
      ring
    rw [hm]
    field_simp
    ring
  calc
    psi₁ ((1 : ℝ) / 2) = ∑' m : ℕ, (4 : ℝ) * ((1 : ℝ) / (((2 * m + 1 : ℕ) : ℝ) ^ 2)) := by
          unfold psi₁
          exact tsum_congr hterm
    _ = (4 : ℝ) * ∑' m : ℕ, (1 : ℝ) / (((2 * m + 1 : ℕ) : ℝ) ^ 2) := by
          rw [tsum_mul_left]
    _ = (4 : ℝ) * (3 * zeta2Real / 4) := by rw [hodd]
    _ = zeta2Real * 3 := by ring
    _ = (Real.pi : ℝ) ^ 2 / 2 := by
          rw [zeta2Real_eq_pi]
          ring

/-- a nonzero rational multiple of an irrational number is irrational -/
lemma irrational_of_mul_rat {x : ℝ} {q : ℚ} (hq : q ≠ 0) (hx : Irrational x) :
    Irrational ((q : ℝ) * x) := by
  rw [Irrational] at hx ⊢
  rintro ⟨r, hr⟩
  apply hx ⟨r / q, ?_⟩
  -- (r/q : ℝ) = x from (q:ℝ)·x = (r:ℝ)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  calc
    ((r / q : ℚ) : ℝ) = (r : ℝ) / (q : ℝ) := by rw [Rat.cast_div]
    _ = ((q : ℝ) * x) / (q : ℝ) := by rw [hr]
    _ = x := by field_simp [hqR]

/-- `ψ₁(1) = π²/6` (the trigamma at 1 is ζ(2)) -/
lemma psi₁_one : psi₁ 1 = (Real.pi : ℝ) ^ 2 / 6 := by
  have hf : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := zeta2_summable
  have hg : Summable (fun m : ℕ => (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2) := by
    have hi : Function.Injective (fun m : ℕ => m + 1) := by
      intro k₁ k₂ hk
      dsimp at hk
      exact Nat.succ.inj hk
    exact hf.comp_injective hi
  have hP : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2)
      atTop (𝓝 (∑' m : ℕ, (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2)) := by
    exact HasSum.tendsto_sum_nat (Summable.hasSum hg)
  have hQ : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), (1 : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2)) := by
    have hQ0 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1 : ℝ) / (n : ℝ) ^ 2)
        atTop (𝓝 (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2)) :=
      HasSum.tendsto_sum_nat (Summable.hasSum hf)
    have hsucc : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
      refine Filter.tendsto_atTop_atTop.mpr ?_
      intro b
      refine ⟨b, ?_⟩
      intro a ha
      omega
    exact hQ0.comp hsucc
  have hcong : (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), (1 : ℝ) / (n : ℝ) ^ 2)
      =ᶠ[atTop] (fun N : ℕ => ∑ k ∈ Finset.range N, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
    refine Eventually.of_forall ?_
    intro N
    dsimp
    have hfs := Finset.sum_range_succ' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) N
    rw [hfs]
    simp
  have heq : (∑' m : ℕ, (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2)
      = (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) :=
    tendsto_nhds_unique hP (hQ.congr' hcong)
  calc
    psi₁ 1 = ∑' m : ℕ, (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2 := by
      unfold psi₁
      exact tsum_congr (fun m => by
        have hc : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by norm_num
        rw [hc]
        ring)
    _ = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := heq
    _ = zeta2Real := by rfl
    _ = (Real.pi : ℝ) ^ 2 / 6 := zeta2Real_eq_pi

/-- `(zeta2Real : ℂ) = riemannZeta 2` (the real `p`-series is ζ(2)) -/
lemma zeta2Real_complex : (zeta2Real : ℂ) = riemannZeta 2 := by
  let f : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ) ^ 2
  have hterm : ∀ n : ℕ, (f n : ℂ) = (1 : ℂ) / (n : ℂ) ^ 2 := by
    intro n
    by_cases hn : n = 0
    · subst n; simp [f]
    · simp [f]
  calc
    (zeta2Real : ℂ) = ∑' n : ℕ, (f n : ℂ) := by
      rw [zeta2Real]
      dsimp [f]
      exact Complex.ofReal_tsum f
    _ = ∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ 2 := by
      exact tsum_congr hterm
    _ = riemannZeta 2 := by
      exact (zeta_nat_eq_tsum_of_gt_one (k := 2) (by norm_num)).symm

/-- a real number whose complex embedding is transcendental is irrational -/
lemma irrational_of_transcendental_cast {x : ℝ} (hx : Transcendental ℚ ((x : ℝ) : ℂ)) :
    Irrational x := by
  rw [Irrational]
  rintro ⟨r, hr⟩
  apply hx
  have hc : ((r : ℚ) : ℂ) = ((r : ℝ) : ℂ) := by norm_num
  rw [← hr, ← hc]
  exact isAlgebraic_ratCast (R := ℚ) (A := ℂ) r

/-- `ζ(2)` (real) is irrational: `ζ(2) = π²/6` is transcendental -/
lemma irr_zeta2Real : Irrational zeta2Real := by
  apply irrational_of_transcendental_cast (x := zeta2Real)
  simpa [zeta2Real_complex] using
    (Submission.Transcendence.transcendental_riemannZeta_two_complex)

/-- `ψ₁(1/2) = π²/2` is irrational (from `ζ(2)` transcendental) -/
lemma irr_psi₁_half : Irrational (psi₁ ((1 : ℝ) / 2)) := by
  rw [psi₁_half]
  -- π²/2 = 3·ζ(2)
  have hcomb : (Real.pi : ℝ) ^ 2 / 2 = 3 * zeta2Real := by
    rw [zeta2Real_eq_pi]
    ring
  rw [hcomb]
  exact irrational_of_mul_rat (by norm_num : (3 : ℚ) ≠ 0) irr_zeta2Real

/-- **The trigamma corollary, conditional on Theorem A**: for
`x = 1/6, 1/3, 1/2, 2/3, 5/6` (i.e. `ψ₁(n/6)`, `n = 1, …, 5`) the value
`ψ₁(x)` is irrational. -/
theorem trigamma_irrational (hleaf : theoremA_leaf) :
    Irrational (psi₁ ((1 : ℝ) / 6)) ∧ Irrational (psi₁ ((1 : ℝ) / 3)) ∧
      Irrational (psi₁ ((1 : ℝ) / 2)) ∧ Irrational (psi₁ ((2 : ℝ) / 3)) ∧
        Irrational (psi₁ ((5 : ℝ) / 6)) := by
  have hl : theoremA_leaf_real := leaf_real_of_leaf hleaf
  have h1 : Irrational (psi₁ ((1 : ℝ) / 6)) := by
    rw [psi₁_sixth]
    exact irrational_of_mul_rat (by norm_num : (36 : ℚ) ≠ 0) (irr_res61 hl)
  have h2 : Irrational (psi₁ ((1 : ℝ) / 3)) := by
    rw [psi₁_third]
    exact irrational_of_mul_rat (by norm_num : (9 : ℚ) ≠ 0) (irr_res31 hl)
  have h3 : Irrational (psi₁ ((1 : ℝ) / 2)) := irr_psi₁_half
  have h4 : Irrational (psi₁ ((2 : ℝ) / 3)) := by
    rw [psi₁_two_thirds]
    exact irrational_of_mul_rat (by norm_num : (9 : ℚ) ≠ 0) (irr_res32 hl)
  have h5 : Irrational (psi₁ ((5 : ℝ) / 6)) := by
    rw [psi₁_five_sixths]
    exact irrational_of_mul_rat (by norm_num : (36 : ℚ) ≠ 0) (irr_res65 hl)
  exact ⟨h1, h2, h3, h4, h5⟩

end Submission.CDT
