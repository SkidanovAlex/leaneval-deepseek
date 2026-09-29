import Mathlib
import Submission.CDT.L2chi3Real
import Submission.CDT.L2chi3Zagier

/-!
# The Markov–WZ certificate for Zagier's evaluation of `L(2,χ₋₃)` (sub-leaf 4)

The identity to be proved (`theoremA_leaf_hypergeom` in `L2chi3Zagier.lean`) is

```lean
zagierL2chiSeries = 27 · L2chi3Real,
zagierL2chiSeries := Σₙ tₙ,  tₙ = (4−15n)(−27)ⁿ/(n³·C(2n,n)²·C(3n,n))
```

Hessami Pilehrood & Hessami Pilehrood (Electron. J. Combin. 18 (2011), §3,
Thm. 1, `MR2900448`) prove this by creative telescoping from a *Markov–WZ
pair*.  At the specialization `a = 0, α = 1/3, β = 2/3` their objects reduce
to (verified by exact computation and by the numerics below):

* the WZ kernel `H(n,k) = (1/3)_k²(2/3)_k²(n+2k+1) / ((1/3)_{n+k+1}²(2/3)_{n+k+1}²)`;
* `F(n,k) = H(n,k)·(−1)ⁿ(2/3)_n(4/3)_n(n!)²/C(2n,n)`;
* `G(n,k) = F(n,k)·Q(n,k)` with the rational multiplier
  `Q(n,k) = (5n²+7n+6nk+2k²+4k+22/9)/(2(2n+1)(n+2k+1))`;
* and `(F,G)` satisfies the WZ relation
  `F(n+1,k) − F(n,k) = G(n,k+1) − G(n,k)`.

Both series collapse to one-variable ones:

* `F(0,k) = 81(2k+1)/((3k+1)²(3k+2)²) = 27·pairSum k`, so
  `Σ_k F(0,k) = 27·L2chi3Real`;
* `G(n,0) = t_{n+1}`, so `Σ_n G(n,0) = Σ_n tₙ` (modulo `t₀ = 0`).

Consequently (Proposition A of HHP) the single telescoping identity

```lean
Σ_{n≥0} G(n,0) = Σ_{k≥0} F(0,k)
```

is exactly equivalent to `theoremA_leaf_hypergeom`.  This module formalises
the objects and the *algebraic core* of that proof:

* `zagierV k n = ∏_{j=0}^{n}(3k+3j+1)(3k+3j+2)` — the window product;
* `zagierS n` and `zagierF n k` (the closed forms of the WZ kernel);
* the one-step recurrences (`zagierS_succ`, `zagierF_succ_n`,
  `zagierF_succ_k`);
* the rational multiplier `zagierQ`, `zagierG := zagierF · zagierQ`;
* **the WZ relation** `zagier_wz` (the algebraic heart; the pure rational
  identity behind it is `zagier_wz_pure`);
* the finite-rectangle telescoping lemma `zagier_rect` (summing the WZ
  relation over an `(n,k)`-rectangle collapses to boundary terms);
* the explicit value `zagierF_zero` of `F(0,k)`.

**Sub-leaf 4 is CLOSED.**  This module formalises the full Markov–WZ
certificate at `a=0, α=1/3, β=2/3` AND the analytic limits that turn it
into Zagier's hypergeometric-type evaluation of `L(2,χ₋₃)`.  Concretely:

* the algebraic core: the WZ relation `zagier_wz`, the rectangle
  telescoping `zagier_rect`/`zagier_rect'`, and the termwise
  identifications `F(0,k) = 27·pairSum k` (`zagierF_zero_eq_pair`, hence
  `Σ_k F(0,k) = 27·L(2,χ₋₃)` by `zagierF_zero_tsum`) and
  `G(n,0) = t_{n+1}` (`zagierG_zero_eq_term`, hence
  `Σ_n G(n,0) = Σ_n tₙ` by `zagierG_zero_tsum`);
* the analytic half: the uniform step bound `|R(n,k)| ≤ 1/2`
  (`zagierR_abs_le_half`), the decay `|F(n,k)| ≤ 2⁻ⁿ·|F(0,k)|`
  (`zagierF_abs_pow`), the pointwise and finite-sum limits in `N`
  (`zagierF_tendsto_zero`, `zagierF_finitesum_tendsto_zero`), the
  `n`-summability of `G(·,k)` for each `k` (`summable_zagierG_fixed`),
  the **`N → ∞` limit at fixed `K`** (`zagier_rect_limit_N`), the exact
  `k = 0`-row decay `|F(0,k)| = 81(2k+1)/((3k+1)²(3k+2)²)`
  (`zagierF_zero_abs`, `zagierF_zero_sq_le`) and the domination
  `‖Σ'ₙG(n,M)‖ ≤ 28(M+1)²·|F(0,M)| = O(M⁻¹)`
  (`tsum_zagierG_norm_bound`, `tsum_zagierG_norm_real`), hence
  `Σ'ₙG(n,M) → 0` (`tsum_zagierG_M_tendsto_zero`), and the **`K → ∞`
  limit** `zagier_wz_infinite_thm : zagier_wz_infinite` where
  `zagier_wz_infinite := (Σ'ₙ G(n,0)) = (Σ'ₖ F(0,k))`;
* the closure `theoremA_leaf_hypergeom_of_wz` and the two theorems
  `zagierL2chi_identity : theoremA_leaf_hypergeom` and
  `zagierL2chi_leaf_main` (formerly the `sorry` placeholders of
  `Submission.CDT.L2chi3Zagier`, which cannot import this module).
All declarations in this module are fully proved (no axioms, no `sorry`).
-/

open scoped BigOperators
open Filter
open scoped Topology

noncomputable section

namespace Submission.CDT

/-! ## Window products and the closed forms -/

/-- The window product `V(k,n) = ∏_{j=0}^{n} (3k+3j+1)(3k+3j+2)` over `ℚ`
(the two nonzero residue classes mod 3 on the window `{k, …, k+n}`). -/
def zagierV (k n : ℕ) : ℚ :=
  ∏ j ∈ Finset.range (n + 1), (((3 * k + 3 * j + 1) * (3 * k + 3 * j + 2) : ℕ) : ℚ)

/-- `V(k,0) = (3k+1)(3k+2)` -/
lemma zagierV_zero (k : ℕ) : zagierV k 0 = (((3 * k + 1) * (3 * k + 2) : ℕ) : ℚ) := by
  unfold zagierV
  simp

/-- step in the `n`-direction: `V(k,n+1) = V(k,n)·(3k+3n+4)(3k+3n+5)` -/
lemma zagierV_succ_n (k n : ℕ) :
    zagierV k (n + 1) =
      zagierV k n * (((3 * k + 3 * (n + 1) + 1) * (3 * k + 3 * (n + 1) + 2) : ℕ) : ℚ) := by
  unfold zagierV
  rw [Finset.prod_range_succ]

/-- step in the `k`-direction: `V(k,n+1) = (3k+1)(3k+2)·V(k+1,n)` -/
lemma zagierV_succ_k (k n : ℕ) :
    zagierV k (n + 1) =
      (((3 * k + 1) * (3 * k + 2) : ℕ) : ℚ) * zagierV (k + 1) n := by
  unfold zagierV
  let f : ℕ → ℕ → ℚ := fun k j => (((3 * k + 3 * j + 1) * (3 * k + 3 * j + 2) : ℕ) : ℚ)
  calc
    ∏ j ∈ Finset.range (n + 1 + 1), f k j
        = (∏ j ∈ Finset.range (n + 1), f k (j + 1)) * f k 0 := by
            exact Finset.prod_range_succ' (fun j => f k j) (n + 1)
    _ = (∏ j ∈ Finset.range (n + 1), f (k + 1) j) * f k 0 := by
            congr 1
            · apply Finset.prod_congr rfl
              intro j hj
              simp [f]
              ring_nf
    _ = (((3 * k + 1) * (3 * k + 2) : ℕ) : ℚ) * ∏ j ∈ Finset.range (n + 1), f (k + 1) j := by
            rw [show f k 0 = (((3 * k + 1) * (3 * k + 2) : ℕ) : ℚ) by simp [f]]
            ring

/-- `V(k,n)` is positive -/
lemma zagierV_pos (k n : ℕ) : 0 < zagierV k n := by
  unfold zagierV
  apply Finset.prod_pos
  intro j hj
  have hpos : 0 < (3 * k + 3 * j + 1) * (3 * k + 3 * j + 2) := by
    exact mul_pos (by omega : 0 < 3 * k + 3 * j + 1) (by omega : 0 < 3 * k + 3 * j + 2)
  exact_mod_cast hpos

/-- `V(k,n) ≠ 0` -/
lemma zagierV_ne_zero (k n : ℕ) : zagierV k n ≠ 0 := ne_of_gt (zagierV_pos k n)

/-- the `n`-dependent factor of the WZ kernel:
`s(n) = (−1)ⁿ(3n+1)(3n)!·n!·3^{4(n+1)}/(27ⁿ·C(2n,n))` -/
def zagierS (n : ℕ) : ℚ :=
  (-1 : ℚ) ^ n * (3 * (n : ℚ) + 1) * ((3 * n).factorial : ℚ) * (n.factorial : ℚ) *
    (3 : ℚ) ^ (4 * (n + 1)) / ((27 : ℚ) ^ n * (Nat.choose (2 * n) n : ℚ))

/-- `s(n+1) = s(n)·sr(n)` with the rational step
`sr(n) = −(3n+2)(3n+3)(3n+4)(n+1)³·3/((2n+2)(2n+1))` -/
lemma zagierS_succ (n : ℕ) :
    zagierS (n + 1) =
      zagierS n * (-(3 * (n : ℚ) + 2) * (3 * (n : ℚ) + 3) * (3 * (n : ℚ) + 4) *
        ((n : ℚ) + 1) ^ 3 * 3 / ((2 * (n : ℚ) + 2) * (2 * (n : ℚ) + 1))) := by
  unfold zagierS
  have hfac3 := cast_fact_three_succ n
  have hfac1 : ((n + 1).factorial : ℚ) = (n.factorial : ℚ) * ((n : ℚ) + 1) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hcb : (Nat.choose (2 * (n + 1)) (n + 1) : ℚ) =
      (Nat.choose (2 * n) n : ℚ) * (2 * (2 * (n : ℚ) + 1) / ((n : ℚ) + 1)) := by
    simpa [Nat.centralBinom] using (centralBinom_succ_ratio n)
  have hsig : (-1 : ℚ) ^ (n + 1) = -(-1 : ℚ) ^ n := by
    rw [pow_succ]
    ring
  have hpow : (3 : ℚ) ^ (4 * (n + 1 + 1)) = (3 : ℚ) ^ (4 * (n + 1)) * 81 := by
    rw [show 4 * (n + 1 + 1) = 4 * (n + 1) + 4 by omega]
    rw [pow_add]
    norm_num
  have hpow27 : (27 : ℚ) ^ (n + 1) = (27 : ℚ) ^ n * 27 := by
    rw [pow_succ]
  have hcast : (3 * ((n + 1 : ℕ) : ℚ) + 1) = 3 * (n : ℚ) + 4 := by
    rw [Nat.cast_add, Nat.cast_one]
    ring
  rw [hsig, hfac3, hfac1, hcb, hpow, hpow27, hcast]
  field_simp
  ring


/-- `s(0) = 81` -/
lemma zagierS_zero : zagierS 0 = 81 := by
  unfold zagierS
  norm_num

/-- the WZ-kernel function in closed form:
`F(n,k) = s(n)·(n+2k+1)/V(k,n)²` -/
def zagierF (n k : ℕ) : ℚ :=
  zagierS n * ((n : ℚ) + 2 * (k : ℚ) + 1) / (zagierV k n) ^ 2

/-- the rational multiplier `Q(n,k)` of the Markov–WZ mate -/
def zagierQ (n k : ℕ) : ℚ :=
  (45 * (n : ℚ) ^ 2 + 63 * (n : ℚ) + 54 * (n : ℚ) * (k : ℚ) + 18 * (k : ℚ) ^ 2 +
    36 * (k : ℚ) + 22) / (18 * (2 * (n : ℚ) + 1) * ((n : ℚ) + 2 * (k : ℚ) + 1))

/-- `G(n,k) = F(n,k)·Q(n,k)` (the MWZ mate of `F`) -/
def zagierG (n k : ℕ) : ℚ := zagierF n k * zagierQ n k

/-- the `n`-step multiplier `R(n,k)` with `F(n+1,k) = F(n,k)·R(n,k)` -/
def zagierR (n k : ℕ) : ℚ :=
  (-(3 * (n : ℚ) + 2) * (3 * (n : ℚ) + 3) * (3 * (n : ℚ) + 4) * ((n : ℚ) + 1) ^ 3 * 3 *
      ((n : ℚ) + 2 * (k : ℚ) + 2)) /
    ((2 * (n : ℚ) + 2) * (2 * (n : ℚ) + 1) * ((n : ℚ) + 2 * (k : ℚ) + 1) *
      (3 * (k : ℚ) + 3 * (n : ℚ) + 4) ^ 2 * (3 * (k : ℚ) + 3 * (n : ℚ) + 5) ^ 2)

/-- the `k`-step multiplier `S(n,k)` with `F(n,k+1) = F(n,k)·S(n,k)` -/
def zagierSrat (n k : ℕ) : ℚ :=
  ((n : ℚ) + 2 * (k : ℚ) + 3) * (3 * (k : ℚ) + 1) ^ 2 * (3 * (k : ℚ) + 2) ^ 2 /
    (((n : ℚ) + 2 * (k : ℚ) + 1) * (3 * (k : ℚ) + 3 * (n : ℚ) + 4) ^ 2 *
      (3 * (k : ℚ) + 3 * (n : ℚ) + 5) ^ 2)

/-- `F(0,k) = 81(2k+1)/((3k+1)²(3k+2)²)` -/
lemma zagierF_zero (k : ℕ) :
    zagierF 0 k = (81 : ℚ) * (2 * (k : ℚ) + 1) /
      ((3 * (k : ℚ) + 1) ^ 2 * (3 * (k : ℚ) + 2) ^ 2) := by
  unfold zagierF
  rw [zagierS_zero]
  have hV : (zagierV k 0) ^ 2 = ((3 * (k : ℚ) + 1) ^ 2 * (3 * (k : ℚ) + 2) ^ 2) := by
    rw [zagierV_zero]
    push_cast
    ring
  rw [hV]
  ring

/-- `F(n+1,k) = F(n,k)·R(n,k)` -/
lemma zagierF_succ_n (n k : ℕ) :
    zagierF (n + 1) k = zagierF n k * zagierR n k := by
  unfold zagierF zagierR
  rw [zagierS_succ]
  have hvn : zagierV k (n + 1) = zagierV k n *
      ((3 * (k : ℚ) + 3 * (n : ℚ) + 4) * (3 * (k : ℚ) + 3 * (n : ℚ) + 5)) := by
    rw [zagierV_succ_n]
    congr 2
    push_cast
    ring_nf
  rw [hvn]
  field_simp [zagierV_ne_zero k n]
  push_cast
  ring

/-- `F(n,k+1) = F(n,k)·S(n,k)` -/
lemma zagierF_succ_k (n k : ℕ) :
    zagierF n (k + 1) = zagierF n k * zagierSrat n k := by
  unfold zagierF zagierSrat
  have hX : (((3 * k + 1) * (3 * k + 2) : ℕ) : ℚ) ≠ 0 := by positivity
  have hvk : zagierV (k + 1) n = zagierV k (n + 1) / (((3 * k + 1) * (3 * k + 2) : ℕ) : ℚ) := by
    calc
      zagierV (k + 1) n
          = ((((3 * k + 1) * (3 * k + 2) : ℕ) : ℚ) * zagierV (k + 1) n) /
              (((3 * k + 1) * (3 * k + 2) : ℕ) : ℚ) := by
              field_simp [hX]
      _ = zagierV k (n + 1) / (((3 * k + 1) * (3 * k + 2) : ℕ) : ℚ) := by
              rw [← zagierV_succ_k]
  rw [hvk]
  have hvn : zagierV k (n + 1) = zagierV k n *
      ((3 * (k : ℚ) + 3 * (n : ℚ) + 4) * (3 * (k : ℚ) + 3 * (n : ℚ) + 5)) := by
    rw [zagierV_succ_n]
    congr 2
    push_cast
    ring_nf
  rw [hvn]
  field_simp [zagierV_ne_zero k n]
  push_cast
  ring

/-- the pure rational identity behind the WZ relation:
`R(n,k) − 1 = S(n,k)·Q(n,k+1) − Q(n,k)` -/
lemma zagier_wz_pure (n k : ℕ) :
    zagierR n k - 1 = zagierSrat n k * zagierQ n (k + 1) - zagierQ n k := by
  unfold zagierR zagierSrat zagierQ
  have h1 : (n : ℚ) + 2 * (k : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℚ) + 2 * (k : ℚ) + 3 ≠ 0 := by positivity
  have h3 : (2 * (n : ℚ) + 1) ≠ 0 := by positivity
  have h4 : (2 * (n : ℚ) + 2) ≠ 0 := by positivity
  have h5 : (3 * (k : ℚ) + 3 * (n : ℚ) + 4) ≠ 0 := by positivity
  have h6 : (3 * (k : ℚ) + 3 * (n : ℚ) + 5) ≠ 0 := by positivity
  field_simp [h1, h2, h3, h4, h5, h6]
  push_cast
  ring

/-- **the WZ relation** of the Markov–WZ pair at `a=0, α=1/3, β=2/3`:
`F(n+1,k) − F(n,k) = G(n,k+1) − G(n,k)` -/
lemma zagier_wz (n k : ℕ) :
    zagierF (n + 1) k - zagierF n k = zagierG n (k + 1) - zagierG n k := by
  rw [zagierG, zagierF_succ_n, zagierF_succ_k]
  have hpure := zagier_wz_pure n k
  calc
    zagierF n k * zagierR n k - zagierF n k
        = zagierF n k * (zagierR n k - 1) := by ring
    _ = zagierF n k * (zagierSrat n k * zagierQ n (k + 1) - zagierQ n k) := by rw [hpure]
    _ = (zagierF n k * zagierSrat n k) * zagierQ n (k + 1) - zagierF n k * zagierQ n k := by ring

/-- finite rectangle telescoping of the WZ relation over `n ≤ N`, `k ≤ K`:
`Σ_{k≤K}(F(N+1,k) − F(0,k)) = Σ_{n≤N}(G(n,K+1) − G(n,0))` -/
lemma zagier_rect (N K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), zagierF (N + 1) k) - (∑ k ∈ Finset.range (K + 1), zagierF 0 k)
      = (∑ n ∈ Finset.range (N + 1), zagierG n (K + 1)) - (∑ n ∈ Finset.range (N + 1), zagierG n 0) := by
  calc
    (∑ k ∈ Finset.range (K + 1), zagierF (N + 1) k) - (∑ k ∈ Finset.range (K + 1), zagierF 0 k)
        = ∑ k ∈ Finset.range (K + 1), (zagierF (N + 1) k - zagierF 0 k) := by
            rw [← Finset.sum_sub_distrib]
    _ = ∑ k ∈ Finset.range (K + 1), ∑ n ∈ Finset.range (N + 1), (zagierF (n + 1) k - zagierF n k) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [← Finset.sum_range_sub (fun n => zagierF n k) (N + 1)]
    _ = ∑ k ∈ Finset.range (K + 1), ∑ n ∈ Finset.range (N + 1), (zagierG n (k + 1) - zagierG n k) := by
            apply Finset.sum_congr rfl
            intro k hk
            apply Finset.sum_congr rfl
            intro n hn
            exact zagier_wz n k
    _ = ∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (K + 1), (zagierG n (k + 1) - zagierG n k) := by
            rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.range (N + 1), (zagierG n (K + 1) - zagierG n 0) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact Finset.sum_range_sub (fun k => zagierG n k) (K + 1)
    _ = (∑ n ∈ Finset.range (N + 1), zagierG n (K + 1)) - (∑ n ∈ Finset.range (N + 1), zagierG n 0) := by
            rw [Finset.sum_sub_distrib]

/-! ## Termwise identifications with the leaf series -/

/-- `F(0,k) = 27·pairSum k` — the WZ left-hand series equals the paired series
(so `Σ_k F(0,k) = 27·L(2,χ₋₃)`) -/
lemma zagierF_zero_eq_pair (k : ℕ) : (zagierF 0 k : ℝ) = 27 * pairSum k := by
  have hf := zagierF_zero k
  have hcast : (zagierF 0 k : ℝ) =
      (81 : ℝ) * (2 * (k : ℝ) + 1) / ((3 * (k : ℝ) + 1) ^ 2 * (3 * (k : ℝ) + 2) ^ 2) := by
    rw [hf]
    norm_num [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_add]
  rw [hcast, pairSum_rat_norm]
  field_simp
  ring

/-- the left-hand series of the WZ identity is summable (its terms decay like
`const/k²`, being `27·pairSum`) -/
lemma summable_zagierF_zero : Summable fun k : ℕ => (zagierF 0 k : ℝ) := by
  let ⟨a, ha⟩ := pairSum_summable
  exact Summable.congr
    (⟨27 * a, by simpa [mul_comm, mul_left_comm, mul_assoc] using ha.mul_left 27⟩ :
      Summable fun k : ℕ => 27 * pairSum k)
    (fun k => (zagierF_zero_eq_pair k).symm)

/-- `V(0,n) = (3n+3)!/(3^{n+1}(n+1)!)` -/
lemma zagierV_zero_n_fact (n : ℕ) :
    zagierV 0 n = ((3 * n + 3).factorial : ℚ) / ((3 : ℚ) ^ (n + 1) * ((n + 1).factorial : ℚ)) := by
  induction n with
  | zero =>
      rw [zagierV_zero]
      norm_num
  | succ n ih =>
      rw [zagierV_succ_n]
      rw [ih]
      have hfac : ((3 * (n + 1) + 3).factorial : ℚ) =
          ((3 * n + 3).factorial : ℚ) *
            ((3 * (n : ℚ) + 4) * (3 * (n : ℚ) + 5) * (3 * (n : ℚ) + 6)) := by
        have hnat : 3 * (n + 1) + 3 = (3 * n + 3) + 3 := by omega
        rw [hnat]
        rw [show (3 * n + 3) + 3 = (3 * n + 3) + 2 + 1 by omega, Nat.factorial_succ]
        rw [show (3 * n + 3) + 2 = (3 * n + 3) + 1 + 1 by omega, Nat.factorial_succ]
        rw [Nat.factorial_succ]
        norm_num
        ring
      have hfacn1 : (((n + 1) + 1).factorial : ℚ) =
          ((n + 1).factorial : ℚ) * ((n : ℚ) + 2) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hfac, hfacn1]
      field_simp
      push_cast
      ring

/-! ## `G(n,0) = t_{n+1}` (termwise identification with the leaf summand) -/

/-- central-binomial step in `choose`-form: `C(2(m+1),m+1) = C(2m,m)·2(2m+1)/(m+1)` -/
lemma cb_step (m : ℕ) :
    (Nat.choose (2 * (m + 1)) (m + 1) : ℚ) =
      (Nat.choose (2 * m) m : ℚ) * (2 * (2 * (m : ℚ) + 1) / ((m : ℚ) + 1)) := by
  have h := centralBinom_succ_ratio m
  rw [Nat.centralBinom_eq_two_mul_choose (m + 1)] at h
  rw [Nat.centralBinom_eq_two_mul_choose m] at h
  exact h

/-- the step of `G(n,0)` in `n` (from the WZ machinery): -/
lemma zagierG_succ_zero (n : ℕ) :
    zagierG (n + 1) 0 = zagierG n 0 * (zagierR n 0 * zagierQ (n + 1) 0 / zagierQ n 0) := by
  unfold zagierG
  rw [zagierF_succ_n]
  have hq : zagierQ n 0 ≠ 0 := by
    unfold zagierQ
    positivity
  field_simp [hq]

/-- the matching step of the leaf summand `t_{n+1}`:
`t_{n+2} = t_{n+1}·R(n,0)·Q(n+1,0)/Q(n,0)` -/
lemma zagier_t_ratio (n : ℕ) :
    zagierL2chiTerm (n + 2) =
      zagierL2chiTerm (n + 1) * (zagierR n 0 * zagierQ (n + 1) 0 / zagierQ n 0) := by
  unfold zagierL2chiTerm zagierR zagierQ
  rw [if_neg (by omega : ¬ n + 2 = 0)]
  rw [if_neg (by omega : ¬ n + 1 = 0)]
  -- central-binomial and 3n-choose steps at index n+1:
  have hcb := cb_step (n + 1)
  have h3 := choose_three_succ_ratio (n + 1)
  have hsig : (-27 : ℚ) ^ (n + 2) = (-27 : ℚ) ^ (n + 1) * (-27) := by
    rw [pow_succ]
  rw [hcb, h3, hsig]
  -- algebra:
  field_simp
  push_cast
  ring

/-- `G(n,0) = t_{n+1}` for every `n` (termwise identification; induction from
the matched one-step ratios `zagierG_succ_zero`/`zagier_t_ratio`) -/
lemma zagierG_zero_eq_term (n : ℕ) : zagierG n 0 = zagierL2chiTerm (n + 1) := by
  induction n with
  | zero =>
      unfold zagierG zagierF
      rw [zagierS_zero, zagierV_zero]
      unfold zagierQ
      rw [zagierL2chiTerm_one]
      norm_num
  | succ n ih =>
      calc
        zagierG (n + 1) 0 = zagierG n 0 * (zagierR n 0 * zagierQ (n + 1) 0 / zagierQ n 0) := by
            exact zagierG_succ_zero n
        _ = zagierL2chiTerm (n + 1) * (zagierR n 0 * zagierQ (n + 1) 0 / zagierQ n 0) := by
            rw [ih]
        _ = zagierL2chiTerm (n + 1 + 1) := by
            rw [zagier_t_ratio n]

/-- `G(n,0) = t_{n+1}` after casting to `ℝ` -/
lemma zagierG_zero_eq_term_real (n : ℕ) :
    (zagierG n 0 : ℝ) = (zagierL2chiTerm (n + 1) : ℝ) := by
  exact congrArg (fun q : ℚ => (q : ℝ)) (zagierG_zero_eq_term n)

/-! ## Bridges from the WZ series to the leaf series -/

/-- the right-hand WZ series equals `27·L(2,χ₋₃)`:
`Σ_k F(0,k) = 27·Σ_k pairSum k` -/
theorem zagierF_zero_tsum : (∑' k : ℕ, (zagierF 0 k : ℝ)) = 27 * L2chi3Real := by
  rw [L2chi3Real_eq_pair_tsum]
  calc
    (∑' k : ℕ, (zagierF 0 k : ℝ)) = ∑' k : ℕ, 27 * pairSum k := by
        apply tsum_congr
        intro k
        exact zagierF_zero_eq_pair k
    _ = 27 * (∑' k : ℕ, pairSum k) := by
        rw [← tsum_mul_left]

/-- the left-hand WZ series equals the leaf series:
`Σ_n G(n,0) = Σ_n tₙ` (the shift is absorbed by `t₀ = 0`) -/
theorem zagierG_zero_tsum :
    (∑' n : ℕ, (zagierG n 0 : ℝ)) = (∑' n : ℕ, (zagierL2chiTerm n : ℝ)) := by
  calc
    (∑' n : ℕ, (zagierG n 0 : ℝ)) = ∑' n : ℕ, (zagierL2chiTerm (n + 1) : ℝ) := by
        apply tsum_congr
        intro n
        exact zagierG_zero_eq_term_real n
    _ = (∑' n : ℕ, (zagierL2chiTerm n : ℝ)) := by
        let f : ℕ → ℝ := fun n => (zagierL2chiTerm n : ℝ)
        let ⟨a, ha⟩ := (summable_zagierL2chi_term : Summable fun n : ℕ => (zagierL2chiTerm n : ℝ))
        have h0 : f 0 = 0 := by simp [f, zagierL2chiTerm]
        have hsh : HasSum (fun n : ℕ => f (n + 1)) a := by
          refine (hasSum_nat_add_iff (f := f) 1).2 ?_
          simpa [h0] using ha
        rw [hsh.tsum_eq]
        exact ha.tsum_eq.symm

/-- **the analytic content of sub-leaf 4** (the one open step): the
infinite telescoping `Σ_n G(n,0) = Σ_k F(0,k)` of the WZ pair, obtained by
passing the finite rectangle identity `zagier_rect` through the limits
`N → ∞`, `K → ∞` (the algebraic content is fully proved in this module:
the WZ relation `zagier_wz` and the rectangle identity `zagier_rect`). -/
def zagier_wz_infinite : Prop :=
  (∑' n : ℕ, (zagierG n 0 : ℝ)) = (∑' k : ℕ, (zagierF 0 k : ℝ))

/-- **Sub-leaf 4 reduces to the WZ infinite telescoping.**  If
`Σ_n G(n,0) = Σ_k F(0,k)` (the analytic step), then Zagier's hypergeometric
evaluation of `L(2,χ₋₃)` follows (`theoremA_leaf_hypergeom`). -/
theorem theoremA_leaf_hypergeom_of_wz (hwz : zagier_wz_infinite) : theoremA_leaf_hypergeom := by
  unfold theoremA_leaf_hypergeom zagierL2chiSeries at ⊢
  unfold zagier_wz_infinite at hwz
  calc
    (∑' n : ℕ, (zagierL2chiTerm n : ℝ)) = (∑' n : ℕ, (zagierG n 0 : ℝ)) := by
        rw [← zagierG_zero_tsum]
    _ = (∑' k : ℕ, (zagierF 0 k : ℝ)) := hwz
    _ = 27 * L2chi3Real := by
        exact zagierF_zero_tsum

/-- the same, in the paired-residue form (equivalent to
`theoremA_leaf_hypergeom` by `zagierL2chi_identity_iff_pair`): -/
theorem zagier_pair_of_wz (hwz : zagier_wz_infinite) :
    (∑' k : ℕ, pairSum k) = (1 / 27 : ℝ) * zagierL2chiSeries := by
  exact (zagierL2chi_identity_iff_pair.mp) (theoremA_leaf_hypergeom_of_wz hwz)

/-- the left-hand series `Σ_n (G(n,0):ℝ)` is summable (via the termwise
identification `G(n,0) = t_{n+1}` and the known summability of `t`) -/
lemma summable_zagierG_zero : Summable fun n : ℕ => (zagierG n 0 : ℝ) := by
  let f : ℕ → ℝ := fun n => (zagierL2chiTerm n : ℝ)
  have hs : Summable fun n : ℕ => f (n + 1) := by
    exact (summable_nat_add_iff (f := f) 1).2 (summable_zagierL2chi_term)
  exact Summable.congr hs (fun n => (zagierG_zero_eq_term_real n).symm)

/-- `F(n,k) ≠ 0` for all `n,k` -/
lemma zagierF_ne_zero (n k : ℕ) : zagierF n k ≠ 0 := by
  unfold zagierF
  have hS : zagierS n ≠ 0 := by
    unfold zagierS
    have h1 : (-1 : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2 : (3 * (n : ℚ) + 1) ≠ 0 := by positivity
    have h3 : ((3 * n).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
    have h4 : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
    have h5 : (3 : ℚ) ^ (4 * (n + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h6 : (27 : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have h7 : (Nat.choose (2 * n) n : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : n ≤ 2 * n)).ne'
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4) h5)
      (mul_ne_zero h6 h7)
  have hnz : ((n : ℚ) + 2 * (k : ℚ) + 1) ≠ 0 := by positivity
  exact div_ne_zero (mul_ne_zero hS hnz) (pow_ne_zero 2 (zagierV_ne_zero k n))

/-- exact `n`-step ratio of `|F|`: `|F(n+1,k)| = |F(n,k)|·ρ(n,k)` where the
rational function `ρ(n,k) = |R(n,k)|` is (for fixed `k`) asymptotic to `1/4`
in `n` (the basis of the analytic limit arguments). -/
lemma zagierF_abs_succ_n (n k : ℕ) :
    |zagierF (n + 1) k| = |zagierF n k| * |zagierR n k| := by
  rw [zagierF_succ_n]
  rw [abs_mul]

/-! ## Analytic half (a): decay of `F` in the `n` direction

With the exact `n`-step ratio of `|F|` (`zagierF_abs_succ_n`) and the
explicit form of `|R(n,k)|`, we show the **uniform (in `k`) bound
`|R(n,k)| ≤ 1/2`**, hence `|F(n,k)| ≤ 2⁻ⁿ·|F(0,k)|` and — the keystone of
the `N → ∞` limit — `|F(N,k)| → 0` as `N → ∞` for every fixed `k`. -/

/-- explicit form of the step multiplier magnitude `|R(n,k)|` -/
lemma zagierR_abs (n k : ℕ) :
    |zagierR n k| =
      (3 * (n : ℚ) + 2) * (3 * (n : ℚ) + 3) * (3 * (n : ℚ) + 4) * ((n : ℚ) + 1) ^ 3 * 3 *
          ((n : ℚ) + 2 * (k : ℚ) + 2) /
        ((2 * (n : ℚ) + 2) * (2 * (n : ℚ) + 1) * ((n : ℚ) + 2 * (k : ℚ) + 1) *
          (3 * (k : ℚ) + 3 * (n : ℚ) + 4) ^ 2 * (3 * (k : ℚ) + 3 * (n : ℚ) + 5) ^ 2) := by
  unfold zagierR
  rw [abs_div]
  congr 1
  · -- |−(3n+2)(3n+3)(3n+4)(n+1)³·3·(n+2k+2)| = the positive product
    rw [show -(3 * (n : ℚ) + 2) * (3 * (n : ℚ) + 3) * (3 * (n : ℚ) + 4) * ((n : ℚ) + 1) ^ 3 * 3 *
          ((n : ℚ) + 2 * (k : ℚ) + 2) =
        -((3 * (n : ℚ) + 2) * (3 * (n : ℚ) + 3) * (3 * (n : ℚ) + 4) * ((n : ℚ) + 1) ^ 3 * 3 *
          ((n : ℚ) + 2 * (k : ℚ) + 2)) by ring]
    rw [abs_neg]
    rw [abs_of_pos]
    positivity
  · rw [abs_of_pos]
    positivity

/-- uniform bound of the step multiplier: `|R(n,k)| ≤ 1/2` for all `n,k` -/
lemma zagierR_abs_le_half (n k : ℕ) : |zagierR n k| ≤ (1 : ℚ) / 2 := by
  rw [zagierR_abs]
  have hQpos : 0 < (2 * (n : ℚ) + 2) * (2 * (n : ℚ) + 1) * ((n : ℚ) + 2 * (k : ℚ) + 1) *
      (3 * (k : ℚ) + 3 * (n : ℚ) + 4) ^ 2 * (3 * (k : ℚ) + 3 * (n : ℚ) + 5) ^ 2 := by positivity
  rw [div_le_iff₀ hQpos]
  have h2 : 0 ≤ (2 * (n : ℚ) + 2) * (2 * (n : ℚ) + 1) * ((n : ℚ) + 2 * (k : ℚ) + 1) *
        (3 * (k : ℚ) + 3 * (n : ℚ) + 4) ^ 2 * (3 * (k : ℚ) + 3 * (n : ℚ) + 5) ^ 2 -
      2 * ((3 * (n : ℚ) + 2) * (3 * (n : ℚ) + 3) * (3 * (n : ℚ) + 4) * ((n : ℚ) + 1) ^ 3 * 3 *
        ((n : ℚ) + 2 * (k : ℚ) + 2)) := by
    ring_nf
    positivity
  nlinarith

/-- the step bound in `|F|`: `|F(n+1,k)| ≤ ½·|F(n,k)|` -/
lemma zagierF_abs_succ_le (n k : ℕ) : |zagierF (n + 1) k| ≤ (1 : ℚ) / 2 * |zagierF n k| := by
  have hb := zagierR_abs_le_half n k
  have h := zagierF_abs_succ_n n k
  rw [h]
  -- |F(n,k)·R(n,k)| ≤ (1/2)|F(n,k)|:
  calc
    |zagierF n k| * |zagierR n k| ≤ |zagierF n k| * (1 : ℚ) / 2 := by
          nlinarith [abs_nonneg (zagierF n k), hb]
    _ = (1 : ℚ) / 2 * |zagierF n k| := by ring

/-- geometric decay of `|F|` in the `n` direction: `|F(n,k)| ≤ 2⁻ⁿ·|F(0,k)|` -/
lemma zagierF_abs_pow (n k : ℕ) : |zagierF n k| ≤ |zagierF 0 k| * ((1 : ℚ) / 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        |zagierF (n + 1) k| ≤ (1 : ℚ) / 2 * |zagierF n k| := by
              exact zagierF_abs_succ_le n k
        _ ≤ (1 : ℚ) / 2 * (|zagierF 0 k| * ((1 : ℚ) / 2) ^ n) := by
              exact mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℚ) ≤ 1 / 2)
        _ = |zagierF 0 k| * ((1 : ℚ) / 2) ^ (n + 1) := by
              rw [show (1 : ℚ) / 2 * (|zagierF 0 k| * ((1 : ℚ) / 2) ^ n) =
                  |zagierF 0 k| * (((1 : ℚ) / 2) * ((1 : ℚ) / 2) ^ n) by ring]
              rw [← pow_succ']

/-! ## Analytic half (b): `F(N,k) → 0` in `N`, summability of `G(·,k)` in `n`

Throughout this section the geometric factor is written as `((1 : ℚ)/2)^n`
(equal to `(1:ℚ)/2^n` in `ℚ`, but the former form casts cleanly to `ℝ`). -/

/-- real-norm version of the geometric decay of `|F|` in `n`:
`‖F(N,k)‖ ≤ |F(0,k)|·2⁻ᴺ` -/
lemma zagierF_norm_pow_real (N k : ℕ) :
    ‖(zagierF N k : ℝ)‖ ≤ (((|zagierF 0 k| : ℚ) : ℝ) * ((1 : ℝ) / 2) ^ N) := by
  have hb := zagierF_abs_pow N k   -- |F(N,k)| ≤ |F(0,k)|·((1:ℚ)/2)^N
  rw [Real.norm_eq_abs]
  rw [← Rat.cast_abs]
  have hb' : (((|zagierF N k|) : ℚ) : ℝ) ≤ ((((|zagierF 0 k| : ℚ) * ((1 : ℚ) / 2) ^ N) : ℚ) : ℝ) := by
    exact_mod_cast hb
  have hcast : ((((|zagierF 0 k| : ℚ) * ((1 : ℚ) / 2) ^ N) : ℚ) : ℝ) =
      (((|zagierF 0 k| : ℚ) : ℝ) * ((1 : ℝ) / 2) ^ N) := by
    norm_num [Rat.cast_mul, Rat.cast_pow, Rat.cast_div]
  rwa [hcast] at hb'

/-- `F(N,k) → 0` as `N → ∞` for every fixed `k` (real-valued) -/
lemma zagierF_tendsto_zero (k : ℕ) :
    Tendsto (fun N : ℕ => (zagierF N k : ℝ)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun N : ℕ => ((1 : ℝ) / 2) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hnorm : Tendsto (fun N : ℕ => ‖(zagierF N k : ℝ)‖) atTop (𝓝 0) := by
    have hc : Tendsto (fun N : ℕ => (((|zagierF 0 k| : ℚ) : ℝ) * ((1 : ℝ) / 2) ^ N)) atTop (𝓝 0) := by
      convert (hpow.const_mul (((|zagierF 0 k| : ℚ) : ℝ))) using 1
      ring_nf
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hc ?_ ?_
    · intro N; exact norm_nonneg _
    · intro N; exact zagierF_norm_pow_real N k
  exact (tendsto_iff_norm_sub_tendsto_zero (f := fun N : ℕ => (zagierF N k : ℝ)) (b := 0)).2
    (by simpa using hnorm)

/-- `Σ_{k<K} F(N,k) → 0` as `N → ∞` (finite sums of decaying terms) -/
lemma zagierF_finitesum_tendsto_zero (K : ℕ) :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range K, (zagierF N k : ℝ))) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (s := Finset.range K) (f := fun k N : ℕ => (zagierF N k : ℝ))
      (x := Filter.atTop) (a := fun _ : ℕ => 0) (by intro i hi; exact zagierF_tendsto_zero i)
  simpa using h

/-- `|Q(n,k)| ≤ 14·(k+1)²` (bound uniform in `n`) -/
lemma zagierQ_abs_le (n k : ℕ) : |zagierQ n k| ≤ 14 * ((k : ℚ) + 1) ^ 2 := by
  unfold zagierQ
  rw [abs_div]
  have hN0 : 0 ≤ 45 * (n : ℚ) ^ 2 + 63 * (n : ℚ) + 54 * (n : ℚ) * (k : ℚ) + 18 * (k : ℚ) ^ 2 +
      36 * (k : ℚ) := by positivity
  have hN : 0 < 45 * (n : ℚ) ^ 2 + 63 * (n : ℚ) + 54 * (n : ℚ) * (k : ℚ) + 18 * (k : ℚ) ^ 2 +
      36 * (k : ℚ) + 22 := by nlinarith
  have hD : 0 < 18 * (2 * (n : ℚ) + 1) * ((n : ℚ) + 2 * (k : ℚ) + 1) := by positivity
  rw [abs_of_pos hN, abs_of_pos hD]
  rw [div_le_iff₀ hD]
  have h2 : 0 ≤ 14 * ((k : ℚ) + 1) ^ 2 * (18 * (2 * (n : ℚ) + 1) * ((n : ℚ) + 2 * (k : ℚ) + 1)) -
      (45 * (n : ℚ) ^ 2 + 63 * (n : ℚ) + 54 * (n : ℚ) * (k : ℚ) + 18 * (k : ℚ) ^ 2 +
        36 * (k : ℚ) + 22) := by
    ring_nf
    positivity
  nlinarith

/-- `|G(n,k)| ≤ 14(k+1)²·|F(0,k)|·2⁻ⁿ` — decays geometrically in `n` -/
lemma zagierG_abs_pow (n k : ℕ) :
    |zagierG n k| ≤ 14 * ((k : ℚ) + 1) ^ 2 * |zagierF 0 k| * ((1 : ℚ) / 2) ^ n := by
  unfold zagierG
  calc
    |zagierF n k * zagierQ n k| = |zagierF n k| * |zagierQ n k| := abs_mul _ _
    _ ≤ (|zagierF 0 k| * ((1 : ℚ) / 2) ^ n) * (14 * ((k : ℚ) + 1) ^ 2) := by
          exact mul_le_mul (zagierF_abs_pow n k) (zagierQ_abs_le n k) (abs_nonneg _)
            (by positivity : 0 ≤ |zagierF 0 k| * ((1 : ℚ) / 2) ^ n)
    _ = 14 * ((k : ℚ) + 1) ^ 2 * |zagierF 0 k| * ((1 : ℚ) / 2) ^ n := by ring

/-- `G(·,k)` is summable in `n` for every fixed `k` -/
lemma summable_zagierG_fixed (k : ℕ) : Summable fun n : ℕ => (zagierG n k : ℝ) := by
  let C : ℚ := 14 * ((k : ℚ) + 1) ^ 2 * |zagierF 0 k|
  have hgeo : Summable fun n : ℕ => ((1 : ℝ) / 2) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine Summable.of_norm_bounded (g := fun n : ℕ => (C : ℝ) * ((1 : ℝ) / 2) ^ n) ?_ ?_
  · exact Summable.mul_left (C : ℝ) hgeo
  · intro n
    have hb := zagierG_abs_pow n k
    have hb' : ‖(zagierG n k : ℝ)‖ ≤ ((14 * ((k : ℚ) + 1) ^ 2 * |zagierF 0 k| * ((1 : ℚ) / 2) ^ n : ℚ) : ℝ) := by
      rw [Real.norm_eq_abs]
      rw [← Rat.cast_abs]
      exact_mod_cast hb
    have hcast : ((14 * ((k : ℚ) + 1) ^ 2 * |zagierF 0 k| * ((1 : ℚ) / 2) ^ n : ℚ) : ℝ) =
        (C : ℝ) * ((1 : ℝ) / 2) ^ n := by
      dsimp [C]
      norm_num [Rat.cast_mul, Rat.cast_pow, Rat.cast_div]
    rwa [hcast] at hb'

/-- the `n`-partial sums of `G(·,k)` tend to `Σ'ₙ G(n,k)` (per fixed `k`) -/
lemma tendsto_partial_zagierG (k : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (zagierG n k : ℝ))) atTop
      (𝓝 (∑' n : ℕ, (zagierG n k : ℝ))) := by
  exact (summable_zagierG_fixed k).hasSum.tendsto_sum_nat

/-! ## Analytic half (c): the `N → ∞` limit at fixed `K` -/

/-- the finite-rectangle telescoping in `range N`/`range K` form:
`Σ_{k<K}(F(N,k) − F(0,k)) = Σ_{n<N}(G(n,K) − G(n,0))` -/
lemma zagier_rect' (N K : ℕ) :
    (∑ k ∈ Finset.range K, (zagierF N k : ℚ)) - (∑ k ∈ Finset.range K, (zagierF 0 k : ℚ))
      = (∑ n ∈ Finset.range N, (zagierG n K : ℚ)) - (∑ n ∈ Finset.range N, (zagierG n 0 : ℚ)) := by
  calc
    (∑ k ∈ Finset.range K, (zagierF N k : ℚ)) - (∑ k ∈ Finset.range K, (zagierF 0 k : ℚ))
        = ∑ k ∈ Finset.range K, (zagierF N k - zagierF 0 k : ℚ) := by rw [← Finset.sum_sub_distrib]
    _ = ∑ k ∈ Finset.range K, ∑ n ∈ Finset.range N, (zagierF (n + 1) k - zagierF n k) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [← Finset.sum_range_sub (fun n => zagierF n k) N]
    _ = ∑ k ∈ Finset.range K, ∑ n ∈ Finset.range N, (zagierG n (k + 1) - zagierG n k) := by
            apply Finset.sum_congr rfl
            intro k hk
            apply Finset.sum_congr rfl
            intro n hn
            exact zagier_wz n k
    _ = ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range K, (zagierG n (k + 1) - zagierG n k) := by
            rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.range N, (zagierG n K - zagierG n 0) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact Finset.sum_range_sub (fun k => zagierG n k) K
    _ = (∑ n ∈ Finset.range N, (zagierG n K : ℚ)) - (∑ n ∈ Finset.range N, (zagierG n 0 : ℚ)) := by
            rw [Finset.sum_sub_distrib]

/-- the real-valued `range`-form of the rectangle identity -/
lemma zagier_rect_real (N K : ℕ) :
    (∑ k ∈ Finset.range K, (zagierF N k : ℝ)) - (∑ k ∈ Finset.range K, (zagierF 0 k : ℝ))
      = (∑ n ∈ Finset.range N, (zagierG n K : ℝ)) - (∑ n ∈ Finset.range N, (zagierG n 0 : ℝ)) := by
  simpa [Rat.cast_sum] using (congrArg (fun q : ℚ => (q : ℝ)) (zagier_rect' N K))

/-- **the `N → ∞` limit at fixed `K`**: for every `K`,
`Σ_{k<K+1} F(0,k) = Σ'ₙ G(n,0) − Σ'ₙ G(n,K+1)` -/
theorem zagier_rect_limit_N (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), (zagierF 0 k : ℝ)) =
      (∑' n : ℕ, (zagierG n 0 : ℝ)) - (∑' n : ℕ, (zagierG n (K + 1) : ℝ)) := by
  let s : ℕ → ℝ := fun N => ∑ k ∈ Finset.range (K + 1), (zagierF N k : ℝ)
  let b : ℝ := ∑ k ∈ Finset.range (K + 1), (zagierF 0 k : ℝ)
  let c : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, (zagierG n (K + 1) : ℝ)
  let d : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, (zagierG n 0 : ℝ)
  -- (1) `N ↦ s N − c N + d N` is the constant `b` (rectangular telescoping):
  have hpt : (fun N : ℕ => s N - c N + d N) = fun _ : ℕ => b := by
    funext N
    have hr := zagier_rect_real N (K + 1)
    dsimp [s, b, c, d] at hr ⊢
    linarith
  have hconst : Tendsto (fun N : ℕ => s N - c N + d N) atTop (𝓝 b) := by
    rw [hpt]
    exact tendsto_const_nhds
  -- (2) the three summands converge:
  have hs : Tendsto s atTop (𝓝 0) := by
    dsimp [s]
    exact zagierF_finitesum_tendsto_zero (K + 1)
  have hc : Tendsto c atTop (𝓝 (∑' n : ℕ, (zagierG n (K + 1) : ℝ))) := by
    dsimp [c]
    exact tendsto_partial_zagierG (K + 1)
  have hd : Tendsto d atTop (𝓝 (∑' n : ℕ, (zagierG n 0 : ℝ))) := by
    dsimp [d]
    exact tendsto_partial_zagierG 0
  -- (3) hence the whole sequence tends to `0 − Σ'G(K+1) + Σ'G(0)`:
  have hlim : Tendsto (fun N : ℕ => s N - c N + d N) atTop
      (𝓝 (0 - (∑' n : ℕ, (zagierG n (K + 1) : ℝ)) + (∑' n : ℕ, (zagierG n 0 : ℝ)))) := by
    exact (hs.sub hc).add hd
  -- (4) uniqueness of limits:
  have hEq := tendsto_nhds_unique hconst hlim
  dsimp [b] at hEq
  calc
    (∑ k ∈ Finset.range (K + 1), (zagierF 0 k : ℝ))
        = 0 - (∑' n : ℕ, (zagierG n (K + 1) : ℝ)) + (∑' n : ℕ, (zagierG n 0 : ℝ)) := hEq
    _ = (∑' n : ℕ, (zagierG n 0 : ℝ)) - (∑' n : ℕ, (zagierG n (K + 1) : ℝ)) := by ring

/-! ## Analytic half (d): the `K → ∞` limit

From `zagierG_abs_pow` — `|G(n,k)| ≤ 14(k+1)²·|F(0,k)|·2⁻ⁿ` — the total
`n`-mass of `G(·,k)` is bounded by `28(k+1)²·|F(0,k)|`, which decays like
`O(k⁻¹)` by the exact value `|F(0,k)| = 81(2k+1)/((3k+1)²(3k+2)²)`
(`zagierF_zero_abs`).  Passing the fixed-`K` limit
`zagier_rect_limit_N` through `K → ∞` then yields
`zagier_wz_infinite`. -/

/-- `|F(0,k)| = 81(2k+1)/((3k+1)²(3k+2)²)` (positive exact value) -/
lemma zagierF_zero_abs (k : ℕ) :
    |zagierF 0 k| = 81 * (2 * (k : ℚ) + 1) / ((3 * (k : ℚ) + 1) ^ 2 * (3 * (k : ℚ) + 2) ^ 2) := by
  rw [zagierF_zero]
  have hnum : 0 ≤ 81 * (2 * (k : ℚ) + 1) := by positivity
  have hden : 0 < (3 * (k : ℚ) + 1) ^ 2 * (3 * (k : ℚ) + 2) ^ 2 := by positivity
  exact abs_of_nonneg (div_nonneg hnum (le_of_lt hden))

/-- `(k+1)²·|F(0,k)| ≤ 30/(k+1)` — polynomial decay of the `k = 0`-row -/
lemma zagierF_zero_sq_le (k : ℕ) :
    ((k : ℚ) + 1) ^ 2 * |zagierF 0 k| ≤ 30 / ((k : ℚ) + 1) := by
  rw [zagierF_zero_abs]
  have hB : 0 < (3 * (k : ℚ) + 1) ^ 2 * (3 * (k : ℚ) + 2) ^ 2 := by positivity
  have hC : 0 < (k : ℚ) + 1 := by positivity
  rw [le_div_iff₀ hC]
  rw [show ((k : ℚ) + 1) ^ 2 * (81 * (2 * (k : ℚ) + 1) / ((3 * (k : ℚ) + 1) ^ 2 * (3 * (k : ℚ) + 2) ^ 2)) *
        ((k : ℚ) + 1) =
      ((k : ℚ) + 1) ^ 3 * (81 * (2 * (k : ℚ) + 1)) / ((3 * (k : ℚ) + 1) ^ 2 * (3 * (k : ℚ) + 2) ^ 2) by ring]
  rw [div_le_iff₀ hB]
  have h2 : 0 ≤ 30 * ((3 * (k : ℚ) + 1) ^ 2 * (3 * (k : ℚ) + 2) ^ 2) -
      ((k : ℚ) + 1) ^ 3 * (81 * (2 * (k : ℚ) + 1)) := by
    ring_nf
    positivity
  nlinarith

/-- real-norm form of `|G(n,k)| ≤ 14(k+1)²·|F(0,k)|·2⁻ⁿ` -/
lemma zagierG_norm_pow_real (n k : ℕ) :
    ‖(zagierG n k : ℝ)‖ ≤
      (((14 * ((k : ℚ) + 1) ^ 2 * |zagierF 0 k| * ((1 : ℚ) / 2) ^ n : ℚ) : ℚ) : ℝ) := by
  have hb := zagierG_abs_pow n k
  rw [Real.norm_eq_abs]
  rw [← Rat.cast_abs]
  exact_mod_cast hb

/-- `Σ'ₙ G(n,k)` is dominated by `28(k+1)²·|F(0,k)|` (its norm): -/
lemma tsum_zagierG_norm_bound (k : ℕ) :
    ‖(∑' n : ℕ, (zagierG n k : ℝ))‖ ≤
      (((28 * ((k : ℚ) + 1) ^ 2 * |zagierF 0 k| : ℚ) : ℚ) : ℝ) := by
  let c : ℚ := 14 * ((k : ℚ) + 1) ^ 2 * |zagierF 0 k|
  -- Σ_n ‖G(n,k)‖ is summable and ≤ c·Σ(1/2)^n = 2c:
  have hpt (n : ℕ) : ‖(zagierG n k : ℝ)‖ ≤ (c : ℝ) * ((1 : ℝ) / 2) ^ n := by
    have hb' := zagierG_norm_pow_real n k
    have hcast : (((14 * ((k : ℚ) + 1) ^ 2 * |zagierF 0 k| * ((1 : ℚ) / 2) ^ n : ℚ) : ℚ) : ℝ) =
        (c : ℝ) * ((1 : ℝ) / 2) ^ n := by
      dsimp [c]
      norm_num [Rat.cast_mul, Rat.cast_pow, Rat.cast_div]
    rwa [hcast] at hb'
  have hgeo : Summable fun n : ℕ => ((1 : ℝ) / 2) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hbnd : Summable fun n : ℕ => (c : ℝ) * ((1 : ℝ) / 2) ^ n := Summable.mul_left (c : ℝ) hgeo
  have hsum_norm : Summable fun n : ℕ => ‖(zagierG n k : ℝ)‖ := by
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpt hbnd
  have h1 := norm_tsum_le_tsum_norm (f := fun n : ℕ => (zagierG n k : ℝ)) hsum_norm
  -- tsum of the bound:
  have htsum : (∑' n : ℕ, (c : ℝ) * ((1 : ℝ) / 2) ^ n) = ((c : ℝ) * 2) := by
    rw [tsum_mul_left]
    have hg := tsum_geometric_of_norm_lt_one (ξ := (1 : ℝ) / 2) (by norm_num)
    rw [hg]
    norm_num
  calc
    ‖(∑' n : ℕ, (zagierG n k : ℝ))‖ ≤ ∑' n : ℕ, ‖(zagierG n k : ℝ)‖ := h1
    _ ≤ ∑' n : ℕ, (c : ℝ) * ((1 : ℝ) / 2) ^ n := by
          exact Summable.tsum_le_tsum hpt hsum_norm hbnd
    _ = (c : ℝ) * 2 := htsum
    _ = (((28 * ((k : ℚ) + 1) ^ 2 * |zagierF 0 k| : ℚ) : ℚ) : ℝ) := by
          dsimp [c]
          norm_num [Rat.cast_mul]
          ring

/-- real bound: `‖(F(0,M):ℝ)‖·(M+1)² ≤ 30/(M+1)` (decay of the `k = 0`-row) -/
lemma zagierF_zero_sq_real (M : ℕ) :
    ((M : ℝ) + 1) ^ 2 * ‖(zagierF 0 M : ℝ)‖ ≤ (30 : ℝ) / ((M : ℝ) + 1) := by
  have hs := zagierF_zero_sq_le M
  have hs' : ((((M : ℚ) + 1) ^ 2 * |zagierF 0 M| : ℚ) : ℝ) ≤
      (((30 : ℚ) / ((M : ℚ) + 1)) : ℝ) := by
    exact_mod_cast hs
  have hL : ((((M : ℚ) + 1) ^ 2 * |zagierF 0 M| : ℚ) : ℝ) =
      ((M : ℝ) + 1) ^ 2 * ‖(zagierF 0 M : ℝ)‖ := by
    rw [Real.norm_eq_abs]
    rw [← Rat.cast_abs]
    norm_num [Rat.cast_mul, Rat.cast_pow]
  have hR : (((30 : ℚ) / ((M : ℚ) + 1)) : ℝ) = (30 : ℝ) / ((M : ℝ) + 1) := by
    norm_num [Rat.cast_div]
  rwa [hL, hR] at hs'

/-- real bound: `‖Σ'ₙG(n,M)‖ ≤ 28·(M+1)²·‖F(0,M)‖` -/
lemma tsum_zagierG_norm_real (M : ℕ) :
    ‖(∑' n : ℕ, (zagierG n M : ℝ))‖ ≤ (28 : ℝ) * ((M : ℝ) + 1) ^ 2 * ‖(zagierF 0 M : ℝ)‖ := by
  have hb := tsum_zagierG_norm_bound M
  have hcast : (((28 * ((M : ℚ) + 1) ^ 2 * |zagierF 0 M|) : ℚ) : ℝ) =
      (28 : ℝ) * ((M : ℝ) + 1) ^ 2 * ‖(zagierF 0 M : ℝ)‖ := by
    rw [Real.norm_eq_abs]
    rw [← Rat.cast_abs]
    norm_num [Rat.cast_mul, Rat.cast_pow]
  rwa [hcast] at hb

/-- `Σ'ₙ G(n,M) → 0` as `M → ∞` (squeeze `0 ≤ ‖Σ'ₙG(n,M)‖ ≤ 840/(M+1)`) -/
lemma tsum_zagierG_M_tendsto_zero :
    Tendsto (fun M : ℕ => (∑' n : ℕ, (zagierG n M : ℝ))) atTop (𝓝 0) := by
  have hbM (M : ℕ) : ‖(∑' n : ℕ, (zagierG n M : ℝ))‖ ≤ (840 : ℝ) / ((M : ℝ) + 1) := by
    have h1 := tsum_zagierG_norm_real M
    have h2 := zagierF_zero_sq_real M
    have h3' : (28 : ℝ) * (((M : ℝ) + 1) ^ 2 * ‖(zagierF 0 M : ℝ)‖) ≤
        (28 : ℝ) * ((30 : ℝ) / ((M : ℝ) + 1)) := by
      exact mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 28)
    calc
      ‖(∑' n : ℕ, (zagierG n M : ℝ))‖ ≤ (28 : ℝ) * ((M : ℝ) + 1) ^ 2 * ‖(zagierF 0 M : ℝ)‖ := h1
      _ = (28 : ℝ) * (((M : ℝ) + 1) ^ 2 * ‖(zagierF 0 M : ℝ)‖) := by ring
      _ ≤ (28 : ℝ) * ((30 : ℝ) / ((M : ℝ) + 1)) := h3'
      _ = (840 : ℝ) / ((M : ℝ) + 1) := by
            field_simp [show (M : ℝ) + 1 ≠ 0 by positivity]
            ring
  have ht : Tendsto (fun M : ℕ => ((840 : ℝ) / ((M : ℝ) + 1))) atTop (𝓝 0) := by
    have hbase : Tendsto (fun M : ℕ => ((1 : ℝ) / ((M : ℝ) + 1))) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    convert hbase.const_mul (840 : ℝ) using 1
    · ext M
      ring
    · ring
  have hnorm : Tendsto (fun M : ℕ => ‖(∑' n : ℕ, (zagierG n M : ℝ))‖) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) ht ?_ ?_
    · intro M
      exact norm_nonneg _
    · intro M
      exact hbM M
  exact (tendsto_iff_norm_sub_tendsto_zero (f := fun M : ℕ => (∑' n : ℕ, (zagierG n M : ℝ))) (b := 0)).2
    (by simpa using hnorm)

/-- the `M`-indexed version of the fixed-`K` limit:
`Σ_{k<M}F(0,k) = Σ'ₙG(n,0) − Σ'ₙG(n,M)` for every `M` -/
lemma zagier_rect_limit_M (M : ℕ) :
    (∑ k ∈ Finset.range M, (zagierF 0 k : ℝ)) =
      (∑' n : ℕ, (zagierG n 0 : ℝ)) - (∑' n : ℕ, (zagierG n M : ℝ)) := by
  by_cases hM : 1 ≤ M
  · have h := zagier_rect_limit_N (M - 1)
    have hsub : M - 1 + 1 = M := Nat.sub_add_cancel hM
    simpa [hsub] using h
  · have hM0 : M = 0 := by omega
    subst M
    simp

/-! ## `zagier_wz_infinite`: the infinite telescoping of the WZ pair

Passing `zagier_rect_limit_M` through `M → ∞`: the left side tends to
`Σ'ₖF(0,k)` (partial sums of the summable `F(0,·)`), the right side tends
to `Σ'ₙG(n,0) − 0` by `tsum_zagierG_M_tendsto_zero`.  Hence
`Σ'ₙG(n,0) = Σ'ₖF(0,k)`, which is `zagier_wz_infinite`. -/

/-- **the analytic identity**: `ΣₙG(n,0) = ΣₖF(0,k)` (WZ infinite telescoping) -/
theorem zagier_wz_infinite_thm : zagier_wz_infinite := by
  unfold zagier_wz_infinite
  -- partial sums of F(0,·) tend to Σ'ₖF(0,k):
  have hFpart : Tendsto (fun M : ℕ => (∑ k ∈ Finset.range M, (zagierF 0 k : ℝ))) atTop
      (𝓝 (∑' k : ℕ, (zagierF 0 k : ℝ))) := by
    exact summable_zagierF_zero.hasSum.tendsto_sum_nat
  -- the M-dependent function (Σ'G(0) − Σ'G(M)) tends to Σ'G(0) − 0:
  have hGlim : Tendsto (fun M : ℕ => (∑' n : ℕ, (zagierG n 0 : ℝ)) - (∑' n : ℕ, (zagierG n M : ℝ))) atTop
      (𝓝 ((∑' n : ℕ, (zagierG n 0 : ℝ)) - 0)) := by
    exact (tendsto_const_nhds.sub tsum_zagierG_M_tendsto_zero)
  -- the two functions agree pointwise (rect_limit_M):
  have hpt : (fun M : ℕ => (∑ k ∈ Finset.range M, (zagierF 0 k : ℝ))) =ᶠ[atTop]
      (fun M : ℕ => (∑' n : ℕ, (zagierG n 0 : ℝ)) - (∑' n : ℕ, (zagierG n M : ℝ))) := by
    filter_upwards with M
    exact zagier_rect_limit_M M
  have hGlim' : Tendsto (fun M : ℕ => (∑' n : ℕ, (zagierG n 0 : ℝ)) - (∑' n : ℕ, (zagierG n M : ℝ))) atTop
      (𝓝 (∑' k : ℕ, (zagierF 0 k : ℝ))) := hFpart.congr' hpt
  have hEq := tendsto_nhds_unique hGlim hGlim'
  -- hEq : Σ'G(0) − 0 = Σ'F(0)
  simpa using hEq

/-! ## Sub-leaf 4 is CLOSED: Zagier's evaluation of `L(2,χ₋₃)`

The Markov–WZ certificate (`zagier_wz`, `zagier_rect'`) together with the
analytic limits (`zagier_rect_limit_N`, `tsum_zagierG_M_tendsto_zero`)
produce `zagier_wz_infinite_thm`, i.e. `ΣₙG(n,0) = ΣₖF(0,k)`, and — by the
termwise identifications — Zagier's hypergeometric-type evaluation of
`L(2,χ₋₃)`, i.e. `theoremA_leaf_hypergeom` (`zagierL2chi_identity` below)
and its integral-form corollary (`zagierL2chi_leaf_main`).  These two
theorems used to be the `sorry` placeholders at the end of
`Submission.CDT.L2chi3Zagier`; they are declared here because that module
cannot import this one (import cycle). -/

/-- **Zagier's hypergeometric-type evaluation of `L(2,χ₋₃)`** (paper display
after Thm. `mainA`): `Σₙ tₙ = 27·L(2,χ₋₃)`, i.e. `theoremA_leaf_hypergeom`.
Obtained from the Markov–WZ certificate by the analytic
`N → ∞`/`K → ∞` limits of the rectangle identity. -/
theorem zagierL2chi_identity : theoremA_leaf_hypergeom :=
  theoremA_leaf_hypergeom_of_wz zagier_wz_infinite_thm

/-- the main summation lemma in integral (box) form:
`L(2,χ₋₃) = (1/27)·Σ'ₙ zagierL2chiIntegralTerm n` — follows from
`zagierL2chi_identity` by the termwise equality
`(tₙ:ℝ) = zagierL2chiIntegralTerm n` (`zagierL2chiTerm_eq_integralTerm`,
plus the `n = 0` case where both sides vanish). -/
theorem zagierL2chi_leaf_main :
    L2chi3Real = (1 / 27 : ℝ) * ∑' n : ℕ, zagierL2chiIntegralTerm n := by
  have hhyp := zagierL2chi_identity
  unfold theoremA_leaf_hypergeom zagierL2chiSeries at hhyp
  have hsum : (∑' n : ℕ, (zagierL2chiTerm n : ℝ)) = ∑' n : ℕ, zagierL2chiIntegralTerm n := by
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp [zagierL2chiTerm, zagierL2chiIntegralTerm]
    · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      exact zagierL2chiTerm_eq_integralTerm n hn1
  calc
    L2chi3Real = (1 / 27 : ℝ) * (27 * L2chi3Real) := by field_simp
    _ = (1 / 27 : ℝ) * (∑' n : ℕ, (zagierL2chiTerm n : ℝ)) := by rw [← hhyp]
    _ = (1 / 27 : ℝ) * (∑' n : ℕ, zagierL2chiIntegralTerm n) := by rw [hsum]
