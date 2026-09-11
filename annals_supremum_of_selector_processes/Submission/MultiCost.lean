import Submission.Multi
import Submission.MultiMass

/-!
# Child task: multiset-cost trimming lemmas for Theorem 1.3's discretization.
Context (see Submission/The13.lean): a finite cell type `C`, masses `μ : C → ℝ ≥ 0`,
a cover `Cov0 : Finset (C → ℕ)` with  `Multi.mTotalCost (Multi.eN N) μ Cov0 ≤ (2:ℝ)⁻¹`.
We trim each multiset `G` coordinatewise:
  `trim G c := if (N : ℝ) * μ c ≤ (G c : ℝ) then G c else 0`
(small coordinates are zeroed; coordinates with μc = 0 are kept).
`Multi.wCost (Multi.eN N) μ G = ∏ c, (Multi.eN N * μ c) ^ (G c) / (G c)!`.
`Multi.eN N = Real.exp 1 * (N : ℝ)`.

PROVE ALL lemmas below (statements fixed; helpers allowed; no sorries).  Proof routes:
- `ee_one_le`: `Real.exp_lt_exp` (strictly increasing) applied to `0 < 1`; `Real.exp_zero` = 1.
- `factorial_le_self_pow (k)`: induction on k; `Nat.factorial_succ`, `pow_succ`;
  `(k+1)! = k!·(k+1)`; combine `k! ≤ k^k` with `k^k ≤ (k+1)^k` (`pow_le_pow_left₀`
  since 0 ≤ (k:ℝ) ≤ (k+1:ℝ)) and multiply by `(k+1) ≥ 0`.  Base k=0: `norm_num`.
- `one_le_pow_div_factorial`: induction on k.  k=0: `simp`.  k→k+1 with
  `(k+1 : ℝ) < a`: `a^(k+1)/(k+1)! = (a^k/k!) * (a/(k+1))` (rewrite `pow_succ`,
  `Nat.factorial_succ`, field_simp), both factors ≥ 1 (IH with `k < k+1 < a`;
  `a/(k+1) ≥ 1` since `a ≥ k+1`), then `one_le_mul`.
- `wCost_trim_le`: per-coordinate: coordinate unchanged gives `≤` by `le_rfl`;
  coordinate zeroed has `G c ≥ 1` and `(G c : ℝ) < (N:ℝ)*μc` so
  `(G c : ℝ) < Multi.eN N * μ c` (since `Multi.eN N = Real.exp 1 * N ≥ N` by `ee_one_le`,
  and `(N:ℝ)*μc ≥ 0`), so `one_le_pow_div_factorial` gives
  `1 ≤ (eN*μc)^(Gc)/(Gc)!`; multiply all coordinate inequalities
  (`Finset.prod_le_prod` over `univ`, all factors ≥ 0).
- `sum_le_sum_image`: induction on the finset `s` (`Finset.induction_on`), using
  `s.image`-insert behaviour (by_cases on whether `f a` already in image of `A`),
  nonnegativity of `g`.
- `total_cost_trim_le`: `sum_le_sum_image` + `Finset.sum_le_sum` of `wCost_trim_le`.
- `total_cost_filter_le`: `Finset.sum_le_sum_of_subset_of_nonneg` (or
  `Finset.sum_le_sum` with per-term ≤ since filter ⊆ set).
All in `namespace Submission.MultiCost`; import as needed.  Typeclass params:
`[Fintype X] [DecidableEq X]` on the index type where sums range.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators NNReal

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace MultiCost

/-- e = exp 1 ≥ 1 -/
lemma ee_one_le : (1 : ℝ) ≤ Submission.Multi.ee := by
  unfold Submission.Multi.ee
  exact Real.one_le_exp (by norm_num)

/-- eN N ≥ 0 -/
lemma eN_nonneg (N : ℕ) : 0 ≤ Submission.Multi.eN N := by
  unfold Submission.Multi.eN
  exact mul_nonneg (by unfold Submission.Multi.ee; exact (Real.exp_pos 1).le)
    (by positivity : 0 ≤ (N : ℝ))

/-- (Nat.factorial k : ℝ) ≤ (k : ℝ)^k -/
lemma factorial_le_self_pow (k : ℕ) : (Nat.factorial k : ℝ) ≤ (k : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have h1 : (Nat.factorial (k + 1) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * (k : ℝ) ^ k := by
        calc
          (Nat.factorial (k + 1) : ℝ) = ((k + 1 : ℕ) : ℝ) * (Nat.factorial k : ℝ) := by
            rw [Nat.factorial_succ, Nat.cast_mul]
          _ ≤ ((k + 1 : ℕ) : ℝ) * (k : ℝ) ^ k := by
            exact mul_le_mul_of_nonneg_left ih (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))
      have h2 : ((k + 1 : ℕ) : ℝ) * (k : ℝ) ^ k ≤ ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by
        calc
          ((k + 1 : ℕ) : ℝ) * (k : ℝ) ^ k ≤ ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ k := by
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (k : ℝ))
                (by exact_mod_cast Nat.le_succ k) k)
              (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))
          _ = ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by rw [pow_succ']
      exact le_trans h1 h2

/-- if 0 ≤ a and k < a then 1 ≤ a^k / k! -/
lemma one_le_pow_div_factorial (a : ℝ) (k : ℕ) (ha0 : 0 ≤ a) (hk : (k : ℝ) < a) :
    (1 : ℝ) ≤ a ^ k / (Nat.factorial k : ℝ) := by
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      have hklt : (k : ℝ) < a := lt_trans (by exact_mod_cast Nat.lt_succ_self k) hk
      have ih1 : (1 : ℝ) ≤ a ^ k / (Nat.factorial k : ℝ) := ih hklt
      have hfactpos : (0 : ℝ) < (Nat.factorial k : ℝ) := by
        exact_mod_cast Nat.factorial_pos k
      have hfact_le : (Nat.factorial k : ℝ) ≤ a ^ k := (one_le_div hfactpos).mp ih1
      have hstep1 : ((k + 1 : ℕ) : ℝ) * (Nat.factorial k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * a ^ k := by
        exact mul_le_mul_of_nonneg_left hfact_le (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))
      have hstep2 : ((k + 1 : ℕ) : ℝ) * a ^ k ≤ a * a ^ k := by
        exact mul_le_mul_of_nonneg_right (le_of_lt hk) (pow_nonneg ha0 k)
      have hcast : (Nat.factorial (k + 1) : ℝ) = ((k + 1 : ℕ) : ℝ) * (Nat.factorial k : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul]
      have htotal : (Nat.factorial (k + 1) : ℝ) ≤ a ^ (k + 1) := by
        calc
          (Nat.factorial (k + 1) : ℝ) = ((k + 1 : ℕ) : ℝ) * (Nat.factorial k : ℝ) := hcast
          _ ≤ ((k + 1 : ℕ) : ℝ) * a ^ k := hstep1
          _ ≤ a * a ^ k := hstep2
          _ = a ^ (k + 1) := by rw [pow_succ']
      have hfactpos2 : (0 : ℝ) < (Nat.factorial (k + 1) : ℝ) := by
        exact_mod_cast Nat.factorial_pos (k + 1)
      exact (one_le_div hfactpos2).mpr htotal

/-- each wCost term is nonnegative -/
lemma wCost_nonneg {X : Type*} [Fintype X] (c : ℝ) (μ : X → ℝ) (hc0 : 0 ≤ c)
    (hμ0 : ∀ x : X, 0 ≤ μ x) (G : X → ℕ) :
    0 ≤ Submission.Multi.wCost c μ G := by
  unfold Submission.Multi.wCost
  exact Finset.prod_nonneg (by
    intro x hx
    have h1 : 0 ≤ c * μ x := mul_nonneg hc0 (hμ0 x)
    have hnum : 0 ≤ (c * μ x) ^ G x := pow_nonneg h1 (G x)
    have hden : (0 : ℝ) < (Nat.factorial (G x) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (G x)
    exact div_nonneg hnum hden.le)

/-- per-coordinate trimming never increases the weighted cost -/
lemma wCost_trim_le {X : Type*} [Fintype X] (N : ℕ) (μ : X → ℝ) (G : X → ℕ)
    (hμ0 : ∀ x : X, 0 ≤ μ x) :
    Submission.Multi.wCost (Submission.Multi.eN N) μ
        (fun x : X => if (N : ℝ) * μ x ≤ (G x : ℝ) then G x else 0)
      ≤ Submission.Multi.wCost (Submission.Multi.eN N) μ G := by
  classical
  have he0 : 0 ≤ Submission.Multi.eN N := eN_nonneg N
  have hNle : (N : ℝ) ≤ Submission.Multi.eN N := by
    unfold Submission.Multi.eN
    simpa using (mul_le_mul_of_nonneg_right ee_one_le (by positivity : (0 : ℝ) ≤ (N : ℝ)))
  have hcoord : ∀ x : X,
      (Submission.Multi.eN N * μ x) ^
          (if (N : ℝ) * μ x ≤ (G x : ℝ) then G x else 0) /
        (Nat.factorial (if (N : ℝ) * μ x ≤ (G x : ℝ) then G x else 0) : ℝ)
      ≤ (Submission.Multi.eN N * μ x) ^ (G x) / (Nat.factorial (G x) : ℝ) := by
    intro x
    by_cases hx : (N : ℝ) * μ x ≤ (G x : ℝ)
    · rw [if_pos hx]
    · rw [if_neg hx]
      have hlt : (G x : ℝ) < (N : ℝ) * μ x := lt_of_not_ge hx
      have hle : (N : ℝ) * μ x ≤ Submission.Multi.eN N * μ x := by
        exact mul_le_mul_of_nonneg_right hNle (hμ0 x)
      have hlt' : (G x : ℝ) < Submission.Multi.eN N * μ x := lt_of_lt_of_le hlt hle
      have hnonneg : 0 ≤ Submission.Multi.eN N * μ x := mul_nonneg he0 (hμ0 x)
      simpa using (one_le_pow_div_factorial (Submission.Multi.eN N * μ x) (G x) hnonneg hlt')
  unfold Submission.Multi.wCost
  apply Finset.prod_le_prod
  · intro x hxuniv
    have hnonneg : 0 ≤ Submission.Multi.eN N * μ x := mul_nonneg he0 (hμ0 x)
    have hnum : 0 ≤ (Submission.Multi.eN N * μ x) ^
        (if (N : ℝ) * μ x ≤ (G x : ℝ) then G x else 0) := pow_nonneg hnonneg _
    have hden : (0 : ℝ) < (Nat.factorial
        (if (N : ℝ) * μ x ≤ (G x : ℝ) then G x else 0) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    exact div_nonneg hnum hden.le
  · intro x hxuniv
    exact hcoord x

/-- sum over the image is at most the sum over the domain (nonnegative weights) -/
lemma sum_le_sum_image {X Y : Type*} [DecidableEq Y] (s : Finset X) (f : X → Y) (g : Y → ℝ)
    (hg : ∀ y ∈ s.image f, 0 ≤ g y) :
    (∑ y ∈ s.image f, g y) ≤ ∑ x ∈ s, g (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a A haA ih =>
      rw [Finset.image_insert]
      rw [Finset.sum_insert haA]
      have ih' : (∑ y ∈ A.image f, g y) ≤ ∑ x ∈ A, g (f x) := ih (by
        intro y hy
        exact hg y (by
          rcases (Finset.mem_image.mp hy) with ⟨x, hxA, hxy⟩
          exact Finset.mem_image.mpr ⟨x, Finset.mem_insert_of_mem hxA, hxy⟩))
      have hga : 0 ≤ g (f a) := hg (f a) (Finset.mem_image.mpr ⟨a, Finset.mem_insert_self a A, rfl⟩)
      by_cases hmem : f a ∈ A.image f
      · rw [Finset.insert_eq_of_mem hmem]
        rw [add_comm]
        exact le_trans ih' (le_add_of_nonneg_right hga)
      · rw [Finset.sum_insert hmem]
        exact add_le_add_right ih' (g (f a))

/-- trimming the whole cover: total cost of the image cover ≤ total cost of the original -/
lemma total_cost_trim_le {X : Type*} [Fintype X] (N : ℕ) (μ : X → ℝ)
    (hμ0 : ∀ x : X, 0 ≤ μ x) (Cov0 : Finset (X → ℕ)) :
    Submission.Multi.mTotalCost (Submission.Multi.eN N) μ
        (Cov0.image (fun G : X → ℕ => fun x : X =>
          if (N : ℝ) * μ x ≤ (G x : ℝ) then G x else 0))
      ≤ Submission.Multi.mTotalCost (Submission.Multi.eN N) μ Cov0 := by
  classical
  let trimFn : (X → ℕ) → (X → ℕ) := fun G x =>
    if (N : ℝ) * μ x ≤ (G x : ℝ) then G x else 0
  unfold Submission.Multi.mTotalCost
  calc
    (∑ G ∈ Cov0.image trimFn, Submission.Multi.wCost (Submission.Multi.eN N) μ G)
        ≤ ∑ G ∈ Cov0, Submission.Multi.wCost (Submission.Multi.eN N) μ (trimFn G) := by
            exact sum_le_sum_image Cov0 trimFn
              (fun G => Submission.Multi.wCost (Submission.Multi.eN N) μ G)
              (by intro y hy; exact wCost_nonneg (Submission.Multi.eN N) μ (eN_nonneg N) hμ0 y)
    _ ≤ ∑ G ∈ Cov0, Submission.Multi.wCost (Submission.Multi.eN N) μ G := by
            exact Finset.sum_le_sum (by
              intro G hG
              exact wCost_trim_le N μ G hμ0)

/-- filtering a cover can only lower its total cost -/
lemma total_cost_filter_le {X : Type*} [Fintype X] (c : ℝ) (μ : X → ℝ)
    (hc0 : 0 ≤ c) (hμ0 : ∀ x : X, 0 ≤ μ x) (s : Finset (X → ℕ)) (p : (X → ℕ) → Prop) :
    Submission.Multi.mTotalCost c μ (s.filter p) ≤ Submission.Multi.mTotalCost c μ s := by
  classical
  unfold Submission.Multi.mTotalCost
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset p s) (by
    intro G hG hnot
    exact wCost_nonneg c μ hc0 hμ0 G)

end MultiCost
end Submission
