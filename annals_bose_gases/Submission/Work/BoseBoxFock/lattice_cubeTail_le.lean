import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Submission.Work.BoseBoxFock.kinFT_lattice_tail_sq_lt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.lattice_cubeTail_le`

The **cube tail of a summable nonnegative family on the lattice `ℤ³`**:

    ∀ ε > 0, ∃ N, ∀ N' ≥ N,  Σ'_{n : ∃ i, N' < |n i|} g n ≤ ε .

The index set `{n : Fin 3 → ℤ | ∃ i, N' < |n i|}` is the complement, in `ℤ³`, of the finite cube
`{n | ∀ i, |n i| ≤ N'}`.  So the statement says exactly that *the sums of a summable nonnegative
family over the complements of finite sets are arbitrarily small*, a fact whose proof is purely
order-theoretic on the net of finite subsets of `ℤ³`.

## Proof

`HasSum` unfolds to `Tendsto (fun s : Finset (Fin 3 → ℤ) ↦ ∑ n ∈ s, g n) atTop (𝓝 (∑' n, g n))`
for the (directed) filter `atTop` of finite subsets ordered by inclusion, so some finite `F₀`
satisfies `dist (∑ n ∈ F₀, g n) (∑' n, g n) < ε`.  Writing
`∑' n, g n = ∑ n ∈ F₀, g n + ∑' b : ↑(F₀ᶜ), g b` (`Summable.sum_add_tsum_compl`, the latter series
being the `tsum` over the subtype `↑(F₀ᶜ)`, `tsum_subtype`) shows that the tail over the *set*
`F₀ᶜ` is already `< ε`.

Choose `N := max_{n ∈ F₀} max_i |n i|`.  For `N' ≥ N` every `n ∈ F₀` fails the truncation
predicate `∃ i, N' < |n i|` (each coordinate of `n` is bounded by `N ≤ N'`), whence the truncated
integrand is pointwise dominated by the indicator of `F₀ᶜ`:
`(if ∃ i, N' < |n i| then g n else 0) ≤ 1_{F₀ᶜ} n · g n`.  Both truncated families are summable
(the dominating one because of `Summable.indicator`), so `Summable.tsum_le_tsum` compares the sums
and the bound `≤ ε` follows.  No monotonicity in `N'` is needed: the estimate holds for *every*
`N' ≥ N` simultaneously.

The result is the cube-index companion of the workspace's
`Work.BoseBoxFock.tail_le_of_summable` (truncation by the momentum radius `‖k_n‖ ≥ Λ`) and its
statement coincides with the `private` helper `cubeTail_le_of_summable` of
`Submission.Work.BoseBoxFock.kinFT_lattice_tail_sq_lt`, whose proof is reproduced here so that it
is available as a named, importable theorem.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock

theorem lattice_cubeTail_le {g : (Fin 3 → ℤ) → ℝ} (hnn : ∀ n, 0 ≤ g n) (hg : Summable g) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      (∑' n : Fin 3 → ℤ, (if ∃ i : Fin 3, N' < |n i| then g n else 0)) ≤ ε := by
  intro ε hε
  -- a finite set outside which the series is small
  have hev : ∀ᶠ s : Finset (Fin 3 → ℤ) in Filter.atTop,
      dist (∑ n ∈ s, g n) (∑' n, g n) < ε :=
    hg.hasSum.eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨F₀, hF₀⟩ := Filter.eventually_atTop.mp hev
  have hcompl : (∑' b : ↑((F₀ : Set (Fin 3 → ℤ))ᶜ), g b) < ε := by
    have h1 := hF₀ F₀ le_rfl
    rw [Real.dist_eq] at h1
    have h2 := hg.sum_add_tsum_compl (s := F₀)
    have h3 := abs_lt.mp h1
    linarith [h3.1, h2]
  -- the index bound: every coordinate of a member of `F₀` is bounded by `B`
  set B : ℕ := F₀.sup (fun n => Finset.univ.sup (fun i : Fin 3 => (n i).natAbs)) with hBdef
  have hbnd : ∀ n ∈ F₀, ∀ i : Fin 3, |n i| ≤ (B : ℤ) := by
    intro n hn i
    have h1 : (n i).natAbs ≤ Finset.univ.sup (fun i : Fin 3 => (n i).natAbs) :=
      Finset.le_sup (f := fun i : Fin 3 => (n i).natAbs) (Finset.mem_univ i)
    have h2 : Finset.univ.sup (fun i : Fin 3 => (n i).natAbs) ≤ B := by
      rw [hBdef]
      exact Finset.le_sup (f := fun n : Fin 3 → ℤ =>
        Finset.univ.sup (fun i : Fin 3 => (n i).natAbs)) hn
    have h3 : (n i).natAbs ≤ B := le_trans h1 h2
    have h4 : (((n i).natAbs : ℤ)) ≤ (B : ℤ) := by exact_mod_cast h3
    rwa [Int.natCast_natAbs] at h4
  refine ⟨B, fun N' hN' => ?_⟩
  -- the truncation is dominated by the indicator of the complement of `F₀`
  have hpt : ∀ n : Fin 3 → ℤ,
      (if ∃ i : Fin 3, N' < |n i| then g n else 0)
        ≤ ((F₀ : Set (Fin 3 → ℤ))ᶜ).indicator g n := by
    intro n
    by_cases hn : n ∈ F₀
    · have hno : ¬ ∃ i : Fin 3, N' < |n i| := by
        rintro ⟨i, hi⟩
        have h1 : |n i| ≤ (B : ℤ) := hbnd n hn i
        have h2 : (B : ℤ) ≤ (N' : ℤ) := by exact_mod_cast hN'
        linarith
      rw [if_neg hno, Set.indicator_of_notMem (by simpa using hn)]
    · rw [Set.indicator_of_mem (by simpa using hn)]
      by_cases h2 : ∃ i : Fin 3, N' < |n i|
      · rw [if_pos h2]
      · rw [if_neg h2]
        exact hnn n
  have hsumL : Summable (fun n : Fin 3 → ℤ =>
      (if ∃ i : Fin 3, N' < |n i| then g n else 0)) :=
    Summable.of_nonneg_of_le
      (f := fun n : Fin 3 → ℤ => ((F₀ : Set (Fin 3 → ℤ))ᶜ).indicator g n)
      (g := fun n : Fin 3 → ℤ => (if ∃ i : Fin 3, N' < |n i| then g n else 0))
      (fun n => by
        by_cases h : ∃ i : Fin 3, N' < |n i|
        · rw [if_pos h]; exact hnn n
        · rw [if_neg h])
      (fun n => hpt n) (hg.indicator _)
  have hcompl' : (∑' n : Fin 3 → ℤ, ((F₀ : Set (Fin 3 → ℤ))ᶜ).indicator g n) < ε := by
    rw [← tsum_subtype ((F₀ : Set (Fin 3 → ℤ))ᶜ) g]
    exact hcompl
  exact le_trans (Summable.tsum_le_tsum hpt hsumL (hg.indicator _)) hcompl'.le

end Work.BoseBoxFock
