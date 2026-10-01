import Mathlib
import Submission.Work.LinnikAreas.Density4.duality_principle

namespace Work.LinnikAreas2

open scoped BigOperators Topology
open Work.LinnikAreas.Density4

/-- **Duality for `ℓ²` series.**  This is the infinite-sum (`tsum`) form of
`Work.LinnikAreas.Density4.duality_principle`: the transposed matrix has the same `ℓ²` operator
norm.  Concretely, if the matrix `A n χ` maps every coefficient vector `C : κ → ℂ` to a sequence
with `Σ_n ‖Σ_χ A n χ · C χ‖² ≤ B · Σ_χ ‖C χ‖²`, then for every square-summable `b : ℕ → ℂ` for
which the sums `Σ_n A n χ · b n` converge,
`Σ_χ ‖Σ'_n A n χ · b n‖² ≤ B · Σ'_n ‖b n‖²`. -/
theorem duality_tsum {κ : Type*} [Fintype κ] (A : ℕ → κ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ C : κ → ℂ, Summable (fun n : ℕ => ‖∑ χ, A n χ * C χ‖ ^ 2) ∧
      (∑' n : ℕ, ‖∑ χ, A n χ * C χ‖ ^ 2) ≤ B * ∑ χ, ‖C χ‖ ^ 2) :
    ∀ b : ℕ → ℂ, Summable (fun n => ‖b n‖ ^ 2) →
      (∀ χ, Summable fun n => A n χ * b n) →
      (∑ χ, ‖∑' n : ℕ, A n χ * b n‖ ^ 2) ≤ B * ∑' n : ℕ, ‖b n‖ ^ 2 := by
  intro b hb hAb
  -- Step 1: the inequality holds for every truncation `n < N`, by the finite duality principle.
  have key : ∀ N : ℕ, (∑ χ, ‖∑ n ∈ Finset.range N, A n χ * b n‖ ^ 2)
      ≤ B * ∑ n ∈ Finset.range N, ‖b n‖ ^ 2 := by
    intro N
    -- The hypothesis of the finite principle, obtained by bounding partial sums by the full `tsum`.
    have hN : ∀ C : κ → ℂ,
        (∑ i : Fin N, ‖∑ χ, A i.val χ * C χ‖ ^ 2) ≤ B * ∑ χ, ‖C χ‖ ^ 2 := by
      intro C
      rw [Fin.sum_univ_eq_sum_range (fun n => ‖∑ χ, A n χ * C χ‖ ^ 2) N]
      exact le_trans
        ((h C).1.sum_le_tsum (Finset.range N) (fun n _ => by positivity)) (h C).2
    have hthis :=
      duality_principle (fun (i : Fin N) (χ : κ) => A i.val χ) B hB hN (fun i => b i.val)
    have hlr : (∑ χ, ‖∑ i : Fin N, A i.val χ * b i.val‖ ^ 2)
        = ∑ χ, ‖∑ n ∈ Finset.range N, A n χ * b n‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun χ _ => ?_)
      rw [Fin.sum_univ_eq_sum_range (fun n => A n χ * b n) N]
    have hrr : (∑ i : Fin N, ‖b i.val‖ ^ 2) = ∑ n ∈ Finset.range N, ‖b n‖ ^ 2 := by
      rw [Fin.sum_univ_eq_sum_range (fun n => ‖b n‖ ^ 2) N]
    rw [hlr, hrr] at hthis
    exact hthis
  -- Step 2: pass to the limit `N → ∞`.
  have hL : Filter.Tendsto (fun N => ∑ χ, ‖∑ n ∈ Finset.range N, A n χ * b n‖ ^ 2)
      Filter.atTop (𝓝 (∑ χ, ‖∑' n, A n χ * b n‖ ^ 2)) := by
    have ht := tendsto_finsetSum (s := (Finset.univ : Finset κ))
      (f := fun χ N => ‖∑ n ∈ Finset.range N, A n χ * b n‖ ^ 2)
      (a := fun χ => ‖∑' n, A n χ * b n‖ ^ 2)
      (fun χ _ => (hAb χ).hasSum.tendsto_sum_nat.norm.pow 2)
    simpa using ht
  have hR : Filter.Tendsto (fun N => B * ∑ n ∈ Finset.range N, ‖b n‖ ^ 2)
      Filter.atTop (𝓝 (B * ∑' n, ‖b n‖ ^ 2)) :=
    hb.hasSum.tendsto_sum_nat.const_mul B
  exact le_of_tendsto_of_tendsto hL hR (Filter.Eventually.of_forall key)

end Work.LinnikAreas2
