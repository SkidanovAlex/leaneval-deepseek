import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace Commons.Analysis.TSum

/-- A finite product of nonnegative summable families (over possibly different index
types) is summable, where the product is taken over the full dependent function space. -/
theorem summable_pi_prod_nonneg {ι : Type*} [Fintype ι] {α : ι → Type*}
    (f : ∀ i, α i → ℝ) (hf0 : ∀ i j, 0 ≤ f i j) (hf : ∀ i, Summable (f i)) :
    Summable (fun x : ∀ i, α i => ∏ i, f i (x i)) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' j, f i j)
    (fun x => Finset.prod_nonneg fun i _ => hf0 i (x i)) ?_
  intro u
  let t : ∀ i, Finset (α i) := fun i => u.image (fun x => x i)
  have hsub : u ⊆ Fintype.piFinset t := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  calc ∑ x ∈ u, ∏ i, f i (x i)
      ≤ ∑ x ∈ Fintype.piFinset t, ∏ i, f i (x i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun x _ _ => Finset.prod_nonneg fun i _ => hf0 i (x i))
    _ = ∏ i, ∑ j ∈ t i, f i j := (Finset.prod_univ_sum t f).symm
    _ ≤ ∏ i, ∑' j, f i j := by
        refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => hf0 i j) ?_
        intro i _
        exact (hf i).sum_le_tsum (t i) (fun j _ => hf0 i j)

theorem summable_pi_prod {ι : Type*} [Fintype ι] (u : ι → ℕ → ℂ) (h : ∀ j, Summable (u j)) :
    Summable (fun σ : ι → ℕ => ∏ j, u j (σ j)) := by
  have hn : ∀ j, Summable (fun n => ‖u j n‖) := fun j => (h j).norm
  refine Summable.of_norm ?_
  convert summable_pi_prod_nonneg (f := fun j (n : ℕ) => ‖u j n‖)
    (fun j n => norm_nonneg _) hn using 1
  ext σ
  simp

end Commons.Analysis.TSum