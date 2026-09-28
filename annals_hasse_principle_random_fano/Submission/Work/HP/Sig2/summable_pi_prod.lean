import Mathlib

namespace Work.HP.Sig2

/-- For a finite index type `κ` and a family `f i : ℤ → ℝ` of summable, nonnegative functions,
the product function `n ↦ ∏ i, f i (n i)` on `κ → ℤ` is summable.

The proof bounds every finite partial sum by `∏ i, ∑' m, f i m`: a finite set `u` of tuples is
contained in the product of its coordinate projections `t i = u.image (fun n ↦ n i)`, and the
product of sums over `t i` expands as the sum over `Fintype.piFinset t` of the products
(`Finset.prod_univ_sum`). -/
lemma summable_pi_prod {κ : Type*} [Fintype κ] {f : κ → ℤ → ℝ}
    (hf : ∀ i, Summable (f i)) (hnn : ∀ i m, 0 ≤ f i m) :
    Summable (fun n : κ → ℤ => ∏ i, f i (n i)) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' m, f i m) (fun n => ?_) (fun u => ?_)
  · exact Finset.prod_nonneg (fun i _ => hnn i (n i))
  · let t : κ → Finset ℤ := fun i => u.image (fun n => n i)
    have hsub : u ⊆ Fintype.piFinset t := by
      intro x hx
      rw [Fintype.mem_piFinset]
      intro i
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    calc ∑ n ∈ u, ∏ i, f i (n i)
        ≤ ∑ n ∈ Fintype.piFinset t, ∏ i, f i (n i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun n _ _ => Finset.prod_nonneg (fun i _ => hnn i (n i)))
      _ = ∏ i, ∑ m ∈ t i, f i m := (Finset.prod_univ_sum t f).symm
      _ ≤ ∏ i, ∑' m, f i m :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun m _ => hnn i m))
            (fun i _ => Summable.sum_le_tsum (t i) (fun m _ => hnn i m) (hf i))

end Work.HP.Sig2
