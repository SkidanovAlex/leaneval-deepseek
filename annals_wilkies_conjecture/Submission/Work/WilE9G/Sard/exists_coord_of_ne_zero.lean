import Mathlib

namespace Work.WilE9G.Sard

/-- A nonzero continuous linear map into `Fin m → ℝ` cannot vanish on every standard
basis vector's image: some matrix coefficient `T (Pi.single j 1) i` is nonzero. -/
theorem exists_coord_of_ne_zero {n m : ℕ} (T : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ))
    (hT : T ≠ 0) : ∃ (i : Fin m) (j : Fin n), T (Pi.single j (1 : ℝ)) i ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hT
  ext x
  have hz : ∀ j : Fin n, T (Pi.single j (1 : ℝ)) = 0 := fun j => funext (fun i => h i j)
  have hx : x = ∑ j, x j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
    rw [← Finset.univ_sum_single x]
    apply Finset.sum_congr rfl
    intro i _
    funext k
    simp [Pi.single_apply, Pi.smul_apply]
  rw [hx, map_sum]
  simp [hz]

end Work.WilE9G.Sard
