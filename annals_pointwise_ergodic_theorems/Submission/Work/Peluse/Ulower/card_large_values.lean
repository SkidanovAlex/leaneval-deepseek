import Mathlib

namespace Work.Peluse.Ulower

/-- If `0 ≤ Z i ≤ K` for all `i`, and `δ * card ι ≤ sum of Z`, then at least
`δ/(4K) * card ι` of the values `Z i` are at least `δ/4`. -/
theorem card_large_values {ι : Type*} [Fintype ι] {Z : ι → ℝ} {δ K : ℝ}
    (hδ : 0 < δ) (hK : 0 < K) (hZ0 : ∀ i, 0 ≤ Z i) (hZK : ∀ i, Z i ≤ K)
    (hsum : δ * (Fintype.card ι : ℝ) ≤ ∑ i, Z i) :
    δ / 4 / K * (Fintype.card ι : ℝ) ≤ ((Finset.univ.filter (fun i => δ / 4 ≤ Z i)).card : ℝ) := by
  classical
  have _hZ0 : ∀ i, 0 ≤ Z i := hZ0
  have hcardnat : (Finset.univ.filter (fun i => δ / 4 ≤ Z i)).card
      + (Finset.univ.filter (fun i => ¬ δ / 4 ≤ Z i)).card = Fintype.card ι := by
    simpa [Finset.card_univ] using (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (p := fun i => δ / 4 ≤ Z i))
  have hcard : (((Finset.univ.filter (fun i => δ / 4 ≤ Z i)).card : ℝ)
      + ((Finset.univ.filter (fun i => ¬ δ / 4 ≤ Z i)).card : ℝ)) = (Fintype.card ι : ℝ) := by
    rw [← hcardnat]; push_cast; ring
  have hsplit : (∑ i, Z i) = Finset.sum (Finset.univ.filter (fun i => δ / 4 ≤ Z i)) Z
      + Finset.sum (Finset.univ.filter (fun i => ¬ δ / 4 ≤ Z i)) Z := by
    simpa using (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset ι))
      (p := fun i => δ / 4 ≤ Z i) (f := Z)).symm
  have hA : Finset.sum (Finset.univ.filter (fun i => δ / 4 ≤ Z i)) Z
      ≤ ((Finset.univ.filter (fun i => δ / 4 ≤ Z i)).card : ℝ) * K := by
    calc Finset.sum (Finset.univ.filter (fun i => δ / 4 ≤ Z i)) Z
        ≤ Finset.sum (Finset.univ.filter (fun i => δ / 4 ≤ Z i)) (fun _ => K) :=
          Finset.sum_le_sum (fun i _ => hZK i)
      _ = ((Finset.univ.filter (fun i => δ / 4 ≤ Z i)).card : ℝ) * K := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hB : Finset.sum (Finset.univ.filter (fun i => ¬ δ / 4 ≤ Z i)) Z
      ≤ ((Finset.univ.filter (fun i => ¬ δ / 4 ≤ Z i)).card : ℝ) * (δ / 4) := by
    calc Finset.sum (Finset.univ.filter (fun i => ¬ δ / 4 ≤ Z i)) Z
        ≤ Finset.sum (Finset.univ.filter (fun i => ¬ δ / 4 ≤ Z i)) (fun _ => δ / 4) :=
          Finset.sum_le_sum (fun i hi => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2))
      _ = ((Finset.univ.filter (fun i => ¬ δ / 4 ≤ Z i)).card : ℝ) * (δ / 4) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have h1 : δ * (Fintype.card ι : ℝ)
      ≤ ((Finset.univ.filter (fun i => δ / 4 ≤ Z i)).card : ℝ) * K
        + ((Finset.univ.filter (fun i => ¬ δ / 4 ≤ Z i)).card : ℝ) * (δ / 4) := by
    calc δ * (Fintype.card ι : ℝ) ≤ ∑ i, Z i := hsum
      _ = _ := hsplit
      _ ≤ _ := add_le_add hA hB
  have hmain : (δ / 4) * (Fintype.card ι : ℝ)
      ≤ ((Finset.univ.filter (fun i => δ / 4 ≤ Z i)).card : ℝ) * K := by
    have hdA : 0 ≤ δ * ((Finset.univ.filter (fun i => δ / 4 ≤ Z i)).card : ℝ) :=
      mul_nonneg (le_of_lt hδ) (Nat.cast_nonneg _)
    have hdC : 0 ≤ δ * ((Finset.univ.filter (fun i => ¬ δ / 4 ≤ Z i)).card : ℝ) :=
      mul_nonneg (le_of_lt hδ) (Nat.cast_nonneg _)
    rw [← hcard] at h1 ⊢
    nlinarith [hdA, hdC]
  calc δ / 4 / K * (Fintype.card ι : ℝ)
      = δ / 4 * (Fintype.card ι : ℝ) / K := by ring
    _ ≤ ((Finset.univ.filter (fun i => δ / 4 ≤ Z i)).card : ℝ) := by
        rw [div_le_iff₀ hK]; exact hmain

end Work.Peluse.Ulower
