import Mathlib
import Submission.Work.Peluse.ladderA_defs

namespace Work.Peluse.LadderA

/-!
## Splitting the symmetric window `Ioo (-M) M`

The symmetric window `{1-M, …, M-1}` of integers is the union of its nonpositive half
`{1-M, …, 0}` and its nonnegative half `{0, …, M-1}`, which overlap exactly in `{0}`.  Hence the
sum of any function `g` over the window is the sum of the two half sums minus the doubly counted
term `g 0`; in particular it is at most the two half sums when `g ≥ 0`.  Averaged over the `M`
points of each half this gives the "splitting" statement used in the ladder: from a lower bound
`δ` for the average over the symmetric window one gets a lower bound `δ/2` for the average over
one of the two halves.
-/

/-- **Splitting the symmetric window.**  For `M ≥ 1` the sum of `g` over `Ioo (-M) M` equals the
sum over the two half windows `{1-M, …, 0}` and `{0, …, M-1}` minus the common term `g 0`; the two
halves are reindexed by `Finset.range M`. -/
private lemma sum_Ioo_sym_split {M : ℕ} (hM : 1 ≤ M) (g : ℤ → ℝ) :
    (∑ α ∈ Finset.Ioo (-(M : ℤ)) (M : ℤ), g α)
      = (∑ j ∈ Finset.range M, g ((j : ℤ) + 1 - (M : ℤ)))
        + (∑ j ∈ Finset.range M, g (j : ℤ)) - g 0 := by
  rw [Int.Ioo_eq_finset_map, Finset.sum_map]
  have h1 : ((M : ℤ) - -(M : ℤ) - 1) = ((2 * M - 1 : ℕ) : ℤ) := by omega
  rw [h1, Int.toNat_natCast]
  have h2 : ∀ x : ℕ, (Nat.castEmbedding.trans (addLeftEmbedding (-(M : ℤ) + 1))) x
      = (x : ℤ) + 1 - (M : ℤ) := by
    intro x
    rw [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
    ring
  simp_rw [h2]
  have h3 : 2 * M - 1 = M + (M - 1) := by omega
  have h4 : ∀ x : ℕ, (((M + x : ℕ) : ℤ) + 1 - (M : ℤ)) = (x : ℤ) + 1 := by
    intro x
    push_cast
    ring
  have hsplit : (∑ x ∈ Finset.range (2 * M - 1), g ((x : ℤ) + 1 - (M : ℤ)))
      = (∑ x ∈ Finset.range M, g ((x : ℤ) + 1 - (M : ℤ)))
        + (∑ x ∈ Finset.range (M - 1), g ((x : ℤ) + 1)) := by
    rw [h3, Finset.sum_range_add]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => by rw [h4 x])
  have hsecond : (∑ x ∈ Finset.range (M - 1), g ((x : ℤ) + 1))
      = (∑ j ∈ Finset.range M, g (j : ℤ)) - g 0 := by
    have hs := Finset.sum_range_succ' (fun j : ℕ => g ((j : ℤ))) (M - 1)
    rw [show (M - 1) + 1 = M from by omega] at hs
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at hs
    linarith
  rw [hsplit, hsecond]
  ring

/-- **Reindexing `{1, …, M}` by `{0, …, M-1}`.**  The sum over `Finset.Icc 1 M` is the sum over
`Finset.range M` of the shifted function `j ↦ g (j+1)`. -/
private lemma sum_Icc_one_eq_range {M : ℕ} (g : ℕ → ℝ) :
    (∑ a ∈ Finset.Icc (1 : ℕ) M, g a) = ∑ j ∈ Finset.range M, g (j + 1) := by
  refine (Finset.sum_bij (fun (j : ℕ) (_ : j ∈ Finset.range M) => j + 1) ?_ ?_ ?_ ?_).symm
  · intro j hj
    rw [Finset.mem_Icc]
    exact ⟨Nat.le_add_left 1 j, Nat.succ_le_of_lt (Finset.mem_range.mp hj)⟩
  · intro j₁ _ j₂ _ heq
    omega
  · intro b hb
    rw [Finset.mem_Icc] at hb
    exact ⟨b - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j _
    rfl

/-- **The splitting bound.**  If the average of a nonnegative function `g : ℤ → ℝ` over the
symmetric window `Ioo (-M) M` is at least `δ`, then the average over one of the two half windows
`{1-M, …, 0}`, `{0, …, M-1}` is at least `δ/2`. -/
private lemma symmWindow_split_bound {M : ℕ} (hM : 1 ≤ M) {δ : ℝ} (hδ0 : 0 < δ) (g : ℤ → ℝ)
    (hg : ∀ α : ℤ, 0 ≤ g α)
    (hδ : δ ≤ ((Finset.Ioo (-(M : ℤ)) (M : ℤ)).card : ℝ)⁻¹ *
      ∑ α ∈ Finset.Ioo (-(M : ℤ)) (M : ℤ), g α) :
    δ / 2 ≤ (M : ℝ)⁻¹ * ∑ a ∈ Finset.Icc (1 : ℕ) M, g ((a : ℤ) - (M : ℤ)) ∨
    δ / 2 ≤ (M : ℝ)⁻¹ * ∑ a ∈ Finset.Icc (1 : ℕ) M, g ((a : ℤ) - 1) := by
  -- the two half sums, reindexed over `Finset.range M`
  have hH1 : (∑ a ∈ Finset.Icc (1 : ℕ) M, g ((a : ℤ) - (M : ℤ)))
      = ∑ j ∈ Finset.range M, g ((j : ℤ) + 1 - (M : ℤ)) := by
    rw [sum_Icc_one_eq_range (fun a : ℕ => g ((a : ℤ) - (M : ℤ)))]
    exact Finset.sum_congr rfl (fun j _ => by congr 1 <;> omega)
  have hH2 : (∑ a ∈ Finset.Icc (1 : ℕ) M, g ((a : ℤ) - 1))
      = ∑ j ∈ Finset.range M, g (j : ℤ) := by
    rw [sum_Icc_one_eq_range (fun a : ℕ => g ((a : ℤ) - 1))]
    exact Finset.sum_congr rfl (fun j _ => by congr 1 <;> omega)
  -- the window sum is at most the sum of the two halves
  have hWle : (∑ α ∈ Finset.Ioo (-(M : ℤ)) (M : ℤ), g α)
      ≤ (∑ a ∈ Finset.Icc (1 : ℕ) M, g ((a : ℤ) - (M : ℤ)))
        + (∑ a ∈ Finset.Icc (1 : ℕ) M, g ((a : ℤ) - 1)) := by
    rw [hH1, hH2, sum_Ioo_sym_split hM g]
    linarith [hg 0]
  -- the cardinality of the window
  have hcard : 2 * M - 1 ≤ (Finset.Ioo (-(M : ℤ)) (M : ℤ)).card := by
    rw [Int.card_Ioo]
    have h : ((M : ℤ) - -(M : ℤ) - 1) = ((2 * M - 1 : ℕ) : ℤ) := by omega
    rw [h, Int.toNat_natCast]
  have hcardpos : (0 : ℝ) < ((Finset.Ioo (-(M : ℤ)) (M : ℤ)).card : ℝ) := by
    have h0 : 0 < (Finset.Ioo (-(M : ℤ)) (M : ℤ)).card :=
      lt_of_lt_of_le (by omega : 0 < 2 * M - 1) hcard
    exact_mod_cast h0
  -- the window average lower bound, cleared of the normalisation
  have hmain : ((2 * M - 1 : ℕ) : ℝ) * δ
      ≤ ∑ α ∈ Finset.Ioo (-(M : ℤ)) (M : ℤ), g α := by
    have h1 := mul_le_mul_of_nonneg_left hδ (le_of_lt hcardpos)
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcardpos), one_mul] at h1
    have h2 : ((2 * M - 1 : ℕ) : ℝ)
        ≤ ((Finset.Ioo (-(M : ℤ)) (M : ℤ)).card : ℝ) := by
      exact_mod_cast hcard
    have h3 := mul_le_mul_of_nonneg_right h2 (le_of_lt hδ0)
    linarith
  -- if both halves averaged less than `δ/2`, the two half sums would total less than `M δ`
  by_contra hcon
  simp only [not_or, not_le] at hcon
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  have hmul1 : (∑ a ∈ Finset.Icc (1 : ℕ) M, g ((a : ℤ) - (M : ℤ)))
      < (M : ℝ) * δ / 2 := by
    have h1 := mul_lt_mul_of_pos_left hcon.1 hMpos
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at h1
    linarith
  have hmul2 : (∑ a ∈ Finset.Icc (1 : ℕ) M, g ((a : ℤ) - 1)) < (M : ℝ) * δ / 2 := by
    have h1 := mul_lt_mul_of_pos_left hcon.2 hMpos
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at h1
    linarith
  have hfin : (∑ a ∈ Finset.Icc (1 : ℕ) M, g ((a : ℤ) - (M : ℤ)))
      + (∑ a ∈ Finset.Icc (1 : ℕ) M, g ((a : ℤ) - 1)) < (M : ℝ) * δ := by
    linarith
  have hMle : (M : ℝ) * δ ≤ ((2 * M - 1 : ℕ) : ℝ) * δ := by
    have h : (M : ℝ) ≤ ((2 * M - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : M ≤ 2 * M - 1)
    exact mul_le_mul_of_nonneg_right h (le_of_lt hδ0)
  linarith

theorem symmWindowSplit {s : ℕ} (c : ℤ) {M₁ M₂ : ℕ} (hM₂ : 1 ≤ M₂) (d : Fin s → ℤ)
    (S : Finset ℤ) (f : ℤ → ℂ) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ ((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ)⁻¹ *
      ∑ α ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
        Work.Peluse.boxNorm s (fun i : Fin s => Work.Peluse.arithIcc (c * α + d i) M₁) S f) :
    δ / 2 ≤ (M₂ : ℝ)⁻¹ * ∑ a ∈ Finset.Icc (1 : ℕ) M₂,
        Work.Peluse.boxNorm s (fun i : Fin s =>
          Work.Peluse.arithIcc (c * (a : ℤ) + (d i - c * (M₂ : ℤ))) M₁) S f ∨
    δ / 2 ≤ (M₂ : ℝ)⁻¹ * ∑ a ∈ Finset.Icc (1 : ℕ) M₂,
        Work.Peluse.boxNorm s (fun i : Fin s =>
          Work.Peluse.arithIcc (c * (a : ℤ) + (d i - c)) M₁) S f := by
  classical
  let B : ℤ → ℝ := fun α : ℤ =>
    Work.Peluse.boxNorm s (fun i : Fin s => Work.Peluse.arithIcc (c * α + d i) M₁) S f
  have hg : ∀ α : ℤ, 0 ≤ B α := by
    intro α
    exact Real.rpow_nonneg
      (norm_nonneg (Work.Peluse.boxSumPow s
        (fun i : Fin s => Work.Peluse.arithIcc (c * α + d i) M₁) S f)) _
  have hδ' : δ ≤ ((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ)⁻¹ *
      ∑ α ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ), B α := hδ
  have key := symmWindow_split_bound hM₂ hδ0 B hg hδ'
  -- identify the two sums of the statement with the corresponding sums of `B`
  have h1 : (∑ a ∈ Finset.Icc (1 : ℕ) M₂,
        Work.Peluse.boxNorm s (fun i : Fin s =>
          Work.Peluse.arithIcc (c * (a : ℤ) + (d i - c * (M₂ : ℤ))) M₁) S f)
      = ∑ a ∈ Finset.Icc (1 : ℕ) M₂, B ((a : ℤ) - (M₂ : ℤ)) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    show Work.Peluse.boxNorm s (fun i : Fin s =>
          Work.Peluse.arithIcc (c * (a : ℤ) + (d i - c * (M₂ : ℤ))) M₁) S f
        = Work.Peluse.boxNorm s (fun i : Fin s =>
          Work.Peluse.arithIcc (c * ((a : ℤ) - (M₂ : ℤ)) + d i) M₁) S f
    congr 1
    funext i
    congr 1
    ring
  have h2 : (∑ a ∈ Finset.Icc (1 : ℕ) M₂,
        Work.Peluse.boxNorm s (fun i : Fin s =>
          Work.Peluse.arithIcc (c * (a : ℤ) + (d i - c)) M₁) S f)
      = ∑ a ∈ Finset.Icc (1 : ℕ) M₂, B ((a : ℤ) - 1) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    show Work.Peluse.boxNorm s (fun i : Fin s =>
          Work.Peluse.arithIcc (c * (a : ℤ) + (d i - c)) M₁) S f
        = Work.Peluse.boxNorm s (fun i : Fin s =>
          Work.Peluse.arithIcc (c * ((a : ℤ) - 1) + d i) M₁) S f
    congr 1
    funext i
    congr 1
    ring
  rcases key with hk | hk
  · left
    rw [h1]
    exact hk
  · right
    rw [h2]
    exact hk

end Work.Peluse.LadderA
