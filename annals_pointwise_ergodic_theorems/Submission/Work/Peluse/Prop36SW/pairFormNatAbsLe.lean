import Mathlib
import Submission.Work.Peluse.Prop36SW.toeplitzWeightedAbsLe

namespace Work.Peluse.Prop36SW

/-- The map `i ↦ i - M` from `Fin (2M+1)` onto the symmetric interval `[-M,M]`. -/
private lemma finSubMem (M : ℕ) (i : Fin (2 * M + 1)) :
    (i : ℤ) - (M : ℤ) ∈ Work.Peluse.symIcc M := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  have hi : (i : ℕ) ≤ 2 * M := by omega
  constructor <;> omega

private lemma finSubInj (M : ℕ) {i j : Fin (2 * M + 1)}
    (h : (i : ℤ) - (M : ℤ) = (j : ℤ) - (M : ℤ)) : i = j := by
  have h' : (i : ℤ) = (j : ℤ) := by omega
  exact Fin.ext (Int.ofNat_inj.mp h')

private lemma finSubSurj (M : ℕ) {y : ℤ} (hy : y ∈ Work.Peluse.symIcc M) :
    ∃ i : Fin (2 * M + 1), (i : ℤ) - (M : ℤ) = y := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc] at hy
  refine ⟨⟨(y + (M : ℤ)).toNat, ?_⟩, ?_⟩
  · omega
  · rw [Int.toNat_of_nonneg (by omega)]
    ring

/-- The `Fin (2M+1)`-indexed form of the "Toeplitz pairing" inequality: the second
difference form `∑_{y,k∈[-M,M]} |y-k| Re (f y conj (f k))` is bounded by `M ‖∑ f‖²`.

This is `toeplitzWeightedAbsLe` transported from `Fin (2M+1)` to the symmetric
interval `[-M,M]` of the integers along the bijection `i ↦ i - M`. -/
theorem pairFormNatAbsLe {M : ℕ} {f : ℤ → ℂ} (hsup : Work.Peluse.SupportIn f M) :
    (∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
        (((y - k).natAbs : ℝ)) * (f y * star (f k)).re)
      ≤ (M : ℝ) * ‖∑ y ∈ Work.Peluse.symIcc M, f y‖ ^ 2 := by
  classical
  have hA1 : ∀ y ∈ Work.Peluse.symIcc M,
      (∑ k ∈ Work.Peluse.symIcc M, (((y - k).natAbs : ℝ)) * (f y * star (f k)).re)
      = ∑ i : Fin (2*M+1),
          (((y - ((i:ℤ) - (M:ℤ))).natAbs : ℝ)) *
            (f y * star (f ((i:ℤ) - (M:ℤ)))).re := by
    intro y hy
    exact (Finset.sum_bij (fun (i : Fin (2*M+1)) (_ : i ∈ Finset.univ) => (i:ℤ) - (M:ℤ))
      (fun i _ => finSubMem M i)
      (fun i _ j _ h => finSubInj M h)
      (fun b hb => by
        obtain ⟨i, hi⟩ := finSubSurj M hb
        exact ⟨i, Finset.mem_univ i, hi⟩)
      (fun i _ => rfl)).symm
  have hA2 : (∑ y ∈ Work.Peluse.symIcc M,
        ∑ i : Fin (2*M+1),
          (((y - ((i:ℤ) - (M:ℤ))).natAbs : ℝ)) *
            (f y * star (f ((i:ℤ) - (M:ℤ)))).re)
      = ∑ i : Fin (2*M+1), ∑ j : Fin (2*M+1),
          (((((i:ℤ) - (M:ℤ)) - ((j:ℤ) - (M:ℤ))).natAbs : ℝ)) *
            (f ((i:ℤ) - (M:ℤ)) * star (f ((j:ℤ) - (M:ℤ)))).re := by
    exact (Finset.sum_bij (fun (i : Fin (2*M+1)) (_ : i ∈ Finset.univ) => (i:ℤ) - (M:ℤ))
      (fun i _ => finSubMem M i)
      (fun i _ j _ h => finSubInj M h)
      (fun b hb => by
        obtain ⟨i, hi⟩ := finSubSurj M hb
        exact ⟨i, Finset.mem_univ i, hi⟩)
      (fun i _ => rfl)).symm
  have hB : ∀ i j : Fin (2*M+1),
      (((((i:ℤ) - (M:ℤ)) - ((j:ℤ) - (M:ℤ))).natAbs : ℝ)) *
            (f ((i:ℤ) - (M:ℤ)) * star (f ((j:ℤ) - (M:ℤ)))).re
      = (|(((i:ℤ) - (j:ℤ)) : ℝ)|) *
            (f ((i:ℤ) - (M:ℤ)) * star (f ((j:ℤ) - (M:ℤ)))).re := by
    intro i j
    have harg : ((i:ℤ) - (M:ℤ)) - ((j:ℤ) - (M:ℤ)) = (i:ℤ) - (j:ℤ) := by ring
    rw [harg, Nat.cast_natAbs, Int.cast_abs]
    push_cast
    ring
  have key : (∑ y ∈ Work.Peluse.symIcc M, ∑ k ∈ Work.Peluse.symIcc M,
        (((y - k).natAbs : ℝ)) * (f y * star (f k)).re)
      = ∑ i : Fin (2*M+1), ∑ j : Fin (2*M+1),
          (|(((i:ℤ) - (j:ℤ)) : ℝ)|) *
            (f ((i:ℤ) - (M:ℤ)) * star (f ((j:ℤ) - (M:ℤ)))).re := by
    rw [Finset.sum_congr (rfl : Work.Peluse.symIcc M = Work.Peluse.symIcc M)
      (fun y hy => hA1 y hy), hA2]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hB i j))
  have hT : ∑ i : Fin (2*M+1), f ((i:ℤ) - (M:ℤ)) = ∑ y ∈ Work.Peluse.symIcc M, f y := by
    exact Finset.sum_bij (fun (i : Fin (2*M+1)) (_ : i ∈ Finset.univ) => (i:ℤ) - (M:ℤ))
      (fun i _ => finSubMem M i)
      (fun i _ j _ h => finSubInj M h)
      (fun b hb => by
        obtain ⟨i, hi⟩ := finSubSurj M hb
        exact ⟨i, Finset.mem_univ i, hi⟩)
      (fun i _ => rfl)
  have ht := toeplitzWeightedAbsLe (2*M+1) (by omega)
    (fun i : Fin (2*M+1) => f ((i:ℤ) - (M:ℤ)))
  have hcard : ((2*M+1 : ℕ) : ℝ) - 1 = 2 * (M:ℝ) := by push_cast; ring
  rw [hcard] at ht
  rw [key, ← hT]
  linarith [ht]

end Work.Peluse.Prop36SW
