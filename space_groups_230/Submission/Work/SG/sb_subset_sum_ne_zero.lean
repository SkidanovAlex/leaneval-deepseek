import Mathlib
import Submission.Work.SG.SellingDefs

/-! ### A nonempty proper subset of a superbase never sums to zero

The superbase `sb W = (-(v₁+v₂+v₃), v₁, v₂, v₃)` of a unimodular integer matrix `W` (columns
`v₁, v₂, v₃`) has the property that **no** subset sum over a nonempty proper subset of `Fin 4`
vanishes.  Equivalently, the four points of the superbase are in "general position" with respect
to the four-element affine relation `∑ m, sb W m = 0`: the only vanishing sub-sum is the empty
one and the full one.

Proof: writing `u = ∑ m ∈ T, coordVec m`, linearity of `mulVec` together with
`mulVec_coordVec` gives `∑ m ∈ T, sb W m = W *ᵥ u`; unimodularity of `W` makes `W *ᵥ ·` injective,
so a vanishing subset sum forces `u = 0`.  The `i`-th coordinate of `u` is
`(if i.succ ∈ T then 1 else 0) - (if 0 ∈ T then 1 else 0)`, whence either `0 ∈ T` forces
`T = univ`, or `0 ∉ T` forces `T = ∅`.
-/

namespace Work.SG

open scoped Matrix

/-- A `3 × 3` integer matrix of unit determinant is injective on integer vectors: its only
vector with `W *ᵥ y = 0` is `0`.  (`adjugate_mul` writes `W.adjugate * W = W.det • 1`, and
`W.det` is a unit of `ℤ`, hence `1` or `-1`.) -/
private theorem mulVec_eq_zero_of_isUnit_det {W : IMat} (hW : IsUnit W.det) {y : IVec}
    (hy : W *ᵥ y = 0) : y = 0 := by
  have hdet : W.det • y = 0 := by
    calc W.det • y = (W.det • (1 : IMat)) *ᵥ y := by rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = (W.adjugate * W) *ᵥ y := by rw [Matrix.adjugate_mul]
      _ = W.adjugate *ᵥ (W *ᵥ y) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hy, Matrix.mulVec_zero]
  rcases Int.isUnit_iff.mp hW with h | h
  · rw [h, one_smul] at hdet; exact hdet
  · rw [h] at hdet; simpa using hdet

/-- `W` applied to the sum of the coordinate vectors of the superbase elements in `T` is the
sum of the corresponding superbase vectors (`Matrix.mulVec_sum` and `mulVec_coordVec`). -/
private theorem sum_sb_eq_mulVec (W : IMat) (T : Finset (Fin 4)) :
    (∑ m ∈ T, sb W m) = W *ᵥ (∑ m ∈ T, coordVec m) := by
  rw [Matrix.mulVec_sum]
  exact (Finset.sum_congr rfl fun m _ => mulVec_coordVec W m).symm

/-- The `i`-th coordinate of `u = ∑ m ∈ T, coordVec m`: each `coordVec (j.succ)` is the `j`-th
standard basis vector and `coordVec 0 = -1`, so the only contributions are `-1` from `0` (if it
lies in `T`) and `+1` from `i.succ` (if it lies in `T`). -/
private theorem sum_coordVec_apply (T : Finset (Fin 4)) (i : Fin 3) :
    (∑ m ∈ T, coordVec m) i =
      -(if (0:Fin 4) ∈ T then (1:ℤ) else 0) + (if i.succ ∈ T then 1 else 0) := by
  have hkey : ∀ m : Fin 4, coordVec m i =
      (if m = 0 then (-1:ℤ) else 0) + (if m = i.succ then 1 else 0) := by
    intro m
    fin_cases m <;> fin_cases i <;> decide
  rw [Finset.sum_apply, Finset.sum_congr rfl (fun m _ => hkey m), Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' T (0:Fin 4) (fun _ => (-1:ℤ)),
      Finset.sum_ite_eq' T i.succ (fun _ => (1:ℤ))]
  by_cases h : (0:Fin 4) ∈ T <;> simp [h]

/-- A nonempty proper subset of the superbase of a unimodular integer matrix has nonzero sum. -/
theorem sb_subset_sum_ne_zero (W : IMat) (T : Finset (Fin 4)) (hne : T.Nonempty)
    (hprop : T ≠ Finset.univ) (hW : IsUnit W.det) : (∑ m ∈ T, sb W m) ≠ 0 := by
  intro hzero
  have hu : (∑ m ∈ T, coordVec m) = 0 :=
    mulVec_eq_zero_of_isUnit_det hW (by rw [← sum_sb_eq_mulVec]; exact hzero)
  have hval : ∀ i : Fin 3, (if i.succ ∈ T then (1:ℤ) else 0) =
      (if (0:Fin 4) ∈ T then 1 else 0) := by
    intro i
    have h : (∑ m ∈ T, coordVec m) i = 0 := by rw [hu]; rfl
    rw [sum_coordVec_apply T i] at h
    linarith
  have hmem : ∀ i : Fin 3, i.succ ∈ T ↔ (0:Fin 4) ∈ T := by
    intro i
    have hv := hval i
    by_cases h0 : (0:Fin 4) ∈ T
    · have hv1 : (if i.succ ∈ T then (1:ℤ) else 0) = 1 := by simpa [h0] using hv
      refine ⟨fun _ => h0, fun _ => ?_⟩
      by_contra hc
      have hz : (if i.succ ∈ T then (1:ℤ) else 0) = 0 := by simp [hc]
      omega
    · have hv1 : (if i.succ ∈ T then (1:ℤ) else 0) = 0 := by simpa [h0] using hv
      refine ⟨fun hc => ?_, fun hc => absurd hc h0⟩
      have ho : (if i.succ ∈ T then (1:ℤ) else 0) = 1 := by simp [hc]
      omega
  by_cases h0 : (0:Fin 4) ∈ T
  · apply hprop
    apply Finset.eq_univ_iff_forall.mpr
    intro m
    rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨i, rfl⟩
    · exact h0
    · exact (hmem i).mpr h0
  · have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp (by
      rintro ⟨m, hm⟩
      rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨i, rfl⟩
      · exact h0 hm
      · exact h0 ((hmem i).mp hm))
    rw [hT] at hne
    exact hne.ne_empty rfl

end Work.SG
