import Mathlib

/-!
# Re-indexing finite convex combinations by `Fin 3`

Given an injection `e : ι ↪ Fin 3` from a finite index type and a weighted family
`∑ j, w j • z j`, we may re-index the sum over `Fin 3`, padding with a base point.
This is the combinatorial step in the proof that the convex hull of a compact subset
of `ℂ` is compact (Carathéodory's theorem in the plane).
-/

namespace Work.Smooth.JordanSeparation

open Finset

variable {ι : Type*} [Fintype ι]

/-- Re-index a finite weighted sum along an injection into `Fin 3`. -/
theorem exists_fin_three_transfer [DecidableEq ι]
    {K : Set ℂ} {k0 : ℂ} (hk0 : k0 ∈ K)
    (e : ι ↪ Fin 3) (w : ι → ℝ) (z : ι → ℂ) (hz : ∀ j, z j ∈ K) (hw : ∀ j, 0 ≤ w j) :
    ∃ (w' : Fin 3 → ℝ) (f : Fin 3 → ℂ),
      (∀ i, f i ∈ K) ∧ (∀ i, 0 ≤ w' i) ∧
      (∑ i, w' i = ∑ j, w j) ∧ (∑ i, w' i • f i = ∑ j, w j • z j) := by
  classical
  let w' : Fin 3 → ℝ := fun i => if h : ∃ j, e j = i then w (Classical.choose h) else 0
  let f : Fin 3 → ℂ := fun i => if h : ∃ j, e j = i then z (Classical.choose h) else k0
  have hw' : ∀ j : ι, w' (e j) = w j := by
    intro j
    have h : ∃ j', e j' = e j := ⟨j, rfl⟩
    simp only [w', dif_pos h]
    rw [e.injective (Classical.choose_spec h)]
  have hf' : ∀ j : ι, f (e j) = z j := by
    intro j
    have h : ∃ j', e j' = e j := ⟨j, rfl⟩
    simp only [f, dif_pos h]
    rw [e.injective (Classical.choose_spec h)]
  have hzero_w : ∀ i : Fin 3, i ∉ Finset.univ.image e → w' i = 0 := by
    intro i hi
    have h : ¬ ∃ j, e j = i := by
      rintro ⟨j, hj⟩
      exact hi (Finset.mem_image.2 ⟨j, Finset.mem_univ j, hj⟩)
    simp only [w', dif_neg h]
  have hzero_f : ∀ i : Fin 3, i ∉ Finset.univ.image e → f i = k0 := by
    intro i hi
    have h : ¬ ∃ j, e j = i := by
      rintro ⟨j, hj⟩
      exact hi (Finset.mem_image.2 ⟨j, Finset.mem_univ j, hj⟩)
    simp only [f, dif_neg h]
  refine ⟨w', f, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ Finset.univ.image e
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hi
      rw [← hj, hf']
      exact hz j
    · rw [hzero_f i hi]
      exact hk0
  · intro i
    by_cases hi : i ∈ Finset.univ.image e
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hi
      rw [← hj, hw']
      exact hw j
    · exact le_of_eq (hzero_w i hi).symm
  · calc ∑ i : Fin 3, w' i
        = ∑ i ∈ Finset.univ.image e, w' i :=
          (Finset.sum_subset (Finset.subset_univ _)
            (fun x _ hx => hzero_w x hx)).symm
      _ = ∑ j : ι, w' (e j) :=
          Finset.sum_image (f := w') (s := Finset.univ) (g := e)
            (fun a _ b _ h => e.injective h)
      _ = ∑ j : ι, w j := Finset.sum_congr rfl (fun j _ => hw' j)
  · calc ∑ i : Fin 3, w' i • f i
        = ∑ i ∈ Finset.univ.image e, w' i • f i :=
          (Finset.sum_subset (Finset.subset_univ _)
            (fun x _ hx => by rw [hzero_w x hx, zero_smul])).symm
      _ = ∑ j : ι, w' (e j) • f (e j) :=
          Finset.sum_image (f := fun i => w' i • f i) (s := Finset.univ) (g := e)
            (fun a _ b _ h => e.injective h)
      _ = ∑ j : ι, w j • z j := Finset.sum_congr rfl (fun j _ => by rw [hw' j, hf' j])

end Work.Smooth.JordanSeparation
