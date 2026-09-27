import Mathlib
import Submission.Work.PL.Defs

/-!
# Barycentric coordinates and the convex hull of a vertex set with one vertex removed

For an affinely independent vertex map `v : ι → ℝᴺ` (`ι` finite) and a point
`x = ∑ j, t j • v j` which is a convex combination of the `v j` (`t ≥ 0`, `∑ t = 1`),
the barycentric coordinate of `v i` vanishes exactly when `x` lies in the convex hull
of the remaining vertices `v '' {i}ᶜ`.

The mathematical content is the uniqueness of barycentric coordinates with respect to
an affinely independent family, together with the description of the convex hull of an
image as the set of convex combinations of the images
(`convexHull_range_eq_exists_affineCombination`).
-/

namespace Work.PL.Subdiv.Simplex

open Set

/-- A point lies in the convex hull of `v '' {i}ᶜ` iff it is a convex combination of the
`v j` (`j ≠ i`); equivalently, iff it admits barycentric weights `a` with `a ≥ 0`,
`a i = 0` and `∑ a = 1`. -/
theorem mem_convexHull_compl_iff_exists_weights {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → PL.E N) (i : ι) (x : PL.E N) :
    x ∈ convexHull ℝ (v '' ({i}ᶜ : Set ι)) ↔
      ∃ a : ι → ℝ, (∀ j, 0 ≤ a j) ∧ a i = 0 ∧ (∑ j, a j = 1) ∧ ∑ j, a j • v j = x := by
  classical
  constructor
  · intro hx
    rw [Set.image_eq_range, convexHull_range_eq_exists_affineCombination] at hx
    obtain ⟨s, w, hw0, hw1, hxw⟩ := hx
    set w' : ↥(({i}ᶜ : Set ι)) → ℝ := fun t => if t ∈ s then w t else 0 with hw'def
    set a : ι → ℝ := fun j => if h : j ∈ ({i}ᶜ : Set ι) then w' ⟨j, h⟩ else 0 with hadef
    have ha_apply : ∀ t : ↥(({i}ᶜ : Set ι)), a ↑t = w' t := by
      intro t
      simp only [hadef, dite_eq_left t.2]
    have ha0 : ∀ j, 0 ≤ a j := by
      intro j
      by_cases h : j ∈ ({i}ᶜ : Set ι)
      · simp only [hadef, dite_eq_left h]
        by_cases h2 : (⟨j, h⟩ : ↥(({i}ᶜ : Set ι))) ∈ s
        · simp only [hw'def, ite_eq_left h2]; exact hw0 ⟨j, h⟩ h2
        · simp only [hw'def, ite_eq_right h2]; exact le_refl 0
      · simp only [hadef, dite_eq_right h]; exact le_refl 0
    have hai : a i = 0 := by simp [hadef]
    have hS1 : ∑ j ∈ Finset.univ.erase i, a j = ∑ t : ↥(({i}ᶜ : Set ι)), w' t := by
      rw [Finset.sum_subtype (p := fun j => j ∈ ({i}ᶜ : Set ι)) (Finset.univ.erase i)
        (fun x => by simp [Finset.mem_erase]) a]
      exact Finset.sum_congr rfl (fun t _ => ha_apply t)
    have hS2 : ∑ j, a j = ∑ j ∈ Finset.univ.erase i, a j := by
      have h := Finset.sum_erase_add (Finset.univ : Finset ι) a (Finset.mem_univ i)
      rw [hai, add_zero] at h
      exact h.symm
    have hS3 : ∑ t : ↥(({i}ᶜ : Set ι)), w' t = 1 := by
      have h1 : ∑ t : ↥(({i}ᶜ : Set ι)), w' t = ∑ t ∈ s, w' t :=
        (Finset.sum_subset (Finset.subset_univ s) (fun t _ ht => by simp [hw'def, ht])).symm
      have h2 : ∑ t ∈ s, w' t = ∑ t ∈ s, w t :=
        Finset.sum_congr rfl (fun t ht => by simp [hw'def, ht])
      rw [h1, h2, hw1]
    have hV1 : ∑ j ∈ Finset.univ.erase i, a j • v j = ∑ t : ↥(({i}ᶜ : Set ι)), w' t • v ↑t := by
      rw [Finset.sum_subtype (p := fun j => j ∈ ({i}ᶜ : Set ι)) (Finset.univ.erase i)
        (fun x => by simp [Finset.mem_erase]) (fun j => a j • v j)]
      exact Finset.sum_congr rfl (fun t _ => by rw [ha_apply t])
    have hV2 : ∑ j, a j • v j = ∑ j ∈ Finset.univ.erase i, a j • v j := by
      have h := Finset.sum_erase_add (Finset.univ : Finset ι) (fun j => a j • v j)
        (Finset.mem_univ i)
      rw [hai, zero_smul, add_zero] at h
      exact h.symm
    have hV3 : ∑ t : ↥(({i}ᶜ : Set ι)), w' t • v ↑t = ∑ t ∈ s, w' t • v ↑t :=
      (Finset.sum_subset (Finset.subset_univ s) (fun t _ ht => by simp [hw'def, ht])).symm
    have hV4 : ∑ t ∈ s, w' t • v ↑t = ∑ t ∈ s, w t • v ↑t :=
      Finset.sum_congr rfl (fun t ht => by rw [hw'def]; simp [ht])
    have hV5 : ∑ t ∈ s, w t • v ↑t = x :=
      (Finset.affineCombination_eq_linear_combination s (fun t => v ↑t) w hw1).symm.trans hxw
    exact ⟨a, ha0, hai, by rw [hS2, hS1, hS3], by rw [hV2, hV1, hV3, hV4, hV5]⟩
  · rintro ⟨a, ha0, hai, ha1, rfl⟩
    have hsum : ∑ j ∈ Finset.univ.erase i, a j = 1 := by
      have h := Finset.sum_erase_add (Finset.univ : Finset ι) a (Finset.mem_univ i)
      rw [ha1, hai, add_zero] at h
      exact h
    have hpos : 0 < ∑ j ∈ Finset.univ.erase i, a j := by rw [hsum]; norm_num
    have hmem : ∀ j ∈ Finset.univ.erase i, v j ∈ v '' ({i}ᶜ : Set ι) := by
      intro j hj
      refine ⟨j, ?_, rfl⟩
      exact (by simpa [Set.mem_compl_iff] using (Finset.mem_erase.mp hj).1)
    have hcm : (Finset.univ.erase i).centerMass a v ∈ convexHull ℝ (v '' ({i}ᶜ : Set ι)) :=
      Finset.centerMass_mem_convexHull (Finset.univ.erase i) (fun j _ => ha0 j) hpos
        (fun j hj => hmem j hj)
    rw [Finset.centerMass_eq_of_sum_1 (Finset.univ.erase i) (w := a) v hsum] at hcm
    rw [← Finset.sum_erase_add (Finset.univ : Finset ι) (fun j => a j • v j) (Finset.mem_univ i)]
    simp only [hai, zero_smul, add_zero]
    exact hcm

/-- For an affinely independent family `v` and a convex combination `∑ j, t j • v j`, the
point lies in the convex hull of the vertices other than `v i` exactly when the
barycentric coordinate `t i` vanishes. -/
theorem sum_smul_mem_convexHull_compl_iff {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {v : ι → PL.E N} (hv : AffineIndependent ℝ v) {t : ι → ℝ} (ht0 : ∀ i, 0 ≤ t i)
    (ht1 : ∑ i, t i = 1) (i : ι) :
    (∑ j, t j • v j) ∈ convexHull ℝ (v '' {i}ᶜ) ↔ t i = 0 := by
  classical
  rw [mem_convexHull_compl_iff_exists_weights v i]
  constructor
  · rintro ⟨a, ha0, hai, ha1, haeq⟩
    have huniq : a i = t i :=
      AffineIndependent.eq_of_sum_eq_sum (s := Finset.univ) hv (by rw [ha1, ht1]) haeq i
        (Finset.mem_univ i)
    rw [← huniq, hai]
  · intro hti
    exact ⟨t, ht0, hti, ht1, rfl⟩

end Work.PL.Subdiv.Simplex
