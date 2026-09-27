import Mathlib
import Submission.Work.EKLContract.Defs

namespace Work.Misiurewicz

theorem card_atoms_eq_card (E : Finset Work.EKLContract.X3) {ι : Type*} [Fintype ι]
    (A : ι → Set Work.EKLContract.X3) (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcov : ⋃ i, A i = Set.univ)
    (hinj : ∀ x ∈ E, ∀ y ∈ E, (∀ i, x ∈ A i ↔ y ∈ A i) → x = y) :
    (∀ i, (A i ∩ (E : Set Work.EKLContract.X3)).ncard ≤ 1) ∧
      (Finset.univ.filter (fun i => 1 ≤ (A i ∩ (E : Set Work.EKLContract.X3)).ncard)).card
        = E.card := by
  classical
  -- A point lies in at most one atom.
  have hmem_unique : ∀ {i j : ι} {x : Work.EKLContract.X3}, x ∈ A i → x ∈ A j → i = j := by
    intro i j x hxi hxj
    by_contra hne
    have hd : Disjoint (A i) (A j) := @hdisj i j hne
    rw [Set.disjoint_left] at hd
    exact hd hxi hxj
  -- Every point lies in some atom.
  have hcover : ∀ x, ∃ i, x ∈ A i := by
    intro x
    have hx : x ∈ (⋃ i, A i : Set Work.EKLContract.X3) := by
      rw [hcov]; exact Set.mem_univ x
    simpa only [Set.mem_iUnion] using hx
  -- A choice of the atom containing a point.
  let f : Work.EKLContract.X3 → ι := fun x => Classical.choose (hcover x)
  have hf_mem : ∀ x, x ∈ A (f x) := fun x => Classical.choose_spec (hcover x)
  -- Part 1: each atom meets `E` in at most one point.
  have hle : ∀ i, (A i ∩ (E : Set Work.EKLContract.X3)).ncard ≤ 1 := by
    intro i
    rw [Set.ncard_le_one]
    intro a ha b hb
    obtain ⟨haA, haE⟩ := ha
    obtain ⟨hbA, hbE⟩ := hb
    refine hinj a (by simpa using haE) b (by simpa using hbE) ?_
    intro j
    constructor
    · intro haj
      have h1 : j = i := hmem_unique haj haA
      rw [h1]; exact hbA
    · intro hbj
      have h1 : j = i := hmem_unique hbj hbA
      rw [h1]; exact haA
  refine ⟨hle, ?_⟩
  -- Part 2: the atoms meeting `E` are in bijection with `E` via `f`.
  have hf_injOn : Set.InjOn f (E : Set Work.EKLContract.X3) := by
    intro x hxE y hyE hxy
    refine hinj x (by simpa using hxE) y (by simpa using hyE) ?_
    intro j
    constructor
    · intro hj
      have hfxj : f x = j := hmem_unique (hf_mem x) hj
      have hfyj : f y = j := by rw [← hxy]; exact hfxj
      rw [← hfyj]; exact hf_mem y
    · intro hj
      have hfyj : f y = j := hmem_unique (hf_mem y) hj
      have hfxj : f x = j := by rw [hxy]; exact hfyj
      rw [← hfxj]; exact hf_mem x
  have himage : E.image f
      = Finset.univ.filter (fun i => 1 ≤ (A i ∩ (E : Set Work.EKLContract.X3)).ncard) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hxE, hfx⟩
      have hxA : x ∈ A i := hfx ▸ hf_mem x
      have hne : (A i ∩ (E : Set Work.EKLContract.X3)).Nonempty :=
        ⟨x, hxA, by simpa using hxE⟩
      have := hne.ncard_pos
      omega
    · intro h1
      have hpos : 0 < (A i ∩ (E : Set Work.EKLContract.X3)).ncard := by omega
      obtain ⟨x, hxA, hxE⟩ := (Set.ncard_pos).mp hpos
      exact ⟨x, by simpa using hxE, hmem_unique (hf_mem x) hxA⟩
  rw [← himage]
  exact Finset.card_image_of_injOn hf_injOn

end Work.Misiurewicz
