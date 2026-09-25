import Mathlib

namespace NK.CFTLib

variable {G : Type*} [CommGroup G] {ι : Type*}

/-- The pure "single generator" computation: the product over `S` of `d w' ^ (single w n w')`
collapses to `d w ^ n`, because the only index contributing is `w`. -/
private lemma prod_zpow_single (S : Finset ι) (d : ι → G) {w : ι} (hw : w ∈ S) (n : ℤ) :
    (∏ w' ∈ S, d w' ^ ((Finsupp.single w n) w')) = d w ^ n := by
  classical
  rw [Finset.prod_eq_single_of_mem w hw
    (fun b _ hne => by rw [Finsupp.single_eq_of_ne hne, zpow_zero])]
  rw [Finsupp.single_eq_same]

/-- The exponents add on the product side. -/
private lemma prod_zpow_add (S : Finset ι) (d : ι → G) (e e' : ι →₀ ℤ) :
    (∏ w ∈ S, d w ^ ((e + e') w)) =
      (∏ w ∈ S, d w ^ (e w)) * (∏ w ∈ S, d w ^ (e' w)) := by
  classical
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro w _
  rw [Finsupp.add_apply, zpow_add]

/-- Negating the exponents inverts the product. -/
private lemma prod_zpow_neg (S : Finset ι) (d : ι → G) (e : ι →₀ ℤ) :
    (∏ w ∈ S, d w ^ ((-e) w)) = (∏ w ∈ S, d w ^ (e w))⁻¹ := by
  classical
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl ?_
  intro w _
  rw [Finsupp.neg_apply, zpow_neg]

theorem exists_finsupp_of_mem_closure_image {G : Type} [CommGroup G] {ι : Type} (S : Finset ι)
    (d : ι → G) {c : G} (hc : c ∈ Subgroup.closure (d '' (S : Set ι))) :
    ∃ e : ι →₀ ℤ, e.support ⊆ ↑S ∧ c = ∏ w ∈ S, d w ^ (e w) := by
  classical
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      refine ⟨Finsupp.single w 1, ?_, ?_⟩
      · intro y hy
        have h1 : y ∈ ({w} : Finset ι) := Finsupp.support_single_subset hy
        have h2 : y = w := Finset.mem_singleton.mp h1
        rw [h2]
        exact hw
      · rw [prod_zpow_single S d hw 1, zpow_one]
  | one =>
      refine ⟨0, ?_, ?_⟩
      · simp
      · simp
  | mul x y _ _ ihx ihy =>
      obtain ⟨e, he, rfl⟩ := ihx
      obtain ⟨e', he', rfl⟩ := ihy
      refine ⟨e + e', ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_union.mp (Finsupp.support_add hw) with h | h
        · exact he h
        · exact he' h
      · rw [prod_zpow_add]
  | inv x _ ih =>
      obtain ⟨e, he, rfl⟩ := ih
      refine ⟨-e, ?_, ?_⟩
      · simpa [Finsupp.support_neg] using he
      · rw [prod_zpow_neg]

end NK.CFTLib
