import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Submission.Work.BoseFixB2.Sector.secPermDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Sector.slotMap_sum_reindex`

Reindexing lemma for `slotMap`: for a permutation `σ : Equiv.Perm (Fin n)` the map
`S ↦ slotMap σ S` is a bijection of the `k`-element subsets of `{0,…,n−1}`, hence
the sum over those subsets of `f (slotMap σ S)` equals the sum of `f S`.

The proof: `slotMap σ` agrees with `Finset.image (slotMapNat σ)`, where

  `slotMapNat σ m = if h : m < n then (σ ⟨m, h⟩).val else 0`

is injective on `{0,…,n−1}` and maps `{0,…,n−1}` into itself.  Consequently
`slotMap σ` is injective on the subsets of `range n` (a `Finset` of naturals is
determined by its image under an injective-on-`range n` function, because every
element of a subset of `range n` is itself in `range n`), and it preserves
cardinality, so it maps the `k`-subsets of `range n` injectively into themselves.
Injectivity plus equal (finite) cardinalities gives surjectivity, i.e. the image of
the finset is the finset itself, and `Finset.sum_image` finishes the reindexing.
-/

namespace Work.BoseFixB2.Sector

/-- The slot map `σ` viewed as a plain function `ℕ → ℕ` (values outside
`{0,…,n−1}` are sent to `0`; irrelevant, as it is only applied to elements of
`range n`). -/
def slotMapNat {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : ℕ) : ℕ :=
  if h : m < n then (σ ⟨m, h⟩).val else 0

lemma slotMap_eq_image {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset ℕ) :
    slotMap σ S = (S ∩ Finset.range n).image (slotMapNat σ) := rfl

lemma slotMapNat_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : m < n) :
    slotMapNat σ m < n := by
  rw [slotMapNat, dif_pos hm]
  exact (σ ⟨m, hm⟩).isLt

lemma slotMapNat_injOn {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Set.InjOn (slotMapNat σ) (↑(Finset.range n) : Set ℕ) := by
  intro a ha b hb h
  rw [Finset.mem_coe, Finset.mem_range] at ha hb
  rw [slotMapNat, dif_pos ha, slotMapNat, dif_pos hb] at h
  have h2 : (⟨a, ha⟩ : Fin n) = ⟨b, hb⟩ := σ.injective (Fin.ext h)
  exact congrArg Fin.val h2

lemma mem_slotMap' {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset ℕ) (j : ℕ) :
    j ∈ slotMap σ S ↔ ∃ m ∈ S, m < n ∧ slotMapNat σ m = j := by
  rw [slotMap_eq_image, Finset.mem_image]
  constructor
  · rintro ⟨m, hm, hmj⟩
    rw [Finset.mem_inter, Finset.mem_range] at hm
    exact ⟨m, hm.1, hm.2, hmj⟩
  · rintro ⟨m, hmS, hmn, hmj⟩
    exact ⟨m, Finset.mem_inter.mpr ⟨hmS, Finset.mem_range.mpr hmn⟩, hmj⟩

/-- A subset of `range n` is determined by its image under `slotMap σ`. -/
lemma slotMap_injOn {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Set.InjOn (slotMap σ) {S : Finset ℕ | S ⊆ Finset.range n} := by
  have key : ∀ {S₁ S₂ : Finset ℕ}, S₁ ⊆ Finset.range n → S₂ ⊆ Finset.range n →
      slotMap σ S₁ = slotMap σ S₂ → S₁ ⊆ S₂ := by
    intro S₁ S₂ hS₁ hS₂ h j hj
    have hjn : j < n := Finset.mem_range.mp (hS₁ hj)
    have : slotMapNat σ j ∈ slotMap σ S₂ := by
      rw [← h]
      exact (mem_slotMap' σ S₁ (slotMapNat σ j)).mpr ⟨j, hj, hjn, rfl⟩
    obtain ⟨m, hmS₂, hmn, hmj⟩ := (mem_slotMap' σ S₂ (slotMapNat σ j)).mp this
    have hmj' : m = j :=
      slotMapNat_injOn σ (Finset.mem_range.mpr hmn) (Finset.mem_range.mpr hjn) hmj
    rwa [hmj'] at hmS₂
  intro S₁ hS₁ S₂ hS₂ h
  exact Finset.Subset.antisymm (key hS₁ hS₂ h) (key hS₂ hS₁ h.symm)

/-- `slotMap σ` preserves the cardinality of subsets of `range n`. -/
lemma card_slotMap_of_subset {n : ℕ} (σ : Equiv.Perm (Fin n)) {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) : (slotMap σ S).card = S.card := by
  rw [slotMap_eq_image, Finset.inter_eq_left.mpr hS]
  refine Finset.card_image_of_injOn fun a ha b hb h => ?_
  exact slotMapNat_injOn σ (Finset.mem_range.mpr (Finset.mem_range.mp (hS ha)))
    (Finset.mem_range.mpr (Finset.mem_range.mp (hS hb))) h

/-- `slotMap σ` maps the `k`-subsets of `range n` to `k`-subsets of `range n`. -/
lemma mem_powersetCard_slotMap {n k : ℕ} (σ : Equiv.Perm (Fin n)) {S : Finset ℕ}
    (hS : S ∈ (Finset.range n).powersetCard k) :
    slotMap σ S ∈ (Finset.range n).powersetCard k := by
  rw [Finset.mem_powersetCard] at hS ⊢
  exact ⟨slotMap_subset_range σ S, by rw [card_slotMap_of_subset σ hS.1, hS.2]⟩

theorem slotMap_sum_reindex {n k : ℕ} (σ : Equiv.Perm (Fin n))
    (f : Finset ℕ → Submission.BoseGases.X n → ℝ) :
    Finset.sum ((Finset.range n).powersetCard k) (fun S => f (Work.BoseFixB2.Sector.slotMap σ S))
      = Finset.sum ((Finset.range n).powersetCard k) f := by
  have hinj : Set.InjOn (slotMap σ)
      (↑((Finset.range n).powersetCard k) : Set (Finset ℕ)) := by
    intro a ha b hb h
    exact slotMap_injOn σ (Finset.mem_powersetCard.mp ha).1 (Finset.mem_powersetCard.mp hb).1 h
  have hsub : ((Finset.range n).powersetCard k).image (slotMap σ)
      ⊆ (Finset.range n).powersetCard k := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    exact mem_powersetCard_slotMap σ hS
  have hcard : (((Finset.range n).powersetCard k).image (slotMap σ)).card
      = ((Finset.range n).powersetCard k).card := Finset.card_image_of_injOn hinj
  have himage : ((Finset.range n).powersetCard k).image (slotMap σ)
      = (Finset.range n).powersetCard k :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  rw [← Finset.sum_image hinj, himage]

end Work.BoseFixB2.Sector
