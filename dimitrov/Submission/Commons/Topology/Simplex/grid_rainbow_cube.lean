import Mathlib
import Submission.Commons.Topology.Simplex.sperner_parity_mod2

/-!
# The grid rainbow cube

We prove `grid_rainbow_cube` via Sperner's lemma for the standard staircase triangulation of the
order polytope.
-/

namespace Commons.Topology.Simplex

noncomputable section
open Finset

/-! ## The order polytope -/

/-- Lattice points of the order polytope `0 ≤ z_0 ≤ ⋯ ≤ z_{d-1} ≤ m`, as a finite type. -/
abbrev OPt (d m : ℕ) := {z : Fin d → Fin (m+1) // ∀ i j : Fin d, i ≤ j → (z i : ℕ) ≤ (z j : ℕ)}

/-- The `t`-th vertex of the staircase cell with base `b` and direction order `σ`. -/
def vtN {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (t : Fin (d+1)) (j : Fin d) : ℕ :=
  (b.1 j : ℕ) + if (σ.symm j : ℕ) < (t : ℕ) then 1 else 0

/-- A staircase cell is valid when all its vertices lie in the order polytope. -/
def IsCell {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) : Prop :=
  (∀ t j, vtN b σ t j ≤ m) ∧ (∀ t i j, i ≤ j → vtN b σ t i ≤ vtN b σ t j)

instance {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) : Decidable (IsCell b σ) :=
  Classical.propDecidable _

instance {d m : ℕ} : DecidablePred (fun p : OPt d m × Equiv.Perm (Fin d) => IsCell p.1 p.2) :=
  fun p => Classical.propDecidable _

/-- The `t`-th vertex of a valid cell, as an order-polytope element. -/
def vert {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ) (t : Fin (d+1)) :
    OPt d m :=
  ⟨fun j => ⟨vtN b σ t j, by have := h.1 t j; omega⟩,
   by intro i j hij; exact h.2 t i j hij⟩

@[simp] lemma vert_apply {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (t : Fin (d+1)) (j : Fin d) : ((vert b σ h t).1 j : ℕ) = vtN b σ t j := rfl

/-- The vertex set of a staircase cell. -/
def cellSet {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ) :
    Finset (OPt d m) := univ.image (vert b σ h)

@[simp] lemma mem_cellSet {d m : ℕ} {b : OPt d m} {σ : Equiv.Perm (Fin d)} {h : IsCell b σ}
    {x : OPt d m} : x ∈ cellSet b σ h ↔ ∃ t, vert b σ h t = x := by
  simp [cellSet]

/-- The vertices of a cell are pairwise distinct. -/
lemma vert_injective {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ) :
    Function.Injective (vert b σ h) := by
  intro t t' ht
  have hcongr : ∀ j : Fin d, vtN b σ t j = vtN b σ t' j := by
    intro j
    have := congrArg (fun p : OPt d m => ((p.1 j : Fin (m+1)) : ℕ)) ht
    simpa using this
  rcases lt_trichotomy (t : ℕ) (t' : ℕ) with hlt | heq | hgt
  · have htd : (t : ℕ) < d := by have := t'.isLt; omega
    have h1 : vtN b σ t (σ ⟨(t:ℕ), htd⟩) = (b.1 (σ ⟨(t:ℕ), htd⟩) : ℕ) := by
      simp only [vtN]
      have hsym : (σ.symm (σ ⟨(t:ℕ), htd⟩) : ℕ) = (t:ℕ) := by simp
      rw [hsym, if_neg (lt_irrefl _), add_zero]
    have h2 : vtN b σ t' (σ ⟨(t:ℕ), htd⟩) = (b.1 (σ ⟨(t:ℕ), htd⟩) : ℕ) + 1 := by
      simp only [vtN]
      have hsym : (σ.symm (σ ⟨(t:ℕ), htd⟩) : ℕ) = (t:ℕ) := by simp
      rw [hsym, if_pos hlt]
    have := hcongr (σ ⟨(t:ℕ), htd⟩)
    rw [h1, h2] at this
    omega
  · exact Fin.ext heq
  · have htd : (t' : ℕ) < d := by have := t.isLt; omega
    have h1 : vtN b σ t' (σ ⟨(t':ℕ), htd⟩) = (b.1 (σ ⟨(t':ℕ), htd⟩) : ℕ) := by
      simp only [vtN]
      have hsym : (σ.symm (σ ⟨(t':ℕ), htd⟩) : ℕ) = (t':ℕ) := by simp
      rw [hsym, if_neg (lt_irrefl _), add_zero]
    have h2 : vtN b σ t (σ ⟨(t':ℕ), htd⟩) = (b.1 (σ ⟨(t':ℕ), htd⟩) : ℕ) + 1 := by
      simp only [vtN]
      have hsym : (σ.symm (σ ⟨(t':ℕ), htd⟩) : ℕ) = (t':ℕ) := by simp
      rw [hsym, if_pos hgt]
    have := hcongr (σ ⟨(t':ℕ), htd⟩)
    rw [h1, h2] at this
    omega

@[simp] lemma card_cellSet {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ) :
    (cellSet b σ h).card = d + 1 := by
  rw [cellSet, card_image_of_injective _ (vert_injective b σ h), card_univ, Fintype.card_fin]

/-! ## The cell complex -/

/-- The set of valid cell data, as a finite set. -/
def validSet (d m : ℕ) : Finset (OPt d m × Equiv.Perm (Fin d)) :=
  (univ : Finset (OPt d m × Equiv.Perm (Fin d))).filter (fun p => IsCell p.1 p.2)

lemma mem_validSet {d m : ℕ} {p : OPt d m × Equiv.Perm (Fin d)} :
    p ∈ validSet d m ↔ IsCell p.1 p.2 := by
  rw [validSet, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The cell complex: the set of vertex sets of valid staircase cells. -/
def Cells (d m : ℕ) : Finset (Finset (OPt d m)) :=
  (validSet d m).image (fun p => if h : IsCell p.1 p.2 then cellSet p.1 p.2 h else ∅)

lemma mem_Cells {d m : ℕ} {C : Finset (OPt d m)} :
    C ∈ Cells d m ↔ ∃ (b : OPt d m) (σ : Equiv.Perm (Fin d)), ∃ h : IsCell b σ, cellSet b σ h = C := by
  classical
  constructor
  · intro hC
    obtain ⟨p, hp, hpC⟩ := Finset.mem_image.mp hC
    have hh : IsCell p.1 p.2 := mem_validSet.mp hp
    refine ⟨p.1, p.2, hh, ?_⟩
    rw [dif_pos hh] at hpC
    exact hpC
  · rintro ⟨b, σ, h, rfl⟩
    exact Finset.mem_image.mpr ⟨(b, σ), mem_validSet.mpr h, by rw [dif_pos h]⟩

lemma card_of_mem_Cells {d m : ℕ} {C : Finset (OPt d m)} (hC : C ∈ Cells d m) :
    C.card = d + 1 := by
  rw [mem_Cells] at hC
  obtain ⟨b, σ, h, rfl⟩ := hC
  exact card_cellSet b σ h

/-! ## Order structure and cell geometry -/

instance {d m : ℕ} : PartialOrder (OPt d m) where
  le z w := ∀ j, (z.1 j : ℕ) ≤ (w.1 j : ℕ)
  le_refl z j := le_rfl
  le_trans z w v hzw hwv j := le_trans (hzw j) (hwv j)
  le_antisymm z w hzw hwz := by
    apply Subtype.ext; funext j; exact Fin.ext (le_antisymm (hzw j) (hwz j))

lemma le_def {d m : ℕ} {z w : OPt d m} : z ≤ w ↔ ∀ j, (z.1 j : ℕ) ≤ (w.1 j : ℕ) := Iff.rfl

@[simp] lemma vert_zero {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ) :
    vert b σ h 0 = b := by
  apply Subtype.ext; funext j; apply Fin.ext
  simp [vert, vtN]

lemma vtN_mono {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) {t t' : Fin (d+1)}
    (h : t ≤ t') (j : Fin d) : vtN b σ t j ≤ vtN b σ t' j := by
  simp only [vtN]
  by_cases hc : (σ.symm j : ℕ) < (t : ℕ)
  · rw [if_pos hc, if_pos (by omega)]
  · rw [if_neg hc]; split <;> omega

lemma vert_mono {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    {t t' : Fin (d+1)} (htt : t ≤ t') : vert b σ h t ≤ vert b σ h t' := by
  intro j
  exact vtN_mono b σ htt j

lemma vert_lt {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    {t t' : Fin (d+1)} (htt : t < t') : vert b σ h t < vert b σ h t' := by
  refine lt_of_le_of_ne (vert_mono b σ h htt.le) ?_
  intro heq
  exact absurd (vert_injective b σ h heq) (ne_of_lt htt)

lemma vert_le_iff {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    {t t' : Fin (d+1)} : vert b σ h t ≤ vert b σ h t' ↔ t ≤ t' := by
  constructor
  · intro hle
    by_contra hcon
    rw [not_le] at hcon
    exact (not_lt_of_ge hle) (vert_lt b σ h hcon)
  · intro htt; exact vert_mono b σ h htt

/-- The `t`-th vertex of the cell, as an integer vector. -/
def cellV {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (t : Fin (d+1)) : Fin d → ℤ :=
  fun j => (b.1 j : ℤ) + if (σ.symm j : ℕ) < (t : ℕ) then 1 else 0

lemma toZ_vert {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (t : Fin (d+1)) : (fun j => ((vert b σ h t).1 j : ℤ)) = cellV b σ t := by
  funext j
  simp only [cellV, vert_apply, vtN]
  push_cast
  ring

lemma cellV_succ {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (t : Fin d) (j : Fin d) :
    cellV b σ (Fin.succ t) j = cellV b σ (Fin.castSucc t) j + (if j = σ t then 1 else 0) := by
  have hsym : (σ.symm j : ℕ) = (t : ℕ) ↔ j = σ t := by
    constructor
    · intro h
      have ht : σ.symm j = t := Fin.ext h
      exact (Equiv.apply_symm_apply σ j).symm.trans (by rw [ht])
    · intro h; rw [h]; simp
  simp only [cellV, Fin.val_succ, Fin.val_castSucc]
  by_cases h : j = σ t
  · rw [if_pos h]
    have hpos : (σ.symm j : ℕ) = (t : ℕ) := hsym.mpr h
    rw [hpos]; norm_num
  · have hpos : (σ.symm j : ℕ) ≠ t := fun hh => h (hsym.mp hh)
    rw [if_neg h]
    rcases lt_or_gt_of_ne hpos with h2 | h3
    · rw [if_pos (by omega : (σ.symm j : ℕ) < (t:ℕ)+1), if_pos h2]; ring
    · rw [if_neg (by omega : ¬ (σ.symm j : ℕ) < (t:ℕ)+1),
          if_neg (by omega : ¬ (σ.symm j : ℕ) < (t:ℕ))]; ring


/-! ## Facets and their enumeration -/

/-- The position, inside the whole cell, of the `i`-th vertex (in increasing order) of the
facet obtained by deleting the `s`-th vertex. -/
def cIdxN {d : ℕ} (s : Fin (d+1)) (i : Fin d) : ℕ :=
  if (i : ℕ) < (s : ℕ) then (i : ℕ) else (i : ℕ) + 1

lemma cIdxN_lt {d : ℕ} (s : Fin (d+1)) (i : Fin d) : cIdxN s i < d + 1 := by
  unfold cIdxN; split <;> omega

lemma cIdxN_strict {d : ℕ} (s : Fin (d+1)) : StrictMono (cIdxN s) := by
  intro i j hij
  unfold cIdxN
  split_ifs <;> omega

lemma cIdxN_ne {d : ℕ} (s : Fin (d+1)) (i : Fin d) : cIdxN s i ≠ (s : ℕ) := by
  unfold cIdxN; split_ifs <;> omega

lemma cIdxN_inj {d : ℕ} (s : Fin (d+1)) : Function.Injective (cIdxN s) :=
  (cIdxN_strict s).injective

lemma cIdxN_surj {d : ℕ} (s : Fin (d+1)) {k : ℕ} (hk : k < d + 1) (hne : k ≠ (s : ℕ)) :
    ∃ i : Fin d, cIdxN s i = k := by
  by_cases h : k < (s : ℕ)
  · refine ⟨⟨k, by omega⟩, ?_⟩
    simp only [cIdxN, Fin.val_mk]
    rw [if_pos h]
  · refine ⟨⟨k - 1, by omega⟩, ?_⟩
    simp only [cIdxN, Fin.val_mk]
    rw [if_neg (by omega)]
    omega

/-- Increasing enumeration of the facet obtained by deleting the `s`-th vertex of a cell. -/
def facetEnum {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ) (s : Fin (d+1)) :
    Fin d → OPt d m :=
  fun i => vert b σ h ⟨cIdxN s i, cIdxN_lt s i⟩

lemma facetEnum_strict {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (s : Fin (d+1)) : ∀ i j, i < j → facetEnum b σ h s i < facetEnum b σ h s j := by
  intro i j hij
  exact vert_lt b σ h (by exact_mod_cast cIdxN_strict s hij)

lemma facetEnum_image {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (s : Fin (d+1)) :
    (univ.image (facetEnum b σ h s)) = (cellSet b σ h).erase (vert b σ h s) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, mem_cellSet]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨?_, ⟨⟨cIdxN s i, cIdxN_lt s i⟩, rfl⟩⟩
    intro hc
    exact cIdxN_ne s i (congrArg Fin.val (vert_injective b σ h hc))
  · rintro ⟨hne, t, ht⟩
    subst ht
    have hts : t ≠ s := fun hh => hne (by rw [hh])
    have hval : (t : ℕ) ≠ (s : ℕ) := fun hh => hts (Fin.ext hh)
    obtain ⟨i, hi⟩ := cIdxN_surj s t.isLt hval
    refine ⟨i, ?_⟩
    simp only [facetEnum]
    have hfin : (⟨cIdxN s i, cIdxN_lt s i⟩ : Fin (d+1)) = t := Fin.ext hi
    rw [hfin]


/-! ## The coordinate-sum invariant and enumeration uniqueness -/

lemma card_filter_val_lt {d : ℕ} {s : ℕ} (hs : s ≤ d) :
    ((univ : Finset (Fin d)).filter (fun k : Fin d => (k : ℕ) < s)).card = s := by
  have h : ((univ : Finset (Fin d)).filter (fun k : Fin d => (k : ℕ) < s)).card
      = (Finset.range s).card := by
    refine Finset.card_bij (fun k _ => (k : ℕ)) ?_ ?_ ?_
    · intro k hk; rw [Finset.mem_filter] at hk; rw [Finset.mem_range]; exact hk.2
    · intro k1 _ k2 _ h; exact Fin.ext h
    · intro j hj; rw [Finset.mem_range] at hj
      exact ⟨⟨j, by omega⟩, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj⟩, rfl⟩
  rwa [Finset.card_range] at h

/-- Sum of the coordinates of an order-polytope point. -/
def wsum {d m : ℕ} (x : OPt d m) : ℕ := ∑ j, (x.1 j : ℕ)

lemma wsum_vert {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (t : Fin (d+1)) : wsum (vert b σ h t) = (∑ j, (b.1 j : ℕ)) + (t : ℕ) := by
  have ht : (t : ℕ) ≤ d := by have := t.isLt; omega
  have hset : ((univ : Finset (Fin d)).filter (fun j : Fin d => (σ.symm j : ℕ) < (t : ℕ)))
      = ((univ : Finset (Fin d)).filter (fun i : Fin d => (i : ℕ) < (t : ℕ))).image σ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj
      exact ⟨σ.symm j, hj, by simp⟩
    · rintro ⟨i, hi, rfl⟩
      simpa using hi
  have hcard : ((univ : Finset (Fin d)).filter (fun j : Fin d => (σ.symm j : ℕ) < (t : ℕ))).card
      = (t : ℕ) := by
    rw [hset, Finset.card_image_of_injective _ σ.injective, card_filter_val_lt ht]
  simp only [wsum, vert_apply, vtN, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.card_filter, hcard]

/-- If two strictly increasing enumerations have the same image, they are equal. -/
lemma strictMono_enum_eq {d : ℕ} {α : Type*} [PartialOrder α] [DecidableEq α]
    (u u' : Fin d → α)
    (hu : ∀ i j, i < j → u i < u j) (hu' : ∀ i j, i < j → u' i < u' j)
    (himg : (univ.image u) = (univ.image u')) : u = u' := by
  classical
  have hmem : ∀ i, u' i ∈ (univ.image u) := fun i => by
    rw [himg]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hmemu : ∀ i, u i ∈ (univ.image u) := fun i =>
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hrank : ∀ a b : α, a ∈ (univ.image u) → b ∈ (univ.image u) →
      ((univ.image u).filter (fun w => w < a)).card = ((univ.image u).filter (fun w => w < b)).card →
      a = b := by
    intro a b ha hb hab
    by_contra hne
    have hcomp : a < b ∨ b < a := by
      obtain ⟨ia, -, hia⟩ := Finset.mem_image.mp ha
      obtain ⟨ib, -, hib⟩ := Finset.mem_image.mp hb
      rcases lt_trichotomy ia ib with h | h | h
      · exact Or.inl (by rw [← hia, ← hib]; exact hu ia ib h)
      · exact absurd (by rw [← hia, ← hib, h] : a = b) hne
      · exact Or.inr (by rw [← hia, ← hib]; exact hu ib ia h)
    rcases hcomp with h | h
    · have hmemab : a ∈ (univ.image u).filter (fun w => w < b) :=
        Finset.mem_filter.mpr ⟨ha, h⟩
      have hsub : (univ.image u).filter (fun w => w < a)
          ⊆ (univ.image u).filter (fun w => w < b) := by
        intro w hw; rw [Finset.mem_filter] at hw ⊢
        exact ⟨hw.1, lt_trans hw.2 h⟩
      have hne' : (univ.image u).filter (fun w => w < a) ≠ (univ.image u).filter (fun w => w < b) := by
        intro heq
        have hmemfa : a ∈ (univ.image u).filter (fun w => w < a) := heq.symm ▸ hmemab
        exact (lt_irrefl a) (Finset.mem_filter.mp hmemfa).2
      have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne'⟩)
      omega
    · have hmemab : b ∈ (univ.image u).filter (fun w => w < a) :=
        Finset.mem_filter.mpr ⟨hb, h⟩
      have hsub : (univ.image u).filter (fun w => w < b)
          ⊆ (univ.image u).filter (fun w => w < a) := by
        intro w hw; rw [Finset.mem_filter] at hw ⊢
        exact ⟨hw.1, lt_trans hw.2 h⟩
      have hne' : (univ.image u).filter (fun w => w < b) ≠ (univ.image u).filter (fun w => w < a) := by
        intro heq
        have hmemfb : b ∈ (univ.image u).filter (fun w => w < b) := heq.symm ▸ hmemab
        exact (lt_irrefl b) (Finset.mem_filter.mp hmemfb).2
      have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne'⟩)
      omega
  have hcount : ∀ (v : Fin d → α), (∀ i j, i < j → v i < v j) →
      (univ.image v) = (univ.image u) → ∀ i : Fin d,
      ((univ.image u).filter (fun w => w < v i)).card = (i : ℕ) := by
    intro v hv himgv i
    have hinj : Function.Injective v := fun a b hab => by
      rcases lt_trichotomy a b with h | h | h
      · exact absurd hab (ne_of_lt (hv a b h))
      · exact h
      · exact absurd hab.symm (ne_of_lt (hv b a h))
    have hset : (univ.image u).filter (fun w => w < v i)
        = (univ.image v).filter (fun w => w < v i) := by rw [← himgv]
    rw [hset]
    have hset2 : (univ.image v).filter (fun w => w < v i) = (Finset.Iio i).image v := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Iio]
      constructor
      · rintro ⟨⟨j, hvj⟩, hj⟩
        refine ⟨j, ?_, hvj⟩
        rcases lt_trichotomy j i with h | h | h
        · exact h
        · subst h; rw [hvj] at hj; exact absurd hj (lt_irrefl _)
        · have hvw : v i < w := by rw [← hvj]; exact hv i j h
          exact absurd hvw (not_lt_of_ge hj.le)
      · rintro ⟨j, hj, hvj⟩
        exact ⟨⟨j, hvj⟩, by rw [← hvj]; exact hv j i hj⟩
    rw [hset2, Finset.card_image_of_injective _ hinj, Fin.card_Iio i]
  funext i
  exact hrank (u i) (u' i) (hmemu i) (hmem i)
    (by rw [hcount u hu rfl i, hcount u' hu' himg.symm i])


/-! ## Step vectors -/

/-- The `j`-th elementary vector. -/
def evec {d : ℕ} (j : Fin d) : Fin d → ℤ := fun i => if i = j then 1 else 0

lemma evec_inj {d : ℕ} {i j : Fin d} (h : evec i = evec j) : i = j := by
  by_contra hne
  have hh := congrFun h i
  have h1 : evec i i = (1 : ℤ) := by simp [evec]
  have h2 : evec j i = (0 : ℤ) := by simp [evec, hne]
  rw [h1, h2] at hh
  exact one_ne_zero hh

lemma cellV_sub_succ {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (t : Fin d) :
    (fun j => cellV b σ (Fin.succ t) j - cellV b σ (Fin.castSucc t) j) = evec (σ t) := by
  funext j
  rw [cellV_succ]
  simp only [evec]
  ring

lemma vert_step {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ) (t : Fin d) :
    (fun j => ((vert b σ h (Fin.succ t)).1 j : ℤ) - ((vert b σ h (Fin.castSucc t)).1 j : ℤ))
      = evec (σ t) := by
  funext j
  have h1 := congrFun (toZ_vert b σ h (Fin.succ t)) j
  have h2 := congrFun (toZ_vert b σ h (Fin.castSucc t)) j
  rw [h1, h2]
  exact congrFun (cellV_sub_succ b σ t) j

/-- Difference of the index sequence at position `a`. -/
lemma cIdxN_step {d : ℕ} (s : Fin (d+1)) (a : ℕ) (ha : a + 1 < d) :
    cIdxN s ⟨a+1, ha⟩ - cIdxN s ⟨a, by omega⟩ = if (a + 1 = (s : ℕ)) then 2 else 1 := by
  unfold cIdxN
  simp only [Fin.val_mk]
  split_ifs <;> omega


/-- A `d`-element subset of a `(d+1)`-vertex cell is that cell with one vertex deleted. -/
lemma exists_missing {d m : ℕ} {b : OPt d m} {σ : Equiv.Perm (Fin d)} {h : IsCell b σ}
    {f : Finset (OPt d m)} (hf : f ⊆ cellSet b σ h) (hfc : f.card = d) :
    ∃ s : Fin (d+1), f = (cellSet b σ h).erase (vert b σ h s) := by
  have hcard := card_cellSet b σ h
  have hdiffcard : (cellSet b σ h \ f).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hf, hcard, hfc]; omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdiffcard
  have hvmem : v ∈ cellSet b σ h \ f := by rw [hv]; exact Finset.mem_singleton_self v
  obtain ⟨hvc, hvf⟩ := Finset.mem_sdiff.mp hvmem
  obtain ⟨s, hs⟩ := mem_cellSet.mp hvc
  refine ⟨s, ?_⟩
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_erase]
    refine ⟨?_, hf hx⟩
    intro hxs
    exact hvf ((hs.symm.trans hxs.symm) ▸ hx)
  · intro x hx
    rw [Finset.mem_erase] at hx
    by_contra hxf
    have : x ∈ cellSet b σ h \ f := Finset.mem_sdiff.mpr ⟨hx.2, hxf⟩
    rw [hv, Finset.mem_singleton] at this
    exact hx.1 (hs.trans this.symm).symm


/-- Integer lift of an order-polytope point. -/
def toZ {d m : ℕ} (x : OPt d m) : Fin d → ℤ := fun j => (x.1 j : ℤ)

lemma toZ_injective {d m : ℕ} : Function.Injective (toZ (d:=d) (m:=m)) := by
  intro x y hxy
  apply Subtype.ext; funext j; apply Fin.ext
  have := congrFun hxy j
  simpa [toZ] using this

@[simp] lemma toZ_apply {d m : ℕ} (x : OPt d m) (j : Fin d) : toZ x j = (x.1 j : ℤ) := rfl

lemma cellV_pred {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (s : Fin (d+1))
    (hs : 1 ≤ (s : ℕ)) :
    (fun j => cellV b σ s j - cellV b σ ⟨(s:ℕ)-1, by have := s.isLt; omega⟩ j)
      = evec (σ ⟨(s:ℕ)-1, by have := s.isLt; omega⟩) := by
  funext j
  simp only [cellV, evec]
  by_cases h : (σ.symm j : ℕ) < (s:ℕ)-1
  · have hne : ¬ (j = σ ⟨(s:ℕ)-1, by have := s.isLt; omega⟩) := by
      intro hh; rw [hh] at h; simp only [Equiv.symm_apply_apply, Fin.val_mk] at h; omega
    rw [if_pos (by omega : (σ.symm j : ℕ) < (s:ℕ)), if_pos h, if_neg hne]
    ring
  · by_cases h2 : (σ.symm j : ℕ) = (s:ℕ)-1
    · have hj : j = σ ⟨(s:ℕ)-1, by have := s.isLt; omega⟩ :=
        (Equiv.apply_symm_apply σ j).symm.trans (congrArg σ (Fin.ext h2))
      rw [if_pos (by omega : (σ.symm j : ℕ) < (s:ℕ)), if_neg h, if_pos hj]
      ring
    · have hne : ¬ (j = σ ⟨(s:ℕ)-1, by have := s.isLt; omega⟩) :=
        fun hh => h2 (by rw [hh]; simp)
      rw [if_neg (by omega : ¬ ((σ.symm j : ℕ) < (s:ℕ))), if_neg h, if_neg hne]
      ring

lemma vert_pred {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ) (s : Fin (d+1))
    (hs : 1 ≤ (s : ℕ)) :
    (fun j => ((vert b σ h s).1 j : ℤ) - ((vert b σ h ⟨(s:ℕ)-1, by have := s.isLt; omega⟩).1 j : ℤ))
      = evec (σ ⟨(s:ℕ)-1, by have := s.isLt; omega⟩) := by
  funext j
  have h1 := congrFun (toZ_vert b σ h s) j
  have h2 := congrFun (toZ_vert b σ h ⟨(s:ℕ)-1, by have := s.isLt; omega⟩) j
  rw [h1, h2]
  exact congrFun (cellV_pred b σ s hs) j

/-- Equality of the coordinate-sum index relation. -/
lemma facetEnum_wsum {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (s : Fin (d+1)) {b1 : OPt d m} {σ1 : Equiv.Perm (Fin d)} {h1 : IsCell b1 σ1}
    {s1 : Fin (d+1)} (hu : facetEnum b σ h s = facetEnum b1 σ1 h1 s1) (i : Fin d) :
    (∑ j, (b.1 j : ℕ)) + cIdxN s i = (∑ j, (b1.1 j : ℕ)) + cIdxN s1 i := by
  have hcongr := congrFun hu i
  have hw := congrArg wsum hcongr
  rw [show wsum (facetEnum b σ h s i) = (∑ j, (b.1 j : ℕ)) + cIdxN s i
        from wsum_vert b σ h ⟨cIdxN s i, cIdxN_lt s i⟩,
      show wsum (facetEnum b1 σ1 h1 s1 i) = (∑ j, (b1.1 j : ℕ)) + cIdxN s1 i
        from wsum_vert b1 σ1 h1 ⟨cIdxN s1 i, cIdxN_lt s1 i⟩] at hw
  exact hw

lemma facetEnum_step {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (s : Fin (d+1)) {b1 : OPt d m} {σ1 : Equiv.Perm (Fin d)} {h1 : IsCell b1 σ1}
    {s1 : Fin (d+1)} (hu : facetEnum b σ h s = facetEnum b1 σ1 h1 s1)
    (a : ℕ) (ha : a + 1 < d) :
    cIdxN s ⟨a+1, ha⟩ - cIdxN s ⟨a, by omega⟩
      = cIdxN s1 ⟨a+1, ha⟩ - cIdxN s1 ⟨a, by omega⟩ := by
  have e1 := facetEnum_wsum b σ h s hu ⟨a+1, ha⟩
  have e2 := facetEnum_wsum b σ h s hu ⟨a, by omega⟩
  have hd : (cIdxN s ⟨a+1, ha⟩ : ℤ) - (cIdxN s ⟨a, by omega⟩ : ℤ)
      = (cIdxN s1 ⟨a+1, ha⟩ : ℤ) - (cIdxN s1 ⟨a, by omega⟩ : ℤ) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) e1
    have := congrArg (fun x : ℕ => (x : ℤ)) e2
    omega
  omega


lemma cellV_zero {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) :
    cellV b σ 0 = toZ b := by
  funext j; simp [cellV, toZ]

lemma cellV_last {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) :
    cellV b σ (Fin.last d) = fun j => (b.1 j : ℤ) + 1 := by
  funext j
  simp only [cellV, Fin.val_last]
  rw [if_pos (σ.symm j).isLt]

/-- If two cells' vertices agree away from the base, their vertex functions agree. -/
lemma cellV_eq_of_agree {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d))
    (b1 : OPt d m) (σ1 : Equiv.Perm (Fin d))
    (h : ∀ t : Fin (d+1), (t : ℕ) ≠ 0 → cellV b σ t = cellV b1 σ1 t) :
    cellV b σ = cellV b1 σ1 := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    funext t j; exact Fin.elim0 j
  · funext t
    rcases Nat.eq_zero_or_pos (t : ℕ) with ht0 | htpos
    · have ht : t = 0 := Fin.ext ht0
      rw [ht, cellV_zero, cellV_zero]
      funext j
      show (b.1 j : ℤ) = (b1.1 j : ℤ)
      have hlast := h (Fin.last d) (by simp [Fin.val_last]; omega)
      rw [cellV_last, cellV_last] at hlast
      have hthis : (b.1 j : ℤ) + 1 = (b1.1 j : ℤ) + 1 := by simpa using congrFun hlast j
      omega
    · exact h t (by omega)

/-- If the enumerations of a facet agree and the gap index is the same, the vertex functions agree
away from the gap. -/
lemma vert_eq_of_facetEnum_eq {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (s : Fin (d+1)) {b1 : OPt d m} {σ1 : Equiv.Perm (Fin d)} {h1 : IsCell b1 σ1}
    (hu : facetEnum b σ h s = facetEnum b1 σ1 h1 s) :
    ∀ t : Fin (d+1), t ≠ s → vert b σ h t = vert b1 σ1 h1 t := by
  intro t htne
  have htne' : (t:ℕ) ≠ (s:ℕ) := fun hh => htne (Fin.ext hh)
  obtain ⟨i, hi⟩ := cIdxN_surj s t.isLt htne'
  have := congrFun hu i
  have hti : (⟨cIdxN s i, cIdxN_lt s i⟩ : Fin (d+1)) = t := Fin.ext hi
  rw [show facetEnum b σ h s i = vert b σ h t from by simp only [facetEnum]; rw [hti],
      show facetEnum b1 σ1 h1 s i = vert b1 σ1 h1 t from by simp only [facetEnum]; rw [hti]] at this
  exact this

lemma cIdxN_of_zero {d : ℕ} {s : Fin (d+1)} (hs : (s:ℕ) = 0) (i : Fin d) :
    cIdxN s i = (i:ℕ) + 1 := by
  simp only [cIdxN]; rw [if_neg (by omega)]

lemma cIdxN_of_last {d : ℕ} {s : Fin (d+1)} (hs : (s:ℕ) = d) (i : Fin d) :
    cIdxN s i = (i:ℕ) := by
  simp only [cIdxN]; rw [if_pos (by omega)]

/-- Indexed agreement of vertex functions, from the equality of the facet enumerations. -/
lemma cellV_index_eq {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    {b1 : OPt d m} {σ1 : Equiv.Perm (Fin d)} {h1 : IsCell b1 σ1} {s s1 : Fin (d+1)}
    (hu : facetEnum b σ h s = facetEnum b1 σ1 h1 s1) (i : Fin d) :
    cellV b σ ⟨cIdxN s i, cIdxN_lt s i⟩ = cellV b1 σ1 ⟨cIdxN s1 i, cIdxN_lt s1 i⟩ := by
  have hh := congrFun hu i
  simp only [facetEnum] at hh
  rw [← toZ_vert b σ h ⟨cIdxN s i, cIdxN_lt s i⟩,
      ← toZ_vert b1 σ1 h1 ⟨cIdxN s1 i, cIdxN_lt s1 i⟩]
  exact congrArg toZ hh

/-- Two permutations agreeing off `{a,b}` differ at `a` only by sending `a` to `σ a` or `σ b`. -/
lemma sigma_apply_mem {d : ℕ} (σ σ1 : Equiv.Perm (Fin d)) {a b : Fin d}
    (h : ∀ t, t ≠ a → t ≠ b → σ1 t = σ t) : σ1 a = σ a ∨ σ1 a = σ b := by
  obtain ⟨t, ht⟩ := σ.surjective (σ1 a)
  rcases eq_or_ne t a with rfl | hta
  · exact Or.inl ht.symm
  · rcases eq_or_ne t b with rfl | htb
    · exact Or.inr ht.symm
    · exfalso
      have hh := h t hta htb
      rw [ht] at hh
      exact hta (σ1.injective hh)

lemma perm_eq_of_agree_off_one {d : ℕ} (σ σ1 : Equiv.Perm (Fin d)) {a : Fin d}
    (h : ∀ t, t ≠ a → σ1 t = σ t) : σ1 = σ := by
  have hmem := sigma_apply_mem σ σ1 (a := a) (b := a) (fun t h1 _ => h t h1)
  apply Equiv.ext; intro t
  rcases eq_or_ne t a with rfl | ht
  · rcases hmem with hh | hh <;> exact hh
  · exact h t ht

/-- Shift relation for the `s = 0` facet: the vertex functions agree after shifting the index. -/
lemma cellV_shift_succ {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    {b1 : OPt d m} {σ1 : Equiv.Perm (Fin d)} {h1 : IsCell b1 σ1} {s s1 : Fin (d+1)}
    (hs : (s:ℕ) = 0) (hs1 : (s1:ℕ) = d)
    (hu : facetEnum b σ h s = facetEnum b1 σ1 h1 s1) (i : Fin d) :
    cellV b1 σ1 ⟨(i:ℕ), by have := i.isLt; omega⟩ = cellV b σ ⟨(i:ℕ)+1, by have := i.isLt; omega⟩ := by
  have hh := cellV_index_eq b σ h hu i
  rw [show (⟨cIdxN s i, cIdxN_lt s i⟩ : Fin (d+1)) = ⟨(i:ℕ)+1, by have := i.isLt; omega⟩ from by
        apply Fin.ext; simp only [cIdxN]; rw [if_neg (by omega)],
      show (⟨cIdxN s1 i, cIdxN_lt s1 i⟩ : Fin (d+1)) = ⟨(i:ℕ), by have := i.isLt; omega⟩ from by
        apply Fin.ext; simp only [cIdxN]; rw [if_pos (by omega)]] at hh
  exact hh.symm

/-- Shift relation for the `s = d` facet: the vertex functions agree after shifting the index. -/
lemma cellV_shift_pred {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    {b1 : OPt d m} {σ1 : Equiv.Perm (Fin d)} {h1 : IsCell b1 σ1} {s s1 : Fin (d+1)}
    (hs : (s:ℕ) = d) (hs1 : (s1:ℕ) = 0)
    (hu : facetEnum b σ h s = facetEnum b1 σ1 h1 s1) (i : Fin d) :
    cellV b1 σ1 ⟨(i:ℕ)+1, by have := i.isLt; omega⟩ = cellV b σ ⟨(i:ℕ), by have := i.isLt; omega⟩ := by
  have hh := cellV_index_eq b σ h hu i
  rw [show (⟨cIdxN s i, cIdxN_lt s i⟩ : Fin (d+1)) = ⟨(i:ℕ), by have := i.isLt; omega⟩ from by
        apply Fin.ext; simp only [cIdxN]; rw [if_pos (by omega)],
      show (⟨cIdxN s1 i, cIdxN_lt s1 i⟩ : Fin (d+1)) = ⟨(i:ℕ)+1, by have := i.isLt; omega⟩ from by
        apply Fin.ext; simp only [cIdxN]; rw [if_neg (by omega)]] at hh
  exact hh.symm

/-- Agreement of vertex functions yields equality of the cells. -/
lemma cellSet_eq_of_cellV_eq {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (b1 : OPt d m) (σ1 : Equiv.Perm (Fin d)) (h1 : IsCell b1 σ1)
    (hcv : cellV b σ = cellV b1 σ1) : cellSet b σ h = cellSet b1 σ1 h1 := by
  rw [cellSet, cellSet]
  congr 1
  funext t
  apply toZ_injective
  rw [show toZ (vert b σ h t) = cellV b σ t from toZ_vert b σ h t,
      show toZ (vert b1 σ1 h1 t) = cellV b1 σ1 t from toZ_vert b1 σ1 h1 t, hcv]

/-- Agreement away from the top vertex forces equality of the vertex functions. -/
lemma cellV_eq_of_agree_last {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d))
    (b1 : OPt d m) (σ1 : Equiv.Perm (Fin d))
    (h : ∀ t : Fin (d+1), (t : ℕ) ≠ d → cellV b σ t = cellV b1 σ1 t) :
    cellV b σ = cellV b1 σ1 := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0; funext t j; exact Fin.elim0 j
  · funext t
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ t.isLt) with ht | ht
    · have htd : t = Fin.last d := Fin.ext ht
      rw [htd, cellV_last, cellV_last]
      funext j
      have h0 := h 0 (by simp; omega)
      rw [cellV_zero, cellV_zero] at h0
      have := congrFun h0 j
      simp only [toZ_apply] at this
      omega
    · exact h t (by omega)

/-- If two cells share the facet `f` and both differ from the reference cell, they coincide. -/
lemma facetshare_subsingleton {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (s : Fin (d+1)) {C1 C2 : Finset (OPt d m)} (hC1 : C1 ∈ Cells d m) (hC2 : C2 ∈ Cells d m)
    (hf1 : (cellSet b σ h).erase (vert b σ h s) ⊆ C1)
    (hf2 : (cellSet b σ h).erase (vert b σ h s) ⊆ C2)
    (hne1 : C1 ≠ cellSet b σ h) (hne2 : C2 ≠ cellSet b σ h) : C1 = C2 := by
  classical
  obtain ⟨b1, σ1, h1, hC1'⟩ := mem_Cells.mp hC1
  obtain ⟨b2, σ2, h2, hC2'⟩ := mem_Cells.mp hC2
  rw [← hC1'] at hne1
  rw [← hC2'] at hne2
  rw [← hC1', ← hC2']
  set f := (cellSet b σ h).erase (vert b σ h s) with hfdef
  have hcellmem : vert b σ h s ∈ cellSet b σ h := Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
  have hfcard : f.card = d := by
    rw [hfdef, Finset.card_erase_of_mem hcellmem, card_cellSet]; omega
  have hf1' : f ⊆ cellSet b1 σ1 h1 := by rw [hfdef]; exact hC1'.symm ▸ hf1
  have hf2' : f ⊆ cellSet b2 σ2 h2 := by rw [hfdef]; exact hC2'.symm ▸ hf2
  obtain ⟨s1, hs1⟩ := exists_missing hf1' hfcard
  obtain ⟨s2, hs2⟩ := exists_missing hf2' hfcard
  have himg1 : (univ.image (facetEnum b σ h s)) = (univ.image (facetEnum b1 σ1 h1 s1)) := by
    rw [facetEnum_image, facetEnum_image, ← hfdef]; exact hs1
  have hueq1 : facetEnum b σ h s = facetEnum b1 σ1 h1 s1 :=
    strictMono_enum_eq _ _ (facetEnum_strict b σ h s) (facetEnum_strict b1 σ1 h1 s1) himg1
  have himg2 : (univ.image (facetEnum b σ h s)) = (univ.image (facetEnum b2 σ2 h2 s2)) := by
    rw [facetEnum_image, facetEnum_image, ← hfdef]; exact hs2
  have hueq2 : facetEnum b σ h s = facetEnum b2 σ2 h2 s2 :=
    strictMono_enum_eq _ _ (facetEnum_strict b σ h s) (facetEnum_strict b2 σ2 h2 s2) himg2
  -- It suffices to show the two vertex functions agree.
  have hstep1 : ∀ (a : ℕ) (ha : a + 1 < d),
      (a + 1 = (s:ℕ)) ↔ (a + 1 = (s1:ℕ)) := by
    intro a ha
    have h1 := facetEnum_step b σ h s hueq1 a ha
    rw [cIdxN_step s a ha, cIdxN_step s1 a ha] at h1
    constructor
    · intro hh; rw [if_pos hh] at h1
      by_contra hc; rw [if_neg hc] at h1; omega
    · intro hh; rw [if_pos hh] at h1
      by_contra hc; rw [if_neg hc] at h1; omega
  have hstep2 : ∀ (a : ℕ) (ha : a + 1 < d),
      (a + 1 = (s:ℕ)) ↔ (a + 1 = (s2:ℕ)) := by
    intro a ha
    have h1 := facetEnum_step b σ h s hueq2 a ha
    rw [cIdxN_step s a ha, cIdxN_step s2 a ha] at h1
    constructor
    · intro hh; rw [if_pos hh] at h1
      by_contra hc; rw [if_neg hc] at h1; omega
    · intro hh; rw [if_pos hh] at h1
      by_contra hc; rw [if_neg hc] at h1; omega
  -- The gap indices s1, s2 relative to s.
  have key1 : (s1:ℕ) = (s:ℕ) ∨ ((s:ℕ) = 0 ∧ (s1:ℕ) = d) ∨ ((s:ℕ) = d ∧ (s1:ℕ) = 0) := by
    rcases Nat.eq_zero_or_pos (s:ℕ) with hs0 | hspos
    · rcases Nat.eq_zero_or_pos (s1:ℕ) with h10 | h1pos
      · exact Or.inl (by omega)
      · right; left
        refine ⟨hs0, ?_⟩
        by_contra hnd
        have hnd' : (s1:ℕ) ≠ d := hnd
        have h1d : (s1:ℕ) < d := by have := s1.isLt; omega
        have := (hstep1 ((s1:ℕ)-1) (by omega)).mpr (by omega)
        omega
    · rcases eq_or_lt_of_le (show (s:ℕ) ≤ d by have := s.isLt; omega) with hsd | hslt
      · by_cases h10 : (s1:ℕ) = 0
        · exact Or.inr (Or.inr ⟨hsd, h10⟩)
        · left
          by_contra hnd
          have hnd' : (s1:ℕ) ≠ d := fun hh => hnd (by rw [hh, hsd])
          have h1d : (s1:ℕ) < d := by have := s1.isLt; omega
          have := (hstep1 ((s1:ℕ)-1) (by omega)).mpr (by omega)
          omega
      · left
        have := (hstep1 ((s:ℕ)-1) (by omega)).mp (by omega)
        omega
  have key2 : (s2:ℕ) = (s:ℕ) ∨ ((s:ℕ) = 0 ∧ (s2:ℕ) = d) ∨ ((s:ℕ) = d ∧ (s2:ℕ) = 0) := by
    rcases Nat.eq_zero_or_pos (s:ℕ) with hs0 | hspos
    · rcases Nat.eq_zero_or_pos (s2:ℕ) with h10 | h1pos
      · exact Or.inl (by omega)
      · right; left
        refine ⟨hs0, ?_⟩
        by_contra hnd
        have hnd' : (s2:ℕ) ≠ d := hnd
        have h1d : (s2:ℕ) < d := by have := s2.isLt; omega
        have := (hstep2 ((s2:ℕ)-1) (by omega)).mpr (by omega)
        omega
    · rcases eq_or_lt_of_le (show (s:ℕ) ≤ d by have := s.isLt; omega) with hsd | hslt
      · by_cases h10 : (s2:ℕ) = 0
        · exact Or.inr (Or.inr ⟨hsd, h10⟩)
        · left
          by_contra hnd
          have hnd' : (s2:ℕ) ≠ d := fun hh => hnd (by rw [hh, hsd])
          have h1d : (s2:ℕ) < d := by have := s2.isLt; omega
          have := (hstep2 ((s2:ℕ)-1) (by omega)).mpr (by omega)
          omega
      · left
        have := (hstep2 ((s:ℕ)-1) (by omega)).mp (by omega)
        omega
  -- If the gap index equals `s`, the enumerations force agreement off `s`.
  have agree_off : ∀ (b' : OPt d m) (σ' : Equiv.Perm (Fin d)) (h' : IsCell b' σ') (t' : Fin (d+1)),
      (t':ℕ) = (s:ℕ) → facetEnum b σ h s = facetEnum b' σ' h' t' →
      ∀ t : Fin (d+1), t ≠ s → cellV b σ t = cellV b' σ' t := by
    intro b' σ' h' t' ht' hu t htne
    have ht'eq : t' = s := Fin.ext ht'
    rw [ht'eq] at hu
    have htne' : (t:ℕ) ≠ (s:ℕ) := fun hh => htne (Fin.ext hh)
    obtain ⟨i, hi⟩ := cIdxN_surj s t.isLt htne'
    have hcongr := congrFun hu i
    have hti : (⟨cIdxN s i, cIdxN_lt s i⟩ : Fin (d+1)) = t := Fin.ext hi
    simp only [facetEnum] at hcongr
    rw [hti] at hcongr
    rw [← toZ_vert b σ h t, ← toZ_vert b' σ' h' t]
    exact congrArg toZ hcongr
  have hcv : cellV b1 σ1 = cellV b2 σ2 := by
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0; funext t j; exact Fin.elim0 j
    rcases Nat.eq_zero_or_pos (s:ℕ) with hs0 | hspos
    · -- s = 0
      have hs1d : (s1:ℕ) = d := by
        rcases key1 with k | ⟨k, k'⟩ | ⟨k, k'⟩
        · exfalso; apply hne1
          have hoff := agree_off b1 σ1 h1 s1 (by omega) hueq1
          have heq : cellV b σ = cellV b1 σ1 := by
            apply cellV_eq_of_agree; intro t ht
            exact hoff t (by intro hh; exact ht (by rw [hh, hs0]))
          exact (cellSet_eq_of_cellV_eq b σ h b1 σ1 h1 heq).symm
        · exact k'
        · omega
      have hs2d : (s2:ℕ) = d := by
        rcases key2 with k | ⟨k, k'⟩ | ⟨k, k'⟩
        · exfalso; apply hne2
          have hoff := agree_off b2 σ2 h2 s2 (by omega) hueq2
          have heq : cellV b σ = cellV b2 σ2 := by
            apply cellV_eq_of_agree; intro t ht
            exact hoff t (by intro hh; exact ht (by rw [hh, hs0]))
          exact (cellSet_eq_of_cellV_eq b σ h b2 σ2 h2 heq).symm
        · exact k'
        · omega
      have e1 : toZ b1 = cellV b σ ⟨1, by omega⟩ := by
        have hh := cellV_shift_succ b σ h hs0 hs1d hueq1 (⟨0, by omega⟩ : Fin d)
        rw [← cellV_zero b1 σ1]; exact hh
      have e2 : toZ b2 = cellV b σ ⟨1, by omega⟩ := by
        have hh := cellV_shift_succ b σ h hs0 hs2d hueq2 (⟨0, by omega⟩ : Fin d)
        rw [← cellV_zero b2 σ2]; exact hh
      have hb_eq : toZ b1 = toZ b2 := e1.trans e2.symm
      funext t
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ t.isLt) with htd | htlt
      · have htd' : t = Fin.last d := Fin.ext htd
        rw [htd', cellV_last, cellV_last]
        funext j
        have hh := congrFun hb_eq j
        simp only [toZ_apply] at hh
        omega
      · have hsh1 : cellV b1 σ1 t = cellV b σ ⟨(t:ℕ)+1, by omega⟩ := by
          have hh := cellV_shift_succ b σ h hs0 hs1d hueq1 ⟨(t:ℕ), htlt⟩
          convert hh using 1 <;> apply Fin.ext <;> simp only [Fin.val_mk, Fin.val_last] <;> omega
        have hsh2 : cellV b2 σ2 t = cellV b σ ⟨(t:ℕ)+1, by omega⟩ := by
          have hh := cellV_shift_succ b σ h hs0 hs2d hueq2 ⟨(t:ℕ), htlt⟩
          convert hh using 1 <;> apply Fin.ext <;> simp only [Fin.val_mk, Fin.val_last] <;> omega
        rw [hsh1, hsh2]
    · rcases eq_or_lt_of_le (show (s:ℕ) ≤ d by have := s.isLt; omega) with hsd | hslt
      · -- s = d
        have hs10 : (s1:ℕ) = 0 := by
          rcases key1 with k | ⟨k, k'⟩ | ⟨k, k'⟩
          · exfalso; apply hne1
            have hoff := agree_off b1 σ1 h1 s1 (by omega) hueq1
            have heq : cellV b σ = cellV b1 σ1 := by
              apply cellV_eq_of_agree_last; intro t ht
              exact hoff t (by intro hh; exact ht (by rw [hh, hsd]))
            exact (cellSet_eq_of_cellV_eq b σ h b1 σ1 h1 heq).symm
          · omega
          · exact k'
        have hs20 : (s2:ℕ) = 0 := by
          rcases key2 with k | ⟨k, k'⟩ | ⟨k, k'⟩
          · exfalso; apply hne2
            have hoff := agree_off b2 σ2 h2 s2 (by omega) hueq2
            have heq : cellV b σ = cellV b2 σ2 := by
              apply cellV_eq_of_agree_last; intro t ht
              exact hoff t (by intro hh; exact ht (by rw [hh, hsd]))
            exact (cellSet_eq_of_cellV_eq b σ h b2 σ2 h2 heq).symm
          · omega
          · exact k'
        have e1 : cellV b1 σ1 (Fin.last d) = cellV b σ ⟨(d:ℕ)-1, by omega⟩ := by
          have hh := cellV_shift_pred b σ h hsd hs10 hueq1 (⟨(d:ℕ)-1, by omega⟩ : Fin d)
          rw [show (⟨(↑(⟨(d:ℕ)-1, by omega⟩ : Fin d)) + 1,
                by have := (⟨(d:ℕ)-1, by omega⟩ : Fin d).isLt; omega⟩ : Fin (d+1)) = Fin.last d
              from Fin.ext (by simp only [Fin.val_mk, Fin.val_last] <;> omega)] at hh
          exact hh
        have e2 : cellV b2 σ2 (Fin.last d) = cellV b σ ⟨(d:ℕ)-1, by omega⟩ := by
          have hh := cellV_shift_pred b σ h hsd hs20 hueq2 (⟨(d:ℕ)-1, by omega⟩ : Fin d)
          rw [show (⟨(↑(⟨(d:ℕ)-1, by omega⟩ : Fin d)) + 1,
                by have := (⟨(d:ℕ)-1, by omega⟩ : Fin d).isLt; omega⟩ : Fin (d+1)) = Fin.last d
              from Fin.ext (by simp only [Fin.val_mk, Fin.val_last] <;> omega)] at hh
          exact hh
        have hb_eq : toZ b1 = toZ b2 := by
          have e1' : (fun j => (b1.1 j : ℤ) + 1) = cellV b σ ⟨(d:ℕ)-1, by omega⟩ :=
            (cellV_last (b:=b1) (σ:=σ1)).symm.trans e1
          have e2' : (fun j => (b2.1 j : ℤ) + 1) = cellV b σ ⟨(d:ℕ)-1, by omega⟩ :=
            (cellV_last (b:=b2) (σ:=σ2)).symm.trans e2
          funext j
          have h1 := congrFun e1' j
          have h2 := congrFun e2' j
          show (b1.1 j : ℤ) = (b2.1 j : ℤ)
          omega
        funext t
        rcases Nat.eq_zero_or_pos (t:ℕ) with ht0 | htpos
        · have ht0' : t = 0 := Fin.ext ht0
          rw [ht0', cellV_zero, cellV_zero]; exact hb_eq
        · have hsh1 : cellV b1 σ1 t = cellV b σ ⟨(t:ℕ)-1, by omega⟩ := by
            have hh := cellV_shift_pred b σ h hsd hs10 hueq1 ⟨(t:ℕ)-1, by omega⟩
            rw [show (⟨(↑(⟨(t:ℕ)-1, by omega⟩ : Fin d)) + 1,
                  by have := (⟨(t:ℕ)-1, by omega⟩ : Fin d).isLt; omega⟩ : Fin (d+1)) = t
                from Fin.ext (by simp only [Fin.val_mk] <;> omega)] at hh
            exact hh
          have hsh2 : cellV b2 σ2 t = cellV b σ ⟨(t:ℕ)-1, by omega⟩ := by
            have hh := cellV_shift_pred b σ h hsd hs20 hueq2 ⟨(t:ℕ)-1, by omega⟩
            rw [show (⟨(↑(⟨(t:ℕ)-1, by omega⟩ : Fin d)) + 1,
                  by have := (⟨(t:ℕ)-1, by omega⟩ : Fin d).isLt; omega⟩ : Fin (d+1)) = t
                from Fin.ext (by simp only [Fin.val_mk] <;> omega)] at hh
            exact hh
          rw [hsh1, hsh2]
      · -- 0 < s < d
        have hs1s : (s1:ℕ) = (s:ℕ) := by
          rcases key1 with k | ⟨k, _⟩ | ⟨k, _⟩
          · exact k
          · omega
          · omega
        have hs2s : (s2:ℕ) = (s:ℕ) := by
          rcases key2 with k | ⟨k, _⟩ | ⟨k, _⟩
          · exact k
          · omega
          · omega
        have hoff1 := agree_off b1 σ1 h1 s1 hs1s hueq1
        have hoff2 := agree_off b2 σ2 h2 s2 hs2s hueq2
        have hsigoff1 : ∀ t : Fin d, t ≠ ⟨(s:ℕ)-1, by omega⟩ → t ≠ ⟨(s:ℕ), by omega⟩ →
            σ1 t = σ t := by
          intro t ht1 ht2
          have h1 : (Fin.castSucc t : Fin (d+1)) ≠ s := by
            intro hh; exact ht2 (by apply Fin.ext; simpa using congrArg Fin.val hh)
          have h2 : (Fin.succ t : Fin (d+1)) ≠ s := fun hh =>
            ht1 (Fin.ext (by
              show (t:ℕ) = (s:ℕ)-1
              have hh' := congrArg Fin.val hh
              simp only [Fin.val_succ] at hh'
              omega))
          have e1 := cellV_sub_succ b1 σ1 t
          have e2 := cellV_sub_succ b σ t
          have hc' := (hoff1 (Fin.castSucc t) h1).symm
          have hs'' := (hoff1 (Fin.succ t) h2).symm
          have : evec (σ1 t) = evec (σ t) := by
            rw [← e1, ← e2]; funext j; rw [congrFun hc' j, congrFun hs'' j]
          exact evec_inj this
        have hsigoff2 : ∀ t : Fin d, t ≠ ⟨(s:ℕ)-1, by omega⟩ → t ≠ ⟨(s:ℕ), by omega⟩ →
            σ2 t = σ t := by
          intro t ht1 ht2
          have h1 : (Fin.castSucc t : Fin (d+1)) ≠ s := by
            intro hh; exact ht2 (by apply Fin.ext; simpa using congrArg Fin.val hh)
          have h2 : (Fin.succ t : Fin (d+1)) ≠ s := fun hh =>
            ht1 (Fin.ext (by
              show (t:ℕ) = (s:ℕ)-1
              have hh' := congrArg Fin.val hh
              simp only [Fin.val_succ] at hh'
              omega))
          have e1 := cellV_sub_succ b2 σ2 t
          have e2 := cellV_sub_succ b σ t
          have hc' := (hoff2 (Fin.castSucc t) h1).symm
          have hs'' := (hoff2 (Fin.succ t) h2).symm
          have : evec (σ2 t) = evec (σ t) := by
            rw [← e1, ← e2]; funext j; rw [congrFun hc' j, congrFun hs'' j]
          exact evec_inj this
        have hb1b : b1 = b := by
          apply toZ_injective
          rw [← cellV_zero b1 σ1, ← cellV_zero b σ]
          exact (hoff1 0 (by intro hh; have hh' := congrArg Fin.val hh; simp at hh'; omega)).symm
        have hb2b : b2 = b := by
          apply toZ_injective
          rw [← cellV_zero b2 σ2, ← cellV_zero b σ]
          exact (hoff2 0 (by intro hh; have hh' := congrArg Fin.val hh; simp at hh'; omega)).symm
        have hsig1 : σ1 ⟨(s:ℕ)-1, by omega⟩ = σ ⟨(s:ℕ), by omega⟩ := by
          rcases sigma_apply_mem σ σ1 (a := ⟨(s:ℕ)-1, by omega⟩) (b := ⟨(s:ℕ), by omega⟩) hsigoff1
            with k | k
          · exfalso
            have hσ : σ1 = σ := perm_eq_of_agree_off_one σ σ1 (by
              intro t ht
              by_cases hta : t = ⟨(s:ℕ)-1, by omega⟩
              · rw [hta]; exact k
              · exact hsigoff1 t hta ht)
            exact hne1 (cellSet_eq_of_cellV_eq b1 σ1 h1 b σ h (by rw [hσ, hb1b]))
          · exact k
        have hsig2 : σ2 ⟨(s:ℕ)-1, by omega⟩ = σ ⟨(s:ℕ), by omega⟩ := by
          rcases sigma_apply_mem σ σ2 (a := ⟨(s:ℕ)-1, by omega⟩) (b := ⟨(s:ℕ), by omega⟩) hsigoff2
            with k | k
          · exfalso
            have hσ : σ2 = σ := perm_eq_of_agree_off_one σ σ2 (by
              intro t ht
              by_cases hta : t = ⟨(s:ℕ)-1, by omega⟩
              · rw [hta]; exact k
              · exact hsigoff2 t hta ht)
            exact hne2 (cellSet_eq_of_cellV_eq b2 σ2 h2 b σ h (by rw [hσ, hb2b]))
          · exact k
        funext t
        rcases eq_or_ne t s with hts | htne
        · rw [hts]
          have step1 : (fun j => cellV b1 σ1 s j - cellV b1 σ1 ⟨(s:ℕ)-1, by omega⟩ j)
              = evec (σ1 ⟨(s:ℕ)-1, by omega⟩) := cellV_pred b1 σ1 s (by omega)
          have step2 : (fun j => cellV b2 σ2 s j - cellV b2 σ2 ⟨(s:ℕ)-1, by omega⟩ j)
              = evec (σ2 ⟨(s:ℕ)-1, by omega⟩) := cellV_pred b2 σ2 s (by omega)
          have hg1 : cellV b1 σ1 ⟨(s:ℕ)-1, by omega⟩ = cellV b σ ⟨(s:ℕ)-1, by omega⟩ :=
            (hoff1 ⟨(s:ℕ)-1, by omega⟩ (by intro hh; have := congrArg Fin.val hh; simp at this; omega)).symm
          have hg2 : cellV b2 σ2 ⟨(s:ℕ)-1, by omega⟩ = cellV b σ ⟨(s:ℕ)-1, by omega⟩ :=
            (hoff2 ⟨(s:ℕ)-1, by omega⟩ (by intro hh; have := congrArg Fin.val hh; simp at this; omega)).symm
          funext j
          have h1 := congrFun step1 j
          have h2 := congrFun step2 j
          have hg1j := congrFun hg1 j
          have hg2j := congrFun hg2 j
          have hs1j : evec (σ1 ⟨(s:ℕ)-1, by omega⟩) j = evec (σ ⟨(s:ℕ), by omega⟩) j :=
            congrFun (congrArg evec hsig1) j
          have hs2j : evec (σ2 ⟨(s:ℕ)-1, by omega⟩) j = evec (σ ⟨(s:ℕ), by omega⟩) j :=
            congrFun (congrArg evec hsig2) j
          linarith [h1, h2, hg1j, hg2j, hs1j, hs2j]
        · exact (hoff1 t htne).symm.trans (hoff2 t htne)
  rw [cellSet_eq_of_cellV_eq b1 σ1 h1 b2 σ2 h2 hcv]


/-! ## Incidence and the abstract Sperner parity theorem -/

/-- At most two cells contain a given `d`-element facet-like subset. -/
lemma incidence_card_le_two {d m : ℕ} {f : Finset (OPt d m)} (hf : f.card = d)
    (hex : ∃ C ∈ Cells d m, f ⊆ C) :
    ((Cells d m).filter (fun C => f ⊆ C)).card ≤ 2 := by
  classical
  obtain ⟨C0, hC0, hfC0⟩ := hex
  obtain ⟨b, σ, h, rfl⟩ := mem_Cells.mp hC0
  obtain ⟨s, hs⟩ := exists_missing hfC0 hf
  rw [hs]
  set F := (Cells d m).filter (fun C => (cellSet b σ h).erase (vert b σ h s) ⊆ C)
  have h1 : (F.filter (fun C => C = cellSet b σ h)).card ≤ 1 := by
    have hsub : F.filter (fun C => C = cellSet b σ h) ⊆
        ({cellSet b σ h} : Finset (Finset (OPt d m))) := by
      intro C hC; rw [Finset.mem_filter] at hC; exact Finset.mem_singleton.mpr hC.2
    calc _ ≤ ({cellSet b σ h} : Finset (Finset (OPt d m))).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  have h2 : (F.filter (fun C => ¬ (C = cellSet b σ h))).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro C1 hC1 C2 hC2
    obtain ⟨hC1F, hC1ne⟩ := Finset.mem_filter.mp hC1
    obtain ⟨hC2F, hC2ne⟩ := Finset.mem_filter.mp hC2
    rw [Finset.mem_filter] at hC1F hC2F
    exact facetshare_subsingleton b σ h s hC1F.1 hC2F.1 hC1F.2 hC2F.2 hC1ne hC2ne
  have hcard := Finset.card_filter_add_card_filter_not (s := F) (p := fun C => C = cellSet b σ h)
  omega

/-- The incidence hypothesis of the abstract Sperner parity theorem. -/
lemma incidence {d m : ℕ} {f : Finset (OPt d m)} (hf : f.card = d)
    (hex : ∃ C ∈ Cells d m, f ⊆ C) :
    ((Cells d m).filter (fun C => f ⊆ C)).card = 1 ∨
      ((Cells d m).filter (fun C => f ⊆ C)).card = 2 := by
  have hle := incidence_card_le_two hf hex
  obtain ⟨C, hC, hfC⟩ := hex
  have hge : 1 ≤ ((Cells d m).filter (fun C => f ⊆ C)).card :=
    Finset.card_pos.mpr ⟨C, Finset.mem_filter.mpr ⟨hC, hfC⟩⟩
  omega


/-! ## Compositions: the gap coordinates -/

def ext {d m : ℕ} (z : OPt d m) : Fin (d + 2) → ℕ
  | ⟨0, _⟩ => 0
  | ⟨n + 1, _⟩ => if hn : n < d then ((z.1 ⟨n, hn⟩ : Fin (m + 1)) : ℕ) else m

lemma ext_zero {d m : ℕ} (z : OPt d m) : ext z 0 = 0 := rfl

lemma ext_succ {d m : ℕ} (z : OPt d m) (n : ℕ) (h : n + 1 < d + 2) :
    ext z ⟨n + 1, h⟩ = if hn : n < d then ((z.1 ⟨n, hn⟩ : Fin (m + 1)) : ℕ) else m := rfl

lemma ext_last {d m : ℕ} (z : OPt d m) : ext z (Fin.last (d+1)) = m := by
  show ext z ⟨d+1, _⟩ = m
  rw [ext_succ, dif_neg (lt_irrefl d)]

def extN {d m : ℕ} (z : OPt d m) (i : ℕ) : ℕ :=
  if i = 0 then 0 else if h : i - 1 < d then ((z.1 ⟨i - 1, h⟩ : Fin (m + 1)) : ℕ) else m

lemma extN_zero {d m : ℕ} (z : OPt d m) : extN z 0 = 0 := by rw [extN, if_pos rfl]

lemma extN_last {d m : ℕ} (z : OPt d m) : extN z (d+1) = m := by
  rw [extN, if_neg (by omega : ¬ (d+1 = 0)), Nat.add_sub_cancel, dif_neg (by omega)]

lemma ext_eq_extN {d m : ℕ} (z : OPt d m) (t : Fin (d + 2)) : ext z t = extN z (t : ℕ) := by
  obtain ⟨n, hn⟩ := t
  rcases n with _ | k
  · rfl
  · show ext z ⟨k+1, _⟩ = extN z (k+1)
    rw [ext_succ, extN, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]

lemma extN_step {d m : ℕ} (z : OPt d m) (i : ℕ) : extN z i ≤ extN z (i+1) := by
  rw [extN, extN]
  by_cases hi : i = 0
  · rw [if_pos hi, if_neg (by omega : ¬ (i+1 = 0))]
    by_cases h1 : i + 1 - 1 < d
    · rw [dif_pos h1]; exact Nat.zero_le _
    · rw [dif_neg h1]; exact Nat.zero_le _
  · rw [if_neg hi, if_neg (by omega : ¬ (i+1 = 0))]
    by_cases h1 : i - 1 < d
    · rw [dif_pos h1]
      by_cases h2 : i + 1 - 1 < d
      · rw [dif_pos h2]
        have hle : (⟨i-1, h1⟩ : Fin d) ≤ ⟨i+1-1, h2⟩ := by
          simp only [Fin.mk_le_mk]; omega
        exact z.2 _ _ hle
      · rw [dif_neg h2]
        exact Nat.lt_succ_iff.mp (z.1 ⟨i-1, h1⟩).isLt
    · rw [dif_neg h1]
      have h2 : ¬ (i + 1 - 1 < d) := by omega
      rw [dif_neg h2]

lemma extN_mono {d m : ℕ} (z : OPt d m) : Monotone (extN z) :=
  monotone_nat_of_le_succ (extN_step z)

lemma ext_mono {d m : ℕ} (z : OPt d m) : Monotone (ext z) := by
  intro i j hij
  rw [ext_eq_extN, ext_eq_extN]
  exact extN_mono z hij

def gap {d m : ℕ} (z : OPt d m) (k : Fin (d + 1)) : ℕ :=
  ext z (Fin.succ k) - ext z (Fin.castSucc k)

lemma gap_le_m {d m : ℕ} (z : OPt d m) (k : Fin (d + 1)) : gap z k ≤ m := by
  refine le_trans (Nat.sub_le _ _) ?_
  have := ext_mono z (Fin.le_last (Fin.succ k))
  rwa [ext_last] at this

lemma sum_range_sub_nat {f : ℕ → ℕ} (hmono : Monotone f) (n : ℕ) :
    ∑ i ∈ Finset.range n, (f (i+1) - f i) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : f n ≤ f (n+1) := hmono (Nat.le_succ n)
    have h2 : f 0 ≤ f n := hmono (Nat.zero_le n)
    omega

lemma sum_gap {d m : ℕ} (z : OPt d m) : ∑ k : Fin (d + 1), gap z k = m := by
  rw [Finset.sum_fin_eq_sum_range]
  have hcongr : ∀ i ∈ Finset.range (d+1),
      (if h : i < d+1 then gap z ⟨i, h⟩ else 0) = extN z (i+1) - extN z i := by
    intro i hi
    rw [dif_pos (Finset.mem_range.mp hi), gap, ext_eq_extN, ext_eq_extN]
    simp only [Fin.val_succ, Fin.val_castSucc]
  rw [Finset.sum_congr rfl hcongr]
  rw [sum_range_sub_nat (extN_mono z) (d+1), extN_zero, Nat.sub_zero, extN_last]


/-! ## The bijection with compositions -/

lemma gap_eq {d m : ℕ} (z : OPt d m) (k : Fin (d + 1)) :
    gap z k = extN z ((k : ℕ) + 1) - extN z (k : ℕ) := by
  rw [gap, ext_eq_extN, ext_eq_extN, Fin.val_succ, Fin.val_castSucc]

/-- The composition coordinates of an order-polytope point. -/
def comp {d m : ℕ} (z : OPt d m) : Fin (d + 1) → Fin (m + 1) :=
  fun k => ⟨gap z k, Nat.lt_succ_iff.mpr (gap_le_m z k)⟩

@[simp] lemma comp_apply {d m : ℕ} (z : OPt d m) (k : Fin (d + 1)) :
    ((comp z k : Fin (m + 1)) : ℕ) = gap z k := rfl

/-- The order-polytope point as a composition of `m`. -/
def Phi {d m : ℕ} (z : OPt d m) :
    {x : Fin (d + 1) → Fin (m + 1) // ∑ k, ((x k : Fin (m + 1)) : ℕ) = m} :=
  ⟨comp z, sum_gap z⟩

@[simp] lemma Phi_apply {d m : ℕ} (z : OPt d m) (k : Fin (d + 1)) :
    ((Phi z).1 k : ℕ) = gap z k := rfl

lemma extN_succ {d m : ℕ} (z : OPt d m) (i : Fin d) : extN z ((i : ℕ) + 1) = (z.1 i : ℕ) := by
  rw [extN, if_neg (by omega : ¬ ((i : ℕ) + 1 = 0)), Nat.add_sub_cancel, dif_pos i.isLt]

lemma extN_eq_sum {d m : ℕ} (z : OPt d m) (n : ℕ) :
    extN z n = ∑ i ∈ Finset.range n, (extN z (i + 1) - extN z i) := by
  have h := sum_range_sub_nat (extN_mono z) n
  rw [extN_zero, Nat.sub_zero] at h
  exact h.symm

lemma Phi_injective {d m : ℕ} : Function.Injective (Phi (d:=d) (m:=m)) := by
  intro z z' h
  apply Subtype.ext; funext i; apply Fin.ext
  have hv : ∀ k : Fin (d + 1), gap z k = gap z' k := by
    intro k
    have := congrFun (congrArg Subtype.val h) k
    exact congrArg Fin.val this
  rw [← extN_succ z i, ← extN_succ z' i]
  rw [extN_eq_sum z ((i : ℕ) + 1), extN_eq_sum z' ((i : ℕ) + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < d + 1 := by have := Finset.mem_range.mp hk; omega
  have e1 : extN z (k + 1) - extN z k = gap z ⟨k, hk'⟩ := (gap_eq z ⟨k, hk'⟩).symm
  have e2 : extN z' (k + 1) - extN z' k = gap z' ⟨k, hk'⟩ := (gap_eq z' ⟨k, hk'⟩).symm
  rw [e1, e2, hv ⟨k, hk'⟩]


/-- prepend 0 -/
def lift {e m : ℕ} (z' : OPt e m) (j : Fin (e+1)) : Fin (m+1) :=
  if h : (j:ℕ) = 0 then 0 else z'.1 ⟨(j:ℕ)-1, by have := j.isLt; omega⟩

lemma lift_val_of_eq {e m : ℕ} (z' : OPt e m) (j : Fin (e+1)) (h : (j:ℕ) = 0) :
    ((lift z' j : Fin (m+1)) : ℕ) = 0 := by
  rw [lift]; rw [dif_pos h]; rfl

lemma lift_val_of_ne {e m : ℕ} (z' : OPt e m) (j : Fin (e+1)) (h : (j:ℕ) ≠ 0) :
    ((lift z' j : Fin (m+1)) : ℕ) = (z'.1 ⟨(j:ℕ)-1, by have := j.isLt; omega⟩ : ℕ) := by
  rw [lift]; rw [dif_neg h]

lemma lift_mono {e m : ℕ} (z' : OPt e m) : ∀ i j : Fin (e+1), i ≤ j → (lift z' i : ℕ) ≤ (lift z' j : ℕ) := by
  intro i j hij
  by_cases hi : (i:ℕ) = 0
  · rw [lift_val_of_eq z' i hi]; exact Nat.zero_le _
  · rw [lift_val_of_ne z' i hi]
    by_cases hj : (j:ℕ) = 0
    · omega
    · rw [lift_val_of_ne z' j hj]
      exact z'.2 _ _ (by simp only [Fin.mk_le_mk]; omega)

def liftO {e m : ℕ} (z' : OPt e m) : OPt (e+1) m := ⟨lift z', lift_mono z'⟩

@[simp] lemma liftO_zero {e m : ℕ} (z' : OPt e m) : ((liftO z').1 0 : ℕ) = 0 :=
  lift_val_of_eq z' 0 rfl

lemma liftO_succ {e m : ℕ} (z' : OPt e m) (i : Fin e) : ((liftO z').1 i.succ : ℕ) = (z'.1 i : ℕ) := by
  show ((lift z' (Fin.succ i) : Fin (m+1)) : ℕ) = (z'.1 i : ℕ)
  rw [lift_val_of_ne z' i.succ (by simp)]
  congr 1

def drop {e m : ℕ} (z : OPt (e+1) m) : OPt e m :=
  ⟨fun i => z.1 i.succ, by intro i j hij; exact z.2 _ _ (Fin.succ_le_succ_iff.mpr hij)⟩

@[simp] lemma drop_apply {e m : ℕ} (z : OPt (e+1) m) (i : Fin e) :
    (drop z).1 i = z.1 i.succ := rfl

lemma drop_lift {e m : ℕ} (z' : OPt e m) : drop (liftO z') = z' := by
  apply Subtype.ext; funext i; apply Fin.ext
  simp only [drop_apply, liftO_succ]

/-! ## Lifting a permutation -/

def sigmaInv {e : ℕ} (σ' : Equiv.Perm (Fin e)) : Fin (e+1) → Fin (e+1) :=
  fun j => if h : j = 0 then Fin.last e else Fin.castSucc (σ'.symm (Fin.pred j h))

lemma sigmaInv_zero {e : ℕ} (σ' : Equiv.Perm (Fin e)) : sigmaInv σ' 0 = Fin.last e := by
  rw [sigmaInv]; simp

lemma sigmaInv_succ {e : ℕ} (σ' : Equiv.Perm (Fin e)) (i : Fin e) :
    sigmaInv σ' i.succ = Fin.castSucc (σ'.symm i) := by
  rw [sigmaInv, dif_neg (Fin.succ_ne_zero i)]
  simp [Fin.pred_succ]

lemma sigmaInv_injective {e : ℕ} (σ' : Equiv.Perm (Fin e)) : Function.Injective (sigmaInv σ') := by
  intro a b hab
  rcases Fin.eq_zero_or_eq_succ a with ha | ⟨a', rfl⟩
  · rcases Fin.eq_zero_or_eq_succ b with hb | ⟨b', rfl⟩
    · rw [ha, hb]
    · rw [ha, sigmaInv_zero, sigmaInv_succ] at hab
      have h1 := congrArg Fin.val hab
      simp only [Fin.val_last, Fin.val_castSucc] at h1
      have h2 := (σ'.symm b').isLt
      omega
  · rcases Fin.eq_zero_or_eq_succ b with hb | ⟨b', rfl⟩
    · rw [hb, sigmaInv_zero, sigmaInv_succ] at hab
      have h1 := congrArg Fin.val hab
      simp only [Fin.val_last, Fin.val_castSucc] at h1
      have h2 := (σ'.symm a').isLt
      omega
    · rw [sigmaInv_succ, sigmaInv_succ] at hab
      have h1 : σ'.symm a' = σ'.symm b' := Fin.castSucc_injective e hab
      rw [σ'.symm.injective h1]

lemma sigmaInv_surjective {e : ℕ} (σ' : Equiv.Perm (Fin e)) : Function.Surjective (sigmaInv σ') := by
  intro k
  by_cases hk : k = Fin.last e
  · exact ⟨0, by rw [hk, sigmaInv_zero]⟩
  · have hne : (k:ℕ) ≠ e := fun h => hk (Fin.ext (by rw [h, Fin.val_last]))
    have hlt : (k:ℕ) < e := by have := k.isLt; omega
    obtain ⟨i, hi⟩ := σ'.symm.surjective (⟨(k:ℕ), hlt⟩ : Fin e)
    refine ⟨i.succ, ?_⟩
    rw [sigmaInv_succ, hi]
    exact Fin.ext (by simp only [Fin.val_castSucc])

def sigmaLift {e : ℕ} (σ' : Equiv.Perm (Fin e)) : Equiv.Perm (Fin (e+1)) :=
  Equiv.ofBijective (sigmaInv σ') ⟨sigmaInv_injective σ', sigmaInv_surjective σ'⟩

@[simp] lemma sigmaLift_apply {e : ℕ} (σ' : Equiv.Perm (Fin e)) (j : Fin (e+1)) :
    sigmaLift σ' j = sigmaInv σ' j := rfl

/-! ## The lifted cell -/

lemma add_one_le {e m : ℕ} {b' : OPt e m} {σ' : Equiv.Perm (Fin e)} (h' : IsCell b' σ')
    (i : Fin e) : (b'.1 i : ℕ) + 1 ≤ m := by
  have hh := h'.1 (Fin.last e) i
  rw [vtN] at hh
  have hlt : ((σ'.symm i : Fin e) : ℕ) < ((Fin.last e : Fin (e+1)) : ℕ) := by
    rw [Fin.val_last]; exact (σ'.symm i).isLt
  rw [if_pos hlt] at hh
  simpa using hh

lemma lift_add_one_le {e m : ℕ} {b' : OPt e m} {σ' : Equiv.Perm (Fin e)} (h' : IsCell b' σ')
    (hm : 0 < m) (j : Fin (e+1)) : ((liftO b').1 j : ℕ) + 1 ≤ m := by
  rcases Fin.eq_zero_or_eq_succ j with hj | ⟨i, rfl⟩
  · rw [hj, liftO_zero]; omega
  · rw [liftO_succ b' i]; exact add_one_le h' i

lemma vtN_lift_castSucc {e m : ℕ} (b' : OPt e m) (σ' : Equiv.Perm (Fin e)) (h' : IsCell b' σ')
    (t0 : Fin (e+1)) (j : Fin (e+1)) :
    vtN (liftO b') ((sigmaLift σ').symm) t0.castSucc j = ((liftO (vert b' σ' h' t0)).1 j : ℕ) := by
  rcases Fin.eq_zero_or_eq_succ j with hj | ⟨i, rfl⟩
  · rw [hj, vtN, Equiv.symm_symm, sigmaLift_apply, sigmaInv_zero, Fin.val_last]
    simp only [liftO_zero, Fin.val_castSucc]
    rw [if_neg (by have := t0.isLt; omega), add_zero]
  · rw [vtN, Equiv.symm_symm, sigmaLift_apply, sigmaInv_succ, Fin.val_castSucc,
        liftO_succ b' i, liftO_succ (vert b' σ' h' t0) i, vert_apply, vtN]
    simp only [Fin.val_castSucc]

lemma vtN_lift_last {e m : ℕ} (b' : OPt e m) (σ' : Equiv.Perm (Fin e)) (h' : IsCell b' σ')
    (j : Fin (e+1)) :
    vtN (liftO b') ((sigmaLift σ').symm) (Fin.last (e+1)) j = ((liftO b').1 j : ℕ) + 1 := by
  rcases Fin.eq_zero_or_eq_succ j with hj | ⟨i, rfl⟩
  · rw [hj, vtN, Equiv.symm_symm, sigmaLift_apply, sigmaInv_zero, Fin.val_last, Fin.val_last]
    rw [if_pos (by omega)]
  · rw [vtN, Equiv.symm_symm, sigmaLift_apply, sigmaInv_succ, liftO_succ b' i,
        Fin.val_castSucc, Fin.val_last]
    congr 1
    exact if_pos (by have := (σ'.symm i).isLt; omega)

lemma isCell_lift {e m : ℕ} (b' : OPt e m) (σ' : Equiv.Perm (Fin e)) (h' : IsCell b' σ')
    (hm : 0 < m) : IsCell (liftO b') ((sigmaLift σ').symm) := by
  have hltaux : ∀ t : Fin (e+2), t ≠ Fin.last (e+1) → (t:ℕ) < e+1 := by
    intro t ht
    have h1 : (t:ℕ) ≠ e+1 := fun h => ht (Fin.ext (by rw [h, Fin.val_last]))
    have h2 := t.isLt
    omega
  constructor
  · intro t j
    by_cases ht : t = Fin.last (e+1)
    · rw [ht, vtN_lift_last b' σ' h']
      exact lift_add_one_le h' hm j
    · have hlt := hltaux t ht
      have ht' : t = (⟨(t:ℕ), hlt⟩ : Fin (e+1)).castSucc := by ext; simp [Fin.val_castSucc]
      rw [ht', vtN_lift_castSucc b' σ' h']
      exact Nat.lt_succ_iff.mp ((liftO (vert b' σ' h' ⟨(t:ℕ), hlt⟩)).1 j).isLt
  · intro t i j hij
    by_cases ht : t = Fin.last (e+1)
    · rw [ht, vtN_lift_last b' σ' h', vtN_lift_last b' σ' h']
      exact Nat.add_le_add_right (lift_mono b' i j hij) 1
    · have hlt := hltaux t ht
      have ht' : t = (⟨(t:ℕ), hlt⟩ : Fin (e+1)).castSucc := by ext; simp [Fin.val_castSucc]
      rw [ht', vtN_lift_castSucc b' σ' h', vtN_lift_castSucc b' σ' h']
      exact (liftO (vert b' σ' h' ⟨(t:ℕ), hlt⟩)).2 i j hij

lemma vert_lift_castSucc {e m : ℕ} (b' : OPt e m) (σ' : Equiv.Perm (Fin e)) (h' : IsCell b' σ')
    (hm : 0 < m) (t0 : Fin (e+1)) :
    vert (liftO b') ((sigmaLift σ').symm) (isCell_lift b' σ' h' hm) t0.castSucc
      = liftO (vert b' σ' h' t0) := by
  apply Subtype.ext; funext j; apply Fin.ext
  rw [vert_apply, vtN_lift_castSucc b' σ' h']

lemma facet_lift {e m : ℕ} (b' : OPt e m) (σ' : Equiv.Perm (Fin e)) (h' : IsCell b' σ')
    (hm : 0 < m) :
    ((cellSet (liftO b') ((sigmaLift σ').symm) (isCell_lift b' σ' h' hm)).erase
        (vert (liftO b') ((sigmaLift σ').symm) (isCell_lift b' σ' h' hm) (Fin.last (e+1))))
      = (cellSet b' σ' h').image (liftO) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hx
    obtain ⟨t, ht⟩ := mem_cellSet.mp hmem
    subst ht
    have htne : t ≠ Fin.last (e+1) := fun h => hne (congrArg _ h)
    have h1 : (t:ℕ) ≠ e+1 := fun h => htne (Fin.ext (by rw [h]; exact (Fin.val_last (e+1)).symm))
    have hlt : (t:ℕ) < e+1 := by have h2 := t.isLt; omega
    have ht_eq : t = (⟨(t:ℕ), hlt⟩ : Fin (e+1)).castSucc := by ext; simp [Fin.val_castSucc]
    refine Finset.mem_image.mpr ⟨vert b' σ' h' ⟨(t:ℕ), hlt⟩, mem_cellSet.mpr ⟨_, rfl⟩, ?_⟩
    exact (show vert (liftO b') ((sigmaLift σ').symm) (isCell_lift b' σ' h' hm) t
        = liftO (vert b' σ' h' ⟨(t:ℕ), hlt⟩) from by
      conv_lhs => rw [ht_eq]
      exact vert_lift_castSucc b' σ' h' hm ⟨(t:ℕ), hlt⟩).symm
  · intro hx
    obtain ⟨a, ha, hxa⟩ := Finset.mem_image.mp hx
    obtain ⟨t0, rfl⟩ := mem_cellSet.mp ha
    refine Finset.mem_erase.mpr ⟨?_, mem_cellSet.mpr ⟨t0.castSucc,
      (vert_lift_castSucc b' σ' h' hm t0).trans hxa⟩⟩
    rw [← hxa]
    intro hh
    have h2 := congrArg (fun z : OPt (e+1) m => ((z.1 0 : Fin (m+1)) : ℕ)) hh
    rw [liftO_zero, vert_apply, vtN_lift_last b' σ' h'] at h2
    simp only [liftO_zero] at h2
    omega


/-! ## The structure of a facet contained in the first face -/

lemma facet_f0_structure {e m : ℕ} (b : OPt (e+1) m) (σ : Equiv.Perm (Fin (e+1)))
    (h : IsCell b σ) (s : Fin (e+2))
    (hs : ∀ t : Fin (e+2), t ≠ s → ((vert b σ h t).1 0 : ℕ) = 0) :
    s = Fin.last (e+1) ∧ (b.1 0 : ℕ) = 0 ∧ σ (Fin.last e) = 0 := by
  have key : ∀ t : Fin (e+2),
      ((vert b σ h t).1 0 : ℕ)
        = (b.1 0 : ℕ) + if ((σ.symm 0 : Fin (e+1)) : ℕ) < (t:ℕ) then 1 else 0 := by
    intro t; rw [vert_apply, vtN]
  have ht0 : (0 : Fin (e+2)) ≠ Fin.last (e+1) := by
    intro hh; have h2 := congrArg Fin.val hh; rw [Fin.val_last] at h2; simp at h2
  have hlast : s = Fin.last (e+1) := by
    by_contra hne
    have hh := hs (Fin.last (e+1)) (fun hh' => hne hh'.symm)
    rw [key] at hh
    have hlt : ((σ.symm 0 : Fin (e+1)) : ℕ) < ((Fin.last (e+1) : Fin (e+2)) : ℕ) := by
      rw [Fin.val_last]; exact (σ.symm 0).isLt
    rw [if_pos hlt] at hh
    omega
  have hb0 : (b.1 0 : ℕ) = 0 := by
    have hh := hs 0 (by rw [hlast]; exact ht0)
    rw [key] at hh
    rw [if_neg (by simp : ¬ ((σ.symm 0 : Fin (e+1)) : ℕ) < (((0 : Fin (e+2)) : ℕ)))] at hh
    omega
  refine ⟨hlast, hb0, ?_⟩
  have htc : ((Fin.last e).castSucc : Fin (e+2)) ≠ Fin.last (e+1) := by
    intro hh; have h2 := congrArg Fin.val hh
    rw [Fin.val_last, Fin.val_castSucc, Fin.val_last] at h2; omega
  have hh := hs ((Fin.last e).castSucc) (by rw [hlast]; exact htc)
  rw [key, hb0, Fin.val_castSucc] at hh
  have hcond : ¬ ((σ.symm 0 : Fin (e+1)) : ℕ) < e := by
    intro hc; rw [Fin.val_last] at hh; rw [if_pos hc] at hh; omega
  have : (σ.symm (0 : Fin (e+1)) : ℕ) = e := by have := (σ.symm 0).isLt; omega
  have hsymm : σ.symm (0 : Fin (e+1)) = Fin.last e := Fin.ext (by rw [Fin.val_last]; exact this)
  rw [← hsymm]
  exact Equiv.apply_symm_apply σ 0

lemma vert_last_eq {e m : ℕ} (b : OPt (e+1) m) (σ : Equiv.Perm (Fin (e+1)))
    (h : IsCell b σ) (hσ0 : σ (Fin.last e) = 0) (j : Fin (e+1)) :
    ((vert b σ h (Fin.last (e+1))).1 j : ℕ)
      = ((vert b σ h (Fin.last e).castSucc).1 j : ℕ) + (if j = 0 then 1 else 0) := by
  rw [vert_apply, vert_apply, vtN, vtN, Fin.val_last, Fin.val_castSucc, Fin.val_last]
  have hiff : (σ.symm j = Fin.last e) ↔ (j = 0) := by
    rw [Equiv.symm_apply_eq, hσ0]
  have hnum : (if ((σ.symm j : Fin (e+1)) : ℕ) < e+1 then 1 else 0)
      = (if ((σ.symm j : Fin (e+1)) : ℕ) < e then 1 else 0) + (if j = 0 then 1 else 0) := by
    have hle : ((σ.symm j : Fin (e+1)) : ℕ) ≤ e := by have := (σ.symm j).isLt; omega
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hj0 : ¬ (j = 0) := fun hj => by
        have hh : σ.symm j = Fin.last e := hiff.mpr hj
        rw [hh, Fin.val_last] at hlt; omega
      rw [if_pos (by omega), if_pos hlt, if_neg hj0, add_zero]
    · have hj0 : j = 0 := hiff.mp (Fin.ext (by rw [heq, Fin.val_last]))
      rw [if_pos (by omega), if_neg (by omega), if_pos hj0, zero_add]
  rw [hnum]
  ring

lemma cell_eq_of_facet_f0 {e m : ℕ} {C C2 : Finset (OPt (e+1) m)} (hC : C ∈ Cells (e+1) m)
    (hC2 : C2 ∈ Cells (e+1) m) {f : Finset (OPt (e+1) m)} (hfC : f ⊆ C) (hfC2 : f ⊆ C2)
    (hcard : f.card = e+1) (h0 : ∀ x ∈ f, (x.1 0 : ℕ) = 0) : C2 = C := by
  obtain ⟨b, σ, h, hC'⟩ := mem_Cells.mp hC
  obtain ⟨b2, σ2, h2, hC2'⟩ := mem_Cells.mp hC2
  have hfC' : f ⊆ cellSet b σ h := hC'.symm ▸ hfC
  have hfC2' : f ⊆ cellSet b2 σ2 h2 := hC2'.symm ▸ hfC2
  obtain ⟨s, hs⟩ := exists_missing hfC' hcard
  obtain ⟨s2, hs2⟩ := exists_missing hfC2' hcard
  rw [← hC', ← hC2']
  have hs0 : ∀ t : Fin (e+2), t ≠ s → ((vert b σ h t).1 0 : ℕ) = 0 := by
    intro t ht
    refine h0 _ ?_
    rw [hs, Finset.mem_erase]
    exact ⟨fun hh => ht (vert_injective b σ h hh), mem_cellSet.mpr ⟨t, rfl⟩⟩
  have hs20 : ∀ t : Fin (e+2), t ≠ s2 → ((vert b2 σ2 h2 t).1 0 : ℕ) = 0 := by
    intro t ht
    refine h0 _ ?_
    rw [hs2, Finset.mem_erase]
    exact ⟨fun hh => ht (vert_injective b2 σ2 h2 hh), mem_cellSet.mpr ⟨t, rfl⟩⟩
  obtain ⟨hsl, hb0, hσ0⟩ := facet_f0_structure b σ h s hs0
  obtain ⟨hs2l, hb20, hσ20⟩ := facet_f0_structure b2 σ2 h2 s2 hs20
  have hVs : vert b σ h s ∉ f := by rw [hs]; exact Finset.notMem_erase _ _
  have hWs : vert b2 σ2 h2 s2 ∉ f := by rw [hs2]; exact Finset.notMem_erase _ _
  have hC3 : cellSet b σ h = insert (vert b σ h s) f := by
    rw [hs]
    exact (Finset.insert_erase (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩)).symm
  have hC23 : cellSet b2 σ2 h2 = insert (vert b2 σ2 h2 s2) f := by
    rw [hs2]
    exact (Finset.insert_erase (Finset.mem_image.mpr ⟨s2, Finset.mem_univ _, rfl⟩)).symm
  have hle1 : ∀ x ∈ f, x ≤ vert b σ h (Fin.last e).castSucc := by
    intro x hx
    have hxC : x ∈ cellSet b σ h := by rw [hC3]; exact Finset.mem_insert_of_mem hx
    obtain ⟨t, ht⟩ := mem_cellSet.mp hxC
    rw [← ht]
    have htne : t ≠ Fin.last (e+1) := by
      intro hh; exact hVs (by rw [hsl, ← hh, ht]; exact hx)
    have htlt : t ≤ (Fin.last e).castSucc := by
      have hlt : t < Fin.last (e+1) := lt_of_le_of_ne (Fin.le_last t) htne
      have h4 := Fin.lt_def.mp hlt
      rw [Fin.val_last] at h4
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_last]
      omega
    exact vert_mono b σ h htlt
  have hmem1 : vert b σ h (Fin.last e).castSucc ∈ f := by
    rw [hs, Finset.mem_erase]
    refine ⟨?_, mem_cellSet.mpr ⟨_, rfl⟩⟩
    intro hh
    have h3 := vert_injective b σ h hh
    rw [hsl] at h3
    have hlt : (Fin.last e).castSucc < Fin.last (e+1) := by
      rw [Fin.lt_def, Fin.val_castSucc, Fin.val_last, Fin.val_last]; omega
    rw [h3] at hlt
    exact lt_irrefl _ hlt
  have hle2 : ∀ x ∈ f, x ≤ vert b2 σ2 h2 (Fin.last e).castSucc := by
    intro x hx
    have hxC : x ∈ cellSet b2 σ2 h2 := by rw [hC23]; exact Finset.mem_insert_of_mem hx
    obtain ⟨t, ht⟩ := mem_cellSet.mp hxC
    rw [← ht]
    have htne : t ≠ Fin.last (e+1) := by
      intro hh; exact hWs (by rw [hs2l, ← hh, ht]; exact hx)
    have htlt : t ≤ (Fin.last e).castSucc := by
      have hlt : t < Fin.last (e+1) := lt_of_le_of_ne (Fin.le_last t) htne
      have h4 := Fin.lt_def.mp hlt
      rw [Fin.val_last] at h4
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_last]
      omega
    exact vert_mono b2 σ2 h2 htlt
  have hmem2 : vert b2 σ2 h2 (Fin.last e).castSucc ∈ f := by
    rw [hs2, Finset.mem_erase]
    refine ⟨?_, mem_cellSet.mpr ⟨_, rfl⟩⟩
    intro hh
    have h3 := vert_injective b2 σ2 h2 hh
    rw [hs2l] at h3
    have hlt : (Fin.last e).castSucc < Fin.last (e+1) := by
      rw [Fin.lt_def, Fin.val_castSucc, Fin.val_last, Fin.val_last]; omega
    rw [h3] at hlt
    exact lt_irrefl _ hlt
  have hVe : vert b σ h (Fin.last e).castSucc = vert b2 σ2 h2 (Fin.last e).castSucc :=
    le_antisymm (hle2 _ hmem1) (hle1 _ hmem2)
  have e1 : vert b σ h (Fin.last (e+1)) = vert b2 σ2 h2 (Fin.last (e+1)) := by
    apply Subtype.ext; funext j; apply Fin.ext
    rw [vert_last_eq b σ h hσ0 j, vert_last_eq b2 σ2 h2 hσ20 j, hVe]
  rw [hC23, hC3, hsl, hs2l, e1]



/-! ## The interior flip -/

lemma flip_symm_apply {d : ℕ} (a b : Fin d) (σ : Equiv.Perm (Fin d)) (j : Fin d) :
    (((Equiv.swap a b).trans σ)).symm j = Equiv.swap a b (σ.symm j) := by
  rw [Equiv.symm_trans_apply, Equiv.symm_swap]

lemma ite_lt_succ (x n : ℕ) :
    (if x < n+1 then (1:ℕ) else 0) = (if x < n then 1 else 0) + (if x = n then 1 else 0) := by
  rcases lt_trichotomy x n with h | h | h
  · rw [if_pos (by omega), if_pos h, if_neg (by omega), add_zero]
  · rw [h, if_pos (by omega), if_neg (by omega), if_pos rfl, zero_add]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma ite_lt_of_ne {n t : ℕ} (h : t ≠ n+1) :
    (if n+1 < t then (1:ℕ) else 0) = (if n < t then 1 else 0) := by
  rcases lt_trichotomy t (n+1) with h1 | h1 | h1
  · rw [if_neg (by omega), if_neg (by omega)]
  · exact absurd h1 h
  · rw [if_pos (by omega), if_pos (by omega)]

lemma ite_lt_of_ne' {n t : ℕ} (h : t ≠ n+1) :
    (if n < t then (1:ℕ) else 0) = (if n+1 < t then 1 else 0) := (ite_lt_of_ne h).symm

lemma vtN_succ_apply {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (a : Fin d) (j : Fin d) :
    vtN b σ (Fin.succ a) j = vtN b σ a.castSucc j + (if j = σ a then 1 else 0) := by
  rw [vtN, vtN, Fin.val_succ, Fin.val_castSucc]
  have hkey : (if ((σ.symm j : Fin d) : ℕ) = (a:ℕ) then (1:ℕ) else 0)
      = (if j = σ a then 1 else 0) := by
    by_cases hh : ((σ.symm j : Fin d) : ℕ) = (a:ℕ)
    · have hs : σ.symm j = a := Fin.ext hh
      rw [if_pos hh, if_pos ((Equiv.symm_apply_eq σ).mp hs)]
    · have hs : σ.symm j ≠ a := fun h => hh (congrArg Fin.val h)
      rw [if_neg hh, if_neg (fun h => hs ((Equiv.symm_apply_eq σ).mpr h))]
  rw [ite_lt_succ ((σ.symm j : Fin d) : ℕ) (a:ℕ), hkey, Nat.add_assoc]

lemma vtN_flip_apply_ne {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (a : Fin d)
    (ha : (a:ℕ)+1 < d) (t : Fin (d+1)) (ht : t ≠ Fin.succ a) (j : Fin d) :
    vtN b ((Equiv.swap a ⟨(a:ℕ)+1, ha⟩).trans σ) t j = vtN b σ t j := by
  rw [vtN, vtN, flip_symm_apply]
  congr 1
  have hta : (t:ℕ) ≠ (a:ℕ)+1 := fun hh => ht (by ext; rw [Fin.val_succ, hh])
  rcases eq_or_ne (σ.symm j) a with h1 | h1
  · have hv : ((Equiv.swap a ⟨(a:ℕ)+1, ha⟩ (σ.symm j) : Fin d) : ℕ) = (a:ℕ)+1 := by
      rw [h1, Equiv.swap_apply_left]
    have hva : ((σ.symm j : Fin d) : ℕ) = (a:ℕ) := by rw [h1]
    rw [hv, hva, ite_lt_of_ne hta]
  · rcases eq_or_ne (σ.symm j) (⟨(a:ℕ)+1, ha⟩ : Fin d) with h2 | h2
    · have hv : ((Equiv.swap a ⟨(a:ℕ)+1, ha⟩ (σ.symm j) : Fin d) : ℕ) = (a:ℕ) := by
        rw [h2, Equiv.swap_apply_right]
      have hv2 : ((σ.symm j : Fin d) : ℕ) = (a:ℕ)+1 := by rw [h2]
      rw [hv, hv2, ite_lt_of_ne' hta]
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

lemma vtN_flip_apply_eq {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (a : Fin d)
    (ha : (a:ℕ)+1 < d) (j : Fin d) :
    vtN b ((Equiv.swap a ⟨(a:ℕ)+1, ha⟩).trans σ) (Fin.succ a) j
      = vtN b σ a.castSucc j + (if j = σ ⟨(a:ℕ)+1, ha⟩ then 1 else 0) := by
  rw [vtN, vtN, flip_symm_apply, Fin.val_castSucc, Fin.val_succ]
  rcases eq_or_ne (σ.symm j) a with h1 | h1
  · have hv : ((Equiv.swap a ⟨(a:ℕ)+1, ha⟩ (σ.symm j) : Fin d) : ℕ) = (a:ℕ)+1 := by
      rw [h1, Equiv.swap_apply_left]
    have hva : ((σ.symm j : Fin d) : ℕ) = (a:ℕ) := by rw [h1]
    have hjb : ¬ (j = σ ⟨(a:ℕ)+1, ha⟩) := fun hh => by
      have h2 : σ.symm j = ⟨(a:ℕ)+1, ha⟩ := (Equiv.symm_apply_eq σ).mpr hh
      rw [h1] at h2
      exact absurd (congrArg Fin.val h2) (by simp)
    rw [hv, hva, if_neg (by omega : ¬ ((a:ℕ)+1 < (a:ℕ)+1)),
        if_neg (by omega : ¬ ((a:ℕ) < (a:ℕ))), if_neg hjb]
  · rcases eq_or_ne (σ.symm j) (⟨(a:ℕ)+1, ha⟩ : Fin d) with h2 | h2
    · have hv : ((Equiv.swap a ⟨(a:ℕ)+1, ha⟩ (σ.symm j) : Fin d) : ℕ) = (a:ℕ) := by
        rw [h2, Equiv.swap_apply_right]
      have hvb : ((σ.symm j : Fin d) : ℕ) = (a:ℕ)+1 := by rw [h2]
      have hjb : j = σ ⟨(a:ℕ)+1, ha⟩ := (Equiv.symm_apply_eq σ).mp h2
      rw [hv, hvb, if_pos (by omega : (a:ℕ) < (a:ℕ)+1),
          if_neg (by omega : ¬ ((a:ℕ)+1 < (a:ℕ))), if_pos hjb]
    · have hv : ((Equiv.swap a ⟨(a:ℕ)+1, ha⟩ (σ.symm j) : Fin d) : ℕ) = ((σ.symm j : Fin d) : ℕ) := by
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      have hva : ((σ.symm j : Fin d) : ℕ) ≠ (a:ℕ) := fun hh => h1 (Fin.ext hh)
      have hjb : ¬ (j = σ ⟨(a:ℕ)+1, ha⟩) := fun hh => h2 ((Equiv.symm_apply_eq σ).mpr hh)
      rw [hv, ite_lt_succ ((σ.symm j : Fin d) : ℕ) (a:ℕ), if_neg hjb, if_neg hva]
      ring


lemma extN_vert {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (t : Fin (d+1)) (i : ℕ) :
    extN (vert b σ h t) i
      = if i = 0 then 0 else if hi : i - 1 < d then vtN b σ t ⟨i-1, hi⟩ else m := by
  rw [extN]
  by_cases h0 : i = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    by_cases hi : i - 1 < d
    · rw [dif_pos hi, dif_pos hi, vert_apply]
    · rw [dif_neg hi, dif_neg hi]

lemma gap_eq_vtN {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (t : Fin (d+1)) {k : Fin (d+1)} (h1 : 1 ≤ (k:ℕ)) (h2 : (k:ℕ) ≤ d - 1) :
    gap (vert b σ h t) k
      = vtN b σ t ⟨(k:ℕ), by omega⟩ - vtN b σ t ⟨(k:ℕ)-1, by omega⟩ := by
  rw [gap, ext_eq_extN, ext_eq_extN, extN_vert, extN_vert, Fin.val_succ, Fin.val_castSucc]
  rw [if_neg (by omega : ¬ ((k:ℕ)+1 = 0)), if_neg (by omega : ¬ ((k:ℕ) = 0))]
  rw [dif_pos (by omega : (k:ℕ)+1-1 < d), dif_pos (by omega : (k:ℕ)-1 < d)]
  congr 3 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega


lemma w_le {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (a : Fin d) (ha : (a:ℕ)+1 < d) (j : Fin d) :
    vtN b σ a.castSucc j + (if j = σ ⟨(a:ℕ)+1, ha⟩ then 1 else 0) ≤ m := by
  by_cases hj : j = σ ⟨(a:ℕ)+1, ha⟩
  · rw [if_pos hj]
    have hsymm : (σ.symm j : Fin d) = ⟨(a:ℕ)+1, ha⟩ := by rw [hj, Equiv.symm_apply_apply]
    have hv : ((σ.symm j : Fin d) : ℕ) = (a:ℕ)+1 := by rw [hsymm]
    rw [vtN, hv, Fin.val_castSucc, if_neg (by omega : ¬ ((a:ℕ)+1 < (a:ℕ))), add_zero, hj]
    exact add_one_le h _
  · rw [if_neg hj, add_zero]
    exact h.1 a.castSucc j
lemma gap_succ_eq {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (t : Fin (d+1)) (j : Fin d) (hj : (j:ℕ)+1 < d) :
    gap (vert b σ h t) ⟨(j:ℕ)+1, by omega⟩ = vtN b σ t ⟨(j:ℕ)+1, hj⟩ - vtN b σ t j := by
  have h1 : (1:ℕ) ≤ ((⟨(j:ℕ)+1, by omega⟩ : Fin (d+1)) : ℕ) := by
    show (1:ℕ) ≤ (j:ℕ)+1; omega
  have h2 : ((⟨(j:ℕ)+1, by omega⟩ : Fin (d+1)) : ℕ) ≤ d-1 := by
    show (j:ℕ)+1 ≤ d-1; omega
  rw [gap_eq_vtN b σ h t (k := ⟨(j:ℕ)+1, by omega⟩) h1 h2]
  rfl

lemma symm_sigma_bb {d : ℕ} (σ : Equiv.Perm (Fin d)) (a : Fin d) :
    σ.symm (σ a) = a := Equiv.symm_apply_apply σ a

lemma gapset_of_not_mono {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (a : Fin d) (ha : (a:ℕ)+1 < d)
    (hnot : ∃ i j : Fin d, i ≤ j ∧ vtN b σ a.castSucc i + (if i = σ ⟨(a:ℕ)+1, ha⟩ then 1 else 0)
        > vtN b σ a.castSucc j + (if j = σ ⟨(a:ℕ)+1, ha⟩ then 1 else 0)) :
    ∃ k : Fin (d+1), ∀ t : Fin (d+1), t ≠ Fin.succ a → gap (vert b σ h t) k = 0 := by
  obtain ⟨i, j, hij, hgt⟩ := hnot
  have hmono : vtN b σ a.castSucc i ≤ vtN b σ a.castSucc j := h.2 a.castSucc i j hij
  have hvac : vtN b σ a.castSucc (σ ⟨(a:ℕ)+1, ha⟩) = (b.1 (σ ⟨(a:ℕ)+1, ha⟩) : ℕ) := by
    have hsymm : (σ.symm (σ ⟨(a:ℕ)+1, ha⟩) : Fin d) = ⟨(a:ℕ)+1, ha⟩ := Equiv.symm_apply_apply σ _
    have hv : ((σ.symm (σ ⟨(a:ℕ)+1, ha⟩) : Fin d) : ℕ) = (a:ℕ)+1 := by rw [hsymm]
    rw [vtN, hv, Fin.val_castSucc, if_neg (by omega : ¬ ((a:ℕ)+1 < (a:ℕ))), add_zero]
  have hic : i = σ ⟨(a:ℕ)+1, ha⟩ := by
    by_contra hne
    have h0 : (if i = σ ⟨(a:ℕ)+1, ha⟩ then (1:ℕ) else 0) = 0 := if_neg hne
    rw [h0] at hgt
    exact absurd hgt (not_lt.mpr (le_trans hmono (Nat.le_add_right _ _)))
  have hilt : i < j := by
    rcases lt_or_eq_of_le hij with hh | hh
    · exact hh
    · rw [hh] at hgt; omega
  have hjc : ¬ (j = σ ⟨(a:ℕ)+1, ha⟩) := by
    intro hj
    rw [hj] at hgt
    have h2 : (if i = σ ⟨(a:ℕ)+1, ha⟩ then (1:ℕ) else 0) = 1 := if_pos hic
    simp only [h2, hic, if_pos rfl, add_zero] at hgt
    omega
  rw [hic, hvac, if_neg hjc] at hgt
  simp only [add_zero, if_pos rfl] at hgt
  have hclt : (σ ⟨(a:ℕ)+1, ha⟩ : Fin d) < j := by rwa [hic] at hilt
  have hclt' : ((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ) < (j:ℕ) := hclt
  have hcc_lt : ((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ) + 1 < d := by have := j.isLt; omega
  have hmono' : (b.1 (σ ⟨(a:ℕ)+1, ha⟩) : ℕ) ≤ vtN b σ a.castSucc j := by
    have := hmono; rw [hic, hvac] at this; exact this
  have hjceq : vtN b σ a.castSucc j = (b.1 (σ ⟨(a:ℕ)+1, ha⟩) : ℕ) :=
    le_antisymm (Nat.le_of_lt_succ hgt) hmono'
  -- flat
  have hflat : vtN b σ a.castSucc ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩
      = (b.1 (σ ⟨(a:ℕ)+1, ha⟩) : ℕ) := by
    have h1 : (b.1 (σ ⟨(a:ℕ)+1, ha⟩) : ℕ)
        ≤ vtN b σ a.castSucc ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ := by
      have := h.2 a.castSucc (σ ⟨(a:ℕ)+1, ha⟩)
        ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ (by rw [Fin.le_def]; simp)
      rwa [hvac] at this
    have h2 : vtN b σ a.castSucc ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩
        ≤ vtN b σ a.castSucc j := by
      apply h.2
      rw [Fin.le_def]; simp; omega
    omega
  have hstep : vtN b σ a.castSucc ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩
      = (b.1 ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ : ℕ)
        + (if ((σ.symm ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ : Fin d) : ℕ) < (a:ℕ)
            then 1 else 0) := by
    rw [vtN, Fin.val_castSucc]
  rw [hstep] at hflat
  have hb_eq : (b.1 (σ ⟨(a:ℕ)+1, ha⟩) : ℕ)
      = (b.1 ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ : ℕ) := by
    have := b.2 (σ ⟨(a:ℕ)+1, ha⟩) ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩
      (by rw [Fin.le_def]; simp)
    omega
  have hsymm_ge : ¬ (((σ.symm ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ : Fin d) : ℕ) < (a:ℕ)) := by
    intro hc; rw [if_pos hc] at hflat; omega
  -- V_{a+2}
  have ha2 : (a:ℕ)+2 < d+1 := by omega
  have hV2 : vtN b σ ⟨(a:ℕ)+2, ha2⟩ (σ ⟨(a:ℕ)+1, ha⟩)
      ≤ vtN b σ ⟨(a:ℕ)+2, ha2⟩ ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ := by
    apply h.2; rw [Fin.le_def]; simp
  have hV2c : vtN b σ ⟨(a:ℕ)+2, ha2⟩ (σ ⟨(a:ℕ)+1, ha⟩)
      = (b.1 (σ ⟨(a:ℕ)+1, ha⟩) : ℕ) + 1 := by
    have hsymm : (σ.symm (σ ⟨(a:ℕ)+1, ha⟩) : Fin d) = ⟨(a:ℕ)+1, ha⟩ := Equiv.symm_apply_apply σ _
    have hv : ((σ.symm (σ ⟨(a:ℕ)+1, ha⟩) : Fin d) : ℕ) = (a:ℕ)+1 := by rw [hsymm]
    rw [vtN, hv, if_pos (by omega : (a:ℕ)+1 < (a:ℕ)+2)]
  have hV2c2 : vtN b σ ⟨(a:ℕ)+2, ha2⟩ ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩
      = (b.1 (σ ⟨(a:ℕ)+1, ha⟩) : ℕ)
        + (if ((σ.symm ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ : Fin d) : ℕ) < (a:ℕ)+2
            then 1 else 0) := by
    rw [vtN, hb_eq]
  rw [hV2c, hV2c2] at hV2
  have hsymm_lt : ((σ.symm ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ : Fin d) : ℕ) < (a:ℕ)+2 := by
    by_contra hc'; rw [if_neg hc'] at hV2; omega
  have hsymm_ne : ((σ.symm ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ : Fin d) : ℕ) ≠ (a:ℕ)+1 := by
    intro hh
    have h2 : σ.symm ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ = ⟨(a:ℕ)+1, ha⟩ := Fin.ext hh
    have h3 : ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ = σ ⟨(a:ℕ)+1, ha⟩ := by
      rw [← Equiv.apply_symm_apply σ ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩, h2]
    exact absurd (congrArg Fin.val h3) (by simp)
  have hsymm_a : ((σ.symm ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ : Fin d) : ℕ) = (a:ℕ) := by
    omega
  have hsa : σ a = ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ := by
    have hsymm_a' : σ.symm ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ = a := Fin.ext hsymm_a
    calc σ a = σ (σ.symm ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩) := by rw [hsymm_a']
      _ = ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ := Equiv.apply_symm_apply σ _
  -- conclusion
  refine ⟨⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, by omega⟩, fun t ht => ?_⟩
  have htne : (t:ℕ) ≠ (a:ℕ)+1 := by
    intro hh; exact ht (by ext; rw [Fin.val_succ, hh])
  rw [gap_succ_eq b σ h t (σ ⟨(a:ℕ)+1, ha⟩) hcc_lt]
  have e1 : vtN b σ t ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩
      = (b.1 (σ ⟨(a:ℕ)+1, ha⟩) : ℕ) + (if (a:ℕ) < (t:ℕ) then 1 else 0) := by
    rw [vtN]
    have hsymm : σ.symm ⟨((σ ⟨(a:ℕ)+1, ha⟩ : Fin d) : ℕ)+1, hcc_lt⟩ = a := Fin.ext hsymm_a
    simp only [hsymm, hb_eq]
  have e2 : vtN b σ t (σ ⟨(a:ℕ)+1, ha⟩) = (b.1 (σ ⟨(a:ℕ)+1, ha⟩) : ℕ)
      + (if (a:ℕ)+1 < (t:ℕ) then 1 else 0) := by
    have hsymm : (σ.symm (σ ⟨(a:ℕ)+1, ha⟩) : Fin d) = ⟨(a:ℕ)+1, ha⟩ := Equiv.symm_apply_apply σ _
    have hv : ((σ.symm (σ ⟨(a:ℕ)+1, ha⟩) : Fin d) : ℕ) = (a:ℕ)+1 := by rw [hsymm]
    rw [vtN, hv]
  rw [e1, e2, Nat.add_sub_add_left]
  by_cases hcase : (a:ℕ) < (t:ℕ)
  · rw [if_pos hcase, if_pos (by omega)]
  · rw [if_neg hcase, if_neg (by omega)]


lemma isCell_flip_interior {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (a : Fin d) (ha : (a:ℕ)+1 < d)
    (hw : (∀ j, vtN b σ a.castSucc j + (if j = σ ⟨(a:ℕ)+1, ha⟩ then 1 else 0) ≤ m)
        ∧ (∀ i j, i ≤ j → vtN b σ a.castSucc i + (if i = σ ⟨(a:ℕ)+1, ha⟩ then 1 else 0)
            ≤ vtN b σ a.castSucc j + (if j = σ ⟨(a:ℕ)+1, ha⟩ then 1 else 0))) :
    IsCell b ((Equiv.swap a ⟨(a:ℕ)+1, ha⟩).trans σ) := by
  constructor
  · intro t j
    by_cases ht : t = Fin.succ a
    · subst ht
      simp only [vtN_flip_apply_eq b σ a ha]; exact hw.1 j
    · simp only [vtN_flip_apply_ne b σ a ha t ht]; exact h.1 t j
  · intro t i j hij
    by_cases ht : t = Fin.succ a
    · subst ht
      simp only [vtN_flip_apply_eq b σ a ha]
      exact hw.2 i j hij
    · simp only [vtN_flip_apply_ne b σ a ha t ht]; exact h.2 t i j hij

lemma gapset_nonempty_of_mult_one_interior {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d))
    (h : IsCell b σ) (s : Fin (d+1)) (hs1 : 1 ≤ (s:ℕ)) (hsd : (s:ℕ) < d)
    (hmult : ((Cells d m).filter (fun C => (cellSet b σ h).erase (vert b σ h s) ⊆ C)).card = 1) :
    ∃ k : Fin (d+1), ∀ t : Fin (d+1), t ≠ s → gap (vert b σ h t) k = 0 := by
  set a : Fin d := ⟨(s:ℕ)-1, by omega⟩ with ha'
  have ha_val : (a:ℕ) = (s:ℕ) - 1 := by rw [ha']
  have ha : (a:ℕ)+1 < d := by have := s.isLt; omega
  have hseq : Fin.succ a = s := by
    apply Fin.ext
    rw [Fin.val_succ, ha_val]
    omega
  by_contra hcon
  push_neg at hcon
  have hw : (∀ j, vtN b σ a.castSucc j + (if j = σ ⟨(a:ℕ)+1, ha⟩ then 1 else 0) ≤ m)
      ∧ (∀ i j, i ≤ j → vtN b σ a.castSucc i + (if i = σ ⟨(a:ℕ)+1, ha⟩ then 1 else 0)
          ≤ vtN b σ a.castSucc j + (if j = σ ⟨(a:ℕ)+1, ha⟩ then 1 else 0)) := by
    refine ⟨fun j => w_le b σ h a ha j, ?_⟩
    by_contra hmono
    push_neg at hmono
    obtain ⟨k, hk⟩ := gapset_of_not_mono b σ h a ha hmono
    obtain ⟨t, htne, htg⟩ := hcon k
    exact htg (hk t (by rw [hseq]; exact htne))
  have hcell : IsCell b ((Equiv.swap a ⟨(a:ℕ)+1, ha⟩).trans σ) := isCell_flip_interior b σ h a ha hw
  have hfv : ∀ t, t ≠ s →
      vert b ((Equiv.swap a ⟨(a:ℕ)+1, ha⟩).trans σ) hcell t = vert b σ h t := by
    intro t ht
    apply Subtype.ext; funext j; apply Fin.ext
    rw [vert_apply, vert_apply, vtN_flip_apply_ne b σ a ha t (by rw [hseq]; exact ht)]
  have hfne : vert b ((Equiv.swap a ⟨(a:ℕ)+1, ha⟩).trans σ) hcell s ≠ vert b σ h s := by
    rw [← hseq]
    intro hh
    have h2 := congrArg (fun z : OPt d m => ((z.1 (σ ⟨(a:ℕ)+1, ha⟩) : Fin (m+1)) : ℕ)) hh
    rw [vert_apply, vert_apply,
        vtN_flip_apply_eq b σ a ha (σ ⟨(a:ℕ)+1, ha⟩)] at h2
    rw [vtN_succ_apply b σ a (σ ⟨(a:ℕ)+1, ha⟩)] at h2
    have h3 : ¬ (σ ⟨(a:ℕ)+1, ha⟩ = σ a) := by
      intro hh'
      have h4 : (⟨(a:ℕ)+1, ha⟩ : Fin d) = a := σ.injective hh'
      have := congrArg Fin.val h4
      simp only [Fin.val_mk] at this
      omega
    rw [if_pos rfl, if_neg h3, add_zero] at h2
    omega
  have hCne : cellSet b σ h
      ≠ cellSet b ((Equiv.swap a ⟨(a:ℕ)+1, ha⟩).trans σ) hcell := by
    intro hh
    have hmem : vert b σ h s ∈ cellSet b ((Equiv.swap a ⟨(a:ℕ)+1, ha⟩).trans σ) hcell := by
      rw [← hh]; exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
    obtain ⟨t, ht⟩ := mem_cellSet.mp hmem
    by_cases hts : t = s
    · exact hfne (by rw [← ht, hts])
    · rw [hfv t hts] at ht
      exact hts (vert_injective b σ h ht)
  have hmem1 : cellSet b σ h ∈ (Cells d m).filter
      (fun C => (cellSet b σ h).erase (vert b σ h s) ⊆ C) :=
    Finset.mem_filter.mpr ⟨mem_Cells.mpr ⟨b, σ, h, rfl⟩, Finset.erase_subset _ _⟩
  have hmem2 : cellSet b ((Equiv.swap a ⟨(a:ℕ)+1, ha⟩).trans σ) hcell ∈ (Cells d m).filter
      (fun C => (cellSet b σ h).erase (vert b σ h s) ⊆ C) := by
    refine Finset.mem_filter.mpr ⟨mem_Cells.mpr ⟨b, _, hcell, rfl⟩, ?_⟩
    intro x hx
    rw [Finset.mem_erase] at hx
    obtain ⟨hxne, hxmem⟩ := hx
    obtain ⟨t, ht⟩ := mem_cellSet.mp hxmem
    rw [mem_cellSet]
    refine ⟨t, ?_⟩
    rw [hfv t ?_, ht]
    intro hts
    exact hxne (by rw [← ht, hts])
  have h2 : 2 ≤ ((Cells d m).filter (fun C => (cellSet b σ h).erase (vert b σ h s) ⊆ C)).card := by
    have hsub : ({cellSet b σ h,
        cellSet b ((Equiv.swap a ⟨(a:ℕ)+1, ha⟩).trans σ) hcell} : Finset (Finset (OPt d m)))
        ⊆ (Cells d m).filter (fun C => (cellSet b σ h).erase (vert b σ h s) ⊆ C) := by
      intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact hmem1
      · rw [Finset.mem_singleton] at hC; rw [hC]; exact hmem2
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair hCne] at hcard
    exact hcard
  omega


/-! ## The shift permutations -/

def shiftUp {d : ℕ} (p : Fin d) : Fin d :=
  if h : (p:ℕ)+1 = d then ⟨0, by omega⟩ else ⟨(p:ℕ)+1, by omega⟩

lemma shiftUp_val {d : ℕ} (p : Fin d) :
    ((shiftUp p : Fin d) : ℕ) = if (p:ℕ)+1 = d then 0 else (p:ℕ)+1 := by
  rw [shiftUp]; split_ifs with hh <;> rfl

lemma shiftUp_injective {d : ℕ} : Function.Injective (shiftUp (d:=d)) := by
  intro p q hpq
  have hv := congrArg Fin.val hpq
  simp only [shiftUp_val] at hv
  split_ifs at hv with h1 h2 <;> apply Fin.ext <;> omega

lemma shiftUp_surjective {d : ℕ} : Function.Surjective (shiftUp (d:=d)) := by
  intro k
  have hd : 0 < d := by have := k.isLt; omega
  by_cases hk : (k:ℕ) = 0
  · refine ⟨⟨d-1, by omega⟩, ?_⟩
    apply Fin.ext
    rw [shiftUp_val, if_pos (by simp only [Fin.val_mk]; omega)]
    exact hk.symm
  · refine ⟨⟨(k:ℕ)-1, by omega⟩, ?_⟩
    apply Fin.ext
    rw [shiftUp_val, if_neg (by simp only [Fin.val_mk]; omega)]
    simp only [Fin.val_mk]
    omega

def shiftP {d : ℕ} : Equiv.Perm (Fin d) :=
  Equiv.ofBijective (shiftUp (d:=d)) ⟨shiftUp_injective, shiftUp_surjective⟩

@[simp] lemma shiftP_apply {d : ℕ} (p : Fin d) : (shiftP (d:=d)) p = shiftUp p := rfl


lemma vtN_shiftP_symm {d : ℕ} (σ : Equiv.Perm (Fin d)) (j : Fin d) :
    (((shiftP.symm.trans σ)).symm j) = shiftUp (σ.symm j) := by
  rw [Equiv.symm_trans_apply, Equiv.symm_symm, shiftP_apply]

lemma vtN_shiftP_succ {d m : ℕ} (b b'' : OPt d m) (σ : Equiv.Perm (Fin d)) (c : Fin d)
    (hd : 1 ≤ d) (hc : σ (⟨d-1, by omega⟩ : Fin d) = c)
    (hb'' : ∀ j, (b''.1 j : ℕ) = (b.1 j : ℕ) - (if j = c then 1 else 0))
    (hbc : 1 ≤ (b.1 c : ℕ)) (i : Fin d) (j : Fin d) :
    vtN b'' (shiftP.symm.trans σ) (Fin.succ i) j = vtN b σ i.castSucc j := by
  rw [vtN, vtN, Fin.val_succ, Fin.val_castSucc, vtN_shiftP_symm, hb'', shiftUp_val]
  rcases eq_or_ne j c with hjc | hjc
  · have hp : ((σ.symm c : Fin d) : ℕ) = d - 1 := by
      rw [← hc, Equiv.symm_apply_apply, Fin.val_mk]
    rw [hjc, if_pos rfl, hp, if_pos (by omega : (d-1)+1 = d),
        if_pos (by omega : (0:ℕ) < (i:ℕ)+1)]
    rw [if_neg (by have := i.isLt; omega : ¬ (d - 1 < (i:ℕ)))]
    have := hbc; omega
  · have hpne : ((σ.symm j : Fin d) : ℕ) + 1 ≠ d := by
      intro hh
      apply hjc
      have hv : ((σ.symm j : Fin d) : ℕ) = d - 1 := Nat.eq_sub_of_add_eq hh
      have h1 : σ.symm j = (⟨d-1, by omega⟩ : Fin d) := Fin.ext (by rw [Fin.val_mk]; exact hv)
      rw [← hc]
      exact (Equiv.symm_apply_eq σ).mp h1
    rw [if_neg hjc, if_neg hpne, Nat.sub_zero]
    by_cases hlt : ((σ.symm j : Fin d) : ℕ) < (i:ℕ)
    · rw [if_pos (Nat.add_lt_add_iff_right.mpr hlt), if_pos hlt]
    · rw [if_neg (fun h => hlt (Nat.add_lt_add_iff_right.mp h)), if_neg hlt]

lemma gap_zero_val {d m : ℕ} (hd : 1 ≤ d) (z : OPt d m) :
    gap z 0 = ((z.1 ⟨0, by omega⟩ : Fin (m+1)) : ℕ) := by
  rw [gap_eq, Fin.val_zero, extN_zero, Nat.sub_zero]
  rw [extN]
  rw [if_neg (by omega : ¬ ((0:ℕ)+1 = 0)), Nat.add_sub_cancel]
  rw [dif_pos (by omega : (0:ℕ) < d)]

lemma isCell_shiftP {d m : ℕ} (b b'' : OPt d m) (σ : Equiv.Perm (Fin d)) (c : Fin d)
    (hd : 1 ≤ d) (hcσ : σ (⟨d-1, by omega⟩ : Fin d) = c)
    (hb'' : ∀ j, (b''.1 j : ℕ) = (b.1 j : ℕ) - (if j = c then 1 else 0))
    (hbc : 1 ≤ (b.1 c : ℕ)) (h : IsCell b σ) : IsCell b'' (shiftP.symm.trans σ) := by
  constructor
  · intro t j
    rcases Fin.eq_zero_or_eq_succ t with ht | ⟨i, rfl⟩
    · rw [ht, vtN]
      simp only [Fin.val_zero, Nat.not_lt_zero, if_false, add_zero]
      exact Nat.lt_succ_iff.mp ((b''.1 j : Fin (m+1))).isLt
    · rw [vtN_shiftP_succ b b'' σ c hd hcσ hb'' hbc i j]; exact h.1 i.castSucc j
  · intro t i j hij
    rcases Fin.eq_zero_or_eq_succ t with ht | ⟨k, rfl⟩
    · rw [ht, vtN, vtN]
      simp only [Fin.val_zero, Nat.not_lt_zero, if_false, add_zero]
      exact b''.2 i j hij
    · rw [vtN_shiftP_succ b b'' σ c hd hcσ hb'' hbc k i,
          vtN_shiftP_succ b b'' σ c hd hcσ hb'' hbc k j]
      exact h.2 k.castSucc i j hij


lemma last_coord_one {d m : ℕ} (hd : 1 ≤ d) (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    {c : Fin d} (hc : σ (⟨d-1, by omega⟩ : Fin d) = c) (hc1 : 1 ≤ (c:ℕ)) :
    (b.1 ⟨(c:ℕ)-1, by omega⟩ : ℕ) < (b.1 c : ℕ) := by
  have hmono := h.2 (⟨d-1, by omega⟩ : Fin (d+1)) ⟨(c:ℕ)-1, by omega⟩ c
    (by simp only [Fin.le_def, Fin.val_mk]; omega)
  have e1 : (vtN b σ (⟨d-1, by omega⟩ : Fin (d+1)) ⟨(c:ℕ)-1, by omega⟩ : ℕ)
      = (b.1 ⟨(c:ℕ)-1, by omega⟩ : ℕ) + 1 := by
    have hne : ((σ.symm ⟨(c:ℕ)-1, by omega⟩ : Fin d) : ℕ) ≠ d - 1 := by
      intro hh
      have hh2 : σ.symm ⟨(c:ℕ)-1, by omega⟩ = (⟨d-1, by omega⟩ : Fin d) :=
        Fin.ext (by rw [hh, Fin.val_mk])
      have hh3 := congrArg σ hh2
      rw [Equiv.apply_symm_apply, hc] at hh3
      have hh4 := congrArg Fin.val hh3
      rw [Fin.val_mk, Fin.val_mk] at hh4
      omega
    have hlt : ((σ.symm ⟨(c:ℕ)-1, by omega⟩ : Fin d) : ℕ) < (d - 1) := by
      have := (σ.symm ⟨(c:ℕ)-1, by omega⟩).isLt
      omega
    rw [vtN, if_pos hlt]
  have e2 : (vtN b σ (⟨d-1, by omega⟩ : Fin (d+1)) c : ℕ) = (b.1 c : ℕ) := by
    have hge : ¬ (((σ.symm c : Fin d) : ℕ) < (d - 1)) := by
      intro hh
      have hh2 : σ.symm c = (⟨d-1, by omega⟩ : Fin d) := (Equiv.symm_apply_eq σ).mpr hc.symm
      rw [hh2, Fin.val_mk] at hh
      omega
    rw [vtN, if_neg hge, add_zero]
  rw [e1, e2] at hmono
  omega

lemma last_coord_zero {d m : ℕ} (hd : 1 ≤ d) (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    {c : Fin d} (hc : σ (⟨d-1, by omega⟩ : Fin d) = c) (hz : (b.1 c : ℕ) = 0) : (c:ℕ) = 0 := by
  by_contra hne
  have hc1 : 1 ≤ (c:ℕ) := by omega
  have := last_coord_one hd b σ h hc hc1
  omega


lemma gapset_nonempty_of_mult_one_last {d m : ℕ} (hd : 1 ≤ d) (b : OPt d m) (σ : Equiv.Perm (Fin d))
    (h : IsCell b σ)
    (hmult : ((Cells d m).filter (fun C => (cellSet b σ h).erase (vert b σ h (Fin.last d)) ⊆ C)).card = 1) :
    ∃ k : Fin (d+1), ∀ t : Fin (d+1), t ≠ Fin.last d → gap (vert b σ h t) k = 0 := by
  haveI : NeZero d := ⟨fun hh => by omega⟩
  by_contra hcon
  push_neg at hcon
  have hz0 : ¬ ((b.1 (⟨0, by omega⟩ : Fin d) : ℕ) = 0 ∧ σ (⟨d-1, by omega⟩ : Fin d) = 0) := by
    rintro ⟨hb0, hc0⟩
    obtain ⟨t, htne, htg⟩ := hcon 0
    refine htg ?_
    have hs0 : σ.symm (⟨0, by omega⟩ : Fin d) = (⟨d-1, by omega⟩ : Fin d) :=
      (Equiv.symm_apply_eq σ).mpr (by rw [hc0]; rfl)
    rw [gap_zero_val hd, vert_apply, vtN, hb0, hs0, Fin.val_mk, zero_add]
    have htlt : ¬ ((d - 1) < (t:ℕ)) := by
      have h1 : (t:ℕ) ≠ d := fun hh => htne (by ext; rw [Fin.val_last]; exact hh)
      have := t.isLt
      omega
    rw [if_neg htlt]
  have hbc : 1 ≤ (b.1 (σ (⟨d-1, by omega⟩ : Fin d)) : ℕ) := by
    by_contra hlt
    have hz : (b.1 (σ (⟨d-1, by omega⟩ : Fin d)) : ℕ) = 0 := by omega
    have hc0v : ((σ (⟨d-1, by omega⟩ : Fin d)) : ℕ) = 0 := last_coord_zero hd b σ h rfl hz
    have hc0f : σ (⟨d-1, by omega⟩ : Fin d) = (0 : Fin d) := Fin.ext (by rw [hc0v, Fin.val_zero])
    have hb0 : (b.1 (⟨0, by omega⟩ : Fin d) : ℕ) = 0 := by
      have h0c : (⟨0, by omega⟩ : Fin d) = σ (⟨d-1, by omega⟩ : Fin d) := hc0f.symm
      rw [h0c]; exact hz
    exact hz0 ⟨hb0, hc0f⟩
  have hmontv : ∀ i j : Fin d, i ≤ j →
      (b.1 i : ℕ) - (if i = σ (⟨d-1, by omega⟩ : Fin d) then 1 else 0)
        ≤ (b.1 j : ℕ) - (if j = σ (⟨d-1, by omega⟩ : Fin d) then 1 else 0) := by
    intro i j hij
    by_cases hic : i = σ (⟨d-1, by omega⟩ : Fin d)
    · rw [hic] at hij
      rw [hic]
      by_cases hjc : j = σ (⟨d-1, by omega⟩ : Fin d)
      · rw [hjc]
      · rw [if_pos rfl, if_neg hjc, Nat.sub_zero]
        exact le_trans (Nat.sub_le _ _) (b.2 _ j hij)
    · rw [if_neg hic]
      by_cases hjc : j = σ (⟨d-1, by omega⟩ : Fin d)
      · rw [hjc]
        rw [if_pos rfl]
        have hicl : (i:ℕ) < ((σ (⟨d-1, by omega⟩ : Fin d)) : ℕ) := by
          have h1 : (i:ℕ) ≤ ((σ (⟨d-1, by omega⟩ : Fin d)) : ℕ) := by rw [← hjc]; exact hij
          rcases lt_or_eq_of_le h1 with hh | hh
          · exact hh
          · exact absurd (Fin.ext hh) hic
        have hc1 : 1 ≤ ((σ (⟨d-1, by omega⟩ : Fin d)) : ℕ) := by omega
        have hlt := last_coord_one hd b σ h rfl hc1
        have hile : (b.1 i : ℕ) ≤ (b.1 ⟨((σ (⟨d-1, by omega⟩ : Fin d)) : ℕ)-1, by omega⟩ : ℕ) :=
          b.2 i _ (by rw [Fin.le_def]; simp; omega)
        omega
      · rw [if_neg hjc, Nat.sub_zero]
        exact b.2 i j hij
  let b'' : OPt d m :=
    ⟨fun j => ⟨(b.1 j : ℕ) - (if j = σ (⟨d-1, by omega⟩ : Fin d) then 1 else 0),
        by have := (b.1 j).isLt; split_ifs <;> omega⟩, hmontv⟩
  have hb'' : ∀ j, (b''.1 j : ℕ) = (b.1 j : ℕ) - (if j = σ (⟨d-1, by omega⟩ : Fin d) then 1 else 0) :=
    fun j => rfl
  have hcell : IsCell b'' (shiftP.symm.trans σ) := isCell_shiftP b b'' σ _ hd rfl hb'' hbc h
  have hfv : ∀ i : Fin d, vert b'' (shiftP.symm.trans σ) hcell (Fin.succ i) = vert b σ h i.castSucc := by
    intro i
    apply Subtype.ext; funext j; apply Fin.ext
    rw [vert_apply, vert_apply, vtN_shiftP_succ b b'' σ _ hd rfl hb'' hbc i j]
  have hb''0 : vert b'' (shiftP.symm.trans σ) hcell 0 = b'' := by
    apply Subtype.ext; funext j; apply Fin.ext
    rw [vert_apply, vtN]
    simp only [Fin.val_zero, Nat.not_lt_zero, if_false, add_zero]
  have hlt_b : b'' < b := by
    apply lt_of_le_of_ne
    · intro j
      rw [hb'' j]
      by_cases hjc : j = σ (⟨d-1, by omega⟩ : Fin d)
      · rw [if_pos hjc]; omega
      · rw [if_neg hjc, Nat.sub_zero]
    · intro hh2
      have h1 := congrArg (fun z : OPt d m => (z.1 (σ (⟨d-1, by omega⟩ : Fin d)) : ℕ)) hh2
      rw [hb'' (σ (⟨d-1, by omega⟩ : Fin d)), if_pos rfl] at h1
      omega
  have hsub : (cellSet b σ h).erase (vert b σ h (Fin.last d))
      ⊆ cellSet b'' (shiftP.symm.trans σ) hcell := by
    intro x hx
    rw [Finset.mem_erase] at hx
    obtain ⟨hxne, hxmem⟩ := hx
    obtain ⟨t, ht⟩ := mem_cellSet.mp hxmem
    have htne : t ≠ Fin.last d := fun hh => hxne (by rw [← ht, hh])
    have hlt : (t:ℕ) < d := by
      have h1 : (t:ℕ) ≠ d := fun hh => htne (by ext; rw [Fin.val_last]; exact hh)
      have := t.isLt; omega
    refine mem_cellSet.mpr ⟨(⟨(t:ℕ), hlt⟩ : Fin d).succ, ?_⟩
    rw [hfv ⟨(t:ℕ), hlt⟩, ← ht]
    congr 1
  have hne : cellSet b'' (shiftP.symm.trans σ) hcell ≠ cellSet b σ h := by
    intro hh
    have hmem : b'' ∈ cellSet b σ h := by
      rw [← hh]; exact mem_cellSet.mpr ⟨0, hb''0.symm⟩
    obtain ⟨t, ht⟩ := mem_cellSet.mp hmem
    have hle : b ≤ b'' := by
      have h1 : vert b σ h 0 ≤ vert b σ h t := vert_mono b σ h (Fin.zero_le t)
      rwa [vert_zero, ht] at h1
    exact absurd hle (not_le_of_gt hlt_b)
  have hmem1 : cellSet b σ h ∈ (Cells d m).filter
      (fun C => (cellSet b σ h).erase (vert b σ h (Fin.last d)) ⊆ C) :=
    Finset.mem_filter.mpr ⟨mem_Cells.mpr ⟨b, σ, h, rfl⟩, Finset.erase_subset _ _⟩
  have hmem2 : cellSet b'' (shiftP.symm.trans σ) hcell ∈ (Cells d m).filter
      (fun C => (cellSet b σ h).erase (vert b σ h (Fin.last d)) ⊆ C) :=
    Finset.mem_filter.mpr ⟨mem_Cells.mpr ⟨b'', _, hcell, rfl⟩, hsub⟩
  have h2 : 2 ≤ ((Cells d m).filter (fun C => (cellSet b σ h).erase (vert b σ h (Fin.last d)) ⊆ C)).card := by
    have hsub2 : ({cellSet b'' (shiftP.symm.trans σ) hcell, cellSet b σ h} : Finset (Finset (OPt d m)))
        ⊆ (Cells d m).filter (fun C => (cellSet b σ h).erase (vert b σ h (Fin.last d)) ⊆ C) := by
      intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact hmem2
      · rw [Finset.mem_singleton] at hC; rw [hC]; exact hmem1
    have hcard := Finset.card_le_card hsub2
    rw [Finset.card_pair (a := cellSet b'' (shiftP.symm.trans σ) hcell) (b := cellSet b σ h) hne] at hcard
    exact hcard
  omega


lemma shiftUp_self {d : ℕ} (hd : 1 ≤ d) (p : Fin d) :
    shiftUp (if (p:ℕ) = 0 then (⟨d-1, by omega⟩ : Fin d) else ⟨(p:ℕ)-1, by have := p.isLt; omega⟩) = p := by
  apply Fin.ext
  rw [shiftUp_val]
  by_cases hp : (p:ℕ) = 0
  · rw [if_pos hp, Fin.val_mk, if_pos (by omega : d-1+1 = d)]
    exact hp.symm
  · rw [if_neg hp, Fin.val_mk]
    have h1 : ¬ ((p:ℕ)-1+1 = d) := by have := p.isLt; omega
    rw [if_neg h1]
    omega

lemma shiftP_symm_val {d : ℕ} (hd : 1 ≤ d) (p : Fin d) :
    ((shiftP.symm p : Fin d) : ℕ) = if (p:ℕ) = 0 then d - 1 else (p:ℕ) - 1 := by
  have hsymm : shiftP.symm p = (if (p:ℕ) = 0 then (⟨d-1, by omega⟩ : Fin d) else ⟨(p:ℕ)-1, by have := p.isLt; omega⟩) :=
    (Equiv.symm_apply_eq shiftP).mpr (by rw [shiftP_apply]; exact (shiftUp_self hd p).symm)
  rw [hsymm]
  by_cases hp : (p:ℕ) = 0
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp]


lemma gap_last_val {d m : ℕ} (hd : 1 ≤ d) (z : OPt d m) :
    gap z (Fin.last d) = m - ((z.1 (⟨d-1, by omega⟩ : Fin d) : Fin (m+1)) : ℕ) := by
  rw [gap_eq, Fin.val_last, extN_last]
  congr 1
  rw [extN, if_neg (by omega : ¬ (d = 0)), dif_pos (by omega : d - 1 < d)]

lemma vtN_shiftP_castSucc {d m : ℕ} (b b' : OPt d m) (σ : Equiv.Perm (Fin d)) (c : Fin d)
    (hd : 1 ≤ d) (hc : σ (⟨0, by omega⟩ : Fin d) = c)
    (hb' : ∀ j, (b'.1 j : ℕ) = (b.1 j : ℕ) + (if j = c then 1 else 0))
    (i : Fin d) (j : Fin d) :
    vtN b' (shiftP.trans σ) i.castSucc j = vtN b σ (Fin.succ i) j := by
  rw [vtN, vtN, Fin.val_castSucc, Fin.val_succ]
  rw [show (((shiftP.trans σ).symm j : Fin d) : ℕ) = (shiftP.symm (σ.symm j) : ℕ) from rfl]
  rw [shiftP_symm_val hd (σ.symm j), hb']
  have hj0 : (if j = c then (1:ℕ) else 0)
      = (if (σ.symm j : Fin d) = ⟨0, by omega⟩ then 1 else 0) := by
    by_cases h : j = c
    · rw [if_pos h, if_pos ((Equiv.symm_apply_eq σ).mpr (by rw [h]; exact hc.symm))]
    · rw [if_neg h, if_neg (fun hh => h (hc ▸ (Equiv.symm_apply_eq σ).mp hh))]
  rw [hj0]
  by_cases hp : ((σ.symm j : Fin d) : ℕ) = 0
  · have hpeq : (σ.symm j : Fin d) = ⟨0, by omega⟩ := Fin.ext (by rw [hp, Fin.val_mk])
    rw [if_pos hpeq, if_pos hp]
    have hid : ¬ (d - 1 < (i:ℕ)) := by have := i.isLt; omega
    rw [if_neg hid, hp, if_pos (by omega : (0:ℕ) < (i:ℕ)+1)]
  · have hpne : (σ.symm j : Fin d) ≠ ⟨0, by omega⟩ := fun hh => hp (by rw [hh, Fin.val_mk])
    rw [if_neg hpne, if_neg hp]
    have hkey : (if ((σ.symm j : Fin d) : ℕ) - 1 < (i:ℕ) then (1:ℕ) else 0)
        = (if ((σ.symm j : Fin d) : ℕ) < (i:ℕ)+1 then 1 else 0) := by
      by_cases hh : ((σ.symm j : Fin d) : ℕ) < (i:ℕ)+1
      · rw [if_pos (by omega), if_pos hh]
      · rw [if_neg (by omega), if_neg hh]
    rw [hkey]
    omega


lemma vtN_shiftP_last {d m : ℕ} (b b' : OPt d m) (σ : Equiv.Perm (Fin d)) (c : Fin d)
    (hd : 1 ≤ d) (hb' : ∀ j, (b'.1 j : ℕ) = (b.1 j : ℕ) + (if j = c then 1 else 0)) (j : Fin d) :
    vtN b' (shiftP.trans σ) (Fin.last d) j = (b'.1 j : ℕ) + 1 := by
  rw [vtN, Fin.val_last]
  rw [show (((shiftP.trans σ).symm j : Fin d) : ℕ) = (shiftP.symm (σ.symm j) : ℕ) from rfl]
  rw [shiftP_symm_val hd (σ.symm j)]
  have hlt : (if ((σ.symm j : Fin d) : ℕ) = 0 then d - 1 else ((σ.symm j : Fin d) : ℕ) - 1) < d := by
    split_ifs <;> omega
  rw [if_pos hlt]

lemma isCell_shiftP' {d m : ℕ} (b b' : OPt d m) (σ : Equiv.Perm (Fin d)) (c : Fin d)
    (hd : 1 ≤ d) (hc : σ (⟨0, by omega⟩ : Fin d) = c)
    (hb' : ∀ j, (b'.1 j : ℕ) = (b.1 j : ℕ) + (if j = c then 1 else 0))
    (h : IsCell b σ) (hW : ∀ j, (b'.1 j : ℕ) + 1 ≤ m) :
    IsCell b' (shiftP.trans σ) := by
  constructor
  · intro t j
    by_cases ht : t = Fin.last d
    · rw [ht, vtN_shiftP_last b b' σ c hd hb' j]; exact hW j
    · have hlt : (t:ℕ) < d := by
        have h1 : (t:ℕ) ≠ d := fun hh => ht (by ext; rw [Fin.val_last]; exact hh)
        have := t.isLt; omega
      have ht' : t = (⟨(t:ℕ), hlt⟩ : Fin d).castSucc := by ext; simp [Fin.val_castSucc]
      rw [ht', vtN_shiftP_castSucc b b' σ c hd hc hb' ⟨(t:ℕ), hlt⟩ j]
      exact h.1 (Fin.succ _) j
  · intro t i j hij
    by_cases ht : t = Fin.last d
    · rw [ht, vtN_shiftP_last b b' σ c hd hb' i, vtN_shiftP_last b b' σ c hd hb' j]
      exact Nat.add_le_add_right (b'.2 i j hij) 1
    · have hlt : (t:ℕ) < d := by
        have h1 : (t:ℕ) ≠ d := fun hh => ht (by ext; rw [Fin.val_last]; exact hh)
        have := t.isLt; omega
      have ht' : t = (⟨(t:ℕ), hlt⟩ : Fin d).castSucc := by ext; simp [Fin.val_castSucc]
      rw [ht', vtN_shiftP_castSucc b b' σ c hd hc hb' ⟨(t:ℕ), hlt⟩ i,
          vtN_shiftP_castSucc b b' σ c hd hc hb' ⟨(t:ℕ), hlt⟩ j]
      exact h.2 (Fin.succ _) i j hij


lemma vtN_one_eq {d m : ℕ} (hd : 1 ≤ d) (b : OPt d m) (σ : Equiv.Perm (Fin d)) (j : Fin d) :
    vtN b σ (Fin.succ (⟨0, by omega⟩ : Fin d)) j
      = (b.1 j : ℕ) + (if j = σ (⟨0, by omega⟩ : Fin d) then 1 else 0) := by
  rw [vtN, Fin.val_succ, Fin.val_mk]
  congr 1
  have hiff : (σ.symm j = (⟨0, by omega⟩ : Fin d)) ↔ (j = σ (⟨0, by omega⟩ : Fin d)) := by
    rw [Equiv.symm_apply_eq]
  by_cases h : σ.symm j = (⟨0, by omega⟩ : Fin d)
  · rw [if_pos (by rw [h]; simp), if_pos (hiff.mp h)]
  · have h1 : ((σ.symm j : Fin d) : ℕ) ≠ 0 := fun hh => h (Fin.ext (by rw [hh, Fin.val_mk]))
    have h2 : j ≠ σ (⟨0, by omega⟩ : Fin d) := fun hh => h (hiff.mpr hh)
    rw [if_neg (by have := h1; omega : ¬ (((σ.symm j : Fin d) : ℕ) < 1)), if_neg h2]


lemma gapset_nonempty_of_mult_one_zero {d m : ℕ} (hd : 1 ≤ d) (b : OPt d m) (σ : Equiv.Perm (Fin d))
    (h : IsCell b σ)
    (hmult : ((Cells d m).filter (fun C => (cellSet b σ h).erase (vert b σ h 0) ⊆ C)).card = 1) :
    ∃ k : Fin (d+1), ∀ t : Fin (d+1), t ≠ 0 → gap (vert b σ h t) k = 0 := by
  haveI : NeZero d := ⟨fun hh => by omega⟩
  by_contra hcon
  push_neg at hcon
  set c : Fin d := σ (⟨0, by omega⟩ : Fin d) with hcdef
  have hcσ : σ (⟨0, by omega⟩ : Fin d) = c := by rw [hcdef]
  -- every coordinate of a valid base satisfies `b_j + 1 ≤ m`
  have hb1 : ∀ j : Fin d, (b.1 j : ℕ) + 1 ≤ m := by
    intro j
    have hlast := h.1 (Fin.last d) j
    have e : vtN b σ (Fin.last d) j = (b.1 j : ℕ) + 1 := by
      rw [vtN, Fin.val_last]
      have : ((σ.symm j : Fin d) : ℕ) < d := by have := (σ.symm j).isLt; omega
      rw [if_pos this]
    omega
  by_cases hA : (b.1 c : ℕ) + 2 ≤ m
  · -- the reflected cell is valid: contradiction with uniqueness
    set b' : OPt d m := vert b σ h (Fin.succ (⟨0, by omega⟩ : Fin d)) with hb'def
    have hb' : ∀ j, (b'.1 j : ℕ) = (b.1 j : ℕ) + (if j = c then 1 else 0) := by
      intro j
      rw [hb'def, vert_apply, hcdef]
      exact vtN_one_eq hd b σ j
    have hW : ∀ j, (b'.1 j : ℕ) + 1 ≤ m := by
      intro j
      rw [hb' j]
      by_cases hjc : j = c
      · rw [if_pos hjc]
        have hbc1 : (b.1 c : ℕ) + 2 ≤ m := hA
        have hjj : (b.1 j : ℕ) = (b.1 c : ℕ) := by rw [hjc]
        omega
      · rw [if_neg hjc]; have := hb1 j; omega
    have hcell : IsCell b' (shiftP.trans σ) := isCell_shiftP' b b' σ c hd hcσ hb' h hW
    have hfv : ∀ i : Fin d, vert b' (shiftP.trans σ) hcell i.castSucc = vert b σ h (Fin.succ i) := by
      intro i
      apply Subtype.ext; funext j; apply Fin.ext
      rw [vert_apply, vert_apply, vtN_shiftP_castSucc b b' σ c hd hcσ hb' i j]
    have hsub : (cellSet b σ h).erase (vert b σ h 0) ⊆ cellSet b' (shiftP.trans σ) hcell := by
      intro x hx
      rw [Finset.mem_erase] at hx
      obtain ⟨hxne, hxmem⟩ := hx
      obtain ⟨t, ht⟩ := mem_cellSet.mp hxmem
      have htne : t ≠ 0 := fun hh => hxne (by rw [← ht, hh])
      have htpos : 1 ≤ (t:ℕ) := by
        rcases Nat.eq_zero_or_pos (t:ℕ) with hh | hh
        · exact absurd (Fin.ext hh) htne
        · exact hh
      refine mem_cellSet.mpr ⟨(⟨(t:ℕ)-1, by have := t.isLt; omega⟩ : Fin d).castSucc, ?_⟩
      rw [hfv ⟨(t:ℕ)-1, by have := t.isLt; omega⟩, ← ht]
      congr 1
      apply Fin.ext
      rw [Fin.val_succ, Fin.val_mk]
      omega
    have hne : cellSet b' (shiftP.trans σ) hcell ≠ cellSet b σ h := by
      intro hh
      have hmem : vert b' (shiftP.trans σ) hcell (Fin.last d) ∈ cellSet b σ h :=
        hh ▸ mem_cellSet.mpr ⟨Fin.last d, rfl⟩
      obtain ⟨t, ht⟩ := mem_cellSet.mp hmem
      have h1 : ((vert b σ h t).1 c : ℕ)
          = ((vert b' (shiftP.trans σ) hcell (Fin.last d)).1 c : ℕ) :=
        congrArg (fun z : OPt d m => ((z.1 c : Fin (m+1)) : ℕ)) ht
      rw [vert_apply, vert_apply, vtN_shiftP_last b b' σ c hd hb' c, hb' c, if_pos rfl] at h1
      rw [vtN] at h1
      have h2 : ((σ.symm c : Fin d) : ℕ) = 0 := by rw [hcdef, Equiv.symm_apply_apply, Fin.val_mk]
      rw [h2] at h1
      by_cases ht0 : (t:ℕ) = 0
      · rw [if_neg (by omega : ¬ ((0:ℕ) < (t:ℕ)))] at h1
        omega
      · rw [if_pos (by omega : (0:ℕ) < (t:ℕ))] at h1
        omega
    have hmem1 : cellSet b σ h ∈ (Cells d m).filter
        (fun C => (cellSet b σ h).erase (vert b σ h 0) ⊆ C) :=
      Finset.mem_filter.mpr ⟨mem_Cells.mpr ⟨b, σ, h, rfl⟩, Finset.erase_subset _ _⟩
    have hmem2 : cellSet b' (shiftP.trans σ) hcell ∈ (Cells d m).filter
        (fun C => (cellSet b σ h).erase (vert b σ h 0) ⊆ C) :=
      Finset.mem_filter.mpr ⟨mem_Cells.mpr ⟨b', _, hcell, rfl⟩, hsub⟩
    have h2 : 2 ≤ ((Cells d m).filter (fun C => (cellSet b σ h).erase (vert b σ h 0) ⊆ C)).card := by
      have hsub2 : ({cellSet b' (shiftP.trans σ) hcell, cellSet b σ h} : Finset (Finset (OPt d m)))
          ⊆ (Cells d m).filter (fun C => (cellSet b σ h).erase (vert b σ h 0) ⊆ C) := by
        intro C hC
        rcases Finset.mem_insert.mp hC with rfl | hC
        · exact hmem2
        · rw [Finset.mem_singleton] at hC; rw [hC]; exact hmem1
      have hcard := Finset.card_le_card hsub2
      rw [Finset.card_pair (a := cellSet b' (shiftP.trans σ) hcell) (b := cellSet b σ h) hne] at hcard
      exact hcard
    omega
  · -- `b_c = m-1`: the whole facet lies in the last face
    push_neg at hA
    have hbc' : (b.1 c : ℕ) = m - 1 := by have := hb1 c; omega
    obtain ⟨t, htne, htg⟩ := hcon (Fin.last d)
    refine htg ?_
    have hvc : vtN b σ t c = m := by
      rw [vtN]
      have hsymm : σ.symm c = (⟨0, by omega⟩ : Fin d) := by
        rw [hcdef]; exact Equiv.symm_apply_apply σ _
      have hv : ((σ.symm c : Fin d) : ℕ) = 0 := by rw [hsymm, Fin.val_mk]
      have ht0 : (0:ℕ) < (t:ℕ) := by
        rcases Nat.eq_zero_or_pos (t:ℕ) with hh | hh
        · exact absurd (Fin.ext hh) htne
        · exact hh
      have hbc1 : (b.1 c : ℕ) + 1 ≤ m := hb1 c
      rw [hv, if_pos ht0, hbc']
      exact Nat.sub_add_cancel (by omega)
    have hvd : ((vert b σ h t).1 ⟨d-1, by omega⟩ : ℕ) = m := by
      rw [vert_apply]
      have hmono : vtN b σ t c ≤ vtN b σ t ⟨d-1, by omega⟩ :=
        h.2 t c ⟨d-1, by omega⟩ (by rw [Fin.le_def]; simp only [Fin.val_mk]; have := c.isLt; omega)
      have hle : vtN b σ t ⟨d-1, by omega⟩ ≤ m := h.1 t ⟨d-1, by omega⟩
      omega
    rw [gap_last_val hd (vert b σ h t), hvd]
    omega


/-! ## Gap coordinates and the lifted point -/

lemma liftO_injective {e m : ℕ} : Function.Injective (liftO (e:=e) (m:=m)) := by
  intro z' w' h
  have h1 := congrArg drop h
  rwa [drop_lift, drop_lift] at h1

lemma liftO_drop_apply {e m : ℕ} (b : OPt (e+1) m)
    (h0 : ((b.1 0 : Fin (m+1)) : ℕ) = 0) (j : Fin (e+1)) :
    ((liftO (drop b)).1 j : ℕ) = (b.1 j : ℕ) := by
  rcases Fin.eq_zero_or_eq_succ j with hj | ⟨i, rfl⟩
  · rw [hj, liftO_zero, h0]
  · rw [liftO_succ]; rfl

lemma extN_of_ge {d m : ℕ} (z : OPt d m) {i : ℕ} (hi : d + 1 ≤ i) : extN z i = m := by
  rcases eq_or_lt_of_le hi with h | h
  · rw [← h]; exact extN_last z
  · rw [extN, if_neg (by omega : ¬ (i = 0)), dif_neg (by omega : ¬ (i - 1 < d))]

/-- The `extN` of a lifted point is shifted by one. -/
lemma extN_lift {e m : ℕ} (z' : OPt e m) (n : ℕ) : extN (liftO z') (n+1) = extN z' n := by
  rcases lt_or_ge n (e+1) with hn | hn
  · rcases Nat.eq_zero_or_pos n with hn0 | hpos
    · subst hn0
      have h1 : extN (liftO z') (0+1) = 0 := by
        rw [extN, if_neg (by omega : ¬ ((0:ℕ)+1 = 0)),
          dif_pos (by omega : (0:ℕ)+1-1 < e+1)]
        exact liftO_zero z'
      rw [h1, extN_zero]
    · obtain ⟨j, hj⟩ : ∃ j : Fin e, (j:ℕ)+1 = n :=
        ⟨⟨n-1, by omega⟩, by simp only [Fin.val_mk]; omega⟩
      subst hj
      have ht : (j:ℕ)+1+1 = ((Fin.succ j : Fin (e+1)) : ℕ) + 1 := by rw [Fin.val_succ]
      rw [ht, extN_succ (liftO z') (Fin.succ j), extN_succ z' j]
      exact liftO_succ z' j
  · rw [extN_of_ge (liftO z') (by omega : (e+1)+1 ≤ n+1),
      extN_of_ge z' (by omega : e+1 ≤ n)]

/-- The gap coordinates of `liftO z'` are those of `z'` shifted by one. -/
lemma gap_lift {e m : ℕ} (z' : OPt e m) (k : Fin (e+1)) :
    gap (liftO z') (Fin.succ k) = gap z' k := by
  rw [gap_eq, gap_eq, Fin.val_succ, extN_lift z' ((k:ℕ)+1), extN_lift z' (k:ℕ)]

/-- The image of the full set of colours under `Fin.succ`. -/
lemma image_succ_univ {e : ℕ} :
    ((Finset.univ : Finset (Fin e)).image (Fin.succ (n:=e)))
      = (Finset.univ : Finset (Fin (e+1))).erase 0 := by
  ext j
  rw [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨Fin.succ_ne_zero i, Finset.mem_univ _⟩
  · rintro ⟨hj0, -⟩
    have hj0' : (j:ℕ) ≠ 0 := fun hh => hj0 (Fin.ext (by rw [hh]; rfl))
    have hlt : (j:ℕ) - 1 < e := by have := j.isLt; omega
    refine ⟨⟨(j:ℕ)-1, hlt⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rw [Fin.val_succ]
    simp only [Fin.val_mk]
    omega

/-! ## Packaging the facet lemma -/

lemma gapset_nonempty_of_mult_one {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d))
    (h : IsCell b σ) (s : Fin (d+1))
    (hmult : ((Cells d m).filter (fun C => (cellSet b σ h).erase (vert b σ h s) ⊆ C)).card = 1) :
    ∃ k : Fin (d+1), ∀ t : Fin (d+1), t ≠ s → gap (vert b σ h t) k = 0 := by
  rcases eq_or_ne d 0 with hd0 | hd0
  · subst hd0
    refine ⟨0, fun t ht => absurd ?_ ht⟩
    exact Fin.ext (by have := t.isLt; have := s.isLt; omega)
  · have hd : 1 ≤ d := by omega
    rcases Fin.eq_zero_or_eq_succ s with hs | ⟨s', hsr⟩
    · rw [hs] at hmult ⊢
      exact gapset_nonempty_of_mult_one_zero hd b σ h hmult
    · subst hsr
      by_cases hsl : s' = (⟨d-1, by omega⟩ : Fin d)
      · have hsle : Fin.succ s' = Fin.last d := by
          rw [hsl]; apply Fin.ext
          rw [Fin.val_succ, Fin.val_last]
          simp only [Fin.val_mk]
          omega
        rw [hsle] at hmult ⊢
        exact gapset_nonempty_of_mult_one_last hd b σ h hmult
      · have hs1 : 1 ≤ ((Fin.succ s' : Fin (d+1)) : ℕ) := by rw [Fin.val_succ]; omega
        have hsd : ((Fin.succ s' : Fin (d+1)) : ℕ) < d := by
          rw [Fin.val_succ]
          have h1 : (s':ℕ) ≠ d - 1 := fun hh => hsl (Fin.ext (by rw [hh, Fin.val_mk]))
          have h2 := s'.isLt
          omega
        exact gapset_nonempty_of_mult_one_interior b σ h (Fin.succ s') hs1 hsd hmult


/-! ## The facets contained in the first face -/

lemma gap_zero_eq {d m : ℕ} [NeZero d] (hd : 1 ≤ d) (z : OPt d m) :
    gap z (0 : Fin (d+1)) = ((z.1 (0 : Fin d) : Fin (m+1)) : ℕ) := by
  rw [gap_zero_val hd (z := z)]
  exact congrArg (fun w : Fin d => ((z.1 w : Fin (m+1)) : ℕ)) (Fin.ext rfl)

/-- The auxiliary map `i ↦ σ⁻¹(i+1)` on `Fin e`, for `σ` with `σ (last e) = 0`. -/
def dropPermFun {e : ℕ} (σ : Equiv.Perm (Fin (e+1))) (hσ : σ (Fin.last e) = 0) (i : Fin e) :
    Fin e :=
  ⟨((σ.symm i.succ : Fin (e+1)) : ℕ), by
    have h1 : ((σ.symm i.succ : Fin (e+1)) : ℕ) < e + 1 := (σ.symm i.succ).isLt
    have h2 : ((σ.symm i.succ : Fin (e+1)) : ℕ) ≠ e := by
      intro hh
      have h3 : σ.symm i.succ = Fin.last e := Fin.ext (by rw [hh, Fin.val_last])
      have h4 := congrArg σ h3
      rw [Equiv.apply_symm_apply, hσ] at h4
      exact Fin.succ_ne_zero i h4
    omega⟩

lemma dropPermFun_val {e : ℕ} (σ : Equiv.Perm (Fin (e+1))) (hσ : σ (Fin.last e) = 0) (i : Fin e) :
    ((dropPermFun σ hσ i : Fin e) : ℕ) = ((σ.symm i.succ : Fin (e+1)) : ℕ) := rfl

lemma dropPermFun_injective {e : ℕ} (σ : Equiv.Perm (Fin (e+1))) (hσ : σ (Fin.last e) = 0) :
    Function.Injective (dropPermFun σ hσ) := by
  intro i j hij
  have h1 : ((σ.symm i.succ : Fin (e+1)) : ℕ) = ((σ.symm j.succ : Fin (e+1)) : ℕ) := by
    rw [← dropPermFun_val σ hσ i, ← dropPermFun_val σ hσ j]
    exact congrArg Fin.val hij
  have h2 : σ.symm i.succ = σ.symm j.succ := Fin.ext h1
  have h3 : i.succ = j.succ := by
    rw [← Equiv.apply_symm_apply σ i.succ, ← Equiv.apply_symm_apply σ j.succ, h2]
  exact Fin.succ_injective e h3

lemma dropPermFun_surjective {e : ℕ} (σ : Equiv.Perm (Fin (e+1))) (hσ : σ (Fin.last e) = 0) :
    Function.Surjective (dropPermFun σ hσ) := by
  intro j
  have hsj : σ (⟨(j:ℕ), by have := j.isLt; omega⟩ : Fin (e+1)) ≠ 0 := by
    intro hh
    have h3 : (⟨(j:ℕ), by have := j.isLt; omega⟩ : Fin (e+1)) = Fin.last e := by
      have h4 := congrArg σ.symm hh
      rw [Equiv.symm_apply_apply] at h4
      rw [h4]
      exact (Equiv.symm_apply_eq σ).mpr hσ.symm
    have h5 := congrArg Fin.val h3
    rw [Fin.val_last] at h5
    have hjval : ((⟨(j:ℕ), by have := j.isLt; omega⟩ : Fin (e+1)) : ℕ) = (j:ℕ) := rfl
    have := j.isLt
    omega
  refine ⟨(σ (⟨(j:ℕ), by have := j.isLt; omega⟩ : Fin (e+1))).pred hsj, ?_⟩
  have hs : ((σ (⟨(j:ℕ), by have := j.isLt; omega⟩ : Fin (e+1))).pred hsj).succ
      = σ (⟨(j:ℕ), by have := j.isLt; omega⟩ : Fin (e+1)) := Fin.succ_pred _ _
  apply Fin.ext
  rw [dropPermFun_val, hs, Equiv.symm_apply_apply]

/-- The permutation of `Fin e` obtained from `σ : Perm (Fin (e+1))` with `σ (last e) = 0`
by deleting the index `0`. -/
noncomputable def dropPerm {e : ℕ} (σ : Equiv.Perm (Fin (e+1))) (hσ : σ (Fin.last e) = 0) :
    Equiv.Perm (Fin e) :=
  (Equiv.ofBijective (dropPermFun σ hσ)
    ⟨dropPermFun_injective σ hσ, dropPermFun_surjective σ hσ⟩).symm

lemma dropPerm_symm_val {e : ℕ} (σ : Equiv.Perm (Fin (e+1))) (hσ : σ (Fin.last e) = 0) (i : Fin e) :
    (((dropPerm σ hσ).symm i : Fin e) : ℕ) = ((σ.symm i.succ : Fin (e+1)) : ℕ) := by
  rw [dropPerm, Equiv.symm_symm]
  exact dropPermFun_val σ hσ i

lemma sigmaInv_dropPerm {e : ℕ} (σ : Equiv.Perm (Fin (e+1))) (hσ : σ (Fin.last e) = 0) :
    sigmaInv (dropPerm σ hσ) = σ.symm := by
  funext j
  rcases Fin.eq_zero_or_eq_succ j with hj | ⟨i, rfl⟩
  · rw [hj, sigmaInv_zero]
    exact ((Equiv.symm_apply_eq σ).mpr hσ.symm).symm
  · rw [sigmaInv_succ]
    apply Fin.ext
    rw [Fin.val_castSucc, dropPerm_symm_val]

lemma sigmaLift_dropPerm {e : ℕ} (σ : Equiv.Perm (Fin (e+1))) (hσ : σ (Fin.last e) = 0) :
    sigmaLift (dropPerm σ hσ) = σ.symm := by
  apply Equiv.ext
  intro j
  rw [sigmaLift_apply]
  exact congrFun (sigmaInv_dropPerm σ hσ) j

lemma vtN_dropPerm {e m : ℕ} (b : OPt (e+1) m) (σ : Equiv.Perm (Fin (e+1)))
    (hσ : σ (Fin.last e) = 0) (t : Fin (e+1)) (i : Fin e) :
    vtN (drop b) (dropPerm σ hσ) t i = vtN b σ t.castSucc i.succ := by
  rw [vtN, vtN, drop_apply, Fin.val_castSucc, dropPerm_symm_val σ hσ i]

lemma isCell_drop {e m : ℕ} (b : OPt (e+1) m) (σ : Equiv.Perm (Fin (e+1))) (h : IsCell b σ)
    (hσ : σ (Fin.last e) = 0) : IsCell (drop b) (dropPerm σ hσ) := by
  constructor
  · intro t i
    rw [vtN_dropPerm b σ hσ t i]
    exact h.1 t.castSucc i.succ
  · intro t i j hij
    rw [vtN_dropPerm b σ hσ t i, vtN_dropPerm b σ hσ t j]
    exact h.2 t.castSucc i.succ j.succ (Fin.succ_le_succ_iff.mpr hij)

/-- A cell whose facet opposite the last vertex lies in the first face is a lifted cell. -/
lemma erase_f0_eq {e m : ℕ} (hm : 0 < m) (b : OPt (e+1) m) (σ : Equiv.Perm (Fin (e+1)))
    (h : IsCell b σ) (hb0 : ((b.1 0 : Fin (m+1)) : ℕ) = 0) (hσ : σ (Fin.last e) = 0) :
    (cellSet b σ h).erase (vert b σ h (Fin.last (e+1)))
      = (cellSet (drop b) (dropPerm σ hσ) (isCell_drop b σ h hσ)).image liftO := by
  have hperm : (sigmaLift (dropPerm σ hσ)).symm = σ := by
    rw [sigmaLift_dropPerm σ hσ, Equiv.symm_symm]
  have hvert : ∀ t : Fin (e+2),
      vert b σ h t = vert (liftO (drop b)) ((sigmaLift (dropPerm σ hσ)).symm)
        (isCell_lift (drop b) (dropPerm σ hσ) (isCell_drop b σ h hσ) hm) t := by
    intro t
    apply Subtype.ext; funext j; apply Fin.ext
    rw [vert_apply, vert_apply, hperm, vtN, vtN, liftO_drop_apply b hb0 j]
  have hcellEq : cellSet b σ h = cellSet (liftO (drop b)) ((sigmaLift (dropPerm σ hσ)).symm)
      (isCell_lift (drop b) (dropPerm σ hσ) (isCell_drop b σ h hσ) hm) := by
    unfold cellSet
    congr 1
    exact funext hvert
  rw [hcellEq, hvert (Fin.last (e+1))]
  exact facet_lift (drop b) (dropPerm σ hσ) (isCell_drop b σ h hσ) hm

lemma liftO_drop_eq {e m : ℕ} (z : OPt (e+1) m) (h0 : ((z.1 0 : Fin (m+1)) : ℕ) = 0) :
    liftO (drop z) = z := by
  apply Subtype.ext; funext j; apply Fin.ext
  rw [liftO_drop_apply z h0 j]

/-! ## Doors -/

/-- The `0`-doors of the staircase complex: facets whose colours are all colours except `0`,
lying in exactly one cell. -/
def Doors (d m : ℕ) (col : OPt d m → Fin (d+1)) : Finset (Finset (OPt d m)) :=
  (((Cells d m).biUnion id).powersetCard d).filter
    (fun f => f.image col = (Finset.univ : Finset (Fin (d+1))).erase 0 ∧
      ((Cells d m).filter (fun C => f ⊆ C)).card = 1)

lemma image_liftO_mem_doors {e m : ℕ} (hm : 0 < m) (col : OPt (e+1) m → Fin (e+2))
    (col' : OPt e m → Fin (e+1)) (hcol' : ∀ z', col (liftO z') = Fin.succ (col' z'))
    {C' : Finset (OPt e m)} (hC' : C' ∈ Cells e m) (hcomp : C'.image col' = Finset.univ) :
    C'.image liftO ∈ Doors (e+1) m col := by
  obtain ⟨b', σ', h', rfl⟩ := mem_Cells.mp hC'
  set C := cellSet (liftO b') ((sigmaLift σ').symm) (isCell_lift b' σ' h' hm) with hCdef
  have hCmem : C ∈ Cells (e+1) m := mem_Cells.mpr ⟨liftO b', (sigmaLift σ').symm, _, rfl⟩
  have hsub : (cellSet b' σ' h').image liftO ⊆ C := by
    rw [hCdef, ← facet_lift b' σ' h' hm]
    exact Finset.erase_subset _ _
  have hcard : ((cellSet b' σ' h').image liftO).card = e+1 := by
    rw [Finset.card_image_of_injective _ liftO_injective, card_cellSet]
  have hbU : (cellSet b' σ' h').image liftO ⊆ (Cells (e+1) m).biUnion id := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨C, hCmem, hsub hx⟩
  have himg : ((cellSet b' σ' h').image liftO).image col
      = (Finset.univ : Finset (Fin (e+2))).erase 0 := by
    rw [Finset.image_image]
    have h2 : (cellSet b' σ' h').image (col ∘ liftO)
        = (cellSet b' σ' h').image (Fin.succ ∘ col') := by
      apply Finset.image_congr
      intro z' _
      exact hcol' z'
    rw [h2, ← Finset.image_image, hcomp]
    exact image_succ_univ (e := e+1)
  have hf0 : ∀ x ∈ (cellSet b' σ' h').image liftO, ((x.1 0 : Fin (m+1)) : ℕ) = 0 := by
    intro x hx
    obtain ⟨z', -, rfl⟩ := Finset.mem_image.mp hx
    exact liftO_zero z'
  have hmult : ((Cells (e+1) m).filter
      (fun C2 => (cellSet b' σ' h').image liftO ⊆ C2)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨C, ?_⟩
    ext C2
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hC2, hfC2⟩
      exact cell_eq_of_facet_f0 hCmem hC2 hsub hfC2 hcard hf0
    · rintro rfl
      exact ⟨hCmem, hsub⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hbU, hcard⟩, himg, hmult⟩

/-- The points of a `0`-door all lie in the first face. -/
lemma f0_of_mem_doors {e m : ℕ} (col : OPt (e+1) m → Fin (e+2))
    (hcol : ∀ z, gap z (col z) ≠ 0)
    {f : Finset (OPt (e+1) m)} (hf : f ∈ Doors (e+1) m col) :
    ∀ z ∈ f, ((z.1 0 : Fin (m+1)) : ℕ) = 0 := by
  obtain ⟨hmem, himg, hmult⟩ := Finset.mem_filter.mp hf
  obtain ⟨-, hfcard⟩ := Finset.mem_powersetCard.mp hmem
  obtain ⟨C0, hC0filter⟩ := Finset.card_pos.mp (by rw [hmult]; norm_num)
  obtain ⟨hC0, hfC0⟩ := Finset.mem_filter.mp hC0filter
  obtain ⟨b, σ, h, hC0eq⟩ := mem_Cells.mp hC0
  have hfsub : f ⊆ cellSet b σ h := hC0eq ▸ hfC0
  obtain ⟨s, hs⟩ := exists_missing hfsub hfcard
  have hmult' : ((Cells (e+1) m).filter
      (fun C => (cellSet b σ h).erase (vert b σ h s) ⊆ C)).card = 1 := by
    rw [← hs]; exact hmult
  obtain ⟨k, hk⟩ := gapset_nonempty_of_mult_one b σ h s hmult'
  have hk0 : k = 0 := by
    by_contra hkne
    have hmem' : k ∈ (Finset.univ : Finset (Fin (e+2))).erase 0 := by
      rw [Finset.mem_erase]; exact ⟨hkne, Finset.mem_univ _⟩
    rw [← himg] at hmem'
    obtain ⟨z, hz, hzk⟩ := Finset.mem_image.mp hmem'
    rw [hs, Finset.mem_erase] at hz
    obtain ⟨hzne, hzmem⟩ := hz
    obtain ⟨t, ht⟩ := mem_cellSet.mp hzmem
    have htne : t ≠ s := fun hh => hzne (by rw [← ht, hh])
    exact hcol z (by rw [hzk, ← ht]; exact hk t htne)
  intro z hz
  rw [hs, Finset.mem_erase] at hz
  obtain ⟨hzne, hzmem⟩ := hz
  obtain ⟨t, ht⟩ := mem_cellSet.mp hzmem
  have htne : t ≠ s := fun hh => hzne (by rw [← ht, hh])
  have hg2 : gap (vert b σ h t) (0 : Fin (e+2)) = 0 := by
    have hh := hk t htne
    rwa [hk0] at hh
  rw [← ht, ← gap_zero_eq (d := e+1) (by omega) (vert b σ h t)]
  exact hg2

/-- The drop of a `0`-door is a complete cell of the lower complex. -/
lemma drop_mem_of_mem_doors {e m : ℕ} (hm : 0 < m) (col : OPt (e+1) m → Fin (e+2))
    (col' : OPt e m → Fin (e+1)) (hcol' : ∀ z', col (liftO z') = Fin.succ (col' z'))
    (hcol : ∀ z, gap z (col z) ≠ 0)
    {f : Finset (OPt (e+1) m)} (hf : f ∈ Doors (e+1) m col) :
    f.image drop ∈ (Cells e m).filter (fun C => C.image col' = Finset.univ) := by
  have hf0 := f0_of_mem_doors col hcol hf
  obtain ⟨hmem, himg, hmult⟩ := Finset.mem_filter.mp hf
  obtain ⟨-, hfcard⟩ := Finset.mem_powersetCard.mp hmem
  obtain ⟨C0, hC0filter⟩ := Finset.card_pos.mp (by rw [hmult]; norm_num)
  obtain ⟨hC0, hfC0⟩ := Finset.mem_filter.mp hC0filter
  obtain ⟨b, σ, h, hC0eq⟩ := mem_Cells.mp hC0
  have hfsub : f ⊆ cellSet b σ h := hC0eq ▸ hfC0
  obtain ⟨s, hs⟩ := exists_missing hfsub hfcard
  have hs0 : ∀ t : Fin (e+2), t ≠ s → ((vert b σ h t).1 0 : ℕ) = 0 := by
    intro t ht
    refine hf0 _ ?_
    rw [hs, Finset.mem_erase]
    exact ⟨fun hh => ht (vert_injective b σ h hh), mem_cellSet.mpr ⟨t, rfl⟩⟩
  obtain ⟨hsl, hb0, hσ0⟩ := facet_f0_structure b σ h s hs0
  have hErase : f = (cellSet (drop b) (dropPerm σ hσ0) (isCell_drop b σ h hσ0)).image liftO := by
    rw [hs, hsl]
    exact erase_f0_eq hm b σ h hb0 hσ0
  have hdrop : f.image drop = cellSet (drop b) (dropPerm σ hσ0) (isCell_drop b σ h hσ0) := by
    rw [hErase, Finset.image_image]
    rw [show (drop ∘ liftO) = (id : OPt e m → OPt e m) from funext (fun z' => drop_lift z')]
    exact Finset.image_id
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · rw [hdrop]
    exact mem_Cells.mpr ⟨drop b, dropPerm σ hσ0, _, rfl⟩
  · rw [hdrop]
    refine Finset.eq_univ_of_card _ ?_
    rw [Fintype.card_fin]
    have h2 : ((cellSet (drop b) (dropPerm σ hσ0) (isCell_drop b σ h hσ0)).image col').image
        (Fin.succ (n := e+1)) = (Finset.univ : Finset (Fin (e+2))).erase 0 := by
      rw [Finset.image_image,
        show (Fin.succ ∘ col') = (col ∘ liftO) from funext (fun z' => (hcol' z').symm),
        ← Finset.image_image, ← hErase]
      exact himg
    have h4 := congrArg Finset.card h2
    rw [Finset.card_image_of_injective _ (Fin.succ_injective (e+1)),
      Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (e+2))), Finset.card_univ,
      Fintype.card_fin] at h4
    omega

/-- For a `0`-door, dropping and then lifting is the identity. -/
lemma image_comp_liftO_drop_of_mem_doors {e m : ℕ} (col : OPt (e+1) m → Fin (e+2))
    (hcol : ∀ z, gap z (col z) ≠ 0)
    {f : Finset (OPt (e+1) m)} (hf : f ∈ Doors (e+1) m col) :
    f.image (liftO (e:=e) (m:=m) ∘ drop) = f := by
  have hfun : ∀ z ∈ f, (liftO ∘ drop) z = z :=
    fun z hz => liftO_drop_eq z (f0_of_mem_doors col hcol hf z hz)
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    rw [← hzx, hfun z hz]
    exact hz
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, hfun x hx⟩

/-! ## The parity theorem on the staircase complex -/

/-- The number of complete cells of the staircase complex is odd. -/
theorem odd_complete (d m : ℕ) (hm : 0 < m) (col : OPt d m → Fin (d+1))
    (hcol : ∀ z, gap z (col z) ≠ 0) :
    Odd ((Cells d m).filter (fun C => C.image col = Finset.univ)).card := by
  revert hm col hcol
  induction d with
  | zero =>
      intro hm col hcol
      have hcard1 : Fintype.card (OPt 0 m) = 1 := by
        refine Fintype.card_eq_one_iff.mpr ⟨⟨fun i => 0, fun i => Fin.elim0 i⟩, fun z => ?_⟩
        exact Subtype.ext (funext fun i => Fin.elim0 i)
      have hU : (Finset.univ : Finset (OPt 0 m)) ∈
          (Cells 0 m).filter (fun C => C.image col = Finset.univ) := by
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · rw [mem_Cells]
          refine ⟨⟨fun i => 0, fun i => Fin.elim0 i⟩, Equiv.refl _, ?_, ?_⟩
          · constructor
            · intro t j; exact Fin.elim0 j
            · intro t i j hij; exact Fin.elim0 i
          · apply Finset.Subset.antisymm
            · intro x hx
              exact Finset.mem_univ x
            · intro x hx
              exact mem_cellSet.mpr ⟨0, Subtype.ext (funext fun i => Fin.elim0 i)⟩
        · ext k
          constructor
          · intro _; exact Finset.mem_univ k
          · intro _
            haveI : Subsingleton (Fin (0+1)) :=
              ⟨fun a b => Fin.ext (by have := a.isLt; have := b.isLt; omega)⟩
            exact Finset.mem_image.mpr
              ⟨⟨fun i => 0, fun i => Fin.elim0 i⟩, Finset.mem_univ _, Subsingleton.elim _ k⟩
      have hset : (Cells 0 m).filter (fun C => C.image col = Finset.univ) = {Finset.univ} := by
        ext C
        rw [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hC, -⟩
          exact Finset.eq_univ_of_card C (by rw [card_of_mem_Cells hC, hcard1])
        · rintro rfl
          exact Finset.mem_filter.mp hU
      rw [hset, Finset.card_singleton]
      exact ⟨0, by norm_num⟩
  | succ e ih =>
      intro hm col hcol
      have hne0 : ∀ z' : OPt e m, col (liftO z') ≠ 0 := by
        intro z' hh
        refine hcol (liftO z') ?_
        rw [hh]
        rw [gap_zero_eq (d := e+1) (by omega)]
        exact liftO_zero z'
      let col' : OPt e m → Fin (e+1) := fun z' => Fin.pred (col (liftO z')) (hne0 z')
      have hcol' : ∀ z', col (liftO z') = Fin.succ (col' z') := by
        intro z'; exact (Fin.succ_pred (col (liftO z')) (hne0 z')).symm
      have hcol'' : ∀ z', gap z' (col' z') ≠ 0 := by
        intro z'
        have h := hcol (liftO z')
        rw [hcol' z'] at h
        rwa [gap_lift z' (col' z')] at h
      have ihh := ih hm col' hcol''
      have hB : Odd (Doors (e+1) m col).card := by
        have hbij : (Doors (e+1) m col).card
            = ((Cells e m).filter (fun C => C.image col' = Finset.univ)).card := by
          refine Finset.card_bij (fun f _ => f.image (drop (e:=e) (m:=m))) ?_ ?_ ?_
          · intro f hf
            exact drop_mem_of_mem_doors hm col col' hcol' hcol hf
          · intro f1 hf1 f2 hf2 heq
            have h1 := congrArg (fun F => F.image (liftO (e:=e) (m:=m))) heq
            rw [Finset.image_image, Finset.image_image] at h1
            rw [image_comp_liftO_drop_of_mem_doors col hcol hf1,
              image_comp_liftO_drop_of_mem_doors col hcol hf2] at h1
            exact h1
          · intro C' hC'
            refine ⟨C'.image liftO, image_liftO_mem_doors hm col col' hcol'
              (Finset.mem_filter.mp hC').1 (Finset.mem_filter.mp hC').2, ?_⟩
            rw [Finset.image_image]
            rw [show (drop ∘ liftO) = (id : OPt e m → OPt e m) from funext (fun z' => drop_lift z')]
            exact Finset.image_id
        rw [hbij]
        exact ihh
      exact sperner_parity_mod2 (e+1) col (Cells (e+1) m)
        (fun C hC => card_of_mem_Cells hC) (fun f hf => incidence hf) (0 : Fin (e+2)) hB


/-! ## Verts of a cell have gap coordinates differing by at most one -/

lemma vtN_le_of_le {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) {t t' : Fin (d+1)}
    (htt : (t:ℕ) ≤ (t':ℕ)) (j : Fin d) : vtN b σ t j ≤ vtN b σ t' j := by
  rw [vtN, vtN]
  have h : (if ((σ.symm j : Fin d) : ℕ) < (t:ℕ) then 1 else 0)
      ≤ (if ((σ.symm j : Fin d) : ℕ) < (t':ℕ) then 1 else 0) := by
    by_cases h1 : ((σ.symm j : Fin d) : ℕ) < (t:ℕ)
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1]; split_ifs <;> omega
  omega

lemma vtN_le_add_one {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) {t t' : Fin (d+1)}
    (htt : (t:ℕ) ≤ (t':ℕ)) (j : Fin d) : vtN b σ t' j ≤ vtN b σ t j + 1 := by
  rw [vtN, vtN]
  split_ifs <;> omega

/-- Vertices `t ≤ t'` of a cell `(b,σ)` have gap coordinates differing by at most one, in both
directions. -/
lemma gap_vert_le_add_one_of_le {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    {t t' : Fin (d+1)} (htt : (t:ℕ) ≤ (t':ℕ)) (k : Fin (d+1)) :
    gap (vert b σ h t) k ≤ gap (vert b σ h t') k + 1 ∧
      gap (vert b σ h t') k ≤ gap (vert b σ h t) k + 1 := by
  have hD : ∀ i : ℕ, 1 ≤ i → i ≤ d →
      0 ≤ (extN (vert b σ h t') i : ℤ) - (extN (vert b σ h t) i : ℤ) ∧
      (extN (vert b σ h t') i : ℤ) - (extN (vert b σ h t) i : ℤ) ≤ 1 := by
    intro i h1 h2
    have e1 : extN (vert b σ h t') i = vtN b σ t' ⟨i-1, by omega⟩ := by
      rw [extN, if_neg (by omega), dif_pos (by omega), vert_apply]
    have e2 : extN (vert b σ h t) i = vtN b σ t ⟨i-1, by omega⟩ := by
      rw [extN, if_neg (by omega), dif_pos (by omega), vert_apply]
    rw [e1, e2]
    have hm1 : vtN b σ t ⟨i-1, by omega⟩ ≤ vtN b σ t' ⟨i-1, by omega⟩ :=
      vtN_le_of_le b σ htt _
    have hm2 : vtN b σ t' ⟨i-1, by omega⟩ ≤ vtN b σ t ⟨i-1, by omega⟩ + 1 :=
      vtN_le_add_one b σ htt _
    constructor <;> omega
  have hkey : ∀ i : ℕ, i ≤ d + 1 →
      0 ≤ (extN (vert b σ h t') i : ℤ) - (extN (vert b σ h t) i : ℤ) ∧
      (extN (vert b σ h t') i : ℤ) - (extN (vert b σ h t) i : ℤ) ≤ 1 := by
    intro i hi
    rcases eq_or_ne i 0 with hi0 | hi0
    · rw [hi0, extN_zero, extN_zero]; constructor <;> norm_num
    · rcases eq_or_ne i (d+1) with hid | hid
      · rw [hid, extN_last, extN_last]; constructor <;> norm_num
      · exact hD i (by omega) (by omega)
  have e1 : (gap (vert b σ h t) k : ℤ)
      = (extN (vert b σ h t) ((k:ℕ)+1) : ℤ) - (extN (vert b σ h t) (k:ℕ) : ℤ) := by
    rw [gap_eq, Nat.cast_sub (extN_step (vert b σ h t) (k:ℕ))]
  have e2 : (gap (vert b σ h t') k : ℤ)
      = (extN (vert b σ h t') ((k:ℕ)+1) : ℤ) - (extN (vert b σ h t') (k:ℕ) : ℤ) := by
    rw [gap_eq, Nat.cast_sub (extN_step (vert b σ h t') (k:ℕ))]
  have hk1 : (k:ℕ) ≤ d + 1 := by have := k.isLt; omega
  have hk2 : (k:ℕ) + 1 ≤ d + 1 := by have := k.isLt; omega
  have hA1 := (hkey (k:ℕ) hk1).1
  have hA2 := (hkey (k:ℕ) hk1).2
  have hB1 := (hkey ((k:ℕ)+1) hk2).1
  have hB2 := (hkey ((k:ℕ)+1) hk2).2
  have hZ1 : (gap (vert b σ h t) k : ℤ) ≤ (gap (vert b σ h t') k : ℤ) + 1 := by
    rw [e1, e2]; linarith
  have hZ2 : (gap (vert b σ h t') k : ℤ) ≤ (gap (vert b σ h t) k : ℤ) + 1 := by
    rw [e1, e2]; linarith
  exact ⟨by exact_mod_cast hZ1, by exact_mod_cast hZ2⟩

/-- Vertices of a cell have gap coordinates differing by at most one. -/
lemma gap_vert_le_add_one {d m : ℕ} (b : OPt d m) (σ : Equiv.Perm (Fin d)) (h : IsCell b σ)
    (t t' : Fin (d+1)) (k : Fin (d+1)) :
    gap (vert b σ h t) k ≤ gap (vert b σ h t') k + 1 := by
  rcases le_total (t:ℕ) (t':ℕ) with hle | hle
  · exact (gap_vert_le_add_one_of_le b σ h hle k).1
  · exact (gap_vert_le_add_one_of_le b σ h hle k).2

/-! ## The grid rainbow cube -/

theorem grid_rainbow_cube (n m : ℕ) (hm : 0 < m) (hn : 0 < n)
    (ℓ : {x : Fin n → Fin (m + 1) // ∑ j, (x j : ℕ) = m} → Fin n)
    (hℓ : ∀ x : {x : Fin n → Fin (m + 1) // ∑ j, (x j : ℕ) = m},
      (x.1 (ℓ x) : ℕ) ≠ 0) :
    ∃ S : Finset {x : Fin n → Fin (m + 1) // ∑ j, (x j : ℕ) = m},
      S.card = n ∧
      (∀ t : Fin n, ∃ x ∈ S, ℓ x = t) ∧
      (∀ x ∈ S, ∀ y ∈ S, ∀ j : Fin n, (x.1 j : ℕ) ≤ (y.1 j : ℕ) + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  set col : OPt d m → Fin (d+1) := fun z => ℓ (Phi z) with hcoldef
  have hcol : ∀ z, gap z (col z) ≠ 0 := by
    intro z
    have h1 := hℓ (Phi z)
    have h2 : ((Phi z).1 (ℓ (Phi z)) : ℕ) = gap z (col z) := rfl
    rwa [h2] at h1
  have hodd := odd_complete d m hm col hcol
  have hpos : 0 < ((Cells d m).filter (fun C => C.image col = Finset.univ)).card := by
    rcases hodd with ⟨k, hk⟩
    omega
  obtain ⟨C, hC⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hC
  obtain ⟨hCmem, hCimg⟩ := hC
  refine ⟨C.image (Phi (d:=d) (m:=m)), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ Phi_injective, card_of_mem_Cells hCmem]
  · intro t
    have ht : t ∈ C.image col := by rw [hCimg]; exact Finset.mem_univ t
    obtain ⟨z, hz, hzcol⟩ := Finset.mem_image.mp ht
    exact ⟨Phi z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, hzcol⟩
  · intro x hx y hy j
    obtain ⟨zx, hzx, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨zy, hzy, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨b, σ, h, hCeq⟩ := mem_Cells.mp hCmem
    obtain ⟨t, rfl⟩ := mem_cellSet.mp (hCeq ▸ hzx)
    obtain ⟨t', rfl⟩ := mem_cellSet.mp (hCeq ▸ hzy)
    exact gap_vert_le_add_one b σ h t t' j

end
end Commons.Topology.Simplex
