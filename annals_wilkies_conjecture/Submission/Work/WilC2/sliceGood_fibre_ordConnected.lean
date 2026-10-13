import Mathlib
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.Convert

set_option maxHeartbeats 1000000

namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

/-!
## The fibre of a `SliceGood` family is a finite union of order-convex sets

`SliceGood K φ M` says that for every choice of parameters `p` there are cut points
`y 0 ≤ y 1 ≤ … ≤ y (K-1)` such that the fibre `S = {t | φ(p, t)}` is convex as soon as one
stays between two consecutive cut points.  Hence `S` is covered by the (finitely many)
pieces `S ∩ (-∞, y 0]`, `S ∩ [y 0, y 1]`, …, `S ∩ [y (K-2), y (K-1)]`, `S ∩ [y (K-1), ∞)`,
each of which is order-convex.
-/

/-- If `J` is an interval that contains no cut point strictly between two of its points, then
the part of `S` inside `J` is order-convex, provided `S` has the `SliceGood`-type convexity
property between any two points with no cut point in between. -/
lemma ordConnected_inter_of_cutFree {M : Type*} [LinearOrder M] {K : ℕ} {y : Fin K → M}
    {S J : Set M} (hJ : J.OrdConnected)
    (hcut : ∀ ⦃u⦄, u ∈ J → ∀ ⦃v⦄, v ∈ J →
      ∀ j : Fin K, ¬ ((u < y j ∧ y j < v) ∨ (v < y j ∧ y j < u)))
    (hconv : ∀ u w v : M, S u → S v →
      ((u < w ∧ w < v) ∨ (v < w ∧ w < u)) →
      (∀ j : Fin K, ¬ ((u < y j ∧ y j < v) ∨ (v < y j ∧ y j < u))) → S w) :
    (S ∩ J).OrdConnected := by
  refine Set.ordConnected_iff.mpr ?_
  intro x hx z hz hxz w hw
  refine ⟨?_, hJ.out hx.2 hz.2 hw⟩
  rcases eq_or_lt_of_le hw.1 with h | h
  · rw [← h]; exact hx.1
  rcases eq_or_lt_of_le hw.2 with h' | h'
  · rw [h']; exact hz.1
  · exact hconv x w z hx.1 hz.1 (Or.inl ⟨h, h'⟩) (fun j => hcut hx.2 hz.2 j)

/-- `(-∞, y a]` contains no cut point strictly between two of its points, when `y a` is the
minimum of the cut points. -/
lemma cutfree_Iic {M : Type*} [LinearOrder M] {K : ℕ} {y : Fin K → M} (a : Fin K)
    (hmin : ∀ j : Fin K, y a ≤ y j)
    ⦃u : M⦄ (hu : u ∈ Set.Iic (y a)) ⦃v : M⦄ (hv : v ∈ Set.Iic (y a)) (j : Fin K) :
    ¬ ((u < y j ∧ y j < v) ∨ (v < y j ∧ y j < u)) := by
  simp only [Set.mem_Iic] at hu hv
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact absurd (lt_of_lt_of_le (lt_of_le_of_lt (hmin j) h2) hv) (lt_irrefl (y a))
  · exact absurd (lt_of_lt_of_le (lt_of_le_of_lt (hmin j) h2) hu) (lt_irrefl (y a))

/-- `[y b, ∞)` contains no cut point strictly between two of its points, when `y b` is the
maximum of the cut points. -/
lemma cutfree_Ici {M : Type*} [LinearOrder M] {K : ℕ} {y : Fin K → M} (b : Fin K)
    (hmax : ∀ j : Fin K, y j ≤ y b)
    ⦃u : M⦄ (hu : u ∈ Set.Ici (y b)) ⦃v : M⦄ (hv : v ∈ Set.Ici (y b)) (j : Fin K) :
    ¬ ((u < y j ∧ y j < v) ∨ (v < y j ∧ y j < u)) := by
  simp only [Set.mem_Ici] at hu hv
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact absurd (lt_of_lt_of_le (lt_of_le_of_lt hu h1) (hmax j)) (lt_irrefl (y b))
  · exact absurd (lt_of_lt_of_le (lt_of_le_of_lt hv h1) (hmax j)) (lt_irrefl (y b))

/-- `[y a, y b]` contains no cut point strictly between two of its points, when `y a, y b` are
consecutive (indices `a.val + 1 = b.val`) and `y` is monotone. -/
lemma cutfree_Icc {M : Type*} [LinearOrder M] {K : ℕ} {y : Fin K → M}
    (hmono : ∀ i j : Fin K, i ≤ j → y i ≤ y j) {a b : Fin K} (hab : a.val + 1 = b.val)
    ⦃u : M⦄ (hu : u ∈ Set.Icc (y a) (y b)) ⦃v : M⦄ (hv : v ∈ Set.Icc (y a) (y b)) (l : Fin K) :
    ¬ ((u < y l ∧ y l < v) ∨ (v < y l ∧ y l < u)) := by
  simp only [Set.mem_Icc] at hu hv
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · have h1' : a.val < l.val := by
      by_contra hle
      have : y l ≤ y a := hmono l a (Fin.le_def.mpr (not_lt.mp hle))
      exact absurd (lt_of_lt_of_le (lt_of_le_of_lt hu.1 h1) this) (lt_irrefl (y a))
    have h2' : l.val < b.val := by
      by_contra hle
      have : y b ≤ y l := hmono b l (Fin.le_def.mpr (not_lt.mp hle))
      exact absurd (lt_of_lt_of_le (lt_of_lt_of_le h2 hv.2) this) (lt_irrefl (y l))
    omega
  · have h1' : a.val < l.val := by
      by_contra hle
      have : y l ≤ y a := hmono l a (Fin.le_def.mpr (not_lt.mp hle))
      exact absurd (lt_of_lt_of_le (lt_of_le_of_lt hv.1 h1) this) (lt_irrefl (y a))
    have h2' : l.val < b.val := by
      by_contra hle
      have : y b ≤ y l := hmono b l (Fin.le_def.mpr (not_lt.mp hle))
      exact absurd (lt_of_lt_of_le (lt_of_lt_of_le h2 hu.2) this) (lt_irrefl (y l))
    omega

/-- The middle piece `S ∩ [y (lo j), y (hi j)]` of the fibre (consecutive cut points);
`j` ranges over `Fin (K-1)` and the two endpoints are the `j`-th and `(j+1)`-st cut points. -/
lemma cutfree_mid {M : Type*} [LinearOrder M] {K : ℕ} (hK : 1 ≤ K) {y : Fin K → M}
    (hmono : ∀ i j : Fin K, i ≤ j → y i ≤ y j) (j : Fin (K - 1)) :
    ∀ ⦃u : M⦄,
      u ∈ Set.Icc (y ⟨j.val, by have := j.isLt; omega⟩)
        (y ⟨j.val + 1, by have := j.isLt; omega⟩) →
      ∀ ⦃v : M⦄,
        v ∈ Set.Icc (y ⟨j.val, by have := j.isLt; omega⟩)
          (y ⟨j.val + 1, by have := j.isLt; omega⟩) →
      ∀ l : Fin K,
        ¬ ((u < y l ∧ y l < v) ∨ (v < y l ∧ y l < u)) := by
  intro u hu v hv l
  have : (⟨j.val, by have := j.isLt; omega⟩ : Fin K).val + 1
      = (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin K).val := rfl
  exact cutfree_Icc hmono this hu hv l

theorem sliceGood_fibre_ordConnected {M : Type} [WilkiesDesign.CG.LRc.Structure M] [Field M] [LinearOrder M]
    {n : ℕ} (K : ℕ) (hK : 1 ≤ K) (φ : ParamFormula n) (v : Fin n → M)
    (h : SliceGood K φ M) :
    ∃ s : Finset (Set M), (∀ I ∈ s, I.OrdConnected) ∧
      {x : Fin 1 → M | φ.Realize (Sum.elim v x)} = {x | x 0 ∈ ⋃₀ (s : Set (Set M))} := by
  classical
  obtain ⟨y, hmono, hconv⟩ := h v
  let S : Set M := {t : M | φ.Realize (Sum.elim v (fun _ => t))}
  have hconvS : ∀ u w q : M, u ∈ S → q ∈ S →
      ((u < w ∧ w < q) ∨ (q < w ∧ w < u)) →
      (∀ j : Fin K, ¬ ((u < y j ∧ y j < q) ∨ (q < y j ∧ y j < u))) → w ∈ S := hconv
  let first : Fin K := ⟨0, by omega⟩
  let last : Fin K := ⟨K - 1, by omega⟩
  let Lp : Set M := S ∩ Set.Iic (y first)
  let Rp : Set M := S ∩ Set.Ici (y last)
  let Mid : Fin (K - 1) → Set M :=
    fun j => S ∩ Set.Icc (y ⟨j.val, by have := j.isLt; omega⟩)
      (y ⟨j.val + 1, by have := j.isLt; omega⟩)
  let s : Finset (Set M) := insert Lp (insert Rp (Finset.univ.image Mid))
  have hmem : ∀ I : Set M, I ∈ s ↔ I = Lp ∨ I = Rp ∨ ∃ j : Fin (K - 1), Mid j = I := by
    intro I
    simp only [s, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
  have hfirst : ∀ l : Fin K, first ≤ l := fun l => Fin.le_def.mpr (Nat.zero_le _)
  have hlast : ∀ l : Fin K, l ≤ last := fun l => by
    refine Fin.le_def.mpr ?_
    show l.val ≤ K - 1
    have := l.isLt; omega
  refine ⟨s, ?_, ?_⟩
  · intro I hI
    rcases (hmem I).mp hI with rfl | rfl | ⟨j, rfl⟩
    · exact ordConnected_inter_of_cutFree Set.ordConnected_Iic
        (fun u hu v hv l => cutfree_Iic first (fun l => hmono first l (hfirst l)) hu hv l) hconvS
    · exact ordConnected_inter_of_cutFree Set.ordConnected_Ici
        (fun u hu v hv l => cutfree_Ici last (fun l => hmono l last (hlast l)) hu hv l) hconvS
    · exact ordConnected_inter_of_cutFree Set.ordConnected_Icc
        (fun u hu v hv l => cutfree_mid hK hmono j hu hv l) hconvS
  · have hsub : (⋃₀ (s : Set (Set M))) = S := by
      apply le_antisymm
      · intro t ht
        rw [Set.mem_sUnion] at ht
        obtain ⟨I, hI, htI⟩ := ht
        rcases (hmem I).mp (Finset.mem_coe.mp hI) with rfl | rfl | ⟨j, rfl⟩
        · exact htI.1
        · exact htI.1
        · exact htI.1
      · intro t ht
        rw [Set.mem_sUnion]
        by_cases ht0 : t ≤ y first
        · exact ⟨Lp, Finset.mem_coe.mpr ((hmem Lp).mpr (Or.inl rfl)), ht, ht0⟩
        · have ht0' : y first < t := not_le.mp ht0
          by_cases ht1 : y last ≤ t
          · exact ⟨Rp, Finset.mem_coe.mpr ((hmem Rp).mpr (Or.inr (Or.inl rfl))), ht, ht1⟩
          · have ht1' : t < y last := not_le.mp ht1
            have hAne : (Finset.univ.filter (fun l : Fin K => y l < t)).Nonempty :=
              ⟨first, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ht0'⟩
            let m : Fin K := (Finset.univ.filter (fun l : Fin K => y l < t)).max' hAne
            have hmA : m ∈ Finset.univ.filter (fun l : Fin K => y l < t) :=
              Finset.max'_mem _ hAne
            have hmt : y m < t := (Finset.mem_filter.mp hmA).2
            have hlast_notin : last ∉ Finset.univ.filter (fun l : Fin K => y l < t) := by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact not_lt.mpr (le_of_lt ht1')
            have hm_ne_last : m ≠ last := fun hh => hlast_notin (hh ▸ hmA)
            have hmval : m.val < K - 1 := by
              have h2 : m.val ≠ K - 1 := by
                intro hh
                exact hm_ne_last (Fin.ext (by show m.val = last.val; rw [hh]))
              have h1 : m.val < K := m.isLt
              omega
            let j : Fin (K - 1) := ⟨m.val, by omega⟩
            let nn : Fin K := ⟨m.val + 1, by omega⟩
            have hnn_notin : nn ∉ Finset.univ.filter (fun l : Fin K => y l < t) := by
              intro hn
              have hle : nn ≤ m := Finset.le_max' _ nn hn
              have hval : nn.val ≤ m.val := Fin.le_def.mp hle
              have hval' : m.val + 1 ≤ m.val := hval
              omega
            have ht_le : t ≤ y nn := by
              by_contra hc
              exact hnn_notin (by
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact not_le.mp hc)
            refine ⟨Mid j, Finset.mem_coe.mpr ((hmem (Mid j)).mpr (Or.inr (Or.inr ⟨j, rfl⟩))),
              ht, ?_⟩
            have hlo : (⟨j.val, by have := j.isLt; omega⟩ : Fin K) = m := Fin.ext rfl
            have hhi : (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin K) = nn := Fin.ext rfl
            rw [hlo, hhi]
            exact ⟨le_of_lt hmt, ht_le⟩
    rw [hsub]
    ext x
    have hx : (fun _ : Fin 1 => x 0) = x := funext (fun i => by fin_cases i; rfl)
    change φ.Realize (Sum.elim v x) ↔ φ.Realize (Sum.elim v (fun _ => x 0))
    rw [hx]

end Work.WilC2
