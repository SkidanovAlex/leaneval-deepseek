import Mathlib
import Submission.Work.RatHurewicz.cellDefs

/-!
# Vocabulary for pushing a path off the origin of an open cell of `Model D`

This module collects the elementary combinatorial invariants of the model
(`Work.RatHurewicz.Model`, `Work.RatHurewicz.MData`, defined in
`Submission.Work.RatHurewicz.cycleModelDefs`) that are used to control the gluing relation
`Work.RatHurewicz.modelRel`.

* `suppOf x` is the support of a point of a standard simplex (the set of nonzero coordinates);
* `szFun a` is the size of the support (one for the points of the arcs), and is invariant under
  the gluing relation, so it descends to `Model D`;
* `rankIn T k` is the number of elements of `T` strictly below `k`;
* `shapeOf x` is the set of pairs `(rank, value)` of the nonzero coordinates of `x`: it is
  invariant under the gluing relation, and on a single stratum (a fixed support, in a fixed copy)
  it determines the point.
-/

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- The support of a point of a standard simplex: the set of vertices with a nonzero coordinate. -/
def suppOf {ι : Type} [Fintype ι] [DecidableEq ι] (x : stdSimplex ℝ ι) : Finset ι :=
  Finset.univ.filter (fun k => (x : ι → ℝ) k ≠ 0)

@[simp] theorem mem_suppOf {ι : Type} [Fintype ι] [DecidableEq ι] {x : stdSimplex ℝ ι} {k : ι} :
    k ∈ suppOf x ↔ (x : ι → ℝ) k ≠ 0 := by
  simp [suppOf]

theorem suppOf_eq_ptSupport {m : ℕ} (x : stdSimplex ℝ (Fin (m+2))) : suppOf x = ptSupport x := rfl

/-- The coordinates of a face of the standard simplex. -/
theorem coord_facept (m : ℕ) (p : Fin (m+2)) (z : stdSimplex ℝ (Fin (m+1))) (k : Fin (m+1+1)) :
    (facept (m+1) p z : Fin (m+1+1) → ℝ) k
      = ∑ i with p.succAbove i = k, (z : Fin (m+1) → ℝ) i := by
  simp only [facept, ContinuousMap.coe_mk, stdSimplex.map_coe]
  rw [show (FunOnFinite.linearMap ℝ ℝ p.succAbove (⇑z))
        = FunOnFinite.map p.succAbove (⇑z) from rfl]
  exact FunOnFinite.map_apply_apply p.succAbove (⇑z) k

/-- A single coordinate of a point of a face, read off from a vanishing sum. -/
theorem sum_face_eq_zero {m : ℕ} (p : Fin (m+2)) (z : stdSimplex ℝ (Fin (m+1)))
    (i : Fin (m+1)) (h : (∑ b with p.succAbove b = p.succAbove i,
      (z : Fin (m+1) → ℝ) b) = 0) : (z : Fin (m+1) → ℝ) i = 0 := by
  rw [Finset.sum_filter] at h
  rw [Finset.sum_eq_single i] at h
  · simpa using h
  · intro b _ hb
    by_cases h' : p.succAbove b = p.succAbove i
    · exact absurd (Fin.succAbove_right_injective h') hb
    · simp [h']
  · intro h'; exact absurd (Finset.mem_univ i) h'

/-- The support of a face of the standard simplex. -/
theorem suppOf_facept (m : ℕ) (p : Fin (m+2)) (z : stdSimplex ℝ (Fin (m+1))) :
    suppOf (facept (m+1) p z) = (suppOf z).image p.succAbove := by
  ext k
  rw [mem_suppOf, Finset.mem_image, coord_facept]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    refine h (Finset.sum_eq_zero fun i hi => ?_)
    rw [Finset.mem_filter] at hi
    by_cases hzi : (z : Fin (m+1) → ℝ) i = 0
    · exact hzi
    · exact absurd hi.2 (hc i (mem_suppOf.mpr hzi))
  · rintro ⟨i, hi, rfl⟩ hsum
    exact (mem_suppOf.mp hi) (sum_face_eq_zero p z i hsum)

/-- The coordinate of a point of a face at the corresponding index. -/
theorem coord_facept_apply (m : ℕ) (p : Fin (m+2)) (z : stdSimplex ℝ (Fin (m+1)))
    (i : Fin (m+1)) : (facept (m+1) p z : Fin (m+1+1) → ℝ) (p.succAbove i)
      = (z : Fin (m+1) → ℝ) i := by
  rw [coord_facept, Finset.sum_filter]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    by_cases h : p.succAbove b = p.succAbove i
    · exact absurd (Fin.succAbove_right_injective h) hb
    · simp [h]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The support of a vertex of the standard simplex. -/
@[simp] theorem suppOf_vertex (m : ℕ) (a : Fin (m+2)) :
    suppOf (stdSimplex.vertex a : stdSimplex ℝ (Fin (m+2))) = {a} := by
  ext k
  rw [mem_suppOf, Finset.mem_singleton, stdSimplex.vertex_coe]
  constructor
  · intro h
    by_contra hne
    exact h (by rw [Pi.single_apply, if_neg hne])
  · rintro rfl
    rw [Pi.single_eq_same]
    norm_num

/-- The rank of an element of a finite set: the number of elements strictly below it. -/
def rankIn {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (T : Finset ι) (k : ι) : ℕ :=
  (T.filter (fun j => j < k)).card

theorem rankIn_image_succAbove (m : ℕ) (p : Fin (m+2)) (A : Finset (Fin (m+1)))
    (i : Fin (m+1)) :
    rankIn (A.image p.succAbove) (p.succAbove i) = rankIn A i := by
  rw [rankIn, rankIn, ← Finset.card_image_of_injective _ (Fin.succAbove_right_injective (p := p))]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hlt⟩
    exact ⟨a, ⟨ha, (Fin.strictMono_succAbove p).lt_iff_lt.mp hlt⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hlt⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, (Fin.strictMono_succAbove p).lt_iff_lt.mpr hlt⟩

theorem rankIn_lt_card {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {T : Finset ι} {k : ι} (hk : k ∈ T) : rankIn T k < T.card := by
  rw [rankIn]
  exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨k, hk, fun h => lt_irrefl k h⟩)

theorem rankIn_injOn {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {T : Finset ι} {k k' : ι} (hk : k ∈ T) (hk' : k' ∈ T) (h : rankIn T k = rankIn T k') :
    k = k' := by
  have key : ∀ a b : ι, a ∈ T → b ∈ T → a ≤ b → rankIn T a = rankIn T b → a = b := by
    intro a b ha hb hab hrank
    by_contra hne
    have hab' : a < b := lt_of_le_of_ne hab hne
    have ha' : a ∈ T.filter (fun j => j < b) := Finset.mem_filter.mpr ⟨ha, hab'⟩
    have hne' : T.filter (fun j => j < a) ≠ T.filter (fun j => j < b) := fun heq => by
      have ha'' : a ∈ T.filter (fun j => j < a) := by
        rw [heq]
        exact ha'
      exact absurd (Finset.mem_filter.mp ha'').2 (lt_irrefl a)
    have hsub : T.filter (fun j => j < a) ⊆ T.filter (fun j => j < b) := by
      intro j hj
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hj).1, lt_trans (Finset.mem_filter.mp hj).2 hab'⟩
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne'⟩)
    rw [rankIn, rankIn] at hrank
    omega
  rcases le_total k k' with hle | hle
  · exact key k k' hk hk' hle h
  · exact (key k' k hk' hk hle h.symm).symm

/-- The shape of a point of the standard simplex: the set of pairs `(rank, value)` of its nonzero
coordinates. -/
def shapeOf {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (x : stdSimplex ℝ ι) : Finset (ℕ × ℝ) :=
  (suppOf x).image (fun k => (rankIn (suppOf x) k, (x : ι → ℝ) k))

theorem shapeOf_facept (m : ℕ) (p : Fin (m+2)) (z : stdSimplex ℝ (Fin (m+1))) :
    shapeOf (facept (m+1) p z) = shapeOf z := by
  rw [shapeOf, shapeOf, suppOf_facept]
  rw [Finset.image_image]
  refine Finset.image_congr fun i _ => ?_
  simp only [Function.comp_apply]
  rw [rankIn_image_succAbove, coord_facept_apply]

/-- The shape determines the point, among the points with a fixed support. -/
theorem shapeOf_injOn {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {x y : stdSimplex ℝ ι} (hs : suppOf x = suppOf y)
    (h : shapeOf x = shapeOf y) : x = y := by
  ext k
  by_cases hk : k ∈ suppOf x
  · have hk' : k ∈ suppOf y := hs ▸ hk
    have hmem : (rankIn (suppOf x) k, (x : ι → ℝ) k) ∈ shapeOf y := by
      rw [← h]
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    obtain ⟨l, hl, hle⟩ := Finset.mem_image.mp hmem
    rw [← hs] at hl hle
    have hlk : l = k := rankIn_injOn hl hk (congrArg Prod.fst hle)
    rw [hlk] at hle
    exact (Prod.mk.inj hle).2.symm
  · have hxk : (x : ι → ℝ) k = 0 := by simpa [mem_suppOf] using hk
    have hyk : (y : ι → ℝ) k = 0 := by
      by_contra hc
      exact hk (hs.symm ▸ mem_suppOf.mpr hc)
    rw [hxk, hyk]

/-- The size of the support, extended to the raw model by `1` on the arcs. -/
def szFun (D : MData X n x₀) (a : Raw D) : ℕ :=
  match a with
  | Sum.inl p => (suppOf p.2).card
  | Sum.inr _ => 1

/-- The shape invariant, extended to the raw model by `{(0, 1)}` on the arcs (the shape of a
vertex). -/
def shapeAt (D : MData X n x₀) (a : Raw D) : Finset (ℕ × ℝ) :=
  match a with
  | Sum.inl p => shapeOf p.2
  | Sum.inr _ => {(0, 1)}

theorem szFun_modelRel {D : MData X n x₀} {a b : Raw D} (h : modelRel D a b) :
    szFun D a = szFun D b := by
  rcases h with ⟨i, j, p, q, x, rfl, rfl, _⟩ | ⟨i, rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩
  · simp only [szFun, suppOf_facept]
    rw [Finset.card_image_of_injective _ (Fin.succAbove_right_injective (p := p)),
      Finset.card_image_of_injective _ (Fin.succAbove_right_injective (p := q))]
  · simp [szFun]
  · simp [szFun]

end

end Work.RatHurewicz
