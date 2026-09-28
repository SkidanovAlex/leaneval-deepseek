import Mathlib
import Submission.Work.RatHurewicz.SkelGraph.graphElementDefs
import Submission.Work.RatHurewicz.SkelGraph.points
import Submission.Work.RatHurewicz.cycleModelDefs
import Submission.Work.RatHurewicz.finiteGraphDefs

/-!
# The graph data of a low dimensional point of the cycle model

The `1`-skeleton of the cycle model `Work.RatHurewicz.Model D` is the set of classes of low
dimensional points of `Work.RatHurewicz.Raw D`: such a point is a vertex of one of the copies of
`Δ^{n+1}`, a point in the relative interior of a `1`-face of such a copy, or a point of one of the
arcs.  `Work.RatHurewicz.SkelGraph.wOf` (in `graphElementDefs.lean`) is the canonical "graph data"
of such a point: the class of a vertex, or the class of a `1`-face together with the parameter of
the point on it.

This file collects the elementary facts about `wOf`, about the support of a point of a standard
simplex and about the canonical form computed by `wOf`, together with the set `good D U` of low
dimensional points whose graph data lies in a given set `U` of vertices and edges, and the
saturation predicate `Sat`.  Everything new lives in the auxiliary namespace `GoodAux`.
-/

namespace Work.RatHurewicz.SkelGraph

open scoped Topology Simplicial unitInterval

noncomputable section

namespace GoodAux

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-! ## The support of the canonical points of a standard simplex -/

theorem supp_vertex {m : ℕ} (p : Fin m) :
    supp (stdSimplex.vertex p : stdSimplex ℝ (Fin m)) = {p} := by
  ext k
  rw [mem_supp, Finset.mem_singleton]
  simp only [stdSimplex.vertex_coe, Pi.single_apply]
  by_cases h : k = p <;> simp [h]

/-- The sum of the coordinates of a point of a standard simplex over its support is `1`. -/
theorem sum_supp_eq_one {m : ℕ} (x : stdSimplex ℝ (Fin m)) :
    ∑ i ∈ supp x, x.1 i = 1 := by
  rw [← x.2.2]
  refine Finset.sum_subset (Finset.filter_subset _ _) (fun i _ hi => ?_)
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
  exact hi

theorem sdPt_coe {m : ℕ} (p q : Fin m) (s : I) :
    (sdPt p q s).1 = fun k => (if k = p then 1 - (s : ℝ) else 0)
      + (if k = q then (s : ℝ) else 0) :=
  funext (fun k => sdPt_apply p q s k)

theorem supp_sdPt_of_ne {m : ℕ} {p q : Fin m} (hpq : p ≠ q) {s : I}
    (h0 : (s : ℝ) ≠ 0) (h1 : (s : ℝ) ≠ 1) : supp (sdPt p q s) = {p, q} := by
  ext k
  rw [mem_supp, Finset.mem_insert, Finset.mem_singleton, sdPt_coe]
  by_cases hkp : k = p
  · subst hkp
    have hs : (1 : ℝ) - (s : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    simp [hpq, hs]
  · by_cases hkq : k = q
    · subst hkq
      simp [hkp, h0]
    · simp [hkp, hkq]

theorem supp_sdPt_zero {m : ℕ} (p q : Fin m) :
    supp (sdPt p q (0 : I)) = {p} := by
  rw [sdPt_zero, supp_vertex]

theorem supp_sdPt_one {m : ℕ} (p q : Fin m) :
    supp (sdPt p q (1 : I)) = {q} := by
  rw [sdPt_one, supp_vertex]

/-- The support of the image of a point of a standard simplex under the map induced by an injective
map of the index types. -/
theorem supp_map {m k : ℕ} (f : Fin m → Fin k) (hf : Function.Injective f)
    (x : stdSimplex ℝ (Fin m)) : supp (stdSimplex.map f x) = (supp x).image f := by
  have hcoe : (stdSimplex.map f x).1
      = fun j => ∑ i : Fin m, if f i = j then x.1 i else 0 := by
    funext j
    have h1 : (stdSimplex.map f x).1 = (FunOnFinite.linearMap ℝ ℝ f) x.1 := rfl
    rw [congrFun h1 j, FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  ext j
  rw [mem_supp, Finset.mem_image, hcoe]
  constructor
  · intro hj
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
    by_cases h : f i = j
    · exact ⟨i, by rw [mem_supp]; simpa [h] using hi, h⟩
    · exact absurd (by simp [h]) hi
  · rintro ⟨i, hi, rfl⟩
    have hpos : 0 < x.1 i := by
      rw [mem_supp] at hi
      exact lt_of_le_of_ne (x.2.1 i) (Ne.symm hi)
    have hle : x.1 i ≤ ∑ i' : Fin m, if f i' = f i then x.1 i' else 0 := by
      have h1 := Finset.single_le_sum (s := (Finset.univ : Finset (Fin m)))
        (f := fun i' => if f i' = f i then x.1 i' else 0)
        (fun i' _ => by by_cases h : f i' = f i <;> simp [h, x.2.1])
        (Finset.mem_univ i)
      simpa using h1
    exact ne_of_gt (lt_of_lt_of_le hpos hle)

theorem supp_map_card_le {m k : ℕ} (f : Fin m → Fin k) (hf : Function.Injective f)
    {x : stdSimplex ℝ (Fin m)} (h : (supp x).card ≤ 2) :
    (supp (stdSimplex.map f x)).card ≤ 2 := by
  rw [supp_map f hf, Finset.card_image_of_injective _ hf]
  exact h

/-! ## Low dimensionality is invariant under the gluing relation -/

theorem isLowDim_inl_iff {D : MData X n x₀} (i : D.Idx)
    (x : stdSimplex ℝ (Fin (n + 2))) :
    isLowDim D (Sum.inl (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2)))) ↔
      (supp x).card ≤ 2 := Iff.rfl

theorem isLowDim_inr {D : MData X n x₀} (i : D.Idx) (s : I) :
    isLowDim D (Sum.inr (⟨i, s⟩ : Σ _ : D.Idx, I)) := trivial

theorem isLowDim_modelRel {D : MData X n x₀} {a b : Raw D} (h : modelRel D a b) :
    (isLowDim D a ↔ isLowDim D b) := by
  rcases h with ⟨i, j, p, q, x, rfl, rfl, hs⟩ | ⟨i, ha, hb⟩ | ⟨i, j, ha, hb⟩
  · show ((supp (facept (n + 1) p x)).card ≤ 2 ↔ (supp (facept (n + 1) q x)).card ≤ 2)
    rw [show facept (n + 1) p x = stdSimplex.map p.succAbove x from rfl,
      show facept (n + 1) q x = stdSimplex.map q.succAbove x from rfl,
      supp_map p.succAbove p.succAbove_right_injective,
      supp_map q.succAbove q.succAbove_right_injective,
      Finset.card_image_of_injective _ p.succAbove_right_injective,
      Finset.card_image_of_injective _ q.succAbove_right_injective]
  · subst ha; subst hb
    exact ⟨fun _ => trivial, fun _ => isLowDim_vertPt D (Sum.inl ⟨i, 0⟩)⟩
  · subst ha; subst hb
    exact ⟨fun _ => trivial, fun _ => trivial⟩

theorem isLowDim_eqvGen {D : MData X n x₀} {a b : Raw D}
    (h : Relation.EqvGen (modelRel D) a b) : (isLowDim D a ↔ isLowDim D b) := by
  induction h with
  | rel x y hr => exact isLowDim_modelRel hr
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## The reconstruction of a point of a standard simplex from its support -/

theorem eq_vertex_of_supp {m : ℕ} {x : stdSimplex ℝ (Fin m)} {p : Fin m}
    (h : supp x = {p}) : x = stdSimplex.vertex p := by
  have hk : ∀ k : Fin m, x.1 k = if k = p then (1 : ℝ) else 0 := by
    intro k
    by_cases hkp : k = p
    · subst hkp
      rw [if_pos rfl, ← sum_supp_eq_one x, h, Finset.sum_singleton]
    · rw [if_neg hkp]
      by_contra hne
      have hk' : k ∈ supp x := by rw [mem_supp]; exact hne
      rw [h, Finset.mem_singleton] at hk'
      exact hkp hk'
  apply Subtype.ext
  funext k
  rw [hk k]
  simp only [stdSimplex.vertex_coe, Pi.single_apply]

theorem exists_sdPt_of_supp {m : ℕ} {p q : Fin m} (hpq : p < q) {x : stdSimplex ℝ (Fin m)}
    (h : supp x = {p, q}) :
    ∃ s : I, x = sdPt p q s ∧ (s : ℝ) = x.1 q ∧ 0 < (s : ℝ) ∧ (s : ℝ) < 1 := by
  have hsum : x.1 p + x.1 q = 1 := by
    rw [← sum_supp_eq_one x, h, Finset.sum_pair hpq.ne]
  have hpmem : p ∈ supp x := by rw [h]; simp
  have hqmem : q ∈ supp x := by rw [h]; simp
  have hppos : 0 < x.1 p := by
    rw [mem_supp] at hpmem
    exact lt_of_le_of_ne (x.2.1 p) (Ne.symm hpmem)
  have hqpos : 0 < x.1 q := by
    rw [mem_supp] at hqmem
    exact lt_of_le_of_ne (x.2.1 q) (Ne.symm hqmem)
  have hqlt : x.1 q < 1 := by linarith
  let s : I := ⟨x.1 q, x.2.1 q, le_of_lt hqlt⟩
  have hsv : (s : ℝ) = x.1 q := rfl
  have hk : ∀ k : Fin m, x.1 k
      = (if k = p then 1 - (s : ℝ) else 0) + (if k = q then (s : ℝ) else 0) := by
    intro k
    by_cases hkp : k = p
    · subst hkp
      rw [if_pos rfl, if_neg hpq.ne, add_zero, hsv]
      linarith
    · by_cases hkq : k = q
      · subst hkq
        rw [if_neg hpq.ne.symm, if_pos rfl, zero_add]
      · rw [if_neg hkp, if_neg hkq, add_zero]
        by_contra hne
        have hk' : k ∈ supp x := by rw [mem_supp]; exact hne
        rw [h, Finset.mem_insert, Finset.mem_singleton] at hk'
        tauto
  refine ⟨s, ?_, hsv, by rw [hsv]; exact hqpos, by rw [hsv]; exact hqlt⟩
  apply Subtype.ext
  funext k
  rw [sdPt_coe, hk k]

/-! ## The canonical form computed by `decomp` -/

theorem decomp_vertex {m : ℕ} (p : Fin m) :
    decomp (stdSimplex.vertex p : stdSimplex ℝ (Fin m)) = Sum.inl p := by
  have h1 : (supp (stdSimplex.vertex p : stdSimplex ℝ (Fin m))).card = 1 := by
    rw [supp_vertex]; exact Finset.card_singleton p
  rw [decomp, dif_pos h1]
  simp only [supp_vertex, Finset.min'_singleton]

theorem decomp_sdPt {m : ℕ} {p q : Fin m} (hpq : p < q) {s : I}
    (h0 : 0 < (s : ℝ)) (h1 : (s : ℝ) < 1) :
    decomp (sdPt p q s) =
      Sum.inr (⟨(⟨(p, q), hpq⟩ : {pq : Fin m × Fin m // pq.1 < pq.2}), s⟩) := by
  have hsupp : supp (sdPt p q s) = {p, q} :=
    supp_sdPt_of_ne hpq.ne (ne_of_gt h0) (ne_of_lt h1)
  have hne : (supp (sdPt p q s)).card ≠ 1 := by
    rw [hsupp, Finset.card_pair hpq.ne]; norm_num
  have hmin : (supp (sdPt p q s)).min' (supp_nonempty (sdPt p q s)) = p := by
    simp only [hsupp, Finset.min'_pair, min_eq_left hpq.le]
  have hmax : (supp (sdPt p q s)).max' (supp_nonempty (sdPt p q s)) = q := by
    simp only [hsupp, Finset.max'_pair, max_eq_right hpq.le]
  rw [decomp]
  rw [dif_neg hne]
  rw [Sum.inr.injEq]
  refine Prod.ext (Subtype.ext (Prod.ext hmin hmax)) ?_
  refine Subtype.ext ?_
  change (sdPt p q s).1 ((supp (sdPt p q s)).max' (supp_nonempty (sdPt p q s))) = (s : ℝ)
  rw [hmax]
  exact sdPt_apply_right hpq.ne s

theorem eq_vertex_of_decomp_inl {m : ℕ} {x : stdSimplex ℝ (Fin m)} {p : Fin m}
    (h : decomp x = Sum.inl p) : x = stdSimplex.vertex p := by
  have hcard : (supp x).card = 1 := by
    by_contra hc
    have h' := h
    rw [decomp] at h'
    rw [dif_neg hc] at h'
    exact absurd h' (by simp)
  have hmin : (supp x).min' (supp_nonempty x) = p := by
    have h' := h
    rw [decomp] at h'
    rw [dif_pos hcard] at h'
    exact Sum.inl.inj h'
  have hminpt : (supp x).min' (supp_nonempty x) = p := hmin
  have hsup : supp x = {p} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    have h1 : a = p := by
      have h' := hminpt
      simp only [ha] at h'
      rw [Finset.min'_singleton] at h'
      exact h'
    rw [ha, h1]
  exact eq_vertex_of_supp hsup

theorem eq_sdPt_of_decomp_inr {m : ℕ} {x : stdSimplex ℝ (Fin m)} {pq : Fin m × Fin m}
    {hpq : pq.1 < pq.2} {s : I}
    (h : decomp x = Sum.inr (⟨(⟨pq, hpq⟩ : {pq : Fin m × Fin m // pq.1 < pq.2}), s⟩))
    (hcard : (supp x).card ≤ 2) :
    x = sdPt pq.1 pq.2 s ∧ 0 < (s : ℝ) ∧ (s : ℝ) < 1 := by
  have hc1 : ¬ (supp x).card = 1 := by
    intro hc
    have h' := h
    rw [decomp] at h'
    rw [dif_pos hc] at h'
    exact absurd h' (by simp)
  have hmin : (supp x).min' (supp_nonempty x) = pq.1 := by
    have h' := h
    rw [decomp] at h'
    rw [dif_neg hc1] at h'
    rw [Sum.inr.injEq, Prod.mk.injEq] at h'
    exact congrArg (fun z : {pq : Fin m × Fin m // pq.1 < pq.2} => z.1.1) h'.1
  have hmax : (supp x).max' (supp_nonempty x) = pq.2 := by
    have h' := h
    rw [decomp] at h'
    rw [dif_neg hc1] at h'
    rw [Sum.inr.injEq, Prod.mk.injEq] at h'
    exact congrArg (fun z : {pq : Fin m × Fin m // pq.1 < pq.2} => z.1.2) h'.1
  have hs : x.1 pq.2 = (s : ℝ) := by
    have h' := h
    rw [decomp] at h'
    rw [dif_neg hc1] at h'
    rw [Sum.inr.injEq, Prod.mk.injEq] at h'
    have h2 : x.1 ((supp x).max' (supp_nonempty x)) = (s : ℝ) :=
      congrArg Subtype.val h'.2
    rw [hmax] at h2
    exact h2
  have hsupp : supp x = {pq.1, pq.2} := by
    have h1 : ({pq.1, pq.2} : Finset (Fin m)) ⊆ supp x := by
      intro k hk
      rw [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · rw [← hmin]; exact Finset.min'_mem _ _
      · rw [← hmax]; exact Finset.max'_mem _ _
    have h2 : (supp x).card ≤ ({pq.1, pq.2} : Finset (Fin m)).card := by
      rw [Finset.card_pair hpq.ne]; exact hcard
    exact (Finset.eq_of_subset_of_card_le h1 h2).symm
  obtain ⟨s', hs', hs'val, hs'0, hs'1⟩ := exists_sdPt_of_supp hpq hsupp
  have hss : s' = s := Subtype.ext (by rw [hs'val, hs])
  subst hss
  exact ⟨hs', hs'0, hs'1⟩

/-! ## The graph data of the canonical points -/

theorem wOf_vertex {D : MData X n x₀} (i : D.Idx) (p : Fin (n + 2))
    (h : isLowDim D (Sum.inl (⟨i, stdSimplex.vertex p⟩ :
      Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))) :
    wOf D ⟨Sum.inl (⟨i, stdSimplex.vertex p⟩ :
      Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))), h⟩ = Sum.inl (vCl D (Sum.inl ⟨i, p⟩)) := by
  rw [wOf_inl_inl D i (stdSimplex.vertex p) h p (decomp_vertex p)]

theorem wOf_sdPt {D : MData X n x₀} {i : D.Idx} {p q : Fin (n + 2)} (hpq : p < q) {s : I}
    (h0 : 0 < (s : ℝ)) (h1 : (s : ℝ) < 1)
    (h : isLowDim D (Sum.inl (⟨i, sdPt p q s⟩ :
      Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))) :
    wOf D ⟨Sum.inl (⟨i, sdPt p q s⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))), h⟩
      = Sum.inr (eCl D (Sum.inl (⟨i,
          (⟨(p, q), hpq⟩ : {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2})⟩ :
          Σ _ : D.Idx, {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2})), s) := by
  rw [wOf_inl_inr D i (sdPt p q s) h
    (⟨(p, q), hpq⟩ : {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2}) s
    (decomp_sdPt hpq h0 h1)]

/-! ## The set `good` and saturation -/

/-- The low dimensional points whose graph data lies in `U`. -/
def good (D : MData X n x₀) (U : Set (V D ⊕ (E D × I))) : Set (Raw D) :=
  {y | ∃ h : isLowDim D y, wOf D ⟨y, h⟩ ∈ U}

theorem mem_good_iff {D : MData X n x₀} {U : Set (V D ⊕ (E D × I))} {y : Raw D} :
    y ∈ good D U ↔ ∃ h : isLowDim D y, wOf D ⟨y, h⟩ ∈ U := Iff.rfl

theorem isLowDim_of_mem_good {D : MData X n x₀} {U : Set (V D ⊕ (E D × I))} {y : Raw D}
    (hy : y ∈ good D U) : isLowDim D y := hy.choose

theorem wOf_congr {D : MData X n x₀} {y : Raw D} (h h' : isLowDim D y) :
    wOf D ⟨y, h⟩ = wOf D ⟨y, h'⟩ := by
  rcases y with ⟨i, x⟩ | ⟨i, s⟩ <;> rfl

theorem mem_good_of {D : MData X n x₀} {U : Set (V D ⊕ (E D × I))} {y : Raw D}
    (h : isLowDim D y) (hm : wOf D ⟨y, h⟩ ∈ U) : y ∈ good D U := ⟨h, hm⟩

theorem mem_good_iff_of {D : MData X n x₀} {U : Set (V D ⊕ (E D × I))} {y : Raw D}
    (h : isLowDim D y) : y ∈ good D U ↔ wOf D ⟨y, h⟩ ∈ U := by
  constructor
  · intro hy
    have hh := hy.choose_spec
    rwa [wOf_congr hy.choose h] at hh
  · intro hm; exact ⟨h, hm⟩

theorem good_mono {D : MData X n x₀} {U U' : Set (V D ⊕ (E D × I))} (h : U ⊆ U') :
    good D U ⊆ good D U' := by
  rintro y ⟨hy, hmem⟩
  exact ⟨hy, h hmem⟩

/-- `U` is a union of classes of the graph relation on `V D ⊕ (E D × I)`. -/
def Sat (D : MData X n x₀) (U : Set (V D ⊕ (E D × I))) : Prop :=
  ∀ ⦃p q⦄, gq (a D) (b D) p = gq (a D) (b D) q → p ∈ U → q ∈ U

theorem Sat.mem {D : MData X n x₀} {U : Set (V D ⊕ (E D × I))} (h : Sat D U) {p q}
    (hpq : gq (a D) (b D) p = gq (a D) (b D) q) (hp : p ∈ U) : q ∈ U := h hpq hp

theorem sat_preimage {D : MData X n x₀} (W : Set (GraphX (a D) (b D))) :
    Sat D (gq (a D) (b D) ⁻¹' W) := fun p q hpq hp => by
  show gq (a D) (b D) q ∈ W
  rw [← hpq]; exact hp

/-! ## Neighbourhoods in the space of vertices and edges -/

/-- A neighbourhood of `(e, s)` in `V D ⊕ (E D × I)` contains a window of all parameters close to
`s` on the same edge. -/
theorem exists_nhds_pair {D : MData X n x₀} {U : Set (V D ⊕ (E D × I))} (hU : IsOpen U)
    {e : E D} {s : I} (h : Sum.inr (e, s) ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : I, |(t : ℝ) - (s : ℝ)| < ε → Sum.inr (e, t) ∈ U := by
  let cl : ℝ → I := fun x => ⟨max 0 (min 1 x), le_max_left 0 (min 1 x),
    max_le zero_le_one (min_le_left 1 x)⟩
  have hcl_cont : Continuous cl := by
    apply Continuous.subtype_mk
    exact continuous_const.max (continuous_const.min continuous_id)
  have hcl_s : cl (s : ℝ) = s := by
    apply Subtype.ext
    show max 0 (min 1 (s : ℝ)) = (s : ℝ)
    rw [min_eq_right s.2.2, max_eq_right s.2.1]
  have hcl_t : ∀ t : I, cl (t : ℝ) = t := by
    intro t
    apply Subtype.ext
    show max 0 (min 1 (t : ℝ)) = (t : ℝ)
    rw [min_eq_right t.2.2, max_eq_right t.2.1]
  have hcont : Continuous (fun x : ℝ => (Sum.inr (e, cl x) : V D ⊕ (E D × I))) :=
    continuous_inr.comp (continuous_const.prodMk hcl_cont)
  have hmem : (fun x : ℝ => Sum.inr (e, cl x)) ⁻¹' U ∈ 𝓝 (s : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [hcl_s]; exact hU.mem_nhds h)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨ε, hε, fun t ht => ?_⟩
  have ht' : (t : ℝ) ∈ Metric.ball (s : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact ht
  have h1 := hsub ht'
  simp only [Set.mem_preimage] at h1
  rwa [hcl_t t] at h1

theorem Sat.mem_zero {D : MData X n x₀} {U : Set (V D ⊕ (E D × I))} (hU : Sat D U)
    {e : E D} {v : V D} (he : a D e = v) (hv : Sum.inl v ∈ U) : Sum.inr (e, 0) ∈ U := by
  have h : gq (a D) (b D) (Sum.inr (e, 0)) = gq (a D) (b D) (Sum.inl v) := by
    rw [rel_ae (a D) (b D) e, he]
  exact hU h.symm hv

theorem Sat.mem_one {D : MData X n x₀} {U : Set (V D ⊕ (E D × I))} (hU : Sat D U)
    {e : E D} {v : V D} (he : b D e = v) (hv : Sum.inl v ∈ U) : Sum.inr (e, 1) ∈ U := by
  have h : gq (a D) (b D) (Sum.inr (e, 1)) = gq (a D) (b D) (Sum.inl v) := by
    rw [rel_be (a D) (b D) e, he]
  exact hU h.symm hv

/-- The initial vertex of a raw edge of a copy of a simplex. -/
theorem a_eCl_inl {D : MData X n x₀} (i : D.Idx) (p q : Fin (n + 2)) (hpq : p < q) :
    a D (eCl D (Sum.inl (⟨i,
      (⟨(p, q), hpq⟩ : {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2})⟩ :
      Σ _ : D.Idx, {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2}))) =
      vCl D (Sum.inl ⟨i, p⟩) := rfl

/-- The terminal vertex of a raw edge of a copy of a simplex. -/
theorem b_eCl_inl {D : MData X n x₀} (i : D.Idx) (p q : Fin (n + 2)) (hpq : p < q) :
    b D (eCl D (Sum.inl (⟨i,
      (⟨(p, q), hpq⟩ : {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2})⟩ :
      Σ _ : D.Idx, {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2}))) =
      vCl D (Sum.inl ⟨i, q⟩) := rfl

/-- The initial vertex of a raw arc. -/
theorem a_eCl_inr {D : MData X n x₀} (i : D.Idx) :
    a D (eCl D (Sum.inr ⟨i, PUnit.unit⟩)) = vCl D (Sum.inr ⟨i, 0⟩) := rfl

/-- The terminal vertex of a raw arc. -/
theorem b_eCl_inr {D : MData X n x₀} (i : D.Idx) :
    b D (eCl D (Sum.inr ⟨i, PUnit.unit⟩)) = vCl D (Sum.inr ⟨i, 1⟩) := rfl

end GoodAux

end

end Work.RatHurewicz.SkelGraph
