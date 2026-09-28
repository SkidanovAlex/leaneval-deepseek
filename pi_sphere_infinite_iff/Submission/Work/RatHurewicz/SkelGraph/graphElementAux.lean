import Mathlib
import Submission.Work.RatHurewicz.SkelGraph.graphElementDefs

/-!
# Auxiliary lemmas for `Work.RatHurewicz.SkelGraph.graphElement`

Elementary facts about the support of a point of a standard simplex and about the canonical form
`decomp` of a low dimensional point.
-/

namespace Work.RatHurewicz.SkelGraph

open scoped Topology Simplicial unitInterval

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-! ## Coordinates of `vertex` and `sdPt` -/

theorem ge_vertex_apply {m : ℕ} (p : Fin m) :
    (stdSimplex.vertex p : stdSimplex ℝ (Fin m)).1 = Pi.single p (1 : ℝ) := rfl

theorem ge_sdPt_apply {m : ℕ} (p q : Fin m) (s : I) (j : Fin m) :
    (sdPt p q s).1 j = (if j = p then 1 - (s : ℝ) else 0) + (if j = q then (s : ℝ) else 0) :=
  sdPt_apply p q s j

theorem ge_sdPt_apply_left {m : ℕ} {p q : Fin m} (hpq : p ≠ q) (s : I) :
    (sdPt p q s).1 p = 1 - (s : ℝ) :=
  sdPt_apply_left hpq s

theorem ge_sdPt_apply_right {m : ℕ} {p q : Fin m} (hpq : p ≠ q) (s : I) :
    (sdPt p q s).1 q = (s : ℝ) :=
  sdPt_apply_right hpq s

theorem ge_sdPt_apply_eq_zero {m : ℕ} {p q j : Fin m} (hpq : p ≠ q) (s : I)
    (hjp : j ≠ p) (hjq : j ≠ q) : (sdPt p q s).1 j = 0 :=
  sdPt_apply_eq_zero hpq s hjp hjq

/-! ## Supports -/

theorem ge_supp_vertex {m : ℕ} (p : Fin m) :
    supp (stdSimplex.vertex p : stdSimplex ℝ (Fin m)) = {p} := by
  ext k
  rw [mem_supp, Finset.mem_singleton]
  by_cases hk : k = p
  · subst hk
    rw [ge_vertex_apply, Pi.single_eq_same]
    simp
  · rw [ge_vertex_apply, Pi.single_eq_of_ne hk]
    simp [hk]

theorem ge_supp_sdPt_of_ne {m : ℕ} {p q : Fin m} (hpq : p ≠ q) {s : I}
    (h0 : (s : ℝ) ≠ 0) (h1 : (s : ℝ) ≠ 1) : supp (sdPt p q s) = {p, q} := by
  ext k
  rw [mem_supp, Finset.mem_insert, Finset.mem_singleton]
  by_cases hkp : k = p
  · subst hkp
    rw [ge_sdPt_apply_left hpq s]
    constructor
    · intro _; exact Or.inl rfl
    · intro _ hcon; exact h1 (by linarith)
  · by_cases hkq : k = q
    · subst hkq
      rw [ge_sdPt_apply_right hpq s]
      constructor
      · intro _; exact Or.inr rfl
      · intro _ hcon; exact h0 hcon
    · rw [ge_sdPt_apply_eq_zero hpq s hkp hkq]
      simp [hkp, hkq]

theorem ge_supp_sdPt_zero {m : ℕ} (p q : Fin m) : supp (sdPt p q (0 : I)) = {p} := by
  rw [sdPt_zero]; exact ge_supp_vertex p

theorem ge_supp_sdPt_one {m : ℕ} (p q : Fin m) : supp (sdPt p q (1 : I)) = {q} := by
  rw [sdPt_one]; exact ge_supp_vertex q

theorem ge_supp_map {m k : ℕ} (f : Fin m → Fin k) (hf : Function.Injective f)
    (x : stdSimplex ℝ (Fin m)) : supp (stdSimplex.map f x) = (supp x).image f := by
  ext j
  rw [mem_supp, Finset.mem_image]
  change (FunOnFinite.linearMap ℝ ℝ f x.1) j ≠ 0 ↔ ∃ a, a ∈ supp x ∧ f a = j
  rw [FunOnFinite.linearMap_apply_apply]
  constructor
  · intro hj
    obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
    rw [Finset.mem_filter] at hi
    exact ⟨i, by simpa [mem_supp] using hne, hi.2⟩
  · rintro ⟨i, hi, rfl⟩
    have hne : x.1 i ≠ 0 := by simpa [mem_supp] using hi
    have hpos : 0 < x.1 i := lt_of_le_of_ne (x.2.1 i) (Ne.symm hne)
    have hmem : i ∈ Finset.univ.filter (fun a : Fin m => f a = f i) := by simp
    exact ne_of_gt (lt_of_lt_of_le hpos (Finset.single_le_sum (fun b _ => x.2.1 b) hmem))

theorem ge_card_supp_le_card_supp_facept {m : ℕ} (r : Fin (m + 1))
    (x : stdSimplex ℝ (Fin m)) :
    (supp x).card ≤ (supp (facept m r x)).card := by
  have hf : Function.Injective r.succAbove := Fin.succAbove_right_injective
  change (supp x).card ≤ (supp (stdSimplex.map r.succAbove x)).card
  rw [ge_supp_map r.succAbove hf x, Finset.card_image_of_injective _ hf]

/-! ## The canonical form `decomp` -/

theorem ge_decomp_vertex {m : ℕ} (p : Fin m) :
    decomp (stdSimplex.vertex p : stdSimplex ℝ (Fin m)) = Sum.inl p := by
  have h1 : (supp (stdSimplex.vertex p : stdSimplex ℝ (Fin m))).card = 1 := by
    rw [ge_supp_vertex]; exact Finset.card_singleton p
  have hmin : (supp (stdSimplex.vertex p : stdSimplex ℝ (Fin m))).min'
      (supp_nonempty (stdSimplex.vertex p : stdSimplex ℝ (Fin m))) = p := by
    simp only [ge_supp_vertex, Finset.min'_singleton]
  unfold decomp
  rw [dif_pos h1]
  exact congrArg Sum.inl hmin

theorem ge_decomp_sdPt {m : ℕ} {p q : Fin m} (hpq : p < q) {s : I}
    (h0 : 0 < (s : ℝ)) (h1 : (s : ℝ) < 1) :
    decomp (sdPt p q s) = Sum.inr (⟨(p, q), hpq⟩, s) := by
  have hs : supp (sdPt p q s) = {p, q} := ge_supp_sdPt_of_ne hpq.ne (ne_of_gt h0) (ne_of_lt h1)
  have hcard : (supp (sdPt p q s)).card ≠ 1 := by
    rw [hs, Finset.card_pair hpq.ne]; norm_num
  have hmin : (supp (sdPt p q s)).min' (supp_nonempty (sdPt p q s)) = p := by
    simp only [hs, Finset.min'_pair, min_eq_left hpq.le]
  have hmax : (supp (sdPt p q s)).max' (supp_nonempty (sdPt p q s)) = q := by
    simp only [hs, Finset.max'_pair, max_eq_right hpq.le]
  unfold decomp
  rw [dif_neg hcard]
  apply congrArg Sum.inr
  apply Prod.ext
  · apply Subtype.ext
    simp only [hmin, hmax]
  · apply Subtype.ext
    simp only [hmax]
    exact ge_sdPt_apply_right hpq.ne s

theorem ge_eq_vertex_of_decomp_inl {m : ℕ} {x : stdSimplex ℝ (Fin m)} {p : Fin m}
    (h : decomp x = Sum.inl p) : x = stdSimplex.vertex p := by
  have hcard : (supp x).card = 1 := by
    by_contra hc
    unfold decomp at h
    rw [dif_neg hc] at h
    exact absurd h (by simp)
  have hmin : (supp x).min' (supp_nonempty x) = p := by
    unfold decomp at h
    rw [dif_pos hcard] at h
    exact Sum.inl.inj h
  have hsupp : supp x = {p} := by
    have hsub : ({p} : Finset (Fin m)) ⊆ supp x := by
      rw [Finset.singleton_subset_iff, ← hmin]
      exact Finset.min'_mem _ _
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton]; omega)).symm
  apply Subtype.ext
  funext k
  by_cases hk : k = p
  · rw [hk]
    rw [ge_vertex_apply, Pi.single_eq_same]
    have hsum : ∑ j, x.1 j = x.1 p :=
      Finset.sum_eq_single (s := Finset.univ) p
        (fun b _ hb => by
          have hnb : b ∉ supp x := by
            rw [hsupp, Finset.mem_singleton]; exact fun hbp => hb hbp
          simpa [mem_supp] using hnb)
        (fun hp' => absurd (Finset.mem_univ p) hp')
    rw [← hsum]; exact x.2.2
  · rw [ge_vertex_apply, Pi.single_eq_of_ne hk]
    by_contra hne
    have hm : k ∈ supp x := by simpa [mem_supp] using hne
    rw [hsupp, Finset.mem_singleton] at hm
    exact hk hm

theorem ge_eq_sdPt_of_decomp_inr {m : ℕ} {x : stdSimplex ℝ (Fin m)}
    {e : {pq : Fin m × Fin m // pq.1 < pq.2}} {s : I}
    (h : decomp x = Sum.inr (e, s)) (hcard : (supp x).card ≤ 2) :
    x = sdPt e.1.1 e.1.2 s ∧ 0 < (s : ℝ) ∧ (s : ℝ) < 1 := by
  have hc1 : (supp x).card ≠ 1 := by
    intro hc
    unfold decomp at h
    rw [dif_pos hc] at h
    exact absurd h (by simp)
  have hsplit := h
  unfold decomp at hsplit
  rw [dif_neg hc1] at hsplit
  obtain ⟨hA, hB⟩ := Prod.mk_inj.mp (Sum.inr.inj hsplit)
  have hmin : (supp x).min' (supp_nonempty x) = e.1.1 :=
    congrArg Prod.fst (congrArg Subtype.val hA)
  have hmax : (supp x).max' (supp_nonempty x) = e.1.2 :=
    congrArg Prod.snd (congrArg Subtype.val hA)
  have hs : x.1 e.1.2 = (s : ℝ) := by
    rw [← hmax]; exact congrArg Subtype.val hB
  have hcard2 : (supp x).card = 2 := by
    have hpos : 0 < (supp x).card := Finset.card_pos.mpr (supp_nonempty x)
    rcases Nat.lt_or_eq_of_le hcard with hlt | heq
    · omega
    · exact heq
  have hsupp : supp x = {e.1.1, e.1.2} := by
    have hsub : ({e.1.1, e.1.2} : Finset (Fin m)) ⊆ supp x := by
      intro j hj
      rw [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with hj | hj
      · rw [hj, ← hmin]; exact Finset.min'_mem _ _
      · rw [hj, ← hmax]; exact Finset.max'_mem _ _
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair e.2.ne]; omega)).symm
  have hmem1 : e.1.1 ∈ supp x := by rw [hsupp]; simp
  have hmem2 : e.1.2 ∈ supp x := by rw [hsupp]; simp
  have hs0 : (s : ℝ) ≠ 0 := by rw [← hs]; simpa [mem_supp] using hmem2
  have hx1 : x.1 e.1.1 = 1 - (s : ℝ) := by
    have hsum : ∑ j, x.1 j = x.1 e.1.1 + x.1 e.1.2 := by
      rw [← Finset.sum_subset (Finset.subset_univ (supp x)) (fun j _ hj => by
        simpa [mem_supp] using hj)]
      rw [hsupp, Finset.sum_pair e.2.ne]
    rw [x.2.2] at hsum
    linarith [hs]
  refine ⟨?_, ?_, ?_⟩
  · apply Subtype.ext
    funext k
    rw [ge_sdPt_apply]
    by_cases hk1 : k = e.1.1
    · rw [hk1]
      rw [if_pos rfl, if_neg e.2.ne, add_zero, hx1]
    · by_cases hk2 : k = e.1.2
      · rw [hk2]
        rw [if_neg e.2.ne.symm, if_pos rfl, zero_add, hs]
      · rw [if_neg hk1, if_neg hk2, add_zero]
        by_contra hne
        have : k ∈ supp x := by simpa [mem_supp] using hne
        rw [hsupp, Finset.mem_insert, Finset.mem_singleton] at this
        tauto
  · exact lt_of_le_of_ne (s.2.1) (Ne.symm hs0)
  · have hpos1 : 0 < x.1 e.1.1 :=
      lt_of_le_of_ne (x.2.1 e.1.1) (Ne.symm (by simpa [mem_supp] using hmem1))
    linarith [hx1]

end

end Work.RatHurewicz.SkelGraph

namespace Work.RatHurewicz.SkelGraph

open scoped Topology Simplicial unitInterval

noncomputable section

theorem ge_facept_vertex {m : ℕ} (r : Fin (m + 1)) (u : Fin m) :
    facept m r (stdSimplex.vertex u) = stdSimplex.vertex (r.succAbove u) :=
  stdSimplex.map_vertex r.succAbove u

theorem ge_card_supp_facept {m : ℕ} (r : Fin (m + 1)) (x : stdSimplex ℝ (Fin m)) :
    (supp (facept m r x)).card = (supp x).card := by
  have hf : Function.Injective r.succAbove := Fin.succAbove_right_injective
  change (supp (stdSimplex.map r.succAbove x)).card = (supp x).card
  rw [ge_supp_map r.succAbove hf x, Finset.card_image_of_injective _ hf]

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

theorem ge_isLowDim_modelRel {D : MData X n x₀} {a b : Raw D} (h : modelRel D a b) :
    (isLowDim D a ↔ isLowDim D b) := by
  rcases h with ⟨i, j, p, q, x, rfl, rfl, h3⟩ | ⟨i, rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩
  · show ((supp (facept (n + 1) p x)).card ≤ 2 ↔ (supp (facept (n + 1) q x)).card ≤ 2)
    rw [ge_card_supp_facept, ge_card_supp_facept]
  · exact ⟨fun _ => trivial, fun _ => isLowDim_vertPt D (Sum.inl ⟨i, (0 : Fin (n + 2))⟩)⟩
  · exact ⟨fun _ => trivial, fun _ => trivial⟩

theorem ge_isLowDim_eqvGen {D : MData X n x₀} {a b : Raw D}
    (h : Relation.EqvGen (modelRel D) a b) : (isLowDim D a ↔ isLowDim D b) := by
  induction h with
  | rel x y hxy => exact ge_isLowDim_modelRel hxy
  | refl x => exact Iff.rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ih1 ih2 => exact ih1.trans ih2

end

end Work.RatHurewicz.SkelGraph
