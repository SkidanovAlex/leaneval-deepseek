/-
# ELRig — the two-sidedness API of pair curves and of the tripod

Derived consequences of the input structures `PairSides` and `TripodSides` of
`Submission/Work/ELRig/Defs.lean`:

* every preconnected subset of the complement of a pair curve lies in one of the two sides;
* the **separation lemma** (T7 of §2 of the contract): a preconnected subset of the filled Julia
  set which meets a side of a pair curve and contains a point outside its closure contains the
  landing point of the pair;
* the same for the three arms of the tripod at `b₂`.
-/
import Submission.Work.ELRig.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.EL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ}

/-! ## The two sides of a pair curve -/

/-- A point off the pair curve of `P` lies in one of its two sides. -/
theorem PairSides.mem_or_mem {P : CoPair hN} (h : PairSides hN P) {z : ℂ}
    (hz : z ∉ pairCurve P) : z ∈ pairSide P ∨ z ∈ pairSideNear P := by
  have hz' : z ∈ (pairCurve P)ᶜ := hz
  rw [← h.union_eq] at hz'
  exact hz'

/-- **Every preconnected subset of the complement of a pair curve lies in one of the two
sides.** -/
theorem PairSides.subset_of_preconnected {P : CoPair hN} (h : PairSides hN P) {T : Set ℂ}
    (hconn : IsPreconnected T) (hsub : T ⊆ (pairCurve P)ᶜ) :
    T ⊆ pairSide P ∨ T ⊆ pairSideNear P := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · exact Or.inl (Set.empty_subset _)
  · have h1 : T ⊆ pairSide P ∪ pairSideNear P := by rw [h.union_eq]; exact hsub
    have h2 : T ∩ (pairSide P ∩ pairSideNear P) = ∅ := by
      rw [Set.disjoint_iff_inter_eq_empty.mp h.disjoint, Set.inter_empty]
    exact isPreconnected_iff_subset_of_disjoint.mp hconn _ _ h.isOpen_far h.isOpen_near h1 h2

/-- A preconnected set which meets an open set and contains a point outside its closure meets the
frontier of that open set. -/
theorem meets_frontier_of {S T : Set ℂ} (hopen : IsOpen S) (hconn : IsPreconnected T)
    {x x' : ℂ} (hx : x ∈ T) (hxs : x ∈ S) (hx' : x' ∈ T) (hx'c : x' ∉ closure S) :
    ∃ z ∈ T, z ∈ frontier S := by
  by_contra hcon
  have hcon' : ∀ z, z ∈ T → z ∉ frontier S := fun z hz hzfr => hcon ⟨z, hz, hzfr⟩
  have hsub : T ⊆ interior S ∪ (closure S)ᶜ := by
    intro z hz
    by_cases hzc : z ∈ closure S
    · refine Or.inl ?_
      by_contra hzi
      have hzcl : z ∈ closure (Sᶜ) := by
        rw [closure_compl]
        exact (Set.mem_compl_iff (s := interior S) (x := z)).mpr hzi
      exact hcon' z hz (by rw [frontier_eq_closure_inter_closure]; exact ⟨hzc, hzcl⟩)
    · exact Or.inr ((Set.mem_compl_iff (s := closure S) (x := z)).mpr hzc)
  have hne : ¬ (T ∩ (interior S ∩ (closure S)ᶜ)).Nonempty := by
    rintro ⟨z, hz⟩
    exact ((Set.mem_compl_iff (s := closure S) (x := z)).mp hz.2.2) (subset_closure (interior_subset (s := S) hz.2.1))
  have hxU : x ∈ interior S := by rw [hopen.interior_eq]; exact hxs
  rcases isPreconnected_iff_subset_of_disjoint.mp hconn _ _ isOpen_interior
      isClosed_closure.isOpen_compl hsub (Set.not_nonempty_iff_eq_empty.mp hne) with hU | hV
  · exact hx'c (subset_closure (interior_subset (s := S) (hU hx')))
  · exact ((Set.mem_compl_iff (s := closure S) (x := x)).mp (hV hx)) (subset_closure hxs)

/-- A preconnected set which meets a side of a pair curve and contains a point outside its
closure meets the frontier of that side. -/
theorem PairSides.meets_frontier {P : CoPair hN} (h : PairSides hN P) {T : Set ℂ}
    (hconn : IsPreconnected T) {x x' : ℂ} (hx : x ∈ T) (hxs : x ∈ pairSide P) (hx' : x' ∈ T)
    (hx'c : x' ∉ closure (pairSide P)) : ∃ z ∈ T, z ∈ frontier (pairSide P) :=
  meets_frontier_of h.isOpen_far hconn hx hxs hx' hx'c

/-- The near-side form of `PairSides.meets_frontier`. -/
theorem PairSides.meets_frontier_near {P : CoPair hN} (h : PairSides hN P) {T : Set ℂ}
    (hconn : IsPreconnected T) {x x' : ℂ} (hx : x ∈ T) (hxs : x ∈ pairSideNear P) (hx' : x' ∈ T)
    (hx'c : x' ∉ closure (pairSideNear P)) : ∃ z ∈ T, z ∈ frontier (pairSideNear P) :=
  meets_frontier_of h.isOpen_near hconn hx hxs hx' hx'c

/-- The pair curve meets the filled Julia set only in its landing point. -/
theorem pairCurve_inter_K_subset {P : CoPair hN} : pairCurve P ∩ K c ⊆ {P.y} := by
  rintro z ⟨hz1, hz2⟩
  simp only [pairCurve, RawPair.curve, Set.mem_union, Set.mem_singleton_iff] at hz1
  rcases hz1 with (h | h) | h
  · exfalso
    exact ((Set.mem_compl_iff (s := K c) (x := z)).mp
      ((Work.Top.NakaneData.paramRay_subset_compl hN P.a) h)) hz2
  · simpa using h
  · exfalso
    exact ((Set.mem_compl_iff (s := K c) (x := z)).mp
      ((Work.Top.NakaneData.paramRay_subset_compl hN P.b) h)) hz2

/-- **Separation (T7).**  A preconnected subset `S` of the filled Julia set which meets the far
side of a pair curve and contains a point outside the closure of that side contains the landing
point of the pair. -/
theorem separation {P : CoPair hN} (h : PairSides hN P) {S : Set ℂ} (hS : S ⊆ K c)
    (hconn : IsPreconnected S) {x x' : ℂ} (hx : x ∈ S) (hxs : x ∈ pairSide P) (hx' : x' ∈ S)
    (hx'c : x' ∉ closure (pairSide P)) : P.y ∈ S := by
  obtain ⟨z, hzT, hzfr⟩ := h.meets_frontier hconn hx hxs hx' hx'c
  have hzK : z ∈ K c := hS hzT
  have hzC : z ∈ pairCurve P := by rw [← h.frontier_far]; exact hzfr
  have hzy : z = P.y := by
    have := pairCurve_inter_K_subset (hN := hN) (P := P) ⟨hzC, hzK⟩
    simpa using this
  exact hzy ▸ hzT

/-- **Separation (T7), near-side form.** -/
theorem separation_near {P : CoPair hN} (h : PairSides hN P) {S : Set ℂ} (hS : S ⊆ K c)
    (hconn : IsPreconnected S) {x x' : ℂ} (hx : x ∈ S) (hxs : x ∈ pairSideNear P) (hx' : x' ∈ S)
    (hx'c : x' ∉ closure (pairSideNear P)) : P.y ∈ S := by
  obtain ⟨z, hzT, hzfr⟩ := h.meets_frontier_near hconn hx hxs hx' hx'c
  have hzK : z ∈ K c := hS hzT
  have hzC : z ∈ pairCurve P := by rw [← h.frontier_near]; exact hzfr
  have hzy : z = P.y := by
    have := pairCurve_inter_K_subset (hN := hN) (P := P) ⟨hzC, hzK⟩
    simpa using this
  exact hzy ▸ hzT

/-- A point of the far side is not on the pair curve. -/
theorem PairSides.notMem_curve_of_mem_far {P : CoPair hN} (h : PairSides hN P) {z : ℂ}
    (hz : z ∈ pairSide P) : z ∉ pairCurve P := by
  have hz' : z ∈ (pairCurve P)ᶜ := by
    rw [← h.union_eq]; exact Or.inl hz
  exact hz'

/-- A point of the near side is not on the pair curve. -/
theorem PairSides.notMem_curve_of_mem_near {P : CoPair hN} (h : PairSides hN P) {z : ℂ}
    (hz : z ∈ pairSideNear P) : z ∉ pairCurve P := by
  have hz' : z ∈ (pairCurve P)ᶜ := by
    rw [← h.union_eq]; exact Or.inr hz
  exact hz'


/-! ## The three arms of the tripod -/

/-- **Every preconnected subset of the complement of the tripod curve lies in one of the three
arms.** -/
theorem TripodSides.subset_of_preconnected {y : ℂ}
    (T : TripodSides hN y) {S : Set ℂ} (hconn : IsPreconnected S)
    (hsub : S ⊆ (tripodCurve hN y)ᶜ) :
    S ⊆ armA hN y T.lands_a T.lands_b ∨ S ⊆ armB hN y T.lands_b T.lands_c ∨
      S ⊆ armC hN y T.lands_c T.lands_a' := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact Or.inl (Set.empty_subset _)
  · have h1 : S ⊆ armA hN y T.lands_a T.lands_b ∪ (armB hN y T.lands_b T.lands_c ∪
        armC hN y T.lands_c T.lands_a') := by
      rw [T.union_eq]; exact hsub
    have hUV : armA hN y T.lands_a T.lands_b ∩ (armB hN y T.lands_b T.lands_c ∪
        armC hN y T.lands_c T.lands_a') = ∅ := by
      rw [Set.inter_union_distrib_left,
        Set.disjoint_iff_inter_eq_empty.mp T.disjoint_AB,
        Set.disjoint_iff_inter_eq_empty.mp T.disjoint_AC, Set.union_empty]
    have h2 : S ∩ (armA hN y T.lands_a T.lands_b ∩ (armB hN y T.lands_b T.lands_c ∪
        armC hN y T.lands_c T.lands_a')) = ∅ := by rw [hUV, Set.inter_empty]
    rcases isPreconnected_iff_subset_of_disjoint.mp hconn _ _ T.isOpen_A
        (T.isOpen_B.union T.isOpen_C) h1 h2 with hA | hBC
    · exact Or.inl hA
    · have h3 : S ∩ (armB hN y T.lands_b T.lands_c ∩ armC hN y T.lands_c T.lands_a') = ∅ := by
        rw [Set.disjoint_iff_inter_eq_empty.mp T.disjoint_BC, Set.inter_empty]
      rcases isPreconnected_iff_subset_of_disjoint.mp hconn _ _ T.isOpen_B T.isOpen_C hBC h3 with
        hB | hC
      · exact Or.inr (Or.inl hB)
      · exact Or.inr (Or.inr hC)

/-- A point of the complement of the tripod curve lies in one of the three arms. -/
theorem TripodSides.mem_arm_of {y : ℂ} (T : TripodSides hN y) {z : ℂ}
    (hz : z ∉ tripodCurve hN y) :
    z ∈ armA hN y T.lands_a T.lands_b ∨ z ∈ armB hN y T.lands_b T.lands_c ∨
      z ∈ armC hN y T.lands_c T.lands_a' := by
  have hz' : z ∈ (tripodCurve hN y)ᶜ := hz
  rw [← T.union_eq] at hz'
  rcases hz' with h | (h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end Work.EL
