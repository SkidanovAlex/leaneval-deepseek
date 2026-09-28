import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_convex_base
import Submission.Work.Cohomology.good_empty

set_option synthInstance.maxHeartbeats 400000

/-!
# `Good` for finite unions of convex coordinate pieces

`Work.Cohomology.Good N c W hW` is the elementwise form of Poincaré–Lefschetz duality for the open
set `W` (see `Work.Cohomology.pd_good`), and `Work.Cohomology.pd_good_convex` proves it for a single
convex coordinate piece

`pdPiece e Q = e ⁻¹' Q ∩ e.source`,  `Q ⊆ Metric.ball (e cc) r ⊆ e.target` open convex.

This file shows that `Good` is stable under taking finite unions of such pieces, by iterated
gluing: the intersection of a piece with a finite union of pieces is again a finite union of pieces
(`pdPiece e a ∩ pdPiece e Q = pdPiece e (Q ∩ a)`, and `a ∩ Q` is again open convex inside the ball).
The gluing step itself (Hatcher's five-lemma argument) is taken here as a hypothesis `glue`, so that
this file is independent of the Mayer–Vietoris machinery; it is instantiated with
`Work.Cohomology.pd_good_union`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **The piece of the open set `Q` in the coordinate chart `e`.** -/
def pdPiece {M : TopCat} {N : ℕ} (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)))
    (Q : Set (EuclideanSpace ℝ (Fin N))) : Set M :=
  (e ⁻¹' Q) ∩ e.source

/-- The piece is open for open `Q`. -/
theorem isOpen_pdPiece {M : TopCat} {N : ℕ} (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)))
    {Q : Set (EuclideanSpace ℝ (Fin N))} (hQ : IsOpen Q) : IsOpen (pdPiece e Q) := by
  rw [pdPiece, Set.inter_comm]
  exact e.isOpen_inter_preimage hQ

/-- The intersection of two pieces is the piece of the intersection. -/
theorem pdPiece_inter {M : TopCat} {N : ℕ} (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)))
    (a Q : Set (EuclideanSpace ℝ (Fin N))) : pdPiece e a ∩ pdPiece e Q = pdPiece e (Q ∩ a) := by
  ext y
  constructor
  · rintro ⟨⟨h1, h3⟩, ⟨h2, -⟩⟩
    exact ⟨⟨h2, h1⟩, h3⟩
  · rintro ⟨⟨h2, h1⟩, h3⟩
    exact ⟨⟨h1, h3⟩, ⟨h2, h3⟩⟩

/-- **The union of the pieces of a list of open sets.** -/
def pdUnion {M : TopCat} {N : ℕ} (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N))) :
    List (Set (EuclideanSpace ℝ (Fin N))) → Set M
  | [] => ∅
  | Q :: l => pdPiece e Q ∪ pdUnion e l

@[simp] theorem pdUnion_nil {M : TopCat} {N : ℕ}
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N))) : pdUnion e [] = ∅ := rfl

@[simp] theorem pdUnion_cons {M : TopCat} {N : ℕ}
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)))
    (Q : Set (EuclideanSpace ℝ (Fin N))) (l : List (Set (EuclideanSpace ℝ (Fin N)))) :
    pdUnion e (Q :: l) = pdPiece e Q ∪ pdUnion e l := rfl

/-- A union of pieces over a list is open. -/
theorem isOpen_pdUnion {M : TopCat} {N : ℕ}
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N))) :
    ∀ (l : List (Set (EuclideanSpace ℝ (Fin N)))), (∀ Q ∈ l, IsOpen Q) → IsOpen (pdUnion e l)
  | [], _ => isOpen_empty
  | Q :: l, h => (isOpen_pdPiece e (h Q List.mem_cons_self)).union
      (isOpen_pdUnion e l (fun Q' hQ' => h Q' (List.mem_cons_of_mem _ hQ')))

/-- **The intersection of a piece with a union of pieces is a union of pieces.** -/
theorem pdPiece_inter_pdUnion {M : TopCat} {N : ℕ}
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)))
    (a : Set (EuclideanSpace ℝ (Fin N))) :
    ∀ (l : List (Set (EuclideanSpace ℝ (Fin N)))),
      pdPiece e a ∩ pdUnion e l = pdUnion e (l.map fun Q => Q ∩ a)
  | [] => by simp
  | Q :: l => by
      show pdPiece e a ∩ (pdPiece e Q ∪ pdUnion e l)
        = pdPiece e (Q ∩ a) ∪ pdUnion e (l.map fun Q => Q ∩ a)
      rw [Set.inter_union_distrib_left, pdPiece_inter, pdPiece_inter_pdUnion]

/-- The union of pieces over a list is the union over the list's members. -/
theorem pdUnion_eq_iUnion {M : TopCat} {N : ℕ}
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N))) :
    ∀ (l : List (Set (EuclideanSpace ℝ (Fin N)))),
      pdUnion e l = ⋃ Q ∈ l, pdPiece e Q
  | [] => by simp
  | Q :: l => by
      rw [pdUnion_cons, pdUnion_eq_iUnion e l]
      ext y
      simp only [Set.mem_union, Set.mem_iUnion, List.mem_cons]
      constructor
      · rintro (hy | ⟨Q', hQ', hy⟩)
        · exact ⟨Q, Or.inl rfl, hy⟩
        · exact ⟨Q', Or.inr hQ', hy⟩
      · rintro ⟨Q', hQ' | hQ', hy⟩
        · exact Or.inl (by rwa [show Q' = Q from hQ'] at hy)
        · exact Or.inr ⟨Q', hQ', hy⟩

/-- The union of pieces over a `Finset`. -/
theorem pdUnion_toList {M : TopCat} {N : ℕ}
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)))
    (s : Finset (Set (EuclideanSpace ℝ (Fin N)))) :
    pdUnion e s.toList = ⋃ Q ∈ s, pdPiece e Q := by
  rw [pdUnion_eq_iUnion]
  congr 1
  ext Q
  simp only [Finset.mem_toList]

/-- The preimage of a union of open sets, intersected with the chart source, is the union of the
pieces. -/
theorem pdPiece_iUnion_inter {M : TopCat} {N : ℕ}
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)))
    (s : Finset (Set (EuclideanSpace ℝ (Fin N)))) :
    (e ⁻¹' (⋃ Q ∈ s, Q)) ∩ e.source = ⋃ Q ∈ s, pdPiece e Q := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, pdPiece]
  constructor
  · rintro ⟨⟨Q, hQ, hy⟩, hys⟩
    exact ⟨Q, hQ, hy, hys⟩
  · rintro ⟨Q, hQ, hy, hys⟩
    exact ⟨⟨Q, hQ, hy⟩, hys⟩

/-- **Transport of `Good` along a change of the openness proof.** -/
theorem good_of_open_eq {M : TopCat} [T2Space M] {N : ℕ}
    {c : (singularChains ℤ M).homology N} {W : Set M}
    (h₁ h₂ : IsOpen W) (h : Good N c W h₁) : Good N c W h₂ := by
  rw [Subsingleton.elim h₁ h₂] at h
  exact h

/-- **Transport of `Good` along an equality of open sets.** -/
theorem good_of_set_eq {M : TopCat} [T2Space M] {N : ℕ}
    {c : (singularChains ℤ M).homology N} {W W' : Set M} (h : W = W')
    (hW : IsOpen W) (hW' : IsOpen W') (hg : Good N c W hW) : Good N c W' hW' := by
  have hcast : Good N c W' (h ▸ hW) := h ▸ hg
  exact good_of_open_eq _ _ hcast

/-- **`Good` holds for a single piece**, whether or not the piece is empty. -/
theorem good_piece {M : TopCat} [CompactSpace M] [T2Space M] {N : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (hN : 1 ≤ N) (cc : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ cc
    Metric.ball (e cc) r ⊆ e.target →
    Work.Cohomology.Good N c (∅ : Set M) isOpen_empty →
    (Q : Set (EuclideanSpace ℝ (Fin N))) → (hQopen : IsOpen Q) → (hQconv : Convex ℝ Q) →
      (hQsub : Q ⊆ Metric.ball (e cc) r) →
    Work.Cohomology.Good N c (pdPiece e Q) (isOpen_pdPiece e hQopen) := by
  intro e hball hempty Q hQopen hQconv hQsub
  rcases Q.eq_empty_or_nonempty with rfl | hne
  · have hEq : pdPiece e (∅ : Set (EuclideanSpace ℝ (Fin N))) = (∅ : Set M) := by
      rw [pdPiece, Set.preimage_empty, Set.empty_inter]
    exact good_of_set_eq hEq.symm isOpen_empty (isOpen_pdPiece e hQopen) hempty
  · exact pd_good_convex N hN M c hc cc r hr hball Q hQopen hQconv hne hQsub
      (isOpen_pdPiece e hQopen)

/-- **`Good` for a finite union of convex coordinate pieces.**

The gluing step is the hypothesis `glue`; `Work.Cohomology.pd_good_union` provides it. -/
theorem pd_good_list_pieces {M : TopCat} [CompactSpace M] [T2Space M] {N : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (hN : 1 ≤ N) (cc : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ cc
    Metric.ball (e cc) r ⊆ e.target →
    (∀ {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V)),
        Good N c U hU → Good N c V hV → Good N c (U ∩ V) hI →
        Good N c (U ∪ V) (hU.union hV)) →
    Good N c (∅ : Set M) isOpen_empty →
    (l : List (Set (EuclideanSpace ℝ (Fin N)))) →
    (hl : ∀ Q ∈ l, IsOpen Q ∧ Convex ℝ Q ∧ Q ⊆ Metric.ball (e cc) r) →
    Good N c (pdUnion e l) (isOpen_pdUnion e l (fun Q hQ => (hl Q hQ).1)) := by
  intro e hball glue hempty
  have main : ∀ (n : ℕ) (l : List (Set (EuclideanSpace ℝ (Fin N)))), l.length = n →
      (hl : ∀ Q ∈ l, IsOpen Q ∧ Convex ℝ Q ∧ Q ⊆ Metric.ball (e cc) r) →
      Good N c (pdUnion e l) (isOpen_pdUnion e l (fun Q hQ => (hl Q hQ).1)) := by
    intro n
    induction n with
    | zero =>
        intro l hlen hl
        have hl_nil : l = [] := List.eq_nil_of_length_eq_zero hlen
        subst hl_nil
        exact good_of_open_eq _ _ hempty
    | succ n ih =>
        intro l hlen hl
        cases l with
        | nil => exact good_of_open_eq _ _ hempty
        | cons a t =>
            have htlen : t.length = n := by
              simp only [List.length_cons] at hlen
              omega
            have haopen : IsOpen (pdPiece e a) :=
              isOpen_pdPiece e (hl a List.mem_cons_self).1
            have htopen : IsOpen (pdUnion e t) :=
              isOpen_pdUnion e t (fun Q hQ => (hl Q (List.mem_cons_of_mem _ hQ)).1)
            have himg : ∀ Q ∈ t.map (fun Q => Q ∩ a),
                IsOpen Q ∧ Convex ℝ Q ∧ Q ⊆ Metric.ball (e cc) r := by
              intro Q hQ
              obtain ⟨Q₀, hQ₀, rfl⟩ := List.mem_map.mp hQ
              have h1 := hl Q₀ (List.mem_cons_of_mem _ hQ₀)
              have h2 := hl a List.mem_cons_self
              exact ⟨h1.1.inter h2.1, h1.2.1.inter h2.2.1,
                Set.inter_subset_right.trans h2.2.2⟩
            have hmapgood : Good N c (pdUnion e (t.map (fun Q => Q ∩ a)))
                (isOpen_pdUnion e _ (fun Q hQ => (himg Q hQ).1)) :=
              ih (t.map (fun Q => Q ∩ a)) (by rw [List.length_map, htlen]) himg
            have hgood : Good N c (pdPiece e a ∪ pdUnion e t) (haopen.union htopen) :=
              glue haopen htopen
                (by rw [pdPiece_inter_pdUnion]
                    exact isOpen_pdUnion e _ (fun Q hQ => (himg Q hQ).1))
                (good_piece c hc hN cc r hr hball hempty a (hl a List.mem_cons_self).1
                  (hl a List.mem_cons_self).2.1 (hl a List.mem_cons_self).2.2)
                (good_of_open_eq _ _
                  (ih t htlen (fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ))))
                (good_of_set_eq (pdPiece_inter_pdUnion e a t).symm
                  (isOpen_pdUnion e _ (fun Q hQ => (himg Q hQ).1))
                  (haopen.inter htopen) hmapgood)
            exact good_of_open_eq _ _ hgood
  intro l hl
  exact main l.length l rfl hl

end

end Work.Cohomology
