import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_convex_base
import Submission.Work.Cohomology.good_empty
import Submission.Work.Cohomology.pd_good_list_pieces

set_option synthInstance.maxHeartbeats 400000

/-!
# `PdGoodListPiecesChart` — import shim of the ISLANDS2 subproject

This file used to declare a **duplicate copy** of the module

* `Submission.Work.Cohomology.pd_good_list_pieces`

(the declarations were verbatim copies: same names, same statements, same proofs).  The duplicate
made the two copies mutually unimportable — Lean refuses an environment that contains two
declarations with the same name — so the copies could not meet in the final assembly
(`Submission/Work/Islands2/AllCritical.lean`).

The ISLANDS2 subproject has removed the duplicate: this module is now a thin **shim** that simply
imports the original, so every name it used to export is still available under exactly the same
name and with exactly the same statement.  Nothing else changed; no consumer needs to be updated.
See `Submission/Work/Islands2/README.md` for the full inventory of duplicates.
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

theorem pd_good_list_pieces_chart' {M : TopCat} [CompactSpace M] [T2Space M] {N : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (hN : 1 ≤ N) (cc : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ cc
    Metric.ball (e cc) r ⊆ e.target →
    (∀ {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V)),
        U ∩ V ⊆ e.source →
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
                (fun x hx => Set.inter_subset_right (Set.inter_subset_left hx))
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
