import Mathlib

/-!
# The "shrinking balls" tool for a finite family of open dense conditions

The lead's item (f) (`exists_generic_triple`) produces a parameter `t` satisfying a *finite* list of
genericity conditions (`Meet3Hyp`, `GoodPair` for the active pairs, the `s = 1` data), each of which is
*open* and *dense near `0`*.  The purely topological step — "pick them one at a time in shrinking
balls" — is isolated here: a finite family of sets that are open and meet every ball around `0` has a
common point in every ball around `0`.

This avoids the Baire category theorem (which would need completeness and a *countable* intersection):
for finitely many conditions the induction below loses only a factor `1/2` at each step.

All declarations are `sorry`-free and rest on `propext, Classical.choice, Quot.sound`.
-/

namespace Work.Drive

open Filter
open scoped Topology

noncomputable section

/-- **A finite family of open conditions, dense at every point of the unit ball, has a common point in
every ball of radius `≤ 1`.**  The hypothesis is the shape the Sard arguments supply: each condition is
open, and one can move to it from any point of the unit ball. -/
theorem exists_mem_all_of_isOpen_dense {m : ℕ} :
    ∀ (n : ℕ) (P : Fin n → Set (EuclideanSpace ℝ (Fin m))),
      (∀ i, IsOpen (P i)) →
      (∀ i, ∀ x : EuclideanSpace ℝ (Fin m), ‖x‖ ≤ 1 → ∀ ε : ℝ, 0 < ε →
        ∃ y, y ∈ P i ∧ ‖y - x‖ < ε) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ t, ‖t‖ < ε ∧ ∀ i, t ∈ P i := by
  intro n
  induction n with
  | zero =>
      intro P _ _ ε hε _
      exact ⟨0, by simpa using hε, fun i => i.elim0⟩
  | succ n ih =>
      intro P hopen hdense ε hε hε1
      -- first satisfy the conditions `0, …, n-1` (in the same ball)
      obtain ⟨t, ht, htmem⟩ := ih (fun i : Fin n => P i.castSucc)
        (fun i => hopen _) (fun i => hdense _) ε hε hε1
      -- that intersection is open and contains `t`
      have hneigh : (⋂ i : Fin n, P i.castSucc) ∈ 𝓝 t := by
        rw [Filter.iInter_mem]
        exact fun i => (hopen _).mem_nhds (htmem i)
      obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hneigh
      -- move to the last condition inside the shrunken ball
      have ht1 : ‖t‖ ≤ 1 := le_of_lt (lt_of_lt_of_le ht hε1)
      obtain ⟨s, hsmem, hs⟩ := hdense (Fin.last n) t ht1 (min δ (ε - ‖t‖))
        (lt_min hδpos (by linarith))
      have hnorm : ‖s‖ ≤ ‖s - t‖ + ‖t‖ := by
        have := norm_add_le (s - t) t
        rwa [sub_add_cancel] at this
      have hlt : ‖s - t‖ < ε - ‖t‖ := lt_of_lt_of_le hs (min_le_right _ _)
      refine ⟨s, by linarith, fun i => ?_⟩
      refine Fin.lastCases hsmem (fun j => ?_) i
      have hmem : s ∈ ⋂ i : Fin n, P i.castSucc := hδsub (by
        rw [Metric.mem_ball, dist_eq_norm]
        exact lt_of_lt_of_le hs (min_le_left _ _))
      exact Set.mem_iInter.mp hmem j

end

end Work.Drive
