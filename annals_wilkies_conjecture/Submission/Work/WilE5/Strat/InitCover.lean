/-
  WilE5 / Strat — the initial states cover `X`, and the state invariants pass to children.

  An initial state is indexed by a *disjunct* `A ∈ X.basics` of `X` together with a face pattern.
  The disjunct's conditions become the state's own conditions (`Ξ := A.eqs`, `ν ∋ A.pos`) and the
  disjunct's equations become the flatness family (`Φ := A.eqs`); the face equations `y_l = ±1`
  (with the face direction as pivot) go into `B` and the interior inequalities `0 < 1 - y_l^2`
  into `ν`.

  Consequently, for every point `z ∈ X.set` there is an initial state whose set contains `z`,
  *and* whose disjunct is one that holds at `z` — the data the flat-leaf correctness
  (`Strat.flatStratum_good`) needs in order to conclude `z' ∈ X.set` for points `z'` of the
  fibre that remain on the level set of the state's equations.
-/
import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.Wilkies.E.Spec

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology
namespace Work.WilE5.Strat
open WilkiesDesign WilkiesDesign.E

variable {p q r M NΦ : ℕ}

/-- Every point of `X.set` belongs to the set of an initial state, and the disjunct of that
initial state holds at the point: pick a disjunct `A` of `X` that holds at `z` (it exists since
`z ∈ X.set`), take the face pattern of `z` (`|z_l| = 1` on the faces) with the matching sign
pattern `ε`, and read off the definition of `initSt`. -/
theorem exists_initSt_mem {p q : ℕ} (X : SemiPf (p + q)) {z : Fin (p + q) → ℝ}
    (hz : z ∈ X.set) :
    ∃ σ ∈ initStates X, ∃ A ∈ X.basics,
      (∀ f ∈ A.eqs, f ∈ (stCond σ).eqs) ∧ (∀ g ∈ A.pos, g ∈ (stCond σ).pos) ∧
      (∀ f ∈ A.eqs, f ∈ σ.Φ) ∧ z ∈ (stSemiPf X σ).set := by
  classical
  have hzc : z ∈ cubeC (p + q) := hz.1
  obtain ⟨A, hA, hAholds⟩ := hz.2
  -- the face pattern of `z`: the fibre directions where `z` hits the boundary of the cube
  set Fy : Finset (Fin q) :=
    Finset.univ.filter (fun l => z (yDir p l) = 1 ∨ z (yDir p l) = -1) with hFy
  have hmem_Fy : ∀ l : Fin q,
      l ∈ Fy ↔ z (yDir p l) = 1 ∨ z (yDir p l) = -1 := by
    intro l; rw [hFy]; simp
  -- the matching sign pattern
  have hex : ∀ l : {l // l ∈ Fy}, ∃ s : Bool,
      z (yDir p l.1) = if s then (1 : ℝ) else -1 := by
    intro l
    rcases (hmem_Fy l.1).mp l.2 with h | h
    · exact ⟨true, by rw [h]; simp⟩
    · exact ⟨false, by rw [h]; simp⟩
  let ε : {l // l ∈ Fy} → Bool := fun l => Classical.choose (hex l)
  have hεspec : ∀ l : {l // l ∈ Fy},
      z (yDir p l.1) = if ε l then (1 : ℝ) else -1 := fun l => Classical.choose_spec (hex l)
  -- the strict inequalities for the non-face directions
  have hν : ∀ l : {l // l ∈ Fyᶜ}, 0 < 1 - z (yDir p l.1) ^ 2 := by
    intro l
    have hnot : ¬ (z (yDir p l.1) = 1 ∨ z (yDir p l.1) = -1) := by
      intro hcon
      exact (Finset.mem_compl.mp l.2) ((hmem_Fy l.1).mpr hcon)
    have hle : |z (yDir p l.1)| ≤ 1 := hzc (yDir p l.1)
    have hlt : z (yDir p l.1) < 1 :=
      lt_of_le_of_ne (abs_le.mp hle).2 fun h => hnot (Or.inl h)
    have hgt : -1 < z (yDir p l.1) :=
      lt_of_le_of_ne (abs_le.mp hle).1 fun h => hnot (Or.inr h.symm)
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - z (yDir p l.1))
      (by linarith : (0 : ℝ) < 1 + z (yDir p l.1))]
  refine ⟨initSt X A Fy ε, ?_, A, hA, ?_, ?_, ?_, ?_⟩
  · -- the initial state is one of the enumerated ones
    exact initSt_mem_initStates X A hA Fy ε
  · -- the equations of the disjunct are among the state's equations
    intro f hf
    exact List.mem_append_right _ hf
  · -- the strict positivity conditions of the disjunct are among the state's
    intro g hg
    exact List.mem_append_left _ hg
  · -- the disjunct's equations are the flatness family of the initial state
    intro f hf
    exact hf
  · -- `z` satisfies all the conditions of the initial state
    rw [stSemiPf, semiPfAnd_set]
    refine ⟨hz, ?_⟩
    refine ⟨?_, ?_⟩
    · -- the face equations `y_l ∓ 1` vanish at `z`, and the equations of `A` hold at `z`
      intro f hf
      simp only [stCond, initSt, List.map_map, Function.comp_apply, List.mem_append,
        List.mem_map] at hf
      rcases hf with ⟨l, hl, rfl⟩ | hf
      · rw [facePoly, eaEval_facePoly]
        have hmem : l.1 ∈ Fy := by simpa using hl
        simp [hεspec ⟨l.1, hmem⟩]
      · exact hAholds.1 f hf
    · -- the strict inequalities `1 - y_l^2 > 0` and the inequalities of `A` hold at `z`
      intro g hg
      simp only [stCond, initSt, List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨l, hl, rfl⟩
      · exact hAholds.2 g hg
      · rw [intPoly, eaEval_intPoly]
        have hmem : l.1 ∈ Fyᶜ := by simpa using hl
        exact hν ⟨l.1, hmem⟩

/-- The state invariants pass to a child: every equation and every strict positivity condition of
the parent is one of the child's, and the flatness family grows. -/
theorem child_invariants {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r)
    (t : Test q) (s : Bool) :
    (∀ f ∈ (stCond σ).eqs, f ∈ (stCond (childSt X.c M NΦ σ t s)).eqs) ∧
      (∀ g ∈ (stCond σ).pos, g ∈ (stCond (childSt X.c M NΦ σ t s)).pos) ∧
      (∀ ψ ∈ σ.Φ, ψ ∈ (childSt X.c M NΦ σ t s).Φ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    simp only [stCond, childSt, childB, childΞ, List.map_append, List.mem_append] at hf ⊢
    tauto
  · intro g hg
    simp only [stCond, childSt, childν, List.mem_append] at hg ⊢
    exact Or.inl hg
  · intro ψ hψ
    simp only [childSt, List.mem_append]
    exact Or.inl hψ

end Work.WilE5.Strat
