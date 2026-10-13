import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG1.Main
import Submission.Work.WilG1.Stmts
import Submission.Work.WilCrux.SphereChoiceDefs
import Submission.Work.WilCrux.SphereChoiceLift
import Submission.Work.WilCrux.SphereChoicePos
import Submission.Work.WilCrux.SphereChoiceLeTail
import Submission.Work.WilG4c.CoordGraphMem
import Submission.Work.WilG4a.subst_mem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

/-- **N4c3 (definable choice with a radius bound).**  For an `Omega`-definable `E` there is a
definable `ζ` that, whenever some `z` with `0 < ||z|| <= τ` and `(w,z) ∈ E` exists, returns such
a point; the coordinate graphs of `(w,τ) ↦ ζ w τ` are `Omega`-definable with fixed format and
degree polynomial in the input degree `D`.

Proof: apply `WilkiesDesign.CG.G1_choice_proved` to the `Omega`-set
`{(x,z) : 0 < ||z|| <= x_last ∧ append (init x) z ∈ E} ⊆ ℝ^{a+1} × ℝ^b` (the sup-norm
inequalities and `z ≠ 0` are semialgebraic of fixed degree).  The choice function's coordinate
graphs are the `Ω`-definable section sets of `G1_choice_proved`, reindexed so that the `j`-th
coordinate of the fibre block sits last. -/
theorem SphereChoice (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) {a b F D : ℕ}
    (E : Set (Fin (a + b) → ℝ)) (hE : E ∈ S.Ω F D (a + b)) :
    ∃ (ζ : (Fin a → ℝ) → ℝ → (Fin b → ℝ)) (F' : ℕ) (b' : Polynomial ℕ),
      (∀ (w : Fin a → ℝ) (τ : ℝ),
        (∃ z : Fin b → ℝ, 0 < ‖z‖ ∧ ‖z‖ ≤ τ ∧ Fin.append w z ∈ E) →
          0 < ‖ζ w τ‖ ∧ ‖ζ w τ‖ ≤ τ ∧ Fin.append w (ζ w τ) ∈ E) ∧
      (∀ j : Fin b, WilkiesDesign.graphOf (fun x : Fin (a + 1) → ℝ =>
          ζ (fun i : Fin a => x (Fin.castSucc i)) (x (Fin.last a))
            j) ∈ S.Ω F' (b'.eval D) (a + 1 + 1)) := by
  -- The three `Ω`-definable ingredients of the choice set, on `ℝ^{(a+1)+b}`:
  -- the lift of `E` (forgetting the radius coordinate), `z ≠ 0`, and `‖z‖ ≤ τ`.
  set A1 : Set (Fin ((a + 1) + b) → ℝ) :=
    {x | Fin.append (blockW x) (blockZ x) ∈ E} with hA1def
  set A2 : Set (Fin ((a + 1) + b) → ℝ) := {x | 0 < ‖blockZ x‖} with hA2def
  set A3 : Set (Fin ((a + 1) + b) → ℝ) := {x | ‖blockZ x‖ ≤ blockT x} with hA3def
  obtain ⟨Φ1, hΦ1⟩ : ∃ Φ : ℕ, A1 ∈ S.Ω Φ (D + 2) ((a + 1) + b) := by
    refine ⟨F + 2 * (((a + 1) + b) + (a + b)) + 1, ?_⟩
    rw [hA1def]
    exact SphereChoiceLift S E hE
  obtain ⟨Φ2, hΦ2⟩ : ∃ Φ : ℕ, A2 ∈ S.Ω Φ (2 + 2) ((a + 1) + b) := by
    refine ⟨(b + 1) + 2 * (((a + 1) + b) + b) + 1, ?_⟩
    rw [hA2def]
    have h := Work.WilG4a.subst_mem S (Fin.natAdd (a + 1)) (SphereChoicePos S b)
    have hset : {x : Fin ((a + 1) + b) → ℝ |
          x ∘ Fin.natAdd (a + 1) ∈ {z : Fin b → ℝ | 0 < ‖z‖}} =
        {x : Fin ((a + 1) + b) → ℝ | 0 < ‖blockZ x‖} := by
      ext x
      simp only [Set.mem_ofPred_eq, Function.comp_def]
      exact Iff.rfl
    rwa [hset] at h
  obtain ⟨Φ3, hΦ3⟩ : ∃ Φ : ℕ, A3 ∈ S.Ω Φ ((2 * b + 2) + 2) ((a + 1) + b) := by
    refine ⟨(b + 5) + 2 * (((a + 1) + b) + (b + 1)) + 1, ?_⟩
    rw [hA3def]
    have h := Work.WilG4a.subst_mem S (tauZMap a b) (SphereChoiceLeTail S b)
    have hset : {x : Fin ((a + 1) + b) → ℝ |
          x ∘ tauZMap a b ∈ {y : Fin (b + 1) → ℝ | ‖Fin.tail y‖ ≤ y 0}} =
        {x : Fin ((a + 1) + b) → ℝ | ‖blockZ x‖ ≤ blockT x} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      rw [tail_tauZMap, zero_tauZMap]
    rwa [hset] at h
  -- A common format for the three pieces.
  obtain ⟨Φ, hA1', hA2', hA3'⟩ : ∃ Φ : ℕ, A1 ∈ S.Ω Φ (D + 2) ((a + 1) + b) ∧
      A2 ∈ S.Ω Φ 4 ((a + 1) + b) ∧ A3 ∈ S.Ω Φ ((2 * b + 2) + 2) ((a + 1) + b) :=
    ⟨max (max Φ1 Φ2) Φ3,
      Work.WilG4a.mem_mono hΦ1 (le_trans (le_max_left _ _) (le_max_left _ _)) le_rfl,
      Work.WilG4a.mem_mono hΦ2 (le_trans (le_max_right _ _) (le_max_left _ _))
        (by omega),
      Work.WilG4a.mem_mono hΦ3 (le_max_right _ _) le_rfl⟩
  -- Their intersection is the choice set, with degree `D + K`.
  set K : ℕ := 2 + (4 + ((2 * b + 2) + 2)) with hKdef
  have hXeq : A1 ∩ (A2 ∩ A3) = sphereSet E := by
    rw [hA1def, hA2def, hA3def, sphereSet]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  obtain ⟨Φ', hX⟩ : ∃ Φ' : ℕ, sphereSet E ∈ S.Ω Φ' (D + K) ((a + 1) + b) :=
    ⟨_, hXeq ▸ Work.WilG4a.mem_mono
      (Work.WilG1.Choice.pair_mem hA1' (Work.WilG1.Choice.pair_mem hA2' hA3'))
      le_rfl (by omega)⟩
  -- Effective choice on the choice set.
  obtain ⟨a', b'c, hchoice⟩ := WilkiesDesign.CG.G1_choice_proved S hcd Φ' (a + 1) b
  obtain ⟨f, hsel, hgset⟩ := hchoice (D + K) (sphereSet E) hX
  -- The coordinate graphs of the chosen section.
  obtain ⟨A, B, hAB⟩ := Work.WilG4c.CoordGraphMem S (a + 1) b
  have hgraphs : ∀ j : Fin b, WilkiesDesign.graphOf (fun l : Fin (a + 1) → ℝ => f l j) ∈
      S.Ω (a' + A) ((b'c + B).eval (D + K)) ((a + 1) + 1) :=
    fun j => hAB (D + K) a' b'c f hgset j
  refine ⟨fun w τ => f (Fin.snoc w τ), a' + A,
    (b'c + B).comp (Polynomial.X + Polynomial.C K), ?_, ?_⟩
  · -- The choice guarantees the three selection conditions at `ζ w τ = f (snoc w τ)`.
    intro w τ hw
    obtain ⟨z, hz1, hz2, hz3⟩ := hw
    have hmem : Fin.append (Fin.snoc w τ) z ∈ sphereSet E := by
      rw [mem_sphereSet, blockW_append, blockT_append, blockZ_append]
      exact ⟨hz1, hz2, hz3⟩
    have hsel' := hsel (Fin.snoc w τ) ⟨z, hmem⟩
    rw [mem_sphereSet, blockW_append, blockT_append, blockZ_append] at hsel'
    simpa using hsel'
  · -- Each coordinate graph is `Ω`-definable, with the degree polynomial composed with `K`.
    intro j
    have hmem := hgraphs j
    have hEq : WilkiesDesign.graphOf (fun x : Fin (a + 1) → ℝ =>
        (fun w τ => f (Fin.snoc w τ)) (fun i : Fin a => x (Fin.castSucc i))
          (x (Fin.last a)) j)
        = WilkiesDesign.graphOf (fun l : Fin (a + 1) → ℝ => f l j) := by
      congr 1
      funext l
      exact congrArg (fun u => f u j) (Fin.snoc_init_self l)
    rw [hEq]
    have hdeg : ((b'c + B).comp (Polynomial.X + Polynomial.C K)).eval D
        = (b'c + B).eval (D + K) := by
      rw [Polynomial.eval_comp]
      congr 1
      rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rw [hdeg]
    exact hmem

end Work.WilCrux
