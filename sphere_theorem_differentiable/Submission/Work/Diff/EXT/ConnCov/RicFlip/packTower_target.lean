import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.TInvDefs
import Submission.Work.Diff.EXT.ConnCov.RicFlip.packTower_val_dep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# From the packed invariants `PInv` to the three conclusions of
`Work.Diff.EXT.ConnCov.RicFlip.towerSlotAddSmValDep`

The target statement asks, for every `k`, for

1. `SlotAdd (tower (lcOf g) base k)`,
2. smoothness of `tower (lcOf g) base k v A B C` on tuples of smooth fields,
3. value dependence of `tower (lcOf g) base k` at every point.

All three are transported from the *packed* invariants `PInv g base k`
(`Work.Diff.EXT.ConnCov.RicFlip.PInv`, `TInvDefs.lean`) along the identification
`tower (lcOf g) base k v A B C = pkTower g base k (mkT3 v (trip3 A B C))` (`pkTower_mkT3`) and the
slot bookkeeping `update_castAdd_mkT3` / `update_natAdd_mkT3` (`ATens/Defs.lean`).

This module takes the two remaining inputs as hypotheses:

* `hAll : ∀ k, PInv g base k` — the induction itself (base case `PInv_zero` + the four steps);
* `hbr : ∀ k F, packTower g base k F = pkTower g base k F` — the bridge proved from the recursion
  `pkTower_succ_rec`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov.RicFlip

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- Updating the first value slot of `trip3 A B C`. -/
theorem update_trip3_zero (A A' B C : Π y : M, TangentSpace I y) :
    Function.update (Work.Diff.EXT.trip3 A B C) (0 : Fin 3) A'
      = Work.Diff.EXT.trip3 A' B C := by
  funext p
  fin_cases p <;> simp [Function.update, Work.Diff.EXT.trip3]

/-- Updating the second value slot of `trip3 A B C`. -/
theorem update_trip3_one (A B B' C : Π y : M, TangentSpace I y) :
    Function.update (Work.Diff.EXT.trip3 A B C) (1 : Fin 3) B'
      = Work.Diff.EXT.trip3 A B' C := by
  funext p
  fin_cases p <;> simp [Function.update, Work.Diff.EXT.trip3]

/-- Updating the third value slot of `trip3 A B C`. -/
theorem update_trip3_two (A B C C' : Π y : M, TangentSpace I y) :
    Function.update (Work.Diff.EXT.trip3 A B C) (2 : Fin 3) C'
      = Work.Diff.EXT.trip3 A B C' := by
  funext p
  fin_cases p <;> simp [Function.update, Work.Diff.EXT.trip3]

/-- The three conclusions of the target, from the packed invariants `PInv` and the bridge
`packTower = pkTower`. -/
theorem tower_conj_of_PInv (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    {base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0}
    (hAll : ∀ k, PInv g base k)
    (hbr : ∀ (k : ℕ) (F : Fin (k + 3) → (Π y : M, TangentSpace I y)),
      packTower g base k F = pkTower g base k F) :
    ∀ k : ℕ,
      Work.Diff.EXT.ATower.SlotAdd (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k) ∧
      (∀ (v : Fin k → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
        (∀ j, Work.Diff.EXT.ATower.SmE I M (v j)) → Work.Diff.EXT.ATower.SmE I M A →
        Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M C →
        Work.Diff.EXT.ATower.SmF I M
          (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k v A B C)) ∧
      (∀ (v v' : Fin k → (Π y : M, TangentSpace I y))
        (A A' B B' C C' : Π y : M, TangentSpace I y) (x : M),
        (∀ j, Work.Diff.EXT.ATower.SmE I M (v j)) →
        (∀ j, Work.Diff.EXT.ATower.SmE I M (v' j)) → (∀ j, v j x = v' j x) →
        Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M A' →
        Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M B' →
        Work.Diff.EXT.ATower.SmE I M C → Work.Diff.EXT.ATower.SmE I M C' →
        A x = A' x → B x = B' x → C x = C' x →
        Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k v A B C x
          = Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k v' A' B' C' x) := by
  intro k
  -- smoothness of the slots of the packed tuple `mkT3 w (trip3 A B C)`
  have hunp : ∀ (w : Fin k → (Π y : M, TangentSpace I y))
      (A B C : Π y : M, TangentSpace I y),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (w i)) →
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M B →
      Work.Diff.EXT.ATower.SmE I M C →
      ∀ s, Work.Diff.EXT.ATower.SmE I M (Work.Diff.EXT.mkT3 w (Work.Diff.EXT.trip3 A B C) s) := by
    intro w A B C hw hA hB hC s
    refine Fin.addCases (motive := fun s => Work.Diff.EXT.ATower.SmE I M
      (Work.Diff.EXT.mkT3 w (Work.Diff.EXT.trip3 A B C) s)) ?_ ?_ s
    · intro i
      rw [Work.Diff.EXT.mkT3_castAdd]
      exact hw i
    · intro p
      rw [Work.Diff.EXT.mkT3_natAdd]
      fin_cases p
      · simpa using hA
      · simpa using hB
      · simpa using hC
  -- **the transports**: the unpacked tower as a packed tower
  have hUnpack : ∀ (v : Fin k → (Π y : M, TangentSpace I y))
      (A B C : Π y : M, TangentSpace I y),
      Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k v A B C
        = packTower g base k (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C)) := by
    intro v A B C
    rw [← pkTower_mkT3, ← hbr k (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))]
  have hDir : ∀ (v : Fin k → (Π y : M, TangentSpace I y)) (i : Fin k)
      (X A B C : Π y : M, TangentSpace I y),
      Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k (Function.update v i X) A B C
        = packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
            (Fin.castAdd 3 i) X) := by
    intro v i X A B C
    rw [hUnpack (Function.update v i X) A B C, ← Work.Diff.EXT.update_castAdd_mkT3]
  have hVal0 : ∀ (v : Fin k → (Π y : M, TangentSpace I y))
      (A B C X : Π y : M, TangentSpace I y),
      Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k v X B C
        = packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
            (Fin.natAdd k (0 : Fin 3)) X) := by
    intro v A B C X
    rw [hUnpack v X B C, Work.Diff.EXT.update_natAdd_mkT3]
    congr 1
    congr 1
    exact (update_trip3_zero A X B C).symm
  have hVal1 : ∀ (v : Fin k → (Π y : M, TangentSpace I y))
      (A B C X : Π y : M, TangentSpace I y),
      Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k v A X C
        = packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
            (Fin.natAdd k (1 : Fin 3)) X) := by
    intro v A B C X
    rw [hUnpack v A X C, Work.Diff.EXT.update_natAdd_mkT3]
    congr 1
    congr 1
    exact (update_trip3_one A B X C).symm
  have hVal2 : ∀ (v : Fin k → (Π y : M, TangentSpace I y))
      (A B C X : Π y : M, TangentSpace I y),
      Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k v A B X
        = packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
            (Fin.natAdd k (2 : Fin 3)) X) := by
    intro v A B C X
    rw [hUnpack v A B X, Work.Diff.EXT.update_natAdd_mkT3]
    congr 1
    congr 1
    exact (update_trip3_two A B C X).symm
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- `SlotAdd`, derivative slot `i`
    intro i v W W' A B C hv hW hW' hA hB hC
    have hF : ∀ s, Work.Diff.EXT.ATower.SmE I M
        (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) s) := hunp v A B C hv hA hB hC
    have hlin := (hAll k (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C)) hF).2.1
      (Fin.castAdd 3 i) W W' (fun _ : M => (1 : ℝ)) (fun _ : M => (1 : ℝ))
      hW hW' (contMDiff_const (c := (1 : ℝ))) (contMDiff_const (c := (1 : ℝ)))
    have e1 : (fun _ : M => (1 : ℝ)) • W + (fun _ : M => (1 : ℝ)) • W' = W + W' := by
      funext y; simp
    have e2 : (fun _ : M => (1 : ℝ))
          • packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.castAdd 3 i) W)
        + (fun _ : M => (1 : ℝ))
          • packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.castAdd 3 i) W')
        = packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.castAdd 3 i) W)
          + packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.castAdd 3 i) W') := by
      funext y; simp
    rw [e1, e2] at hlin
    rw [hDir v i (W + W') A B C, hDir v i W A B C, hDir v i W' A B C]
    exact hlin
  · -- `SlotAdd`, value slot `A`
    intro v A A' B C hv hA hA' hB hC
    have hF : ∀ s, Work.Diff.EXT.ATower.SmE I M
        (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) s) := hunp v A B C hv hA hB hC
    have hlin := (hAll k (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C)) hF).2.1
      (Fin.natAdd k (0 : Fin 3)) A A' (fun _ : M => (1 : ℝ)) (fun _ : M => (1 : ℝ))
      hA hA' (contMDiff_const (c := (1 : ℝ))) (contMDiff_const (c := (1 : ℝ)))
    have e1 : (fun _ : M => (1 : ℝ)) • A + (fun _ : M => (1 : ℝ)) • A' = A + A' := by
      funext y; simp
    have e2 : (fun _ : M => (1 : ℝ))
          • packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.natAdd k (0 : Fin 3)) A)
        + (fun _ : M => (1 : ℝ))
          • packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.natAdd k (0 : Fin 3)) A')
        = packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.natAdd k (0 : Fin 3)) A)
          + packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.natAdd k (0 : Fin 3)) A') := by
      funext y; simp
    rw [e1, e2] at hlin
    rw [hVal0 v A B C (A + A'), hVal0 v A B C A, hVal0 v A B C A']
    exact hlin
  · -- `SlotAdd`, value slot `B`
    intro v A B B' C hv hA hB hB' hC
    have hF : ∀ s, Work.Diff.EXT.ATower.SmE I M
        (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) s) := hunp v A B C hv hA hB hC
    have hlin := (hAll k (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C)) hF).2.1
      (Fin.natAdd k (1 : Fin 3)) B B' (fun _ : M => (1 : ℝ)) (fun _ : M => (1 : ℝ))
      hB hB' (contMDiff_const (c := (1 : ℝ))) (contMDiff_const (c := (1 : ℝ)))
    have e1 : (fun _ : M => (1 : ℝ)) • B + (fun _ : M => (1 : ℝ)) • B' = B + B' := by
      funext y; simp
    have e2 : (fun _ : M => (1 : ℝ))
          • packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.natAdd k (1 : Fin 3)) B)
        + (fun _ : M => (1 : ℝ))
          • packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.natAdd k (1 : Fin 3)) B')
        = packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.natAdd k (1 : Fin 3)) B)
          + packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.natAdd k (1 : Fin 3)) B') := by
      funext y; simp
    rw [e1, e2] at hlin
    rw [hVal1 v A B C (B + B'), hVal1 v A B C B, hVal1 v A B C B']
    exact hlin
  · -- `SlotAdd`, value slot `C`
    intro v A B C C' hv hA hB hC hC'
    have hF : ∀ s, Work.Diff.EXT.ATower.SmE I M
        (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) s) := hunp v A B C hv hA hB hC
    have hlin := (hAll k (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C)) hF).2.1
      (Fin.natAdd k (2 : Fin 3)) C C' (fun _ : M => (1 : ℝ)) (fun _ : M => (1 : ℝ))
      hC hC' (contMDiff_const (c := (1 : ℝ))) (contMDiff_const (c := (1 : ℝ)))
    have e1 : (fun _ : M => (1 : ℝ)) • C + (fun _ : M => (1 : ℝ)) • C' = C + C' := by
      funext y; simp
    have e2 : (fun _ : M => (1 : ℝ))
          • packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.natAdd k (2 : Fin 3)) C)
        + (fun _ : M => (1 : ℝ))
          • packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.natAdd k (2 : Fin 3)) C')
        = packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.natAdd k (2 : Fin 3)) C)
          + packTower g base k (Function.update (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
              (Fin.natAdd k (2 : Fin 3)) C') := by
      funext y; simp
    rw [e1, e2] at hlin
    rw [hVal2 v A B C (C + C'), hVal2 v A B C C, hVal2 v A B C C']
    exact hlin
  · -- smoothness
    intro v A B C hv hA hB hC
    have hF : ∀ s, Work.Diff.EXT.ATower.SmE I M
        (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) s) := hunp v A B C hv hA hB hC
    have hsm := (hAll k (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C)) hF).1
    rw [hUnpack v A B C]
    exact hsm
  · -- value dependence
    intro v v' A A' B B' C C' x hv hv' hvv hA hA' hB hB' hC hC' hAA hBB hCC
    have hF : ∀ s, Work.Diff.EXT.ATower.SmE I M
        (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) s) := hunp v A B C hv hA hB hC
    have hF' : ∀ s, Work.Diff.EXT.ATower.SmE I M
        (Work.Diff.EXT.mkT3 v' (Work.Diff.EXT.trip3 A' B' C') s) := hunp v' A' B' C' hv' hA' hB' hC'
    have hvals : ∀ s, (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C)) s x
        = (Work.Diff.EXT.mkT3 v' (Work.Diff.EXT.trip3 A' B' C')) s x :=
      Work.Diff.EXT.val_mkT3 (k := k) hvv (by
        intro p
        fin_cases p
        · simpa using hAA
        · simpa using hBB
        · simpa using hCC)
    have hmain := packTower_val_dep g base k (hAll k) hF hF' x hvals
    rw [hUnpack v A B C, hUnpack v' A' B' C']
    exact hmain

end Work.Diff.EXT.ConnCov.RicFlip
