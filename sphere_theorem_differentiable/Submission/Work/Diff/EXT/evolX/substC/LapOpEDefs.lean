import Mathlib
import Submission.Work.Diff.EXT.evolX.lapCommAuxDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The frame-insertion tuple of the jet-level Laplacian identity (CLASH-FREE COPY `C`)

This is a copy of `Submission/Work/Diff/EXT/evolX/lapOpEDefs.lean` in which every declaration is
renamed with a trailing `C`, so that it can live in the same environment as
`Submission/Work/Diff/EXT/evolX/substB/Defs.lean` (whose `SOp` clashes with the original).

`Work.Diff.EXT.jetAll g j (m+4) (Work.Diff.EXT.lapOpE Ef g m) G` is the `j`-th jet of the
frame-traced rough Laplacian of the tower.  The computation of this jet (the lemma
`Work.Diff.EXT.evolX.lapOpE_jetAll`) needs the *intermediate* operators in which the frame fields
have travelled from the two leading slots of `lapOpE` to the positions `j, j+1` of the tuple.

This module only collects the tuple-manipulation definitions:

* `Work.Diff.EXT.evolX.insT m n A B F` — the tuple
  `(F_0, …, F_{n-1}, A, B, F_n, …, F_{m+3+n})` of arity `(m+2+n)+4`.  For `A = B = Ef i` and `F = G`
  this is the tuple `Work.Diff.EXT.evolX.tupIns m n Ef G i` on which the `n`-th jet of the
  frame-traced tower is evaluated (the `n` differentiation directions first, then the two frame
  slots, then the remaining entries of `G`).

* `Work.Diff.EXT.evolX.SOp g m n Ef` — the frame-traced tower operator with the frame in the slots
  `n, n+1` of its own tuple:
  `F ↦ ∑ i, ckt g (m+2+n) (insTC m n (Ef i) (Ef i) F)`.
  Thus `SOpC g m 0 Ef` is (definitionally) the operator `Work.Diff.EXT.lapOpE Ef g m` whose jet is
  computed, and `SOpC g m n Ef` is the "already differentiated `n` times" form which the induction
  reaches: the point of the identity is that one `extStep` moves `SOpC g m n` to `SOpC g m (n+1)`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The tuple `(F_0, …, F_{n-1}, A, B, F_n, …, F_{m+3+n})`, of arity `(m+2+n)+4`. -/
noncomputable def insTC (m n : ℕ) (A B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Fin ((m + 2 + n) + 4) → Work.Diff.EXT.TField (I := I) (M := M) :=
  fun r => Fin.append (fun t : Fin n => F ⟨t.val, by omega⟩)
      (Fin.cons A (Fin.cons B (fun t : Fin (m + 4) => F ⟨n + t.val, by omega⟩)))
      (Fin.cast (by omega) r)

theorem insT_apply_ltC {m n : ℕ} (A B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (r : Fin ((m + 2 + n) + 4)) (hr : (r : ℕ) < n) :
    insTC (I := I) (M := M) m n A B F r = F ⟨r.val, by omega⟩ := by
  have hcast : (Fin.cast (show (m + 2 + n) + 4 = n + (m + 4 + 2) by omega) r :
      Fin (n + (m + 4 + 2))) = Fin.castAdd (m + 4 + 2) ⟨r.val, hr⟩ :=
    Fin.ext (by simp)
  simp only [insTC, hcast, Fin.append_left]

theorem insT_apply_leftC {m n : ℕ} (A B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M)) :
    insTC (I := I) (M := M) m n A B F ⟨n, by omega⟩ = A := by
  have hcast : (Fin.cast (show (m + 2 + n) + 4 = n + (m + 4 + 2) by omega)
        ⟨n, by omega⟩ : Fin (n + (m + 4 + 2))) = Fin.natAdd n ⟨0, by omega⟩ :=
    Fin.ext (by simp)
  simp only [insTC, hcast, Fin.append_right]
  rw [show (⟨0, by omega⟩ : Fin (m + 4 + 2)) = 0 from Fin.ext rfl, Fin.cons_zero]

theorem insT_apply_rightC {m n : ℕ} (A B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M)) :
    insTC (I := I) (M := M) m n A B F ⟨n + 1, by omega⟩ = B := by
  have hcast : (Fin.cast (show (m + 2 + n) + 4 = n + (m + 4 + 2) by omega)
        ⟨n + 1, by omega⟩ : Fin (n + (m + 4 + 2))) = Fin.natAdd n ⟨1, by omega⟩ :=
    Fin.ext (by simp)
  simp only [insTC, hcast, Fin.append_right]
  rw [show (⟨1, by omega⟩ : Fin (m + 4 + 2)) = Fin.succ 0 from Fin.ext rfl,
    Fin.cons_succ, Fin.cons_zero]

theorem insT_apply_geC {m n : ℕ} (A B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (r : Fin ((m + 2 + n) + 4)) (hr : n + 2 ≤ (r : ℕ)) :
    insTC (I := I) (M := M) m n A B F r = F ⟨r.val - 2, by omega⟩ := by
  have hcast : (Fin.cast (show (m + 2 + n) + 4 = n + (m + 4 + 2) by omega) r :
      Fin (n + (m + 4 + 2))) = Fin.natAdd n ⟨r.val - n, by omega⟩ :=
    Fin.ext (by simp; omega)
  have hidx : (⟨r.val - n, by omega⟩ : Fin (m + 4 + 2))
      = Fin.succ (Fin.succ ⟨r.val - n - 2, by omega⟩) :=
    Fin.ext (by simp; omega)
  rw [insTC, hcast, Fin.append_right, hidx, Fin.cons_succ, Fin.cons_succ]
  refine congrArg F (Fin.ext ?_)
  simp only [Fin.val_mk]
  omega

/-- The update lemma, case `s < n`. -/
theorem insT_update_of_ltC {m n : ℕ} (A B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (s : Fin (m + 4 + n)) (hs : (s : ℕ) < n)
    (W : Work.Diff.EXT.TField (I := I) (M := M)) :
    Function.update (insTC (I := I) (M := M) m n A B F) ⟨(s : ℕ), by omega⟩ W
      = insTC (I := I) (M := M) m n A B (Function.update F s W) := by
  funext r
  rw [Function.update_apply]
  by_cases hr : (r : ℕ) < n
  · rw [insT_apply_ltC (A := A) (B := B) (F := F) (r := r) hr,
      insT_apply_ltC (A := A) (B := B) (F := Function.update F s W) (r := r) hr,
      Function.update_apply]
    by_cases h : (r : ℕ) = (s : ℕ)
    · rw [if_pos (Fin.ext h), if_pos (Fin.ext h.symm).symm]
    · rw [if_neg (fun hh => h (congrArg Fin.val hh)),
        if_neg (fun hh => h (congrArg Fin.val hh))]
  · have hrne : r ≠ (⟨(s : ℕ), by omega⟩ : Fin ((m + 2 + n) + 4)) := by
      intro hh
      have h' : (r : ℕ) = (s : ℕ) := by simpa only [Fin.val_mk] using congrArg Fin.val hh
      omega
    rw [if_neg hrne]
    by_cases h1 : (r : ℕ) = n
    · rw [show r = (⟨n, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h1,
        insT_apply_leftC (A := A) (B := B) (F := F),
        insT_apply_leftC (A := A) (B := B) (F := Function.update F s W)]
    · by_cases h2 : (r : ℕ) = n + 1
      · rw [show r = (⟨n + 1, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h2,
          insT_apply_rightC (A := A) (B := B) (F := F),
          insT_apply_rightC (A := A) (B := B) (F := Function.update F s W)]
      · rw [show r = (⟨r.val, by omega⟩ : Fin ((m + 2 + n) + 4)) from rfl,
          insT_apply_geC (A := A) (B := B) (F := F) (r := r) (by omega),
          insT_apply_geC (A := A) (B := B) (F := Function.update F s W) (r := r) (by omega),
          Function.update_apply]
        have hne : (⟨r.val - 2, by omega⟩ : Fin (m + 4 + n)) ≠ s := by
          intro hh
          have h' : (r : ℕ) - 2 = (s : ℕ) := by
            simpa only [Fin.val_mk] using congrArg Fin.val hh
          omega
        rw [if_neg hne]

/-- The update lemma, case `n ≤ s`. -/
theorem insT_update_of_geC {m n : ℕ} (A B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (s : Fin (m + 4 + n)) (hs : n ≤ (s : ℕ))
    (W : Work.Diff.EXT.TField (I := I) (M := M)) :
    Function.update (insTC (I := I) (M := M) m n A B F) ⟨(s : ℕ) + 2, by omega⟩ W
      = insTC (I := I) (M := M) m n A B (Function.update F s W) := by
  funext r
  rw [Function.update_apply]
  by_cases hr : (r : ℕ) < n
  · have hrne : r ≠ (⟨(s : ℕ) + 2, by omega⟩ : Fin ((m + 2 + n) + 4)) := by
      intro hh
      have h' : (r : ℕ) = (s : ℕ) + 2 := by
        simpa only [Fin.val_mk] using congrArg Fin.val hh
      omega
    rw [if_neg hrne,
      insT_apply_ltC (A := A) (B := B) (F := F) (r := r) hr,
      insT_apply_ltC (A := A) (B := B) (F := Function.update F s W) (r := r) hr,
      Function.update_apply]
    have hne : (⟨r.val, by omega⟩ : Fin (m + 4 + n)) ≠ s := by
      intro hh
      have h' : (r : ℕ) = (s : ℕ) := by simpa only [Fin.val_mk] using congrArg Fin.val hh
      omega
    rw [if_neg hne]
  · by_cases h1 : (r : ℕ) = n
    · have hrne : r ≠ (⟨(s : ℕ) + 2, by omega⟩ : Fin ((m + 2 + n) + 4)) := by
        intro hh
        have h' : (r : ℕ) = (s : ℕ) + 2 := by
          simpa only [Fin.val_mk] using congrArg Fin.val hh
        omega
      rw [if_neg hrne,
        show r = (⟨n, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h1,
        insT_apply_leftC (A := A) (B := B) (F := F),
        insT_apply_leftC (A := A) (B := B) (F := Function.update F s W)]
    · by_cases h2 : (r : ℕ) = n + 1
      · have hrne : r ≠ (⟨(s : ℕ) + 2, by omega⟩ : Fin ((m + 2 + n) + 4)) := by
          intro hh
          have h' : (r : ℕ) = (s : ℕ) + 2 := by
            simpa only [Fin.val_mk] using congrArg Fin.val hh
          omega
        rw [if_neg hrne,
          show r = (⟨n + 1, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h2,
          insT_apply_rightC (A := A) (B := B) (F := F),
          insT_apply_rightC (A := A) (B := B) (F := Function.update F s W)]
      · rw [insT_apply_geC (A := A) (B := B) (F := F) (r := r) (by omega),
          insT_apply_geC (A := A) (B := B) (F := Function.update F s W) (r := r) (by omega),
          Function.update_apply]
        by_cases h : (r : ℕ) = (s : ℕ) + 2
        · rw [if_pos (Fin.ext h)]
          have hss : (⟨r.val - 2, by omega⟩ : Fin (m + 4 + n)) = s := by
            refine Fin.ext ?_
            simp only [Fin.val_mk]
            omega
          rw [if_pos hss]
        · rw [if_neg (fun hh => h (congrArg Fin.val hh)),
            if_neg (fun hh => ?_)]
          have h' : (r : ℕ) - 2 = (s : ℕ) := by simpa only [Fin.val_mk] using congrArg Fin.val hh
          omega

/-- **The frame-traced tower with the frame in the slots `n, n+1`.**
`SOpC g m n Ef F = ∑ i, ckt g (m+2+n) (insTC m n (Ef i) (Ef i) F)`.  `SOpC g m 0` is the operator
`lapOpE Ef g m` whose `j`-th jet (`j`-fold `extStep`) is the object of the identity. -/
noncomputable def SOpC (g : Submission.Diff.SMet I M) (m n : ℕ)
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)) :
    (Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ :=
  fun F y => ∑ i, Work.Diff.EXT.ckt g (m + 2 + n)
    (insTC (I := I) (M := M) m n (Ef i) (Ef i) F) y

end Work.Diff.EXT.evolX
