import Mathlib
import Submission.Work.Diff.EXT.evolX.substB.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pointwise identification of `substOp` with the pairing operator `SOp`

This module proves `Work.Diff.EXT.evolX.substOp_eq_SOp_comp`: the contracted tower
`substOp g k s V F` (the level-`k` tower `∇^k Rm` with its slot `s` filled by the value of the
vector-valued operator `V`) agrees, near a point where the frame `W` is `g`-orthonormal, with the
*metric pairing* `SOp g V (Zsk g W k s)` of the frame-expanded curvature vector `Zsk g W k s` with
the value of `V`, evaluated on the relabelled tuple `F ∘ brho`.

The proof is the pairing identity of `Zsk` (`Work.Diff.EXT.evolX.ZskPair`) applied at each point of
a neighbourhood of `x` — the neighbourhood on which the frame stays orthonormal
(`Work.Diff.EXT.evolX.eventually_ONFrameAt`).  Two `Fin`-bookkeepings are needed:

* `brho k s (Fin.castAdd 2 i) = upos k s i` (`aux_brho_castAdd`): the `U`-side tuple of the pairing
  is the tuple of the tower slots different from `s`;
* `Fin.succAbove s (skipMap k s j) = j` for `j ≠ s` (`aux_succAbove_skipMap`): inserting the value
  of `V` at the slot `s` of the `skipMap`-relabelled tuple is inserting it into the `succ`-shifted
  tuple of `substOp`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The two `Fin`-bookkeepings -/

/-- The value of `Fin.succAbove`. -/
lemma aux_succAbove_val {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    (p.succAbove i).val = if (i : ℕ) < (p : ℕ) then (i : ℕ) else (i : ℕ) + 1 := by
  rw [Fin.succAbove]
  by_cases h : (i : ℕ) < (p : ℕ)
  · rw [if_pos (by simp only [Fin.lt_def, Fin.val_castSucc]; exact h), if_pos h]
    rfl
  · rw [if_neg (by simp only [Fin.lt_def, Fin.val_castSucc]; omega), if_neg h]
    rfl

/-- The value of `skipMap`. -/
lemma aux_skipMap_val (k : ℕ) (s : Fin (k + 4)) (i : Fin (k + 4)) :
    (skipMap k s i : ℕ) = if (i : ℕ) < (s : ℕ) then (i : ℕ) else (i : ℕ) - 1 := by
  unfold skipMap
  split_ifs <;> rfl

/-- **`skipMap` is a right inverse of `succAbove`**: the `skipMap`-relabelled tuple is the
`succ`-shifted tuple away from the slot `s`. -/
lemma aux_succAbove_skipMap (k : ℕ) (s : Fin (k + 4)) (j : Fin (k + 4)) (hj : j ≠ s) :
    Fin.succAbove s (skipMap k s j) = j := by
  apply Fin.ext
  by_cases h1 : (j : ℕ) < (s : ℕ)
  · have hsk : skipMap k s j = (⟨(j : ℕ), by omega⟩ : Fin (k + 3)) := by
      apply Fin.ext; rw [aux_skipMap_val, if_pos h1]
    rw [hsk, aux_succAbove_val, if_pos h1]
  · have hjlt := j.isLt
    have hsk : skipMap k s j = (⟨(j : ℕ) - 1, by omega⟩ : Fin (k + 3)) := by
      apply Fin.ext; rw [aux_skipMap_val, if_neg h1]
    rw [hsk, aux_succAbove_val]
    simp only [Fin.val_mk]
    rw [if_neg (by omega : ¬ ((j : ℕ) - 1 < (s : ℕ)))]
    omega

/-- **`brho` on the `U`-part of the block** is `upos`. -/
lemma aux_brho_castAdd (k : ℕ) (s : Fin (k + 4)) (i : Fin (k + 3)) :
    brho k s (Fin.castAdd 2 i) = upos k s i := by
  have h : (⟨(i : ℕ), by have := i.isLt; omega⟩ : Fin (k + 5)) = Fin.castAdd 2 i := by
    apply Fin.ext; simp
  rw [← h, stb_brho_apply_upos]

/-! ## The pointwise identification -/

/-- **`substOp` is the pairing with the curvature vector `Zsk`.**  At a point `y` where the frame
`W` is `g`-orthonormal, the pairing of the frame-expanded curvature vector `Zsk g W k s` with the
value of `V` (on the tuple relabelled by `brho`) is the contracted tower `substOp g k s V F` at
`y`. -/
theorem substOp_eq_SOp_pointwise
    (g : Submission.Diff.SMet I M) (y : M) (k : ℕ) (s : Fin (k + 4))
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (W i))
    (hy : ONFrameAt (I := I) (M := M) g y W)
    (F : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    SOp (I := I) (M := M) g V (Zsk (I := I) (M := M) g W k s)
        (fun i : Fin (k + 5) => F (brho k s i)) y
      = substOp (I := I) (M := M) g k s V F y := by
  have hW' : ∀ i, SmTf (I := I) (M := M) (W i) := fun i => hW i
  -- the value of `V` on the `V`-side tuple of `SOp`
  have key0 : (fun t : Fin 2 => (fun j : Fin (k + 5) => F (brho k s j))
        (Fin.natAdd (k + 3) t))
      = Fin.cons (F 0) (Fin.cons (F s.succ) (Fin.elim0)) := by
    funext t
    fin_cases t
    · show F (brho k s (Fin.natAdd (k + 3) (0 : Fin 2))) = F 0
      rw [show Fin.natAdd (k + 3) (0 : Fin 2) = (⟨k + 3, by omega⟩ : Fin (k + 5)) from
        Fin.ext rfl, stb_brho_apply_last1]
      rfl
    · show F (brho k s (Fin.natAdd (k + 3) (1 : Fin 2))) = F s.succ
      rw [show Fin.natAdd (k + 3) (1 : Fin 2) = (⟨k + 4, by omega⟩ : Fin (k + 5)) from
        Fin.ext rfl, stb_brho_apply_last2]
      rfl
  -- the `U`-side tuple of `SOp`
  have key1 : (fun i : Fin (k + 3) => (fun j : Fin (k + 5) => F (brho k s j))
        (Fin.castAdd 2 i))
      = fun i : Fin (k + 3) => F (upos k s i) := by
    funext i
    exact congrArg F (aux_brho_castAdd k s i)
  -- the smooth extension of the value of `V`
  set D : Work.Diff.EXT.TField (I := I) (M := M) :=
    Submission.Diff.smoothExt y (V (Fin.cons (F 0) (Fin.cons (F s.succ) Fin.elim0)) y)
    with hDdef
  have hDsm : SmTf (I := I) (M := M) D := by
    rw [hDdef]; exact Work.Diff.GE.smoothExt_cmdiff y _
  have hDval : D y = V (Fin.cons (F 0) (Fin.cons (F s.succ) Fin.elim0)) y := by
    rw [hDdef]; exact Work.Diff.GE.smoothExt_apply y _
  have hΨsm : ∀ r : Fin (k + 3), SmTf (I := I) (M := M) (F (upos k s r)) := fun r => hF _
  have hzp := ZskPair (I := I) (M := M) g y W hW' hy k s
    (fun i : Fin (k + 3) => F (upos k s i)) hΨsm D hDsm
  -- the relabelled tuple of `ZskPair` is the `succ`-shifted tuple of `substOp`
  have hupd : Function.update (fun j : Fin (k + 4) => F (upos k s (skipMap k s j))) s D
      = Function.update (fun i : Fin (k + 4) => F i.succ) s D := by
    funext i
    by_cases hi : i = s
    · subst hi; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
      show F ((Fin.succAbove s (skipMap k s i)).succ) = F i.succ
      rw [aux_succAbove_skipMap k s i hi]
  have hLHS : SOp (I := I) (M := M) g V (Zsk (I := I) (M := M) g W k s)
        (fun i : Fin (k + 5) => F (brho k s i)) y
      = g.inner y (Zsk (I := I) (M := M) g W k s (fun i : Fin (k + 3) => F (upos k s i)) y)
          (D y) := by
    simp only [SOp, key0, key1, hDval]
  rw [hLHS, hzp, hupd]
  rw [show D = Submission.Diff.smoothExt y
      (V (Fin.cons (F 0) (Fin.cons (F s.succ) Fin.elim0)) y) from hDdef]
  rfl

/-! ## The germ form -/

/-- The main target: `SOp` with the frame-expanded curvature vector equals `substOp` *eventually*
near `x`. -/
theorem substOp_eq_SOp_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M) (k : ℕ) (s : Fin (k + 4))
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (W i))
    (hON : Filter.Eventually (fun y : M =>
        Submission.Diff.IsONFrame g y (fun i => W i y)) (nhds x))
    (F : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    Filter.EventuallyEq (nhds x)
      (fun y : M => Work.Diff.EXT.evolX.SOp (I := I) (M := M) g V
        (Work.Diff.EXT.evolX.Zsk (I := I) (M := M) g W k s)
        (fun i : Fin (k + 5) => F (Work.Diff.EXT.evolX.brho k s i)) y)
      (fun y : M => Work.Diff.EXT.evolX.substOp (I := I) (M := M) g k s V F y) := by
  filter_upwards [eventually_ONFrameAt (I := I) (M := M) g x W hON] with y hy
  exact substOp_eq_SOp_pointwise (I := I) (M := M) g y k s V W hW hy F hF

end Work.Diff.EXT.evolX
