import Mathlib
import Submission.Work.Diff.EXT.evolX.ladderAtoms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the ladder atoms

The object of the target theorem is the atom

`Atom g W m l N s κ ξ F = fun y => ∇^m Rm (y) (tuple)`, where `tuple` is the tuple whose slot `s`
carries the level-`l` curvature vector `Zf g W l (F ∘ ξ)` and whose remaining slots carry the entries
`F (κ i)`.

Two facts give its smoothness:

* `Work.Diff.EXT.tensProp_all` (`Submission/Work/Diff/EXT/curvNormK_frame_indep.lean`): the tower
  `∇^k Rm` is `C^∞` on every tuple of smooth fields;
* `smTf_Zf` below: the curvature vector `Zf g W l Ψ = ∑ i, (ckt g l (snoc Ψ (W i))) • W i` is
  smooth for smooth `Ψ` and a smooth frame field `W` — it is a finite sum of products of the smooth
  scalar function `ckt g l (snoc Ψ (W i))` with the smooth field `W i`.

`smTf_Zf` is the statement of the parallel obligation `Work.Diff.EXT.evolX.atomZf_smooth` (a sibling
file of this directory); it is proved here directly so that this module does not depend on that file.
-/

namespace Work.Diff.EXT.evolX

/-- **The level-`l` curvature vector `Zf` is smooth in smooth data.**  Unfolding `Zf`, the field is
`∑ i, (ckt g l (Fin.snoc Ψ (W i))) • W i`: a finite sum of products `f • W` of the smooth scalar
function `ckt g l (Fin.snoc Ψ (W i))` with the smooth field `W i`.  The tuple `Fin.snoc Ψ (W i)` is
smooth in every slot: its `castSucc` slots are the entries of `Ψ` and its last slot is `W i`. -/
theorem smTf_Zf
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (W i))
    (l : ℕ) (Ψ : Fin (l + 3) → Work.Diff.EXT.TField (I := I) (M := M))
    (hΨ : ∀ r, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (Ψ r)) :
    Work.Diff.EXT.evolX.SmTf (I := I) (M := M)
      (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Ψ) := by
  -- every slot of the tuple `Fin.snoc Ψ (W i)` is a smooth field
  have hsnoc : ∀ i : Fin (Module.finrank ℝ E),
      ∀ r : Fin (l + 4), Work.Diff.EXT.SmoothF (I := I) (M := M)
        ((Fin.snoc Ψ (W i) : Fin (l + 4) →
          Work.Diff.EXT.TField (I := I) (M := M)) r) := by
    intro i r
    rcases Fin.eq_castSucc_or_eq_last r with ⟨r', rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc]
      exact hΨ r'
    · simp only [Fin.snoc_last]
      exact hW i
  -- the sum of the terms is smooth
  have hsum : Work.Diff.EXT.SmoothF (I := I) (M := M)
      (fun y : M => Finset.univ.sum (fun i : Fin (Module.finrank ℝ E) =>
        (Work.Diff.EXT.ckt (I := I) (M := M) g l (Fin.snoc Ψ (W i)) y) • W i y)) := by
    refine ContMDiff.sum_section
      (t := fun (i : Fin (Module.finrank ℝ E)) (y : M) =>
        (Work.Diff.EXT.ckt (I := I) (M := M) g l (Fin.snoc Ψ (W i)) y) • W i y)
      (s := Finset.univ) ?_
    intro i _
    exact ((Work.Diff.EXT.tensProp_all (I := I) (M := M) hLC g l (Fin.snoc Ψ (W i))
      (hsnoc i)).1).smul_section (hW i)
  exact hsum

theorem atomSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (W i))
    (m l N : ℕ) (s : Fin (m + 4))
    (κ : Fin (m + 4) → Fin N) (ξ : Fin (l + 3) → Fin N)
    (F : Fin N → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ u, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (F u)) :
    Work.Diff.GE.SmoothFunT (I := I) (M := M)
      (Work.Diff.EXT.evolX.Atom (I := I) (M := M) g W m l N s κ ξ F) := by
  -- every slot of the tuple on which the level-`m` tower is evaluated is a smooth field
  have htuple : ∀ i : Fin (m + 4),
      Work.Diff.EXT.SmoothF (I := I) (M := M)
        (if i = s then
          Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l (fun r => F (ξ r))
        else F (κ i)) := by
    intro i
    by_cases hi : i = s
    · rw [if_pos hi]
      exact smTf_Zf (I := I) (M := M) hLC g W hW l (fun r => F (ξ r)) (fun r => hF (ξ r))
    · rw [if_neg hi]
      exact hF (κ i)
  exact (Work.Diff.EXT.tensProp_all (I := I) (M := M) hLC g m
    (fun i : Fin (m + 4) => if i = s then
      Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l (fun r => F (ξ r)) else F (κ i)) htuple).1

end Work.Diff.EXT.evolX
