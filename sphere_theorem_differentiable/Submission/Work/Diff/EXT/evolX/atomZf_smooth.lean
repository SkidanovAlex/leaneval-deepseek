import Mathlib
import Submission.Work.Diff.EXT.evolX.ladderAtoms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evolX

theorem atomZf_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (W i))
    (l : ℕ) (Ψ : Fin (l + 3) → Work.Diff.EXT.TField (I := I) (M := M))
    (hΨ : ∀ r, Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (Ψ r)) :
    Work.Diff.EXT.evolX.SmTf (I := I) (M := M) (Work.Diff.EXT.evolX.Zf (I := I) (M := M) g W l Ψ) := by
  -- `Zf g W l Ψ = ∑ i, (ckt g l (snoc Ψ (W i))) • W i` is a finite sum of products of a smooth
  -- scalar function with a smooth field
  refine ContMDiff.sum_section (s := Finset.univ)
    (t := fun (i : Fin (Module.finrank ℝ E)) (y : M) =>
      (Work.Diff.EXT.ckt g l (Fin.snoc Ψ (W i)) y) • W i y) ?_
  intro i _
  exact ((Work.Diff.EXT.tensProp_all hLC g l (Fin.snoc Ψ (W i))
    (fun r => by
      rcases Fin.eq_castSucc_or_eq_last r with ⟨r', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]; exact hΨ r'
      · rw [Fin.snoc_last]; exact hW i)).1).smul_section (hW i)

end Work.Diff.EXT.evolX
