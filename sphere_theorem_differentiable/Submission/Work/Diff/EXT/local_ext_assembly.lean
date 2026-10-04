import Mathlib
import Submission.Work.Diff.EXT.local_ext_of_bounded_curv
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

theorem local_ext_assembly
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M))
    (hmet : ∀ (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ), 0 < T → Submission.Diff.IsRicciFlow G T →
      (∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C) → 0 ≤ C →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
        (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
        (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hconv : ∀ (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ), 0 < T → Submission.Diff.IsRicciFlow G T →
      (∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C) → 0 ≤ C →
      (∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
        (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
        (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u) →
      Work.Diff.EXT.ChartBounds (I := I) (M := M) G (T / 2) T ∧
        ∃ a : ℝ, 0 < a ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (x : M) (u : TangentSpace I x),
          a * (G 0).inner x u u ≤ (G t).inner x u u)
    (hext : ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), 0 < T → Submission.Diff.IsRicciFlow G T →
      Work.Diff.EXT.ChartBounds (I := I) (M := M) G (T / 2) T →
      (∃ a : ℝ, 0 < a ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (x : M) (u : TangentSpace I x),
          a * (G 0).inner x u u ≤ (G t).inner x u u) →
      ∃ δ > 0, ∃ H₁ : ℝ → Submission.Diff.SMet I M,
        Submission.Diff.JointSmooth H₁ (Set.Ioo (T - δ) (T + δ)) ∧
          ∀ t ∈ Set.Ico (T - δ) T, H₁ t = G t)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C) :
    ∃ δ > 0, ∃ H₁ : ℝ → Submission.Diff.SMet I M,
      Submission.Diff.JointSmooth H₁ (Set.Ioo (T - δ) (T + δ)) ∧
        ∀ t ∈ Set.Ico (T - δ) T, H₁ t = G t := by
  -- `CurvBound` is monotone in the bound, so replacing `C` by `max C 0` costs nothing: this
  -- makes the constant nonnegative, which is what the two inputs `hmet`/`hconv` require.
  have hbound' : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) (max C 0) :=
    fun t ht x e he i j k l => le_trans (hbound t ht x e he i j k l) (le_max_left C 0)
  exact Work.Diff.EXT.local_ext_of_bounded_curv_of_inputs hShi hmet hconv hext G T (max C 0) hT
    (le_max_right C 0) hflow hbound'

end Work.Diff.EXT
