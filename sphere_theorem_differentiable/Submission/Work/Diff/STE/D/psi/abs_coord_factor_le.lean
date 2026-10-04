import Mathlib
import Submission.Work.Diff.STE.D.psi.JetAffine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.D.psi

theorem abs_coord_factor_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (a : Fin (Module.finrank ℝ E)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i,
      ∀ j : Fin (Module.finrank ℝ E),
        |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
          (D.e i a (D.pt i y))| ≤ B := by
  classical
  -- The frame field `e i a` is a smooth section, hence its chart coordinates are continuous.
  have hZ : Work.Diff.GE.SmoothField M (D.e i a) := D.hesm i a
  have hcd : ∀ j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun Y : E =>
        Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i)
          ((extChartAt I (D.x₀ i)).symm Y) j (D.e i a ((extChartAt I (D.x₀ i)).symm Y)))
        (extChartAt I (D.x₀ i)).target :=
    fun j =>
      (Work.Diff.STE.D.psi.contDiffOn_coordCLM_symm (I := I) (M := M) (D.x₀ i) hZ j).continuousOn
  have hK : IsCompact (Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i) :=
    Work.Diff.STE.D.psi.isCompact_Ky (I := I) (M := M) D i
  have hflat : Continuous (Work.Diff.STE.flatToE (I := I) (D.x₀ i)) :=
    (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ i)).continuous
  -- The vector of all chart coordinates is continuous on the compact region `Ky D i`.
  have hcomp : ContinuousOn (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      fun j : Fin (Module.finrank ℝ E) =>
        Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
          (D.e i a (D.pt i y)))
      (Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i) :=
    continuousOn_pi.2 fun j =>
      (hcd j).comp hflat.continuousOn
        (fun y hy =>
          Work.Diff.STE.D.psi.flatToE_mem_target_of_mem_Ky (I := I) (M := M) D hy)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcomp
  refine ⟨max 0 C, le_max_left 0 C, fun y hy j => ?_⟩
  have h1 : ‖(fun j : Fin (Module.finrank ℝ E) =>
      Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
        (D.e i a (D.pt i y)))‖ ≤ C := hC y hy
  calc |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
          (D.e i a (D.pt i y))|
      = ‖Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
          (D.e i a (D.pt i y))‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖(fun j : Fin (Module.finrank ℝ E) =>
          Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
            (D.e i a (D.pt i y)))‖ :=
        norm_le_pi_norm (fun j : Fin (Module.finrank ℝ E) =>
          Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
            (D.e i a (D.pt i y))) j
    _ ≤ C := h1
    _ ≤ max 0 C := le_max_right 0 C

end Work.Diff.STE.D.psi
