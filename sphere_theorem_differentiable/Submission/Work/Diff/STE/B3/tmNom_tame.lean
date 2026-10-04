import Mathlib
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_jet_data
import Submission.Work.Diff.STE.B3.tmGK_eq_Gf
import Submission.Work.Diff.STE.B3.tmNom_aux
import Submission.Work.Diff.STE.B3.pdR_Gf_eq_tmDGK

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators Matrix ContDiff
open LeanEval.Geometry.SphereTheorem

namespace Work.Diff.STE.B3

theorem tmNom_tame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (j : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j)
    (af bf : Fin (Module.finrank ℝ E)) :
    (Matrix.of (Work.Diff.STE.B3.tmGK (I := I) (M := M) D j z (fun a b => D.mat j h a b z))
        = Matrix.of (fun i k => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k))
    ∧ (Work.Diff.STE.B3.tmDGKclm (I := I) (M := M) D j z (fun a b => D.mat j h a b z)
          (fun a b r => Work.Diff.STE.pdR r (D.mat j h a b) z)
        = (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
            (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).2.1)
    ∧ (∀ c d : Fin (Module.finrank ℝ E),
        Work.Diff.STE.B3.tmEight (I := I) (M := M) D j z (fun a b => D.mat j h a b z)
            (fun a b r => Work.Diff.STE.pdR r (D.mat j h a b) z) c d af bf
          = Work.Diff.STE.B3.eightTerm (I := I) (M := M) D h j z c d af bf) := by
  classical
  have hzt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target :=
    D.htarget j z hz
  have hdet : (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0 :=
    det_Ff_ne_zero (I := I) (M := M) D j hz
  -- the frame-change identity and its two entrywise consequences
  have hGK1 : Matrix.of (tmGK (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z))
      = Matrix.of (Gf (I := I) (M := M) D h j z) :=
    tmGK_eq_Gf (I := I) (M := M) D h j z hzt hdet
  have hGK : ∀ i k : Fin (Module.finrank ℝ E),
      tmGK (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z) i k
        = Gf (I := I) (M := M) D h j z i k := by
    intro i k
    exact congrFun (congrFun hGK1 i) k
  have hDGK : ∀ (c : Fin (Module.finrank ℝ E)) (i k : Fin (Module.finrank ℝ E)),
      tmDGK (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z)
          (fun a b r => Work.Diff.STE.pdR r
            (fun y => Mf (I := I) (M := M) D h j y a b) z) c i k
        = Work.Diff.STE.pdR c (fun y => Gf (I := I) (M := M) D h j y i k) z :=
    fun c i k => (pdR_Gf_eq_tmDGK (I := I) (M := M) D h hsmooth j hz c i k).symm
  refine ⟨?_, ?_, ?_⟩
  · -- (1) the nominal coordinate chart matrix is the honest one
    show Matrix.of (tmGK (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z))
        = Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k)
    ext i k
    simp only [Matrix.of_apply]
    exact hGK i k
  · -- (2) the nominal first jet is the first jet of the chart jet of `h`
    show tmDGKclm (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z)
        (fun a b r => Work.Diff.STE.pdR r
          (fun y => Mf (I := I) (M := M) D h j y a b) z)
        = (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
            (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).2.1
    -- every continuous linear map is its canonical-basis data
    have hclm := tmNom_clm_eq_sum_coord_smulRight (E := E)
      (L := (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
        (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).2.1)
    have hbase : tmDGKclm (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z)
        (fun a b r => Work.Diff.STE.pdR r
          (fun y => Mf (I := I) (M := M) D h j y a b) z)
        = ∑ c, (((Work.Diff.EXT.bB (E := E)).coord c).toContinuousLinearMap).smulRight
            (Matrix.of (fun i k => tmDGK (I := I) (M := M) D j z
              (Mf (I := I) (M := M) D h j z)
              (fun a b r => Work.Diff.STE.pdR r
                (fun y => Mf (I := I) (M := M) D h j y a b) z) c i k)) := rfl
    rw [hbase, ← hclm]
    refine Finset.sum_congr rfl (fun c _ => congrArg
      (fun X : Work.Diff.EXT.MatE (E := E) =>
        (((Work.Diff.EXT.bB (E := E)).coord c).toContinuousLinearMap).smulRight X) ?_)
    ext i k
    rw [(Work.Diff.STE.B3.transport_jet_data (I := I) (M := M) D h hsmooth j hz).2.1 c i k]
    exact hDGK c i k
  · -- (3) the nominal eight-term correction is the honest one
    intro c d
    show tmEight (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z)
        (fun a b r => Work.Diff.STE.pdR r
          (fun y => Mf (I := I) (M := M) D h j y a b) z) c d af bf
      = eightTerm (I := I) (M := M) D h j z c d af bf
    simp only [tmEight, eightTerm, hGK, hDGK]

end Work.Diff.STE.B3
