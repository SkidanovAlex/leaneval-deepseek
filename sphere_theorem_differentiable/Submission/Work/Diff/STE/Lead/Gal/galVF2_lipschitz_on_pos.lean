import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.Lead.Gal.Span
import Submission.Work.Diff.STE.Lead.Gal.SpanLin
import Submission.Work.Diff.STE.Lead.Gal.SpanBridge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.Gal

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSectionVars false

theorem galVF2_lipschitz_on_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (hLC : Submission.Diff.LCSmooth I M)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner))
    (ε : ℝ) (hε : 0 < ε)
    (c₀ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < (D.J ρ ε (Submission.Diff.STEGal.galState D ε c₀)) x v v) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ c ∈ Metric.closedBall c₀ δ, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (Submission.Diff.STEGal.galState D ε c)) x v v) ∧
      ∃ L : NNReal, LipschitzOnWith L
        (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0)
        (Metric.closedBall c₀ δ) := by
  classical
  -- the Lipschitz bound for the coefficient map of the foreground
  obtain ⟨C, hC0, hClip⟩ := Fcoef_lipschitz (I := I) (M := M) hg D ρ ε
  let hCnn : NNReal := ⟨C, hC0⟩
  -- the base section `a₀ = genMap D ε e₀` and its basic properties
  set e₀ : Coef ι₀ (Module.finrank ℝ E) ε := Fcoef D ρ ε c₀ with he₀
  set a₀ : Work.Diff.STE.Bil (I := I) (M := M) :=
    Work.Diff.STE.D.genMap (I := I) (M := M) D ε e₀ with ha₀
  have hchart_a₀ : Work.Diff.STE.D.ChartData (I := I) (M := M) a₀ :=
    Work.Diff.STE.D.ChartData_genMap (I := I) (M := M) D ε e₀
  have hsym_a₀ : Work.Diff.STE.D.IsSymm (I := I) a₀ :=
    Work.Diff.STE.D.isSymm_genMap (I := I) (M := M) D ε e₀
  have hpos_a₀ : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < a₀ x v v := by
    intro x v hv
    have hEq : a₀ = D.J ρ ε (Submission.Diff.STEGal.galState D ε c₀) := by
      rw [ha₀, he₀]
      simpa only [Fcoef] using
        (Work.Diff.STE.Lead.J_eq_genMap_galCoeff (I := I) (M := M) D ρ ε hε hρ0
          (Submission.Diff.STEGal.galState D ε c₀)
          (Work.Diff.STE.Lead.isSymm_galState (I := I) (M := M) D ε c₀)).symm
    rw [hEq]
    exact hpos x v hv
  -- the positivity ball around the base
  obtain ⟨δp, hδp, hball⟩ :=
    Work.Diff.STE.D.BasePos.exists_isPosF_ball (I := I) (M := M) D ε a₀ hchart_a₀ hpos_a₀
  -- the base-generalised concrete field is `C¹` at `0`
  have hC1 : ContDiffAt ℝ 1
      (Work.Diff.STE.D.Base.psiConcB (I := I) (M := M) a₀ D ρ ε) 0 :=
    Work.Diff.STE.D.Base.contDiffAt_psiConcB (I := I) (M := M) D ε hg a₀ hchart_a₀ hsym_a₀
      ⟨δp, hδp, hball⟩ ρ
  obtain ⟨K, t, ht, hKt⟩ := hC1.exists_lipschitzOnWith
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := Metric.mem_nhds_iff.mp ht
  have hLip₀ : LipschitzOnWith K (Work.Diff.STE.D.Base.psiConcB (I := I) (M := M) a₀ D ρ ε)
      (Metric.closedBall 0 (δ₀ / 2)) :=
    hKt.mono (fun x hx => hδ₀sub (by
      rw [Metric.mem_ball, dist_zero_right]
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      linarith))
  -- the affine shift `G c = Fcoef c - e₀`
  set G : Coef ι₀ (Module.finrank ℝ E) ε → Coef ι₀ (Module.finrank ℝ E) ε :=
    fun c => Fcoef D ρ ε c - e₀ with hG
  have hG0 : G c₀ = 0 := by
    simp only [hG, he₀, sub_self]
  have hGlip : ∀ c c' : Coef ι₀ (Module.finrank ℝ E) ε, ‖G c - G c'‖ ≤ C * ‖c - c'‖ := by
    intro c c'
    have : G c - G c' = Fcoef D ρ ε c - Fcoef D ρ ε c' := by
      simp only [hG]
      abel
    rw [this]
    exact hClip c c'
  -- the radius
  refine ⟨min 1 (min (δp / (2 * (C + 1))) ((δ₀ / 2) / (2 * (C + 1)))), ?_, ?_, ?_⟩
  · refine lt_min one_pos (lt_min ?_ ?_)
    · exact div_pos hδp (by linarith)
    · exact div_pos (by linarith) (by linarith)
  · -- positivity on the ball
    intro c hc x v hv
    rw [Metric.mem_closedBall, dist_eq_norm] at hc
    have hdle : ‖c - c₀‖ ≤ min 1 (min (δp / (2 * (C + 1))) ((δ₀ / 2) / (2 * (C + 1)))) := hc
    have hGc : ‖G c‖ < δp := by
      have h1 : ‖G c‖ = ‖G c - G c₀‖ := by rw [hG0, sub_zero]
      have h2 : ‖G c - G c₀‖ ≤ C * ‖c - c₀‖ := hGlip c c₀
      have h3 : C * ‖c - c₀‖ ≤ C * (δp / (2 * (C + 1))) :=
        mul_le_mul_of_nonneg_left (le_trans hdle (le_trans (min_le_right _ _) (min_le_left _ _))) hC0
      have h4 : C * (δp / (2 * (C + 1))) < δp := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (C + 1))]
        nlinarith [hδp, hC0]
      linarith
    exact (isPosF_iff_spanPos (I := I) (M := M) D ρ ε hε hρ0 e₀ c).mp
      (hball (G c) hGc) x v hv
  · -- Lipschitz on the ball
    refine ⟨K * hCnn, ?_⟩
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro c hc c' hc'
    rw [Metric.mem_closedBall, dist_eq_norm] at hc hc'
    -- the pointwise identity on the ball
    have hid : ∀ c ∈ Metric.closedBall c₀
        (min 1 (min (δp / (2 * (C + 1))) ((δ₀ / 2) / (2 * (C + 1))))),
        Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 c
          = Work.Diff.STE.D.Base.psiConcB (I := I) (M := M) a₀ D ρ ε (G c) := by
      intro c hc
      rw [Metric.mem_closedBall, dist_eq_norm] at hc
      have hGc : ‖G c‖ < δp := by
        have h1 : ‖G c‖ = ‖G c - G c₀‖ := by rw [hG0, sub_zero]
        have h2 : ‖G c - G c₀‖ ≤ C * ‖c - c₀‖ := hGlip c c₀
        have h3 : C * ‖c - c₀‖ ≤ C * (δp / (2 * (C + 1))) :=
          mul_le_mul_of_nonneg_left (le_trans hc (le_trans (min_le_right _ _) (min_le_left _ _))) hC0
        have h4 : C * (δp / (2 * (C + 1))) < δp := by
          rw [mul_div_assoc']
          rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (C + 1))]
          nlinarith [hδp, hC0]
        linarith
      have hposc : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
          0 < (D.J ρ ε (Submission.Diff.STEGal.galState D ε c)) x v v :=
        fun x v hv => (isPosF_iff_spanPos (I := I) (M := M) D ρ ε hε hρ0 e₀ c).mp
          (hball (G c) hGc) x v hv
      rw [galVF2_eq_psiConcB (I := I) (M := M) hLC D ρ ε hε hρ0 e₀ c hposc]
    rw [hid c hc, hid c' hc']
    -- the Lipschitz bounds
    have hGc : G c ∈ Metric.closedBall (0 : Coef ι₀ (Module.finrank ℝ E) ε) (δ₀ / 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖G c‖ = ‖G c - G c₀‖ := by rw [hG0, sub_zero]
      have h2 : ‖G c - G c₀‖ ≤ C * ‖c - c₀‖ := hGlip c c₀
      have h3 : C * ‖c - c₀‖ ≤ C * ((δ₀ / 2) / (2 * (C + 1))) :=
        mul_le_mul_of_nonneg_left (le_trans hc (le_trans (min_le_right _ _) (min_le_right _ _))) hC0
      have h4 : C * ((δ₀ / 2) / (2 * (C + 1))) < δ₀ / 2 := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (C + 1))]
        nlinarith [hδ₀pos, hC0]
      linarith
    have hGc' : G c' ∈ Metric.closedBall (0 : Coef ι₀ (Module.finrank ℝ E) ε) (δ₀ / 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖G c'‖ = ‖G c' - G c₀‖ := by rw [hG0, sub_zero]
      have h2 : ‖G c' - G c₀‖ ≤ C * ‖c' - c₀‖ := hGlip c' c₀
      have h3 : C * ‖c' - c₀‖ ≤ C * ((δ₀ / 2) / (2 * (C + 1))) :=
        mul_le_mul_of_nonneg_left (le_trans hc' (le_trans (min_le_right _ _) (min_le_right _ _))) hC0
      have h4 : C * ((δ₀ / 2) / (2 * (C + 1))) < δ₀ / 2 := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (C + 1))]
        nlinarith [hδ₀pos, hC0]
      linarith
    have h1 : ‖Work.Diff.STE.D.Base.psiConcB (I := I) (M := M) a₀ D ρ ε (G c)
        - Work.Diff.STE.D.Base.psiConcB (I := I) (M := M) a₀ D ρ ε (G c')‖
        ≤ (K : ℝ) * ‖G c - G c'‖ := by
      have h := hLip₀.dist_le_mul (G c) hGc (G c') hGc'
      simpa only [dist_eq_norm] using h
    have h2 : ‖G c - G c'‖ ≤ C * ‖c - c'‖ := hGlip c c'
    calc ‖Work.Diff.STE.D.Base.psiConcB (I := I) (M := M) a₀ D ρ ε (G c)
          - Work.Diff.STE.D.Base.psiConcB (I := I) (M := M) a₀ D ρ ε (G c')‖
        ≤ (K : ℝ) * ‖G c - G c'‖ := h1
      _ ≤ (K : ℝ) * (C * ‖c - c'‖) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ((K * hCnn : NNReal) : ℝ) * ‖c - c'‖ := by
          have hcoe : ((K * hCnn : NNReal) : ℝ) = (K : ℝ) * C := by
            rw [NNReal.coe_mul]
            congr 1
          rw [hcoe]
          ring

end Work.Diff.STE.Lead.Gal
