import Mathlib
import Submission.Work.Diff.EXT.commBoundDefs
import Submission.Work.Diff.EXT.evolK_bridges
import Submission.Work.Diff.GE.swap_defs
import Submission.Work.Diff.GE.swap_curvsection
import Submission.Work.Diff.EXT.Kpt_norm_bound
import Submission.Work.Diff.GE.covLapRm_sub_lapCovRm_summand_bound
import Submission.Work.Diff.GE.EvolB.NrmBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- The vector field `dCurvV cov Z U₁ U₂ U` — written out by the Leibniz rule as
`∇_Z(R(U₁,U₂)U) − R(∇_Z U₁,U₂)U − R(U₁,∇_Z U₂)U − R(U₁,U₂)∇_Z U` — is the covariant derivative
`(∇_Z Rm)(U₁,U₂)U` of the curvature tensor, i.e. the frozen object `Work.Diff.GE.curvDeriv`. -/
theorem dCurvV_eq_curvDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (Z U1 U2 U : Work.Diff.EXT.TField (I := I) (M := M))
    (hZ : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Z)
    (hU1 : Work.Diff.GE.SmoothFieldT (I := I) (M := M) U1)
    (hU2 : Work.Diff.GE.SmoothFieldT (I := I) (M := M) U2)
    (hU : Work.Diff.GE.SmoothFieldT (I := I) (M := M) U) :
    Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g) Z U1 U2 U x
      = Work.Diff.GE.curvDeriv g x (Z x) (U1 x) (U2 x) (U x) := by
  have h := Work.Diff.GE.covAlong_curv_fields (I := I) (M := M) hLC g x
    (Xs := Z) (Ys := U1) (Ps := U2) (As := U) hZ hU1 hU2 hU
  simp only [Work.Diff.EXT.dCurvV]
  rw [h]
  abel

theorem dCurvV_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (Z U1 U2 U : Work.Diff.EXT.TField (I := I) (M := M))
    (hZ : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Z)
    (hU1 : Work.Diff.GE.SmoothFieldT (I := I) (M := M) U1)
    (hU2 : Work.Diff.GE.SmoothFieldT (I := I) (M := M) U2)
    (hU : Work.Diff.GE.SmoothFieldT (I := I) (M := M) U) :
    Real.sqrt (g.inner x (Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g) Z U1 U2 U x)
        (Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g) Z U1 U2 U x))
      ≤ (Real.sqrt ((Module.finrank ℝ E : ℕ) : ℝ) + 1) * Real.sqrt (Work.Diff.EXT.curvNormK g x 1)
        * (Real.sqrt (g.inner x (Z x) (Z x)) * Real.sqrt (g.inner x (U1 x) (U1 x))
           * Real.sqrt (g.inner x (U2 x) (U2 x)) * Real.sqrt (g.inner x (U x) (U x))) := by
  rw [dCurvV_eq_curvDeriv hLC g x Z U1 U2 U hZ hU1 hU2 hU]
  -- `curvDeriv_nrm_le_B`: `‖(∇_Z Rm)(U₁,U₂)U‖ ≤ √|∇Rm|² · ‖Z‖‖U₁‖‖U₂‖‖U‖`.
  have hb := Work.Diff.GE.EvolB.curvDeriv_nrm_le_B (I := I) (M := M) hLC g x
    (Z x) (U1 x) (U2 x) (U x)
  have hb2 : Real.sqrt (g.inner x (Work.Diff.GE.curvDeriv g x (Z x) (U1 x) (U2 x) (U x))
        (Work.Diff.GE.curvDeriv g x (Z x) (U1 x) (U2 x) (U x)))
      ≤ Real.sqrt (Work.Diff.EXT.curvNormK g x 1)
        * (Real.sqrt (g.inner x (Z x) (Z x)) * Real.sqrt (g.inner x (U1 x) (U1 x))
           * Real.sqrt (g.inner x (U2 x) (U2 x)) * Real.sqrt (g.inner x (U x) (U x))) := by
    rw [Work.Diff.EXT.curvNormK_one_eq_dRmNormSq]
    simp only [Work.Diff.GE.EvolB.nrm] at hb ⊢
    exact hb.trans_eq (by ring)
  refine le_trans hb2 ?_
  have hf : (1 : ℝ) ≤ Real.sqrt ((Module.finrank ℝ E : ℕ) : ℝ) + 1 := by
    have := Real.sqrt_nonneg ((Module.finrank ℝ E : ℕ) : ℝ)
    linarith
  have hprod : 0 ≤ Real.sqrt (g.inner x (Z x) (Z x)) * Real.sqrt (g.inner x (U1 x) (U1 x))
      * Real.sqrt (g.inner x (U2 x) (U2 x)) * Real.sqrt (g.inner x (U x) (U x)) := by positivity
  have hstep : Real.sqrt (Work.Diff.EXT.curvNormK g x 1)
        * (Real.sqrt (g.inner x (Z x) (Z x)) * Real.sqrt (g.inner x (U1 x) (U1 x))
           * Real.sqrt (g.inner x (U2 x) (U2 x)) * Real.sqrt (g.inner x (U x) (U x)))
      ≤ (Real.sqrt ((Module.finrank ℝ E : ℕ) : ℝ) + 1)
          * Real.sqrt (Work.Diff.EXT.curvNormK g x 1)
        * (Real.sqrt (g.inner x (Z x) (Z x)) * Real.sqrt (g.inner x (U1 x) (U1 x))
           * Real.sqrt (g.inner x (U2 x) (U2 x)) * Real.sqrt (g.inner x (U x) (U x))) := by
    have h := mul_le_mul_of_nonneg_right hf
      (mul_nonneg (Real.sqrt_nonneg (Work.Diff.EXT.curvNormK g x 1)) hprod)
    have he : (Real.sqrt ((Module.finrank ℝ E : ℕ) : ℝ) + 1)
          * (Real.sqrt (Work.Diff.EXT.curvNormK g x 1)
            * (Real.sqrt (g.inner x (Z x) (Z x)) * Real.sqrt (g.inner x (U1 x) (U1 x))
               * Real.sqrt (g.inner x (U2 x) (U2 x)) * Real.sqrt (g.inner x (U x) (U x))))
        = (Real.sqrt ((Module.finrank ℝ E : ℕ) : ℝ) + 1)
            * Real.sqrt (Work.Diff.EXT.curvNormK g x 1)
          * (Real.sqrt (g.inner x (Z x) (Z x)) * Real.sqrt (g.inner x (U1 x) (U1 x))
             * Real.sqrt (g.inner x (U2 x) (U2 x)) * Real.sqrt (g.inner x (U x) (U x))) := by
      ring
    rwa [one_mul, he] at h
  exact hstep

end Work.Diff.EXT
