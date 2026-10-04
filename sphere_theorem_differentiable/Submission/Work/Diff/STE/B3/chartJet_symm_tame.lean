import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.D.psi.Basic
import Submission.Work.Diff.STE.D.psi.chartMatOf_pd_det_pos
import Submission.Work.Diff.STE.B3.transport_tame_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

set_option maxHeartbeats 2000000

/-!
## The transpose of the chart matrix, and the symmetry of derivatives of symmetric
matrix-valued maps

The chart jet `Work.Diff.STE.D.chartJetOf h x₀ y` is (by definition of `Work.Diff.EXT.jet2`) the
tuple of the value, the first and the second spatial Fréchet derivative of the chart matrix
`y' ↦ chartMatOf h x₀ y'` at `y`.  Every symmetry statement of `chartJet_symm_tame` is therefore a
statement about the derivatives of a *matrix-valued* function which takes symmetric values
pointwise: the `(i,k)`-symmetries (first and second derivative) follow from the pointwise symmetry
by applying the transpose `swapMat`, and the `(m,a)`-symmetry is Schwarz' theorem. -/

/-- **Transposition of the chart matrix**, as a continuous linear map on `MatE`. -/
noncomputable def swapMat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] :
    Work.Diff.EXT.MatE (E := E) →L[ℝ] Work.Diff.EXT.MatE (E := E) :=
  ContinuousLinearMap.mk
    { toFun := fun M i k => M k i
      map_add' := by intro M N; ext i k; rfl
      map_smul' := by intro c M; ext i k; rfl }
    (LinearMap.continuous_of_finiteDimensional _)

lemma swapMat_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] (M : Work.Diff.EXT.MatE (E := E)) (i k : Fin (Module.finrank ℝ E)) :
    swapMat M i k = M k i := rfl

/-- **A map which takes values in the fixed points of a continuous linear map has a derivative
which does too.**  If `T (F y') = F y'` for all `y'` and `F` is differentiable at `y`, then
`T ∘ fderiv F y = fderiv F y`. -/
theorem fderiv_comp_eq_self_of_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : G →L[ℝ] G) {F : E → G} {y : E} (hF : DifferentiableAt ℝ F y)
    (hsym : ∀ y', T (F y') = F y') :
    T.comp (fderiv ℝ F y) = fderiv ℝ F y := by
  have hcomp : HasFDerivAt (fun y' => T (F y')) (T.comp (fderiv ℝ F y)) y :=
    (ContinuousLinearMap.hasFDerivAt T).comp y hF.hasFDerivAt
  have heq : (fun y' => T (F y')) = F := funext hsym
  rw [heq] at hcomp
  exact hcomp.fderiv.symm

theorem chartJet_symm_tame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (hz : ‖z‖ ≤ 2 * D.σ j) :
    (∀ i k : Fin (Module.finrank ℝ E),
      (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).1 i k
        = (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
            (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).1 k i)
    ∧ (∀ a i k : Fin (Module.finrank ℝ E),
      (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).2.1
          (Work.Diff.EXT.bB (E := E) a) i k
        = (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
            (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).2.1
            (Work.Diff.EXT.bB (E := E) a) k i)
    ∧ (∀ m a i k : Fin (Module.finrank ℝ E),
      (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).2.2
          (Work.Diff.EXT.bB (E := E) m) (Work.Diff.EXT.bB (E := E) a) i k
        = (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
            (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).2.2
            (Work.Diff.EXT.bB (E := E) a) (Work.Diff.EXT.bB (E := E) m) i k)
    ∧ (∀ m a i k : Fin (Module.finrank ℝ E),
      (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).2.2
          (Work.Diff.EXT.bB (E := E) m) (Work.Diff.EXT.bB (E := E) a) i k
        = (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
            (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).2.2
            (Work.Diff.EXT.bB (E := E) m) (Work.Diff.EXT.bB (E := E) a) k i)
    ∧ (Matrix.of (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).1).det ≠ 0 := by
  have hy : (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) ∈ (extChartAt I (D.x₀ j)).target :=
    D.htarget j z hz
  have hopen : IsOpen (extChartAt I (D.x₀ j)).target := isOpen_extChartAt_target (D.x₀ j)
  have hCD : ContDiffOn ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j))
      (extChartAt I (D.x₀ j)).target := hsmooth (D.x₀ j)
  have hCDA : ContDiffAt ℝ ↑(⊤ : ℕ∞)
      (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j))
      (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) :=
    hCD.contDiffAt (hopen.mem_nhds hy)
  have hsymM : ∀ (y' : E) (i k : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y' i k
        = Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y' k i :=
    fun y' i k => hsym ((extChartAt I (D.x₀ j)).symm y')
      (Submission.Geodesic.frameVector (I := I) (D.x₀ j)
        ((extChartAt I (D.x₀ j)).symm y') (Work.Diff.EXT.bB (E := E) i))
      (Submission.Geodesic.frameVector (I := I) (D.x₀ j)
        ((extChartAt I (D.x₀ j)).symm y') (Work.Diff.EXT.bB (E := E) k))
  have hTglob : ∀ y' : E,
      swapMat (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y')
        = Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y' :=
    fun y' => funext fun i => funext fun k => (hsymM y' i k).symm
  have hFdiff : DifferentiableAt ℝ
      (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j))
      (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) :=
    hCDA.differentiableAt (by simp)
  have hcomp1 := fderiv_comp_eq_self_of_symm swapMat hFdiff hTglob
  have h2 : ∀ (a : Fin (Module.finrank ℝ E)) (i k : Fin (Module.finrank ℝ E)),
      fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j))
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) (Work.Diff.EXT.bB (E := E) a) i k
        = fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j))
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) (Work.Diff.EXT.bB (E := E) a) k i := by
    intro a i k
    have hb : swapMat (fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j))
        (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) (Work.Diff.EXT.bB (E := E) a))
        = fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j))
        (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) (Work.Diff.EXT.bB (E := E) a) := by
      have hh := congrArg (fun (L : E →L[ℝ] Work.Diff.EXT.MatE (E := E)) =>
        L (Work.Diff.EXT.bB (E := E) a)) hcomp1
      simpa only [ContinuousLinearMap.comp_apply] using hh
    have hc := congrArg (fun (N : Work.Diff.EXT.MatE (E := E)) => N i k) hb
    simpa only [swapMat_apply] using hc.symm
  have hSymm2 : IsSymmSndFDerivAt ℝ
      (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j))
      (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) :=
    hCDA.isSymmSndFDerivAt (by simp)
  have h3 : ∀ (m a : Fin (Module.finrank ℝ E)) (i k : Fin (Module.finrank ℝ E)),
      fderiv ℝ (fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)))
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)
          (Work.Diff.EXT.bB (E := E) m) (Work.Diff.EXT.bB (E := E) a) i k
        = fderiv ℝ (fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)))
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)
          (Work.Diff.EXT.bB (E := E) a) (Work.Diff.EXT.bB (E := E) m) i k :=
    fun m a i k => congrArg (fun (N : Work.Diff.EXT.MatE (E := E)) => N i k)
      (hSymm2.eq (Work.Diff.EXT.bB (E := E) m) (Work.Diff.EXT.bB (E := E) a))
  have hAdiff : DifferentiableAt ℝ
      (fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)))
      (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) :=
    (hCDA.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hAglob : ∀ y' : E,
      ((ContinuousLinearMap.compL ℝ E (Work.Diff.EXT.MatE (E := E))
          (Work.Diff.EXT.MatE (E := E))) swapMat)
          (fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)) y')
        = fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)) y' := by
    intro y'
    by_cases hd : DifferentiableAt ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)) y'
    · exact fderiv_comp_eq_self_of_symm swapMat hd hTglob
    · rw [fderiv_zero_of_not_differentiableAt hd]
      simp
  have h4b := fderiv_comp_eq_self_of_symm
    (((ContinuousLinearMap.compL ℝ E (Work.Diff.EXT.MatE (E := E))
        (Work.Diff.EXT.MatE (E := E))) swapMat)) hAdiff hAglob
  have h4 : ∀ (m a : Fin (Module.finrank ℝ E)) (i k : Fin (Module.finrank ℝ E)),
      fderiv ℝ (fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)))
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)
          (Work.Diff.EXT.bB (E := E) m) (Work.Diff.EXT.bB (E := E) a) i k
        = fderiv ℝ (fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)))
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)
          (Work.Diff.EXT.bB (E := E) m) (Work.Diff.EXT.bB (E := E) a) k i := by
    intro m a i k
    have hb : ((ContinuousLinearMap.compL ℝ E (Work.Diff.EXT.MatE (E := E))
          (Work.Diff.EXT.MatE (E := E))) swapMat)
          (fderiv ℝ (fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)))
            (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) (Work.Diff.EXT.bB (E := E) m))
        = fderiv ℝ (fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)))
            (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) (Work.Diff.EXT.bB (E := E) m) := by
      have hh := congrArg (fun (L : E →L[ℝ] (E →L[ℝ] Work.Diff.EXT.MatE (E := E))) =>
        L (Work.Diff.EXT.bB (E := E) m)) h4b
      simpa only [ContinuousLinearMap.comp_apply] using hh
    have hba : swapMat
          ((fderiv ℝ (fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)))
            (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) (Work.Diff.EXT.bB (E := E) m))
          (Work.Diff.EXT.bB (E := E) a))
        = (fderiv ℝ (fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)))
            (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) (Work.Diff.EXT.bB (E := E) m))
          (Work.Diff.EXT.bB (E := E) a) := by
      have hh := congrArg (fun (L : E →L[ℝ] Work.Diff.EXT.MatE (E := E)) =>
        L (Work.Diff.EXT.bB (E := E) a)) hb
      simpa only [ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply] using hh
    have hc := congrArg (fun (N : Work.Diff.EXT.MatE (E := E)) => N i k) hba
    simpa only [swapMat_apply] using hc.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i k
    exact hsymM (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) i k
  · intro a i k
    exact h2 a i k
  · intro m a i k
    exact h3 m a i k
  · intro m a i k
    exact h4 m a i k
  · exact ne_of_gt (Work.Diff.STE.D.psi.chartMatOf_det_pos_of_posDef (I := I) (M := M) h
      (D.x₀ j) hsym hpos hy)

end Work.Diff.STE.B3
