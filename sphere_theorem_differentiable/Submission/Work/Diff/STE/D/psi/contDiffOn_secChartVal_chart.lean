import Mathlib
import Submission.Work.Diff.STE.D.psi.Basic
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.STE.deTurck.contDiffOn_pPhi
import Submission.Work.Diff.STE.deTurck.posDef_gmat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the chart expression `secChartVal` along a smooth field

`Work.Diff.STE.D.secChartVal g₀ h x₀ x u v` is the chart expression of the DeTurck operator on the
section `h`: the sum

`Σ_{j,k} pPhiJetOf g₀ h x₀ (extChartAt I x₀ x) j k · (coordCLM x₀ x j u · coordCLM x₀ x k v)`

over the canonical basis of the model space, where `pPhi` is the (jet level) DeTurck operator and
`coordCLM x₀ x j` is the `j`-th coordinate functional of the tangent bundle in the trivialisation
at `x₀`.

This file proves that if the chart matrix of `h` is smooth in the chart at `x₀` (the hypothesis
`ChartData h`), its determinant does not vanish there (`hdet`), and `X`, `Y` are smooth sections,
then the composite function of the chart coordinate

`y ↦ secChartVal g₀ h x₀ ((extChartAt I x₀).symm y) (X ((extChartAt I x₀).symm y))
        (Y ((extChartAt I x₀).symm y))`

is `C^∞` on the chart target.

The mathematics is a composition of smooth maps.  Each ingredient is smooth as a function of the
chart coordinate `y`:

* the spatial `2`-jet of the chart matrix of `h` (`ChartData h` and the smoothness of `fderiv`,
  `fderiv²` of a smooth function on an open set); the same for the background metric `g₀`
  (`Work.Diff.EXT.kz_contDiffAt_chartMatFun`);
* the jet-level DeTurck operator `pPhi` on the locus where both Gram matrices are invertible
  (`Work.Diff.STE.deTurck.contDiffOn_pPhi`), the invertibility of the background Gram matrix being
  `Work.Diff.STE.deTurck.posDef_gmat` and the invertibility of the Gram matrix of `h` being `hdet`;
* the coordinate functionals of the trivialisation at `x₀`, applied to a smooth section
  (`Bundle.Trivialization.contMDiffAt_section_iff` plus the smoothness of the chart inverse).
-/

open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.D.psi

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]

/-! ## Elementary chart facts -/

/-- The inverse of the extended chart at `x₀` maps the chart target into the chart source. -/
lemma symm_target_mem_chart_source {x₀ : M} {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
  rw [← extChartAt_source (I := I) x₀]
  exact PartialEquiv.map_target (extChartAt I x₀) hy

/-- The same statement for the base set of the tangent bundle trivialisation at `x₀`. -/
lemma symm_target_mem_baseSet {x₀ : M} {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    (extChartAt I x₀).symm y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet (I := I) x₀]
  exact symm_target_mem_chart_source (I := I) hy

/-! ## The chart coordinates of a smooth field

The coordinate functional `coordCLM x₀ p j` of the trivialisation at `x₀` is the scalar product of
the trivialisation coordinates with the `j`-th basis vector of the model space.  The point is that
this is `C^∞` in the chart coordinate. -/

/-- **The trivialisation coordinates of a smooth field are smooth in the chart coordinate.** -/
lemma contDiffOn_trivCLM_symm (x₀ : M) {Z : Π q : M, TangentSpace I q}
    (hZ : Work.Diff.GE.SmoothField (I := I) (M := M) Z) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
        ((extChartAt I x₀).symm y) (Z ((extChartAt I x₀).symm y)))
      (extChartAt I x₀).target := by
  intro y hy
  have hbase := symm_target_mem_baseSet (I := I) (x₀ := x₀) hy
  have hsec : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun q : M => ((trivializationAt E (TangentSpace I) x₀) ⟨q, Z q⟩).2)
      ((extChartAt I x₀).symm y) :=
    (Bundle.Trivialization.contMDiffAt_section_iff
      (trivializationAt E (TangentSpace I) x₀) hbase).mp hZ.contMDiffAt
  have hχ : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm
      (extChartAt I x₀).target y :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x₀) y hy
  have hcomp : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      ((fun q : M => ((trivializationAt E (TangentSpace I) x₀) ⟨q, Z q⟩).2) ∘
        (extChartAt I x₀).symm) (extChartAt I x₀).target y :=
    (hsec.contMDiffWithinAt).comp y hχ (fun _ _ => Set.mem_univ _)
  have hcd : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      ((fun q : M => ((trivializationAt E (TangentSpace I) x₀) ⟨q, Z q⟩).2) ∘
        (extChartAt I x₀).symm) (extChartAt I x₀).target y :=
    contMDiffWithinAt_iff_contDiffWithinAt.mp hcomp
  refine hcd.congr (fun z hz => ?_) ?_
  · simp only [Function.comp_apply]
    exact Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt E (TangentSpace I) x₀)
      (symm_target_mem_baseSet (I := I) (x₀ := x₀) hz) (Z ((extChartAt I x₀).symm z))
  · simp only [Function.comp_apply]
    exact Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt E (TangentSpace I) x₀) hbase (Z ((extChartAt I x₀).symm y))

/-- **The chart coordinates of a smooth field are smooth in the chart coordinate.** -/
lemma contDiffOn_coordCLM_symm (x₀ : M) {Z : Π q : M, TangentSpace I q}
    (hZ : Work.Diff.GE.SmoothField (I := I) (M := M) Z) (j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => coordCLM (I := I) (M := M) x₀ ((extChartAt I x₀).symm y) j
        (Z ((extChartAt I x₀).symm y)))
      (extChartAt I x₀).target := by
  have h := (contDiffOn_const (c := ((Work.Diff.EXT.bB (E := E)).coord j).toContinuousLinearMap)
      (s := (extChartAt I x₀).target)).clm_apply
    (contDiffOn_trivCLM_symm (I := I) (M := M) x₀ hZ)
  refine ContDiffOn.congr (f := fun y : E =>
      ((Work.Diff.EXT.bB (E := E)).coord j).toContinuousLinearMap
        ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
          ((extChartAt I x₀).symm y) (Z ((extChartAt I x₀).symm y)))) h ?_
  · intro y hy
    simp only [coordCLM, ContinuousLinearMap.comp_apply]

/-! ## The spatial `2`-jet of the chart matrix -/

/-- **Smoothness of the spatial `2`-jet of a smooth function of the chart coordinate.** -/
lemma contDiffOn_jet2_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} (x₀ : M) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (extChartAt I x₀).target) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => Work.Diff.EXT.jet2 (E := E) (fun p : ℝ × E => u p.2) (0, y))
      (extChartAt I x₀).target := by
  have hopen := isOpen_extChartAt_target (I := I) x₀
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ u) (extChartAt I x₀).target :=
    hu.fderiv_of_isOpen hopen (m := (⊤ : ℕ∞)) (by simp)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ u)) (extChartAt I x₀).target :=
    h1.fderiv_of_isOpen hopen (m := (⊤ : ℕ∞)) (by simp)
  refine ContDiffOn.congr (f := fun y : E =>
    (u y, fderiv ℝ u y, fderiv ℝ (fderiv ℝ u) y)) ?_ ?_
  · exact hu.prodMk (h1.prodMk h2)
  · intro y hy
    rfl

/-- The first component of the spatial `2`-jet of the chart matrix of a section is the value of
the chart matrix. -/
lemma chartJetOf_fst (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M) (y : E) :
    (chartJetOf (I := I) (M := M) h x₀ y).1 =
      Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y := rfl

/-- The first component of the spatial `2`-jet of the chart matrix of a metric is the chart Gram
matrix at the point of the chart. -/
lemma chartJetOf_fst_inner (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) :
    (chartJetOf (I := I) (M := M) g.inner x₀ y).1 =
      Work.Diff.EXT.gmat (I := I) g x₀ ((extChartAt I x₀).symm y) := rfl

/-- **Smoothness of the spatial `2`-jet of the chart matrix of a section** whose chart matrix is
smooth. -/
lemma contDiffOn_chartJetOf (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀) (extChartAt I x₀).target) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => chartJetOf (I := I) (M := M) h x₀ y) (extChartAt I x₀).target := by
  have hjet := contDiffOn_jet2_slice (I := I) (x₀ := x₀) (F := Work.Diff.EXT.MatE (E := E)) hh
  refine ContDiffOn.congr hjet (fun y hy => ?_)
  rfl

/-! ## The main theorem -/

theorem contDiffOn_secChartVal_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    (g₀ : Submission.Diff.SMet I M) (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M)
    (X Y : Π q : M, TangentSpace I q)
    (hchart : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (hdet : ∀ y ∈ (extChartAt I x₀).target,
      (Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y)).det ≠ 0)
    (hX : Work.Diff.GE.SmoothField (I := I) (M := M) X)
    (hY : Work.Diff.GE.SmoothField (I := I) (M := M) Y) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => Work.Diff.STE.D.secChartVal (I := I) (M := M) g₀ h x₀
        ((extChartAt I x₀).symm y) (X ((extChartAt I x₀).symm y)) (Y ((extChartAt I x₀).symm y)))
      (extChartAt I x₀).target := by
  -- the spatial `2`-jets of the two chart matrices
  have hjetH : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => chartJetOf (I := I) (M := M) h x₀ y) (extChartAt I x₀).target :=
    contDiffOn_chartJetOf (I := I) (M := M) h x₀ (hchart x₀)
  have hjetG : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => chartJetOf (I := I) (M := M) g₀.inner x₀ y) (extChartAt I x₀).target := by
    refine contDiffOn_chartJetOf (I := I) (M := M) g₀.inner x₀ ?_
    intro y hy
    exact (Work.Diff.EXT.kz_contDiffAt_chartMatFun (I := I) g₀ x₀ hy).contDiffWithinAt
  have hpair : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => (chartJetOf (I := I) (M := M) g₀.inner x₀ y,
        chartJetOf (I := I) (M := M) h x₀ y)) (extChartAt I x₀).target :=
    hjetG.prodMk hjetH
  -- the values lie in the locus where `pPhi` is smooth
  have hmem : ∀ y ∈ (extChartAt I x₀).target,
      (chartJetOf (I := I) (M := M) g₀.inner x₀ y,
        chartJetOf (I := I) (M := M) h x₀ y) ∈
      Work.Diff.STE.deTurck.pPhiDom E := by
    intro y hy
    refine ⟨?_, ?_⟩
    · have hp : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source :=
        symm_target_mem_chart_source (I := I) hy
      have hpos := (Work.Diff.STE.deTurck.posDef_gmat (I := I) g₀ x₀ hp).det_pos
      have hne : (Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ x₀
          ((extChartAt I x₀).symm y))).det ≠ 0 := ne_of_gt hpos
      simpa only [chartJetOf_fst_inner (I := I) g₀ x₀ y] using hne
    · have hne := hdet y hy
      simpa only [chartJetOf_fst (I := I) h x₀ y] using hne
  have hpPhi := (Work.Diff.STE.deTurck.contDiffOn_pPhi (E := E)).comp hpair hmem
  have hpPhi' : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => fun i j : Fin (Module.finrank ℝ E) => Work.Diff.STE.DeTurck.pPhi
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y, chartJetOf (I := I) (M := M) h x₀ y).1.1
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y, chartJetOf (I := I) (M := M) h x₀ y).1.2.1
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y, chartJetOf (I := I) (M := M) h x₀ y).1.2.2
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y, chartJetOf (I := I) (M := M) h x₀ y).2.1
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y, chartJetOf (I := I) (M := M) h x₀ y).2.2.1
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y, chartJetOf (I := I) (M := M) h x₀ y).2.2.2
        i j)
      (extChartAt I x₀).target :=
    hpPhi.congr (fun y hy => rfl)
  have hA : ∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => Work.Diff.STE.DeTurck.pPhi
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y).1
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.1
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.2
        (chartJetOf (I := I) (M := M) h x₀ y).1
        (chartJetOf (I := I) (M := M) h x₀ y).2.1
        (chartJetOf (I := I) (M := M) h x₀ y).2.2 i j) (extChartAt I x₀).target := by
    intro i j
    have h2 := (contDiffOn_pi.mp ((contDiffOn_pi.mp hpPhi') i)) j
    exact h2.congr (fun y hy => rfl)
  -- the coordinates of the two fields
  have hcX : ∀ j : Fin (Module.finrank ℝ E), ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => coordCLM (I := I) (M := M) x₀ ((extChartAt I x₀).symm y) j
        (X ((extChartAt I x₀).symm y))) (extChartAt I x₀).target :=
    fun j => contDiffOn_coordCLM_symm (I := I) (M := M) x₀ hX j
  have hcY : ∀ k : Fin (Module.finrank ℝ E), ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => coordCLM (I := I) (M := M) x₀ ((extChartAt I x₀).symm y) k
        (Y ((extChartAt I x₀).symm y))) (extChartAt I x₀).target :=
    fun k => contDiffOn_coordCLM_symm (I := I) (M := M) x₀ hY k
  have hterm : ∀ j k : Fin (Module.finrank ℝ E), ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => Work.Diff.STE.DeTurck.pPhi
          (chartJetOf (I := I) (M := M) g₀.inner x₀ y).1
          (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.1
          (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.2
          (chartJetOf (I := I) (M := M) h x₀ y).1
          (chartJetOf (I := I) (M := M) h x₀ y).2.1
          (chartJetOf (I := I) (M := M) h x₀ y).2.2 j k
        * (coordCLM (I := I) (M := M) x₀ ((extChartAt I x₀).symm y) j
            (X ((extChartAt I x₀).symm y))
          * coordCLM (I := I) (M := M) x₀ ((extChartAt I x₀).symm y) k
            (Y ((extChartAt I x₀).symm y)))) (extChartAt I x₀).target :=
    fun j k => (hA j k).mul ((hcX j).mul (hcY k))
  have hsum : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        Work.Diff.STE.DeTurck.pPhi
          (chartJetOf (I := I) (M := M) g₀.inner x₀ y).1
          (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.1
          (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.2
          (chartJetOf (I := I) (M := M) h x₀ y).1
          (chartJetOf (I := I) (M := M) h x₀ y).2.1
          (chartJetOf (I := I) (M := M) h x₀ y).2.2 j k
        * (coordCLM (I := I) (M := M) x₀ ((extChartAt I x₀).symm y) j
            (X ((extChartAt I x₀).symm y))
          * coordCLM (I := I) (M := M) x₀ ((extChartAt I x₀).symm y) k
            (Y ((extChartAt I x₀).symm y))))
      (extChartAt I x₀).target := by
    refine ContDiffOn.sum (f := fun j y => ∑ k : Fin (Module.finrank ℝ E),
      Work.Diff.STE.DeTurck.pPhi
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y).1
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.1
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.2
        (chartJetOf (I := I) (M := M) h x₀ y).1
        (chartJetOf (I := I) (M := M) h x₀ y).2.1
        (chartJetOf (I := I) (M := M) h x₀ y).2.2 j k
      * (coordCLM (I := I) (M := M) x₀ ((extChartAt I x₀).symm y) j
          (X ((extChartAt I x₀).symm y))
        * coordCLM (I := I) (M := M) x₀ ((extChartAt I x₀).symm y) k
          (Y ((extChartAt I x₀).symm y)))) ?_
    intro j _
    refine ContDiffOn.sum (f := fun k y => Work.Diff.STE.DeTurck.pPhi
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y).1
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.1
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.2
        (chartJetOf (I := I) (M := M) h x₀ y).1
        (chartJetOf (I := I) (M := M) h x₀ y).2.1
        (chartJetOf (I := I) (M := M) h x₀ y).2.2 j k
      * (coordCLM (I := I) (M := M) x₀ ((extChartAt I x₀).symm y) j
          (X ((extChartAt I x₀).symm y))
        * coordCLM (I := I) (M := M) x₀ ((extChartAt I x₀).symm y) k
          (Y ((extChartAt I x₀).symm y)))) ?_
    intro k _
    exact hterm j k
  refine ContDiffOn.congr (f := fun y : E => ∑ j : Fin (Module.finrank ℝ E),
    ∑ k : Fin (Module.finrank ℝ E),
      Work.Diff.STE.DeTurck.pPhi
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y).1
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.1
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.2
        (chartJetOf (I := I) (M := M) h x₀ y).1
        (chartJetOf (I := I) (M := M) h x₀ y).2.1
        (chartJetOf (I := I) (M := M) h x₀ y).2.2 j k
      * (coordCLM (I := I) (M := M) x₀ ((extChartAt I x₀).symm y) j
          (X ((extChartAt I x₀).symm y))
        * coordCLM (I := I) (M := M) x₀ ((extChartAt I x₀).symm y) k
          (Y ((extChartAt I x₀).symm y)))) hsum ?_
  intro y hy
  simp only [Work.Diff.STE.D.secChartVal, Work.Diff.STE.D.pPhiJetOf_apply,
    Work.Diff.STE.D.chartJetOf_eq]
  rw [(extChartAt I x₀).right_inv hy]

end

end Work.Diff.STE.D.psi
