import Mathlib
import Submission.Work.Diff.STE.D.psi.Core
import Submission.Work.Diff.STE.D.psi.contDiffOn_secChartVal_chart
import Submission.Work.Diff.STE.D.psi.chartJetOf_genMap_affine
import Submission.Work.Diff.STE.D.psi.chartJetOf_jSym_bound
import Submission.Work.Diff.STE.D.psi.continuousOn_chartJetOf_jSym
import Submission.Work.Diff.STE.deTurck.posDef_gmat
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.D.isSymm_genMap
import Submission.Work.Diff.STE.D.isSymm_addSec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer D: continuity of the localised component `Fz` of the smoothness proof of `psiConc`

The localised component is

  `Fz c y = ψ i y · √(dens i y) · secChartVal g₀ (g₀ + genMap D ε c) (x₀ i) (pt i y) (eᵢa) (eᵢb)`

(`i = z.1`, `a = z.2.1`, `b = z.2.2.1`), a function of the *flat* chart coordinate `y` of the chart
at `x₀ i`.  The statement proved here is its continuity, under the only hypothesis that makes the
section positive definite (`IsPos`), which is what turns the chart matrix of `g₀ + genMap D ε c`
into an invertible — indeed positive definite — matrix, and hence puts the jets inside the domain
of the smooth DeTurck operator `pPhi`.

The proof is the local/global dichotomy of the support of the localised weight:

* on the open set `U = {y | flatToE (x₀ i) y ∈ (extChartAt I (x₀ i)).target}` the function is
  `C^∞`: `ψ i` is globally `C^∞` (`B3Data.psi_contDiff`), `√dens i` is `C^∞` on `U` (`densGood`,
  `B3Data.sqrt_dens_contDiffAt`), and the chart expression of the DeTurck operator is `C^∞` on the
  chart target (`contDiffOn_secChartVal_chart`), composed with the affine map `flatToE (x₀ i)`;
* on the open set `{y | σ i < ‖y‖}` the function *vanishes*, because `ψ i` does
  (`B3.norm_lt_sigma_of_psi_ne_zero`).

The two open sets cover the flat space, since the closed `σ i`-ball is contained in `U`
(`B3Data.htarget`, `B3Data.hσ`); the covering by open sets is turned into continuity pointwise.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open Classical
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.D.psi

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

/-- **The explicit form of the localised component `Fz`** in the flat coordinate `y` of the chart
at `x₀ i`.  This is definitionally `Fz g₀ D ε (i,a,b,q) c`, with the chart expression
`secChartVal` of the DeTurck operator written out (`Work.Diff.STE.D.secChart_apply`). -/
noncomputable def FzExpl (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun y => D.psi i y * Real.sqrt (D.dens i y) *
    Work.Diff.STE.D.secChartVal (I := I) (M := M) g₀
      (Work.Diff.STE.D.addSec (I := I) g₀ (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c))
      (D.x₀ i) ((extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y))
      (D.e i a ((extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y)))
      (D.e i b ((extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y)))

/-- The defining equation of `FzExpl`, as an equality of functions (so that it can be used to
replace the function `FzExpl …` inside a `ContDiffOn`/`Continuous` statement). -/
lemma FzExpl_eq (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    FzExpl (I := I) (M := M) g₀ D ε i a b c =
      fun y => D.psi i y * Real.sqrt (D.dens i y) *
        Work.Diff.STE.D.secChartVal (I := I) (M := M) g₀
          (Work.Diff.STE.D.addSec (I := I) g₀ (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c))
          (D.x₀ i) ((extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y))
          (D.e i a ((extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y)))
          (D.e i b ((extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y))) :=
  rfl

/-- The localised component is its explicit form. -/
lemma Fz_eq_FzExpl (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (q : Work.Diff.STE.B3.QIdx (Module.finrank ℝ E) ε)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Work.Diff.STE.D.Fz (I := I) (M := M) g₀ D ε (i, a, b, q) c
      = FzExpl (I := I) (M := M) g₀ D ε i a b c := by
  rw [FzExpl_eq]
  funext y
  simp only [Work.Diff.STE.D.Fz, Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat]
  rw [Work.Diff.STE.D.secChart_apply]
  rfl

/-- **The chart matrices of the positive definite section `g₀ + genMap D ε c` are invertible.**
This is the linear-algebra content of `IsPos`: the chart matrix is the matrix of the positive
definite bilinear form `g₀ + genMap D ε c` in the coordinate frame of the chart, which is a basis
(the coordinate map is `symmL` of the tangent-bundle trivialisation, whose left inverse is
`continuousLinearMapAt`). -/
lemma det_chartMatOf_addSec_genMap_ne_zero
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hc : Work.Diff.STE.D.IsPos (I := I) (M := M) g₀ D ε c) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    (Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M)
      (Work.Diff.STE.D.addSec (I := I) g₀
        (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)) x₀ y)).det ≠ 0 := by
  classical
  -- the point of `M` whose chart coordinate is `y`
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact PartialEquiv.map_target (extChartAt I x₀) hy
  have hbase : (extChartAt I x₀).symm y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hp
  -- the coordinate map of the trivialisation is injective on the base set
  have hL : Function.Injective
      (((trivializationAt E (TangentSpace I) x₀).symmL ℝ
        ((extChartAt I x₀).symm y)).toLinearMap) := by
    intro u v huv
    have huv' : (trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm y) u
        = (trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm y) v := huv
    have h := congrArg ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
      ((extChartAt I x₀).symm y)) huv'
    simpa only [Trivialization.continuousLinearMapAt_symmL _ (R := ℝ) hbase u,
      Trivialization.continuousLinearMapAt_symmL _ (R := ℝ) hbase v] using h
  -- the chart matrix is positive definite
  have hpd := Work.Diff.STE.deTurck.posDef_gram_of_injective
    (L := ((trivializationAt E (TangentSpace I) x₀).symmL ℝ
      ((extChartAt I x₀).symm y)).toLinearMap)
    hL (Work.Diff.STE.D.addSec (I := I) g₀
      (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c) ((extChartAt I x₀).symm y))
    (fun v w => (Work.Diff.STE.D.isSymm_addSec (I := I) (M := M) (ι₀ := ι₀)
      (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)
      (Work.Diff.STE.D.isSymm_genMap (I := I) (M := M) D ε c))
        ((extChartAt I x₀).symm y) v w)
    (fun v hv => hc ((extChartAt I x₀).symm y) v hv)
  have hmat : (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        (Work.Diff.STE.D.addSec (I := I) g₀
            (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c) ((extChartAt I x₀).symm y))
          ((((trivializationAt E (TangentSpace I) x₀).symmL ℝ
            ((extChartAt I x₀).symm y)).toLinearMap) ((Module.finBasis ℝ E) i))
          ((((trivializationAt E (TangentSpace I) x₀).symmL ℝ
            ((extChartAt I x₀).symm y)).toLinearMap) ((Module.finBasis ℝ E) j)))
      = Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M)
          (Work.Diff.STE.D.addSec (I := I) g₀
            (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)) x₀ y) := by
    ext i j
    simp only [Matrix.of_apply, Work.Diff.STE.D.chartMatOf_apply, Work.Diff.EXT.bB,
      Submission.Geodesic.frameVector]
    rfl
  rw [← hmat]
  exact ne_of_gt hpd.det_pos

/-- **The localised component is `C^∞` where the chart is genuine.** -/
lemma contDiffOn_FzExpl
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hc : Work.Diff.STE.D.IsPos (I := I) (M := M) g₀ D ε c) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (FzExpl (I := I) (M := M) g₀ D ε i a b c)
      {y : Fin (Module.finrank ℝ E) → ℝ |
        Work.Diff.STE.flatToE (I := I) (D.x₀ i) y ∈ (extChartAt I (D.x₀ i)).target} := by
  classical
  have hUopen : IsOpen {y : Fin (Module.finrank ℝ E) → ℝ |
      Work.Diff.STE.flatToE (I := I) (D.x₀ i) y ∈ (extChartAt I (D.x₀ i)).target} :=
    (isOpen_extChartAt_target (I := I) (D.x₀ i)).preimage
      (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ i)).continuous
  -- the chart data and the invertibility of the chart matrix
  have hchart : Work.Diff.STE.D.ChartData (I := I) (M := M)
      (Work.Diff.STE.D.addSec (I := I) g₀
        (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)) :=
    Work.Diff.STE.D.GenMap.chartData_add (I := I) hg
      (Work.Diff.STE.D.ChartData_genMap (I := I) (M := M) D ε c)
  have hdet : ∀ y : E, y ∈ (extChartAt I (D.x₀ i)).target →
      (Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M)
        (Work.Diff.STE.D.addSec (I := I) g₀
          (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)) (D.x₀ i) y)).det ≠ 0 :=
    fun y hy => det_chartMatOf_addSec_genMap_ne_zero (I := I) (M := M) D ε c hc (D.x₀ i) hy
  rw [hUopen.contDiffOn_iff]
  intro y hy
  rw [FzExpl_eq]
  -- smoothness of the chart expression, composed with the affine flat coordinate
  have hsec : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : E => Work.Diff.STE.D.secChartVal (I := I) (M := M) g₀
        (Work.Diff.STE.D.addSec (I := I) g₀
          (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c))
        (D.x₀ i) ((extChartAt I (D.x₀ i)).symm z)
        (D.e i a ((extChartAt I (D.x₀ i)).symm z))
        (D.e i b ((extChartAt I (D.x₀ i)).symm z)))
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y) :=
    (Work.Diff.STE.D.psi.contDiffOn_secChartVal_chart (I := I) (M := M) g₀
      (Work.Diff.STE.D.addSec (I := I) g₀
        (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)) (D.x₀ i)
      (D.e i a) (D.e i b) hchart hdet (D.hesm i a) (D.hesm i b)).contDiffAt
      ((isOpen_extChartAt_target (I := I) (D.x₀ i)).mem_nhds hy)
  have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : Fin (Module.finrank ℝ E) → ℝ => Work.Diff.STE.D.secChartVal (I := I) (M := M) g₀
        (Work.Diff.STE.D.addSec (I := I) g₀
          (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c))
        (D.x₀ i) ((extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
        (D.e i a ((extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)))
        (D.e i b ((extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)))) y :=
    hsec.comp y (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ i)).contDiffAt
  have hmul := (((D.psi_contDiff i).contDiffAt).mul
    (D.sqrt_dens_contDiffAt i (Work.Diff.STE.B3.densGood (I := I) (M := M) D i) hy)).mul hcomp
  exact hmul

theorem continuous_Fz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hc : Work.Diff.STE.D.IsPos (I := I) (M := M) g₀ D ε c) :
    Continuous (Work.Diff.STE.D.Fz (I := I) (M := M) g₀ D ε z c) := by
  classical
  obtain ⟨i, a, b, q⟩ := z
  rw [Fz_eq_FzExpl (I := I) (M := M) g₀ D ε i a b q c]
  rw [continuous_iff_continuousAt]
  intro y₀
  by_cases hle : ‖y₀‖ ≤ D.σ i
  · -- the point lies in the closed `σ i`-ball, hence in the open set where the chart is genuine
    have hy₀ : Work.Diff.STE.flatToE (I := I) (D.x₀ i) y₀ ∈ (extChartAt I (D.x₀ i)).target :=
      D.htarget i y₀ (by have h := D.hσ i; linarith)
    have hUopen : IsOpen {y : Fin (Module.finrank ℝ E) → ℝ |
        Work.Diff.STE.flatToE (I := I) (D.x₀ i) y ∈ (extChartAt I (D.x₀ i)).target} :=
      (isOpen_extChartAt_target (I := I) (D.x₀ i)).preimage
        (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ i)).continuous
    exact (contDiffOn_FzExpl (I := I) (M := M) hg D ε c hc i a b).continuousOn.continuousAt
      (hUopen.mem_nhds hy₀)
  · -- the point lies outside the `σ i`-ball, where the localised weight vanishes
    have hlt : D.σ i < ‖y₀‖ := not_le.mp hle
    have hVopen : IsOpen {y : Fin (Module.finrank ℝ E) → ℝ | D.σ i < ‖y‖} :=
      isOpen_lt continuous_const continuous_norm
    have hev : FzExpl (I := I) (M := M) g₀ D ε i a b c =ᶠ[𝓝 y₀] fun _ => (0 : ℝ) := by
      filter_upwards [hVopen.mem_nhds hlt] with y hy
      have hpsi : D.psi i y = 0 := by
        by_contra hne
        exact absurd (Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero (I := I) (M := M) D hne)
          (not_lt.mpr (le_of_lt hy))
      simp only [FzExpl_eq, hpsi, zero_mul]
    exact continuousAt_const.congr hev.symm

end

end Work.Diff.STE.D.psi
