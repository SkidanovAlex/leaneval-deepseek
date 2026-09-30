import Submission.Work.RiemLib.IndexCorner2
import Submission.Work.RiemLib.FlowJacobi
import Submission.Work.RiemLib.JacobiCoordsEq
import Submission.Work.RiemLib.JacobiGlobal
import Submission.Work.RiemLib.JacobiCover
import Submission.Work.RiemLib.IndexFTC

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartCurv
open Submission.JacobiTensor
open Submission.Rauch
open Submission.RauchGlobal
open Submission.SecondVariation
open Submission.BonnetMyers
open Submission.ChartBounds
open Submission.Gauss
open Submission.ChartConnection
open Submission.FlowJacobi
open Submission.IndexCorner2
open Submission.JacobiGlobal
open Submission.JacobiCoords

/-!
# Backward uniqueness for the Jacobi system on an arbitrary interval

`Submission.IndexCorner2.eqOn_zero_of_jacobiSys` proves uniqueness for the Jacobi system
`y' = z - Γ(w)y`, `z' = -Γ(w)z - R(y,w)w` on `Icc 0 t₀` with data at `t₀`.  Two generalisations are
needed for the shortening argument of `σ ≤ κ`:

* **`eqOn_zero_of_jacobiSys_Icc`** — the same on an arbitrary interval `Icc a b`, with data at the
  *right* endpoint `b`;
* **`eqOn_zero_of_covDerivJacobi_Icc`** — the chart form: a Jacobi field `y` with `y b = 0` and
  `∇y(b) = 0` vanishes on `Icc a b`.

The payoff (used by `ConjCut`): a nontrivial Jacobi field along a geodesic with `J(0) = J(t) = 0`
has `∇J(t) ≠ 0` — the non-degeneracy needed by the classical shortening argument.
-/

namespace Submission.IndexBackUnique

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Uniqueness for the Jacobi system on an arbitrary interval, with data at the right end.** -/
theorem eqOn_zero_of_jacobiSys_Icc {x₀ : M} {u w : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hGc : ContinuousOn (fun t : ℝ => gammaOp (cov := cov) x₀ u w t) (Icc a b))
    (hRc : ContinuousOn (fun t : ℝ => curvOp (cov := cov) x₀ u w t) (Icc a b))
    {y z : ℝ → E}
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (z t - gammaOp (cov := cov) x₀ u w t (y t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (-gammaOp (cov := cov) x₀ u w t (z t)
      - curvOp (cov := cov) x₀ u w t (y t)) t)
    (hy0 : y b = 0) (hz0 : z b = 0) :
    ∀ t ∈ Icc a b, y t = 0 ∧ z t = 0 := by
  classical
  obtain ⟨CG, hCG⟩ := isCompact_Icc.exists_bound_of_continuousOn hGc
  obtain ⟨CR, hCR⟩ := isCompact_Icc.exists_bound_of_continuousOn hRc
  set C : ℝ := 1 + 2 * CG + CR with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ CG := le_trans (norm_nonneg _) (hCG a ⟨le_rfl, hab⟩)
    have h2 : 0 ≤ CR := le_trans (norm_nonneg _) (hCR a ⟨le_rfl, hab⟩)
    linarith
  set M : ℝ≥0 := ⟨C, hCnn⟩ with hMdef
  have hAbound : ∀ t ∈ Icc a b, ‖jacobiSysVec (cov := cov) x₀ u w t‖ ≤ (M : ℝ) := by
    intro t ht
    refine ContinuousLinearMap.opNorm_le_bound _ hCnn ?_
    intro x
    refine (norm_jacobiSysVec_le (cov := cov) x₀ u w t x.1 x.2).trans ?_
    have hgt : ‖gammaOp (cov := cov) x₀ u w t‖ ≤ CG := hCG t ht
    have hrt : ‖curvOp (cov := cov) x₀ u w t‖ ≤ CR := hCR t ht
    have hx : 0 ≤ ‖x‖ := norm_nonneg x
    have : (1 + 2 * ‖gammaOp (cov := cov) x₀ u w t‖ + ‖curvOp (cov := cov) x₀ u w t‖)
        ≤ C := by rw [hCdef]; linarith
    exact mul_le_mul_of_nonneg_right this hx
  set Y : ℝ → E × E := fun t => (y t, z t) with hYdef
  have hYode : ∀ t ∈ Icc a b,
      HasDerivAt Y (jacobiSysVec (cov := cov) x₀ u w t (Y t)) t := by
    intro t ht
    have h := (hy t ht).prodMk (hz t ht)
    rw [jacobiSysVec_apply]
    exact h
  have hZode : ∀ t ∈ Icc a b,
      HasDerivAt (fun _ : ℝ => (0 : E × E)) (jacobiSysVec (cov := cov) x₀ u w t
        ((fun _ : ℝ => (0 : E × E)) t)) t := by
    intro t ht
    rw [jacobiSysVec_apply]
    simp only [Prod.fst_zero, Prod.snd_zero, map_zero, sub_zero, neg_zero]
    exact hasDerivAt_const t (0 : E × E)
  have hY0 : Y b = (fun _ : ℝ => (0 : E × E)) b := by
    rw [hYdef]
    simp only [hy0, hz0]
    rfl
  have hEq := Commons.Analysis.ODE.eqOn_of_hasDerivAt_linearODE
    (A := fun t => jacobiSysVec (cov := cov) x₀ u w t)
    (M := M) hAbound ⟨hab, le_refl b⟩ hYode hZode hY0
  intro t ht
  have h := hEq ht
  rw [show (fun _ : ℝ => (0 : E × E)) t = 0 from rfl] at h
  simp only [hYdef, Prod.mk_eq_zero] at h
  exact h

/-- **A chart Jacobi field vanishing with its covariant derivative at `b` is zero on `Icc a b`.** -/
theorem eqOn_zero_of_covDerivJacobi_Icc {x₀ : M} {u w y : ℝ → E} {a b : ℝ} (hab : a < b)
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target)
    (hGc : ContinuousOn (fun t : ℝ => gammaOp (cov := cov) x₀ u w t) (Icc a b))
    (hRc : ContinuousOn (fun t : ℝ => curvOp (cov := cov) x₀ u w t) (Icc a b))
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (deriv y t) t)
    (hDy : ∀ t ∈ Icc a b,
      HasDerivAt (chartCovDeriv cov x₀ u w y) (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Icc a b, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hy0 : y b = 0) (hDy0 : chartCovDeriv cov x₀ u w y b = 0) :
    ∀ t ∈ Icc a b, y t = 0 := by
  have hy' : ∀ t ∈ Icc a b,
      HasDerivAt y (chartCovDeriv cov x₀ u w y t - gammaOp (cov := cov) x₀ u w t (y t)) t := by
    intro t ht
    have h : deriv y t = chartCovDeriv cov x₀ u w y t - gammaOp (cov := cov) x₀ u w t (y t) := by
      simp only [Submission.Jacobi.chartCovDeriv, gammaOp]
      abel
    exact (hy t ht).congr_deriv h
  have hz' : ∀ t ∈ Icc a b,
      HasDerivAt (chartCovDeriv cov x₀ u w y)
        (-gammaOp (cov := cov) x₀ u w t (chartCovDeriv cov x₀ u w y t)
          - curvOp (cov := cov) x₀ u w t (y t)) t := by
    intro t ht
    have hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (htgt t ht)
    have hCv : curvOp (cov := cov) x₀ u w t (y t)
        = chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) :=
      curvOp_apply (cov := cov) hsrc (y t)
    have h : deriv (chartCovDeriv cov x₀ u w y) t
        = -gammaOp (cov := cov) x₀ u w t (chartCovDeriv cov x₀ u w y t)
          - curvOp (cov := cov) x₀ u w t (y t) := by
      have hj := hjac t ht
      rw [← hCv] at hj
      have h2 : deriv (chartCovDeriv cov x₀ u w y) t
          + (gammaOp (cov := cov) x₀ u w t (chartCovDeriv cov x₀ u w y t)
            + curvOp (cov := cov) x₀ u w t (y t)) = 0 := by
        simpa only [Submission.Jacobi.chartCovDeriv, gammaOp, add_assoc] using hj
      have h3 := eq_neg_of_add_eq_zero_left h2
      rw [neg_add] at h3
      rw [sub_eq_add_neg]
      exact h3
    exact (hDy t ht).congr_deriv h
  have h := eqOn_zero_of_jacobiSys_Icc (cov := cov) hab.le hGc hRc hy' hz' hy0 hDy0
  intro t ht
  exact (h t ht).1

/-- **A chart Jacobi field vanishing at `b` together with its `DtQ`-derivative is zero on `Icc a b`**
(the general-interval, right-endpoint form of `IndexCorner2.eqOn_zero_of_chartJacobi`). -/
theorem eqOn_zero_of_chartJacobi_Icc [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (x₀ : M)
    {u w w' J J' J'' : ℝ → E} {a b : ℝ} (hab : a < b)
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Icc a b, HasDerivAt w (w' t) t)
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target)
    (hJ : ∀ t ∈ Icc a b, HasDerivAt J (J' t) t)
    (hJ' : ∀ t ∈ Icc a b, HasDerivAt J' (J'' t) t)
    (hjac : ∀ t ∈ Icc a b, DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0)
    (hJt : J b = 0) (hz0 : DtQ cov x₀ u J w J' b = 0) :
    ∀ t ∈ Icc a b, J t = 0 := by
  have huC : ContinuousOn u (Icc a b) := HasDerivAt.continuousOn hu
  have hwC : ContinuousOn w (Icc a b) := HasDerivAt.continuousOn hw
  have hGc : ContinuousOn (fun t : ℝ => gammaOp (cov := cov) x₀ u w t) (Icc a b) :=
    continuousOn_gammaOp_of_cont (cov := cov) htor huC hwC htgt
  have hRc : ContinuousOn (fun t : ℝ => curvOp (cov := cov) x₀ u w t) (Icc a b) :=
    continuousOn_curvOp (cov := cov) huC hwC htgt
  set z : ℝ → E := fun t => DtQ cov x₀ u J w J' t with hzdef
  have hzfun : z = fun t => J' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (J t) := by
    funext t
    simp only [hzdef, DtQ, covDsP, fam, famP, zero_smul, add_zero]
  have hzd : ∀ t ∈ Icc a b, HasDerivAt z
      (J'' t + dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) (J t)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w' t) (J t)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (J' t)) t := by
    intro t ht
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      (hu t ht).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (htgt t ht))
    have h1 := (hJ' t ht).add (hasDerivAt_chrB_fam_t (cov := cov) (x₀ := x₀)
      (u := u) (η := J) (w := w) (e := J') (w' := w') (t₀ := t) (hu t ht) (hw t ht) (hJ t ht)
      (htgt t ht) hstay)
    have hfe : (J' + fun s : ℝ => chrB cov x₀ ((extChartAt I x₀).symm (u s)) (w s) (J s))
        = fun s : ℝ => J' s + chrB cov x₀ ((extChartAt I x₀).symm (u s)) (w s) (J s) := by
      funext s; rfl
    rw [hfe] at h1
    rw [show (fun s : ℝ => J' s + chrB cov x₀ ((extChartAt I x₀).symm (u s)) (w s) (J s))
        = z from hzfun.symm] at h1
    simpa only [add_assoc] using h1
  have hzsys : ∀ t ∈ Icc a b, HasDerivAt z
      (-gammaOp (cov := cov) x₀ u w t (z t) - curvOp (cov := cov) x₀ u w t (J t)) t := by
    intro t ht
    have hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (htgt t ht)
    have hDtds : DtDsP cov x₀ u J w J' t
        = deriv z t + gammaOp (cov := cov) x₀ u w t (z t) := by
      have h1 : DtDsP cov x₀ u J w J' t
          = deriv z t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (z t) (w t) := by
        show deriv (fun r => covDsP cov x₀ u J w J' 0 r) t
            + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (covDsP cov x₀ u J w J' 0 t) (w t)
          = deriv (fun t => DtQ cov x₀ u J w J' t) t
            + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (DtQ cov x₀ u J w J' t) (w t)
        rfl
      have h2 : chrB cov x₀ ((extChartAt I x₀).symm (u t)) (z t) (w t)
          = gammaOp (cov := cov) x₀ u w t (z t) := by
        simp only [chrB, gammaOp_apply (cov := cov) hsrc]
      rw [h1, h2]
    have hcv : curvOp (cov := cov) x₀ u w t (J t)
        = chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) :=
      curvOp_apply (cov := cov) hsrc (J t)
    have hj := hjac t ht
    rw [hDtds] at hj
    refine (hzd t ht).congr_deriv ?_
    rw [hcv]
    have hderv : deriv z t
        = J'' t + dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) (J t)
          + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w' t) (J t)
          + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (J' t) := (hzd t ht).deriv
    have hj' : deriv z t + (gammaOp (cov := cov) x₀ u w t (z t)
          + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t)) = 0 := by
      simpa only [add_assoc] using hj
    have h3 : deriv z t
        = -(gammaOp (cov := cov) x₀ u w t (z t)
            + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t)) :=
      eq_neg_of_add_eq_zero_left hj'
    rw [← hderv, h3, neg_add]
    rw [sub_eq_add_neg]
  have hy : ∀ t ∈ Icc a b,
      HasDerivAt J (z t - gammaOp (cov := cov) x₀ u w t (J t)) t := by
    intro t ht
    have hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (htgt t ht)
    have hkey : z t - gammaOp (cov := cov) x₀ u w t (J t) = J' t := by
      have h1 : z t = J' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (J t) := by
        rw [hzfun]
      have h2 : chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (J t)
          = gammaOp (cov := cov) x₀ u w t (J t) := by
        simp only [chrB, gammaOp_apply (cov := cov) hsrc, christoffelEval_comm (cov := cov) htor
          x₀ ((extChartAt I x₀).symm (u t)) hsrc (J t) (w t)]
      rw [h1, h2, add_sub_cancel_right]
    exact (hJ t ht).congr_deriv hkey.symm
  have hz0' : z b = 0 := by rw [hzdef]; exact hz0
  have h := eqOn_zero_of_jacobiSys_Icc (cov := cov) (x₀ := x₀) (u := u) (w := w) hab.le hGc hRc
    hy hzsys hJt hz0'
  intro t ht
  exact (h t ht).1


/-! ## The global propagation: a Jacobi field with a double zero vanishes -/

/-- **A Jacobi field along a geodesic with `J t = 0` and `∇J t = 0` vanishes on `[0,t]`.** -/
theorem eqOn_zero_of_isJacobiAt_of_dual_zero
    (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)}
    (hJ : ∀ s, IsJacobiAt cov γ J s) (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : ∀ s, curveVelocity (I := I) γ s ≠ 0)
    {t : ℝ} (ht : 0 < t) (hJt : J t = 0) (hcov : covAlong cov J t = 0) :
    ∀ s ∈ Icc 0 t, J s = 0 := by
  classical
  obtain ⟨N, c, A, B, hc0, hcN, hmono, hpiece⟩ :=
    Submission.IndexFTC.exists_isJacobiPiece_cover (cov := cov) htor hJ hγ hne ht.le
  have hchain : ∀ j ≤ N, ∀ k ≤ j, c k ≤ c j := by
    intro j hj k hkj
    induction j with
    | zero => simp only [Nat.le_zero] at hkj; rw [hkj]
    | succ i ih =>
      rcases Nat.eq_or_lt_of_le hkj with h | h
      · rw [h]
      · have hi : i < N := Nat.lt_of_succ_le hj
        exact le_trans (ih (le_of_lt hi) (Nat.lt_succ_iff.mp h)) (hmono i hi)
  have step : ∀ m, m < N → (∀ s ∈ Icc (c (m + 1)) t, J s = 0)
      → (∀ s ∈ Icc (c m) t, J s = 0) := by
    intro m hm hP
    obtain ⟨x₀, u, w, w', Jc, Jc', Jc'', hA, hB, hγeq, hu, hw, hwc, htgt, hJcd, hJc1,
      hJcd', hJc2, hjac, hV, hZ⟩ := hpiece m hm
    have hcm1t : c (m + 1) ≤ t := le_trans (hchain N le_rfl (m + 1) (by omega)) (le_of_eq hcN)
    have hJm1 : J (c (m + 1)) = 0 := hP (c (m + 1)) ⟨le_rfl, hcm1t⟩
    have hA' : A m < c (m + 1) := lt_of_lt_of_le hA (hmono m hm)
    have hmemm1 : c (m + 1) ∈ Icc (A m) (B m) := ⟨hA'.le, hB.le⟩
    have hsrcm1 : γ (c (m + 1)) ∈ (chartAt H x₀).source := by
      rw [hγeq (c (m + 1)) hmemm1]
      exact mem_source_chartCurve (I := I) (htgt (c (m + 1)) hmemm1)
    have hJcm1 : Jc (c (m + 1)) = 0 := by
      have hfr := hV (c (m + 1)) hmemm1
      rw [hJm1] at hfr
      exact (frameVector_eq_zero_iff (I := I) hsrcm1 (Jc (c (m + 1)))).mp hfr.symm
    -- `DtQ` and `covAlong` vanish at `c (m+1)`
    have hboth : DtQ cov x₀ u Jc w Jc' (c (m + 1)) = 0 ∧
        covAlong cov J (c (m + 1)) = 0 := by
      rcases lt_or_eq_of_le hcm1t with hlt | heq
      · set δ : ℝ := min (t - c (m + 1)) (B m - c (m + 1)) / 2 with hδdef
        have hδpos : 0 < δ := by
          rw [hδdef]
          exact div_pos (lt_min (by linarith) (by linarith)) two_pos
        have hδt : c (m + 1) + δ ≤ t := by
          rw [hδdef]
          linarith [min_le_left (t - c (m + 1)) (B m - c (m + 1))]
        have hδB : c (m + 1) + δ ≤ B m := by
          rw [hδdef]
          linarith [min_le_right (t - c (m + 1)) (B m - c (m + 1))]
        have hJcv : ∀ s ∈ Ioo (c (m + 1)) (c (m + 1) + δ), Jc s = 0 := by
          intro s hs
          have hsroom : s ∈ Icc (A m) (B m) :=
            ⟨by linarith [hA, hmemm1.1, hs.1], le_trans hs.2.le hδB⟩
          have hJ0 : J s = 0 := hP s ⟨hs.1.le, le_trans hs.2.le hδt⟩
          have hsrc : γ s ∈ (chartAt H x₀).source := by
            rw [hγeq s hsroom]
            exact mem_source_chartCurve (I := I) (htgt s hsroom)
          have hfr := hV s hsroom
          rw [hJ0] at hfr
          exact (frameVector_eq_zero_iff (I := I) hsrc (Jc s)).mp hfr.symm
        have hJc'0 : Jc' (c (m + 1)) = 0 := by
          have hca : ContinuousAt Jc' (c (m + 1)) :=
            (hJc1.continuousWithinAt hmemm1).continuousAt
              (Icc_mem_nhds hA' hB)
          have ht1 : Tendsto Jc' (𝓝[>] (c (m + 1))) (𝓝 (Jc' (c (m + 1)))) :=
            hca.mono_left nhdsWithin_le_nhds
          have hmemN : Ioo (c (m + 1)) (c (m + 1) + δ) ∈ 𝓝[>] (c (m + 1)) :=
            Ioo_mem_nhdsGT (lt_add_of_pos_right _ hδpos)
          have hzero : (fun s : ℝ => Jc' s) =ᶠ[𝓝[>] (c (m + 1))] (fun _ => (0 : E)) := by
            filter_upwards [hmemN] with s hs
            have hsroom : s ∈ Icc (A m) (B m) :=
              ⟨by linarith [hA, hmemm1.1, hs.1], le_trans hs.2.le hδB⟩
            have hev : Jc =ᶠ[𝓝 s] (fun _ => (0 : E)) :=
              Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) (fun y hy => hJcv y hy)
            exact ((hJcd s hsroom).congr_of_eventuallyEq hev.symm).unique
              (hasDerivAt_const s (0 : E))
          exact tendsto_nhds_unique ht1
            (tendsto_const_nhds.congr' hzero.symm : Tendsto Jc' (𝓝[>] (c (m + 1))) (𝓝 (0 : E)))
        have hDtQ : DtQ cov x₀ u Jc w Jc' (c (m + 1)) = 0 := by
          have h1 : DtQ cov x₀ u Jc w Jc' (c (m + 1))
              = Jc' (c (m + 1)) + chrB cov x₀ ((extChartAt I x₀).symm (u (c (m + 1))))
                  (w (c (m + 1))) (Jc (c (m + 1))) := by
            simp only [DtQ, covDsP, fam, famP, zero_smul, add_zero]
          rw [h1, hJc'0, hJcm1, chrB_zero_snd, add_zero]
        refine ⟨hDtQ, ?_⟩
        rw [hZ (c (m + 1)) hmemm1, hDtQ]
        exact frameVector_zero' x₀ (γ (c (m + 1)))
      · have hcovm1 : covAlong cov J (c (m + 1)) = 0 := by
          rw [heq]; exact hcov
        refine ⟨?_, hcovm1⟩
        have hthis := hZ (c (m + 1)) hmemm1
        rw [hcovm1] at hthis
        exact (frameVector_eq_zero_iff (I := I) hsrcm1 _).mp hthis.symm
    obtain ⟨hDtQ, hcovm1⟩ := hboth
    rcases lt_or_eq_of_le (hmono m hm) with hltm | heqm
    · have hsub : ∀ s ∈ Icc (c m) (c (m + 1)), s ∈ Icc (A m) (B m) :=
        fun s hs => ⟨by linarith [hs.1, hA], by linarith [hs.2, hB]⟩
      have h := eqOn_zero_of_chartJacobi_Icc (cov := cov) htor x₀ hltm
        (fun s hs => hu s (hsub s hs)) (fun s hs => hw s (hsub s hs))
        (fun s hs => htgt s (hsub s hs))
        (fun s hs => hJcd s (hsub s hs)) (fun s hs => hJcd' s (hsub s hs))
        (fun s hs => hjac s (hsub s hs)) hJcm1 hDtQ
      intro s hs
      by_cases hsc : s ≤ c (m + 1)
      · have hsc' : Jc s = 0 := h s ⟨hs.1, hsc⟩
        have hfr := hV s (hsub s ⟨hs.1, hsc⟩)
        rw [hfr, hsc', frameVector_zero' (I := I) x₀ (γ s)]
      · exact hP s ⟨le_of_lt (lt_of_not_ge hsc), hs.2⟩
    · intro s hs
      rw [heqm] at hs
      exact hP s ⟨hs.1, hs.2⟩
  have key : ∀ d, ∀ m, N - m ≤ d → m ≤ N → (∀ s ∈ Icc (c m) t, J s = 0) := by
    intro d
    induction d with
    | zero =>
        intro m _ hm
        have hmN : m = N := by omega
        subst hmN
        intro s hs
        rw [hcN] at hs
        have hs' : s = t := le_antisymm (Set.mem_Icc.mp hs).2 (Set.mem_Icc.mp hs).1
        rw [hs']; exact hJt
    | succ d ih =>
        intro m hd hm
        rcases eq_or_lt_of_le hm with h | h
        · subst h
          intro s hs
          rw [hcN] at hs
          have hs' : s = t := le_antisymm (Set.mem_Icc.mp hs).2 (Set.mem_Icc.mp hs).1
          rw [hs']; exact hJt
        · exact step m h (fun u hu => ih (m + 1) (by omega) (by omega) u hu)
  intro s hs
  exact key N 0 (by omega) (Nat.zero_le N) s (hc0.symm ▸ hs)


/-- **Non-degeneracy of a conjugate Jacobi field**: a Jacobi field along a geodesic vanishing at `t`
and nontrivial on `(0,t)` has nonzero covariant derivative at `t`. -/
theorem covAlong_ne_zero_of_isJacobiAt
    (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)}
    (hJ : ∀ s, IsJacobiAt cov γ J s) (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : ∀ s, curveVelocity (I := I) γ s ≠ 0)
    {t : ℝ} (ht : 0 < t) (hJt : J t = 0)
    (hnontriv : ∃ s ∈ Ioo 0 t, J s ≠ 0) :
    covAlong cov J t ≠ 0 := by
  intro h0
  obtain ⟨s, hs, hsn⟩ := hnontriv
  exact hsn (eqOn_zero_of_isJacobiAt_of_dual_zero (cov := cov) htor hJ hγ hne ht hJt h0 s
    ⟨hs.1.le, hs.2.le⟩)

end

end Submission.IndexBackUnique
