import Submission.IndexBackUnique
import Submission.Work.Diff.C.JacobiLogDeriv

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniqueness for the Jacobi system with data at an *interior* point

The library has `Submission.IndexBackUnique.eqOn_zero_of_jacobiSys_Icc` /
`eqOn_zero_of_chartJacobi_Icc`, which give uniqueness for the chart Jacobi system on an interval
`Icc a b` with the (zero) data prescribed at the **right** endpoint `b`.  For the propagation
argument of `Work.Diff.C.isJacobiAt_eq_of_data` (two Jacobi fields agreeing at one time are equal,
proved by showing that the set of times near which they agree is *open and closed*) what is needed is
the same uniqueness with the data at an **arbitrary point** `t₀ ∈ Icc a b` of the interval: if two
solutions of the linear system `y' = z - Γ(w)y`, `z' = -Γ(w)z - R(y,w)w` agree at an interior point
then they agree on the whole interval (this is `Commons.Analysis.ODE.eqOn_of_hasDerivAt_linearODE`,
which is stated for an arbitrary base point `t₀ ∈ Icc a b`; the library just specialises it to the
right endpoint because that is what its callers needed).

This file provides the two interior-point forms:

* `Work.Diff.C.eqOn_zero_of_jacobiSys_interior` — the first-order system;
* `Work.Diff.C.eqOn_zero_of_chartJacobi_interior` — the second-order chart form, obtained from the
  first by the reduction `z = DtQ = D(Dy)` of `Submission.JacobiAtSystem`/`IndexBackUnique`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
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
open Submission.JacobiAtSystem

namespace Work.Diff.C

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

/-- **Uniqueness for the Jacobi system, with data at an arbitrary point of the interval.**  If
`(y, z)` solves `y' = z - Γ(w)y`, `z' = -Γ(w)z - R(y,w)w` on `Icc a b` and vanishes at some
`t₀ ∈ Icc a b`, then it vanishes on the whole of `Icc a b`. -/
theorem eqOn_zero_of_jacobiSys_interior {x₀ : M} {u w : ℝ → E} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b)
    (hGc : ContinuousOn (fun t : ℝ => gammaOp (cov := cov) x₀ u w t) (Icc a b))
    (hRc : ContinuousOn (fun t : ℝ => curvOp (cov := cov) x₀ u w t) (Icc a b))
    {y z : ℝ → E}
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (z t - gammaOp (cov := cov) x₀ u w t (y t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (-gammaOp (cov := cov) x₀ u w t (z t)
      - curvOp (cov := cov) x₀ u w t (y t)) t)
    (hy0 : y t₀ = 0) (hz0 : z t₀ = 0) :
    ∀ t ∈ Icc a b, y t = 0 ∧ z t = 0 := by
  classical
  have hab : a ≤ b := le_trans ht₀.1 ht₀.2
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
  have hY0 : Y t₀ = (fun _ : ℝ => (0 : E × E)) t₀ := by
    rw [hYdef]
    simp only [hy0, hz0]
    rfl
  have hEq := Commons.Analysis.ODE.eqOn_of_hasDerivAt_linearODE
    (A := fun t => jacobiSysVec (cov := cov) x₀ u w t)
    (M := M) hAbound ht₀ hYode hZode hY0
  intro t ht
  have h := hEq ht
  rw [show (fun _ : ℝ => (0 : E × E)) t = 0 from rfl] at h
  simp only [hYdef, Prod.mk_eq_zero] at h
  exact h

/-- **A chart Jacobi field vanishing with its `DtQ`-derivative at an arbitrary point of the interval
is zero on the whole interval.**  Interior-point form of
`Submission.IndexBackUnique.eqOn_zero_of_chartJacobi_Icc`. -/
theorem eqOn_zero_of_chartJacobi_interior [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (x₀ : M)
    {u w w' J J' J'' : ℝ → E} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Icc a b, HasDerivAt w (w' t) t)
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target)
    (hJ : ∀ t ∈ Icc a b, HasDerivAt J (J' t) t)
    (hJ' : ∀ t ∈ Icc a b, HasDerivAt J' (J'' t) t)
    (hjac : ∀ t ∈ Icc a b, DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0)
    (hJt : J t₀ = 0) (hz0 : DtQ cov x₀ u J w J' t₀ = 0) :
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
  have hz0' : z t₀ = 0 := by rw [hzdef]; exact hz0
  have h := eqOn_zero_of_jacobiSys_interior (cov := cov) (x₀ := x₀) (u := u) (w := w) ht₀ hGc hRc
    hy hzsys hJt hz0'
  intro t ht
  exact (h t ht).1

/-! ## Linearity of `covAlong` in the field, and `covAlong = 0` for a field vanishing near `t` -/

/-- `chrB` is additive in its second slot (derived form). -/
lemma chrB_sub_snd (x₀ p : M) (a b₁ b₂ : E) :
    chrB cov x₀ p a (b₁ - b₂) = chrB cov x₀ p a b₁ - chrB cov x₀ p a b₂ := by
  have h1 : chrB cov x₀ p a (-b₂) = -chrB cov x₀ p a b₂ := by
    simpa using chrB_smul_snd (x₀ := x₀) (p := p) (c := (-1 : ℝ)) (a := a) (b := b₂)
  rw [sub_eq_add_neg, chrB_add_snd, h1, sub_eq_add_neg]

/-- The value of `DtQ` in terms of the values at `t`: only the values `u t`, `w t`, `η t`, `e t`
matter. -/
lemma DtQ_apply' {x₀ : M} {u w η e : ℝ → E} {t : ℝ} :
    DtQ cov x₀ u η w e t
      = e t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (η t) := by
  simp only [DtQ, covDsP, fam, famP, zero_smul, add_zero]

/-- `DtQ` is linear in the pair (field, field derivative). -/
lemma DtQ_sub {x₀ : M} {u w : ℝ → E} {η₁ η₂ e₁ e₂ : ℝ → E} {t : ℝ} :
    DtQ cov x₀ u (fun s => η₁ s - η₂ s) w (fun s => e₁ s - e₂ s) t
      = DtQ cov x₀ u η₁ w e₁ t - DtQ cov x₀ u η₂ w e₂ t := by
  simp only [DtQ, covDsP, fam, famP, zero_smul, add_zero]
  rw [chrB_sub_snd]
  abel

/-- **`covAlong` is linear in the field**: the covariant derivative along `γ` of a difference is the
difference of the covariant derivatives.  (Both sides are written in the chart at `γ t`, and
`chartCoords`, `deriv` and `DtQ` are all linear in the field.) -/
theorem covAlong_sub (htor : cov.torsion = 0) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    {J Z : (t : ℝ) → TangentSpace I (γ t)} (hJ : ∀ s, IsJacobiAt cov γ J s)
    (hZ : ∀ s, IsJacobiAt cov γ Z s) (t : ℝ) :
    covAlong cov (fun s : ℝ => J s - Z s) t = covAlong cov J t - covAlong cov Z t := by
  -- the chart at `γ t` carries the coordinates of all three fields
  have htI : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hγc : ContinuousAt γ t := hγ.continuous.continuousAt
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (eventually_mem_source_self (H := H) hγc)
  set ε : ℝ := min δ 1 / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hεδ : ε < δ := by
    rw [hεdef]; have : min δ 1 ≤ δ := min_le_left _ _; linarith
  have hε1 : ε < 1 := by
    rw [hεdef]; have : min δ 1 ≤ 1 := min_le_right _ _; linarith
  have hsub : Ioo (t - ε) (t + ε) ⊆ Ioo (t - 1) (t + 1) := by
    intro s hs
    exact ⟨by linarith [hs.1, hε1], by linarith [hs.2, hε1]⟩
  have hsrcU : ∀ s ∈ Ioo (t - ε) (t + ε), γ s ∈ (chartAt H (γ t)).source := by
    intro s hs
    refine hδsub ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hs.1, hεδ], by linarith [hs.2, hεδ]⟩
  have hcdJ : ContDiffOn ℝ ∞ (chartCoords (I := I) (γ t) γ J) (Ioo (t - ε) (t + ε)) :=
    contDiffOn_chartCoords_of_isJacobiAt (cov := cov) htor isOpen_Ioo (hγ.contMDiffOn.mono hsub)
      hsrcU (fun s _ => hJ s)
  have hcdZ : ContDiffOn ℝ ∞ (chartCoords (I := I) (γ t) γ Z) (Ioo (t - ε) (t + ε)) :=
    contDiffOn_chartCoords_of_isJacobiAt (cov := cov) htor isOpen_Ioo (hγ.contMDiffOn.mono hsub)
      hsrcU (fun s _ => hZ s)
  have hdiffJ : DifferentiableAt ℝ (chartCoords (I := I) (γ t) γ J) t :=
    (hcdJ.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds
      ⟨by linarith, by linarith⟩)
  have hdiffZ : DifferentiableAt ℝ (chartCoords (I := I) (γ t) γ Z) t :=
    (hcdZ.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds
      ⟨by linarith, by linarith⟩)
  have hcoords : chartCoords (I := I) (γ t) γ (fun s : ℝ => J s - Z s)
      = chartCoords (I := I) (γ t) γ J - chartCoords (I := I) (γ t) γ Z := by
    funext s
    simp only [Pi.sub_apply, chartCoords, map_sub]
  have hderiv : deriv (chartCoords (I := I) (γ t) γ (fun s : ℝ => J s - Z s)) t
      = deriv (chartCoords (I := I) (γ t) γ J) t
        - deriv (chartCoords (I := I) (γ t) γ Z) t := by
    rw [hcoords]
    exact deriv_sub hdiffJ hdiffZ
  have hval : chartCoords (I := I) (γ t) γ (fun s : ℝ => J s - Z s) t
      = chartCoords (I := I) (γ t) γ J t - chartCoords (I := I) (γ t) γ Z t := by
    rw [hcoords]
    rfl
  rw [covAlong, covAlong, covAlong]
  simp only [DtQ_apply', hderiv, hval, chrB_sub_snd, frameVector_add, frameVector_sub]
  abel

/-- **`covAlong` vanishes at `t` if the field vanishes near `t`.** -/
theorem covAlong_eq_zero_of_eventuallyEq_zero (htor : cov.torsion = 0) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ) {W : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hW : W =ᶠ[𝓝 t] 0) : covAlong cov W t = 0 := by
  have htI : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hγc : ContinuousAt γ t := hγ.continuous.continuousAt
  have hsrcEv : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H (γ t)).source :=
    eventually_mem_source_self (H := H) hγc
  have hcoordsEv : chartCoords (I := I) (γ t) γ W =ᶠ[𝓝 t] (fun _ : ℝ => (0 : E)) := by
    filter_upwards [hW, hsrcEv] with s hs hsrc
    exact (frameVector_eq_zero_iff (I := I) hsrc
      (chartCoords (I := I) (γ t) γ W s)).mp (by
        rw [frameVector_chartCoords (I := I) hsrc]
        exact hs)
  have hderiv : deriv (chartCoords (I := I) (γ t) γ W) t = 0 := by
    rw [hcoordsEv.deriv_eq]
    simp
  have hval : chartCoords (I := I) (γ t) γ W t = 0 := hcoordsEv.self_of_nhds
  rw [covAlong, DtQ_apply', hderiv, hval, chrB_zero_snd, add_zero]
  exact frameVector_zero' (I := I) (γ t) (γ t)

/-! ## The local and global propagation for a Jacobi field with a double zero -/

/-- **Local uniqueness at a point, with the data at an *interior* point.**  If `W` is a Jacobi field
along `γ` and `t` is any time, there is a window `(t - η, t + η)` such that if `W` (together with its
covariant derivative) vanishes at some point `s` of the window, then `W` vanishes on the whole
window.  (`s` may be `t` itself; for `s = t` this is the local uniqueness of the Jacobi equation from
initial data at `t`.) -/
theorem exists_window_of_dual_zero (htor : cov.torsion = 0) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {W : (t : ℝ) → TangentSpace I (γ t)}
    (hW : ∀ s, IsJacobiAt cov γ W s) (t : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ s ∈ Ioo (t - η) (t + η), W s = 0 → covAlong cov W s = 0 →
      ∀ r ∈ Ioo (t - η) (t + η), W r = 0 := by
  obtain ⟨x₀, η₀, hη₀pos, -, hsrc, hcdU, hcdJ, hframe, hjeq⟩ :=
    Submission.JacobiCoordsEq.exists_chartCoords_contDiffOn_eq (cov := cov) htor (γ := γ) (J := W)
      (s := t) (ε := 1) one_pos hγ.contMDiffOn (hW t)
  set a : ℝ := t - η₀ / 2 with hadef
  set b : ℝ := t + η₀ / 2 with hbdef
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have hsub : Icc a b ⊆ Icc (t - η₀) (t + η₀) := by
    intro r hr
    rw [hadef] at hr; rw [hbdef] at hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hsubO : Icc a b ⊆ Ioo (t - η₀) (t + η₀) := by
    intro r hr
    rw [hadef] at hr; rw [hbdef] at hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  -- `C^∞` on the open window (from `C^∞` on the closed one)
  have hmemb : ∀ x ∈ Ioo (t - η₀) (t + η₀), Icc (t - η₀) (t + η₀) ∈ 𝓝 x :=
    fun x hx => Icc_mem_nhds (by linarith [hx.1]) (by linarith [hx.2])
  have hcdU' : ContDiffOn ℝ ∞
      (Submission.IntrinsicVariation.chartCoord (I := I) x₀ γ) (Ioo (t - η₀) (t + η₀)) := by
    rw [isOpen_Ioo.contDiffOn_iff]
    intro x hx
    exact ((hcdU.contDiffWithinAt (⟨by linarith [hx.1], by linarith [hx.2]⟩ :
      x ∈ Icc (t - η₀) (t + η₀))).contDiffAt (hmemb x hx))
  have hcdJ' : ContDiffOn ℝ ∞ (chartCoords (I := I) x₀ γ W) (Ioo (t - η₀) (t + η₀)) := by
    rw [isOpen_Ioo.contDiffOn_iff]
    intro x hx
    exact ((hcdJ.contDiffWithinAt (⟨by linarith [hx.1], by linarith [hx.2]⟩ :
      x ∈ Icc (t - η₀) (t + η₀))).contDiffAt (hmemb x hx))
  have hcdU'' : ContDiffOn ℝ ∞
      (deriv (Submission.IntrinsicVariation.chartCoord (I := I) x₀ γ)) (Ioo (t - η₀) (t + η₀)) :=
    hcdU'.deriv_of_isOpen isOpen_Ioo (le_of_eq (by simp))
  have hcdJ'' : ContDiffOn ℝ ∞
      (deriv (chartCoords (I := I) x₀ γ W)) (Ioo (t - η₀) (t + η₀)) :=
    hcdJ'.deriv_of_isOpen isOpen_Ioo (le_of_eq (by simp))
  refine ⟨η₀ / 2, by linarith, ?_⟩
  intro s hs hWs hcov
  have hsI : s ∈ Icc a b := by
    rw [hadef, hbdef]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsIo : s ∈ Ioo (t - η₀) (t + η₀) := hsubO hsI
  -- the data of the field at `s`
  have hy0 : chartCoords (I := I) x₀ γ W s = 0 := by
    have hsrcs : γ s ∈ (chartAt H x₀).source := hsrc s (hsub hsI)
    exact (frameVector_eq_zero_iff (I := I) hsrcs
      (chartCoords (I := I) x₀ γ W s)).mp (by
        rw [frameVector_chartCoords (I := I) hsrcs]
        exact hWs)
  have hz0 : DtQ cov x₀ (Submission.IntrinsicVariation.chartCoord (I := I) x₀ γ)
      (chartCoords (I := I) x₀ γ W)
      (deriv (Submission.IntrinsicVariation.chartCoord (I := I) x₀ γ))
      (deriv (chartCoords (I := I) x₀ γ W)) s = 0 := by
    refine (frameVector_eq_zero_iff (I := I) (hsrc s (hsub hsI)) _).mp ?_
    have hsmooth : SmoothAlongAt (I := I) γ W s :=
      smoothAlongAt_of_isJacobiAt (cov := cov) htor hW (hγ.contMDiffOn.mono (fun x _ => trivial))
    have hsrcEv : ∀ᶠ r in 𝓝 s, γ r ∈ (chartAt H x₀).source :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hsIo)
        (fun r hr => hsrc r ⟨le_of_lt hr.1, le_of_lt hr.2⟩)
    have huTgt : ∀ᶠ r in 𝓝 s,
        Submission.IntrinsicVariation.chartCoord (I := I) x₀ γ r ∈ (extChartAt I x₀).target := by
      filter_upwards [hsrcEv] with r hr
      exact (extChartAt I x₀).map_source (by rwa [extChartAt_source])
    have hγeq : γ =ᶠ[𝓝 s] fun r =>
        (extChartAt I x₀).symm (Submission.IntrinsicVariation.chartCoord (I := I) x₀ γ r) := by
      filter_upwards [hsrcEv] with r hr
      exact (PartialEquiv.left_inv (extChartAt I x₀) (by rwa [extChartAt_source])).symm
    have hu : ∀ᶠ r in 𝓝 s, HasDerivAt (Submission.IntrinsicVariation.chartCoord (I := I) x₀ γ)
        (deriv (Submission.IntrinsicVariation.chartCoord (I := I) x₀ γ) r) r :=
      eventually_hasDerivAt_of_contDiffOn isOpen_Ioo hsIo hcdU'
    have hyv : ∀ᶠ r in 𝓝 s,
        frameVector (I := I) x₀ (γ r) (chartCoords (I := I) x₀ γ W r) = W r :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hsIo)
        (fun r hr => hframe r ⟨le_of_lt hr.1, le_of_lt hr.2⟩)
    have hy' : ∀ᶠ r in 𝓝 s, HasDerivAt (chartCoords (I := I) x₀ γ W)
        (deriv (chartCoords (I := I) x₀ γ W) r) r :=
      eventually_hasDerivAt_of_contDiffOn isOpen_Ioo hsIo hcdJ'
    have h := Submission.JacobiGlobal.covAlong_eq_chart (cov := cov) htor (γ := γ) (V := W)
      (t := s) (hγ.contMDiffOn.mono (fun x _ => trivial))
      (by intro hzero; exact absurd hzero (hne s)) hsmooth (hsrc s (hsub hsI)) hsrcEv huTgt hγeq hu
      hyv hy'
    rw [← h, hcov]
  have hzero := eqOn_zero_of_chartJacobi_interior (cov := cov) htor x₀ (ht₀ := hsI)
    (fun r hr => (eventually_hasDerivAt_of_contDiffOn isOpen_Ioo (hsubO hr) hcdU').self_of_nhds)
    (fun r hr => (eventually_hasDerivAt_of_contDiffOn isOpen_Ioo (hsubO hr) hcdU'').self_of_nhds)
    (fun r hr => (extChartAt I x₀).map_source (by
      rw [extChartAt_source]; exact hsrc r (hsub hr)))
    (fun r hr => (eventually_hasDerivAt_of_contDiffOn isOpen_Ioo (hsubO hr) hcdJ').self_of_nhds)
    (fun r hr => (eventually_hasDerivAt_of_contDiffOn isOpen_Ioo (hsubO hr) hcdJ'').self_of_nhds)
    (fun r hr => hjeq r (hsub hr)) hy0 hz0
  intro r hr
  have hrI : r ∈ Icc a b := ⟨by rw [hadef]; linarith [hr.1], by rw [hbdef]; linarith [hr.2]⟩
  rw [← hframe r (hsub hrI), hzero r hrI]
  exact frameVector_zero' (I := I) x₀ (γ r)

/-- **Global uniqueness from a double zero at one point.**  If a Jacobi field `W` along `γ` vanishes
together with its covariant derivative at a single time `t₀`, then it vanishes identically.
(The proof is the standard connectedness argument: the set of times near which `W` vanishes is open
and closed, and nonempty.) -/
theorem eq_of_dual_zero (htor : cov.torsion = 0) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {W : (t : ℝ) → TangentSpace I (γ t)} (hW : ∀ s, IsJacobiAt cov γ W s) {t₀ : ℝ}
    (hv : W t₀ = 0) (hd : covAlong cov W t₀ = 0) : ∀ t : ℝ, W t = 0 := by
  set A : Set ℝ := {t | W =ᶠ[𝓝 t] 0} with hAdef
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨U, hU, hWU⟩ := Filter.eventually_iff_exists_mem.mp ht
    obtain ⟨V, hVU, hVopen, htV⟩ := _root_.mem_nhds_iff.mp hU
    refine Filter.mem_of_superset (hVopen.mem_nhds htV) ?_
    intro s hsV
    exact Filter.eventually_of_mem (hVopen.mem_nhds hsV) (fun r hr => hWU r (hVU hr))
  have hAclosed : IsClosed A := by
    rw [← closure_subset_iff_isClosed]
    intro t ht
    obtain ⟨η, hηpos, hη⟩ := exists_window_of_dual_zero (cov := cov) htor hγ hne hW t
    obtain ⟨s, hsI, hsA⟩ := (_root_.mem_closure_iff.mp ht) (Ioo (t - η) (t + η)) isOpen_Ioo
      ⟨by linarith, by linarith⟩
    have hWs : W s = 0 := hsA.self_of_nhds
    have hcs : covAlong cov W s = 0 :=
      covAlong_eq_zero_of_eventuallyEq_zero (cov := cov) htor hγ hsA
    have hz := hη s hsI hWs hcs
    exact Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
      (fun r hr => hz r hr)
  have hAmem : t₀ ∈ A := by
    obtain ⟨η, hηpos, hη⟩ := exists_window_of_dual_zero (cov := cov) htor hγ hne hW t₀
    exact Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
      (fun r hr => hη t₀ ⟨by linarith, by linarith⟩ hv hd r hr)
  have hAne : A.Nonempty := ⟨t₀, hAmem⟩
  have hAuniv : A = Set.univ :=
    (isClopen_iff.mp ⟨hAclosed, hAopen⟩).resolve_left hAne.ne_empty
  intro t
  have ht : t ∈ A := by rw [hAuniv]; trivial
  exact ht.self_of_nhds

end

end Work.Diff.C
