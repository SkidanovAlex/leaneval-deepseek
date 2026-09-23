import Submission.BonnetMyers
import Submission.GeodesicSpeed
import Submission.Minimal
import Submission.GeodesicGlobal2
import Submission.Commons.Geometry.Manifold.pathELength_eq_ofReal_integral_of_enorm_eq_nonneg
import Submission.Commons.Analysis.Calculus.sq_intervalIntegral_le_length_mul_intervalIntegral_sq
import Submission.Commons.Analysis.Calculus.deriv_deriv_nonneg_of_isLocalMin

/-!
# Bonnet–Myers (the chart-local step)

This file turns the index-form computation of `Submission/BonnetMyers.lean` into a contradiction
argument: **a chart geodesic which is unit speed and minimising on `[0,L]` satisfies `L ≤ π`.**

The mechanism is the classical one.

* The straight-line variation `Ψ(s,t) = u t + s • η t` of the chart geodesic `u` (with `η` the
  chosen test field, vanishing at the endpoints) has energy
  `E(s) = ∫_0^L ⟪∂_tΨ, ∂_tΨ⟫ dt`.
* Minimality of the geodesic gives `E(s) ≥ L = E(0)` for every small `s` (the length of `Ψ_s` is at
  least `L`, and the length is at most `√(L E(s))` by Cauchy–Schwarz, so `L ≤ √(L E(s))`).
  Hence `0 ≤ E''(0)`.
* The index form (`BonnetMyers.famEnergy_second_deriv_eq`) gives `E''(0) = -2∫_0^L indexIntegrand`
  and the test-field estimate (`BonnetMyers.indexIntegrand_testField_integral`) gives
  `∫_0^L indexIntegrand ≥ (L² - π²)/(2L)`, so `E''(0) < 0` as soon as `L > π`.

The main theorem is `le_pi_of_minimising_chart_geodesic`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Length
open Submission.GeodesicSpeed
open Submission.Minimal
open Submission.Jacobi
open Submission.ChartCurv
open Submission.ChartConnection
open Submission.ChartBounds
open Submission.SecondVariation
open Submission.IndexForm
open Submission.IndexForm2
open Submission.BonnetMyers

namespace Submission.BonnetMyers2

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-! ## The chart curve of the straight-line variation -/

/-- The derivative in `t` of the straight-line family. -/
lemma hasDerivAt_fam_t {u η w e : ℝ → E} {s t : ℝ}
    (hu : HasDerivAt u (w t) t) (hη : HasDerivAt η (e t) t) :
    HasDerivAt (fun r : ℝ => fam u η s r) (famP w e s t) t := by
  have h1 : HasDerivAt (fun r : ℝ => s • η r) (s • e t) t := hη.const_smul s
  have h2 : HasDerivAt (fun r : ℝ => u r + s • η r) (w t + s • e t) t := by
    have h := hu.add h1
    have hfun : (fun r : ℝ => u r + s • η r) = u + (fun r : ℝ => s • η r) := by
      funext r; rfl
    rw [hfun]
    exact h
  simpa only [fam, famP] using h2

/-- **The speed of the curve of the straight-line variation** is the square root of the energy
integrand. -/
lemma curveSpeed_famCurve {x₀ : M} {u η w e : ℝ → E} {s t : ℝ}
    (hu : HasDerivAt u (w t) t) (hη : HasDerivAt η (e t) t)
    (htgt : fam u η s t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ r in 𝓝 t, fam u η s r ∈ (extChartAt I x₀).target) :
    curveSpeed (I := I) (famCurve (I := I) x₀ u η s) t
      = Real.sqrt (famG (I := I) x₀ u η w e s t) :=
  curveSpeed_chartCurve (I := I) (x₀ := x₀) (u := fam u η s) (t := t) (v := famP w e s t)
    (hasDerivAt_fam_t hu hη) htgt hstay

/-- **The chart curve of the straight-line variation is `C¹` on `[0,L]`.** -/
lemma contMDiffOn_famCurve {x₀ : M} {u η w e w' e' : ℝ → E} {s L : ℝ} (hL : 0 < L)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t)
    (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hstay : ∀ t ∈ Icc 0 L, fam u η s t ∈ (extChartAt I x₀).target) :
    CMDiff[Icc (0:ℝ) L] 1 (famCurve (I := I) x₀ u η s) := by
  have hs : UniqueDiffOn ℝ (Icc (0:ℝ) L) := uniqueDiffOn_Icc hL
  have hdiff : DifferentiableOn ℝ (fun t => fam u η s t) (Icc (0:ℝ) L) :=
    fun t ht => (hasDerivAt_fam_t (hu t ht) (hη t ht)).differentiableAt.differentiableWithinAt
  have hderiv : EqOn (derivWithin (fun t => fam u η s t) (Icc (0:ℝ) L))
      (fun t => famP w e s t) (Icc (0:ℝ) L) :=
    fun t ht => (hasDerivAt_fam_t (hu t ht) (hη t ht)).hasDerivWithinAt.derivWithin (hs t ht)
  have hcontP : ContinuousOn (fun t => famP w e s t) (Icc (0:ℝ) L) := by
    have h1 : ContinuousOn (fun t => s • e t) (Icc (0:ℝ) L) := (HasDerivAt.continuousOn he).const_smul s
    have h2 : ContinuousOn (fun t => w t + s • e t) (Icc (0:ℝ) L) :=
      HasDerivAt.continuousOn hw |>.add h1
    simpa only [famP] using h2
  have hcont : ContinuousOn (derivWithin (fun t => fam u η s t) (Icc (0:ℝ) L)) (Icc (0:ℝ) L) :=
    ContinuousOn.congr hcontP hderiv
  have hu' : ContDiffOn ℝ (1 : ℕ∞ω) (fun t => fam u η s t) (Icc (0:ℝ) L) :=
    (contDiffOn_one_iff_derivWithin hs).mpr ⟨hdiff, hcont⟩
  have hu'' : CMDiff[Icc (0:ℝ) L] 1 (fun t => fam u η s t) := contMDiffOn_iff_contDiffOn.mpr hu'
  have hmaps : MapsTo (fun t => fam u η s t) (Icc (0:ℝ) L) (extChartAt I x₀).target := hstay
  exact (contMDiffOn_extChartAt_symm (I := I) x₀).comp hu'' hmaps

/-! ## The slice of the family at a fixed `s` -/

lemma fam_mem_target {x₀ : M} {u η : ℝ → E} {a₁ a₂ L : ℝ}
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (L+2), fam u η s t ∈ (extChartAt I x₀).target)
    {s : ℝ} (hs : s ∈ Icc a₁ a₂) {t : ℝ} (ht : t ∈ Icc (0:ℝ) L) :
    fam u η s t ∈ (extChartAt I x₀).target :=
  hstay s hs t ⟨by linarith [ht.1], by linarith [ht.2]⟩

lemma continuousOn_famG_slice {x₀ : M} {u η w e : ℝ → E} {a₁ a₂ L : ℝ}
    (hu : ContinuousOn u (Icc (0:ℝ) L)) (hη : ContinuousOn η (Icc (0:ℝ) L))
    (hw : ContinuousOn w (Icc (0:ℝ) L)) (he : ContinuousOn e (Icc (0:ℝ) L))
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (L+2), fam u η s t ∈ (extChartAt I x₀).target)
    {s : ℝ} (hs : s ∈ Icc a₁ a₂) :
    ContinuousOn (fun t : ℝ => famG (I := I) x₀ u η w e s t) (Icc (0:ℝ) L) := by
  have hmem : ∀ q ∈ Icc a₁ a₂ ×ˢ Icc (0:ℝ) L,
      fam u η q.1 q.2 ∈ (extChartAt I x₀).target :=
    fun q hq => fam_mem_target hstay hq.1 hq.2
  have hmsrc : ∀ q ∈ Icc a₁ a₂ ×ˢ Icc (0:ℝ) L,
      famCurve (I := I) x₀ u η q.1 q.2 ∈ (chartAt H x₀).source :=
    fun q hq => mem_source_chartCurve (I := I) (hmem q hq)
  have h := continuousOn_famG (x₀ := x₀) (A := Icc a₁ a₂) (B := Icc (0:ℝ) L)
    hu hη hw he hmem hmsrc
  have hmap : ContinuousOn (fun t : ℝ => (s, t)) (Icc (0:ℝ) L) :=
    (continuousOn_const (c := s)).prodMk continuousOn_id
  have hcomp := h.comp hmap (fun t ht => ⟨hs, ht⟩)
  have hfun : (fun t : ℝ => famG (I := I) x₀ u η w e s t)
      = (fun q : ℝ × ℝ => famG (I := I) x₀ u η w e q.1 q.2) ∘ (fun t : ℝ => (s, t)) := rfl
  rw [hfun]
  exact hcomp

/-! ## The energy of a minimising variation -/

/-- **The energy is at least the length when the geodesic is minimising.**  For the straight-line
variation of a chart geodesic whose endpoints are fixed (`η 0 = η L = 0`), the energy `E(s)` of the
varied curve dominates `L = d(γ 0, γ L)`. -/
theorem le_famEnergy_of_minimising
    (_hmet : IsMetricCompatible cov) {x₀ : M} {L : ℝ} (hL : 0 < L)
    {u η w e w' e' : ℝ → E}
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hη0 : η 0 = 0) (hηL : η L = 0)
    {a₁ a₂ : ℝ} (_ha₁ : a₁ < 0) (_ha₂ : 0 < a₂)
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (L+2), fam u η s t ∈ (extChartAt I x₀).target)
    (hmin : Manifold.riemannianEDist I ((extChartAt I x₀).symm (u 0)) ((extChartAt I x₀).symm (u L))
      = ENNReal.ofReal L)
    {s : ℝ} (hs : s ∈ Icc a₁ a₂) :
    L ≤ famEnergy (I := I) x₀ u η w e L s := by
  have hstay_t : ∀ t ∈ Icc (0:ℝ) L, fam u η s t ∈ (extChartAt I x₀).target :=
    fun t ht => fam_mem_target hstay hs ht
  have hsub : Icc (0:ℝ) L ⊆ Icc (-1:ℝ) (L+2) := Icc_subset_Icc (by linarith) (by linarith)
  -- the varied curve is `C¹`
  have hγ : CMDiff[Icc (0:ℝ) L] 1 (famCurve (I := I) x₀ u η s) :=
    contMDiffOn_famCurve (x₀ := x₀) hL hu hη hw he hstay_t
  -- its endpoints
  have hγ0 : famCurve (I := I) x₀ u η s 0 = (extChartAt I x₀).symm (u 0) := by
    simp only [famCurve, fam]
    rw [hη0, smul_zero, add_zero]
  have hγL : famCurve (I := I) x₀ u η s L = (extChartAt I x₀).symm (u L) := by
    simp only [famCurve, fam]
    rw [hηL, smul_zero, add_zero]
  -- the neighbourhood form of the chart condition
  have hstay_nhds : ∀ t ∈ Icc (0:ℝ) L,
      ∀ᶠ r in 𝓝 t, fam u η s r ∈ (extChartAt I x₀).target := by
    intro t ht
    have htIoo : t ∈ Ioo (-1:ℝ) (L+2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htIoo)
      (fun r hr => hstay s hs r ⟨le_of_lt hr.1, le_of_lt hr.2⟩)
  -- the speed is the square root of the energy integrand, hence continuous
  have hcsq : ContinuousOn (fun t : ℝ => famG (I := I) x₀ u η w e s t) (Icc (0:ℝ) L) :=
    continuousOn_famG_slice (x₀ := x₀) (HasDerivAt.continuousOn hu) (HasDerivAt.continuousOn hη)
      (HasDerivAt.continuousOn hw) (HasDerivAt.continuousOn he) hstay hs
  have hsp : ContinuousOn (fun t : ℝ => curveSpeed (I := I) (famCurve (I := I) x₀ u η s) t)
      (Icc (0:ℝ) L) := by
    refine ContinuousOn.congr hcsq.sqrt (fun t ht => ?_)
    exact curveSpeed_famCurve (x₀ := x₀) (hu t ht) (hη t ht) (hstay_t t ht) (hstay_nhds t ht)
  have hspnn : ∀ t ∈ Icc (0:ℝ) L, 0 ≤ curveSpeed (I := I) (famCurve (I := I) x₀ u η s) t :=
    fun t ht => (curveSpeed_nonneg (I := I) _ t)
  -- the length of the varied curve, and the lower bound for it
  have hlen : Manifold.pathELength I (famCurve (I := I) x₀ u η s) 0 L
      = ENNReal.ofReal (∫ t in (0:ℝ)..L, curveSpeed (I := I) (famCurve (I := I) x₀ u η s) t) := by
    refine Commons.Geometry.Manifold.pathELength_eq_ofReal_integral_of_enorm_eq_nonneg
      (I := I) hL.le hsp.integrableOn_Icc ?_ ?_
    · exact hspnn
    · intro t ht
      show ‖curveVelocity (I := I) (famCurve (I := I) x₀ u η s) t‖ₑ
        = ENNReal.ofReal (curveSpeed (I := I) (famCurve (I := I) x₀ u η s) t)
      rw [enorm_eq_ofReal_norm,
        curveSpeed_eq_norm (I := I) (famCurve (I := I) x₀ u η s) t]
  have hLle : L ≤ ∫ t in (0:ℝ)..L, curveSpeed (I := I) (famCurve (I := I) x₀ u η s) t := by
    have h1 : Manifold.riemannianEDist I ((extChartAt I x₀).symm (u 0)) ((extChartAt I x₀).symm (u L))
        ≤ Manifold.pathELength I (famCurve (I := I) x₀ u η s) 0 L :=
      Manifold.riemannianEDist_le_pathELength hγ hγ0 hγL hL.le
    rw [hlen] at h1
    rw [hmin] at h1
    refine (ENNReal.ofReal_le_ofReal_iff ?_).mp h1
    exact intervalIntegral.integral_nonneg hL.le (fun t ht => hspnn t ht)
  -- Cauchy–Schwarz
  have hcs := Commons.Analysis.Calculus.sq_intervalIntegral_le_length_mul_intervalIntegral_sq
    (f := fun t : ℝ => curveSpeed (I := I) (famCurve (I := I) x₀ u η s) t) hL.le
    (by rwa [uIcc_of_le hL.le]) (by rw [uIcc_of_le hL.le]; exact hspnn)
  have hsq : ∫ t in (0:ℝ)..L, (curveSpeed (I := I) (famCurve (I := I) x₀ u η s) t) ^ 2
      = famEnergy (I := I) x₀ u η w e L s := by
    rw [famEnergy]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have h1 := curveSpeed_famCurve (x₀ := x₀) (hu t (by rwa [uIcc_of_le hL.le] at ht))
      (hη t (by rwa [uIcc_of_le hL.le] at ht))
      (hstay_t t (by rwa [uIcc_of_le hL.le] at ht))
      (hstay_nhds t (by rwa [uIcc_of_le hL.le] at ht))
    rw [h1]
    refine Real.sq_sqrt ?_
    rw [famG]
    exact chartGram_self_nonneg (I := I) x₀ (famCurve (I := I) x₀ u η s t) (famP w e s t)
  rw [hsq] at hcs
  have h2 : L * L ≤ L * famEnergy (I := I) x₀ u η w e L s := by
    calc L * L = L ^ 2 := by ring
      _ ≤ (∫ t in (0:ℝ)..L, curveSpeed (I := I) (famCurve (I := I) x₀ u η s) t) ^ 2 := by
          nlinarith [hLle, hL]
      _ ≤ L * famEnergy (I := I) x₀ u η w e L s := by rw [sub_zero] at hcs; exact hcs
  exact le_of_mul_le_mul_left h2 hL

/-! ## The chart speed is constant, and the energy at `s = 0` -/

/-- **The chart speed of a chart geodesic is constant** (on a closed interval; the general-interval
version is `GeodesicGlobal2.chartGram_const_of_chartODE`). -/
lemma chartGram_const_Icc [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov)
    {x₀ : M} {u w w' : ℝ → E} {L : ℝ} (hL : 0 ≤ L)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hgeo : ∀ t ∈ Icc 0 L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    (hstay : ∀ t ∈ Icc 0 L, u t ∈ (extChartAt I x₀).target) :
    ∀ t ∈ Icc 0 L, chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t)
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) (w 0) (w 0) := by
  have hderiv : ∀ t ∈ Icc (0:ℝ) L,
      HasDerivAt (fun r : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r)) (w r) (w r))
        0 t := by
    intro t ht
    have hstay' : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      (hu t ht).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hstay t ht))
    have h := hasDerivAt_chartGram_curve (cov := cov) hmet x₀ (hu t ht) (hstay t ht) hstay'
      (hw t ht) (hw t ht)
    refine h.congr_deriv ?_
    have hw't : w' t = -chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hgeo t ht
    rw [hw't, ← chrB_apply (cov := cov) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t)]
    rw [neg_add_cancel, Submission.Gauss.chartGram_zero_snd,
      Submission.Gauss.chartGram_zero_fst, add_zero]
  have hconst := Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc hL hderiv
  intro t ht
  rw [hconst t ht, hconst 0 ⟨le_rfl, hL⟩]

/-- **The energy of the straight-line variation at `s = 0`** is the length `L` of the unit-speed
geodesic. -/
lemma famEnergy_zero_eq [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov)
    {x₀ : M} {L : ℝ} (hL : 0 < L) {u η w e w' e' : ℝ → E}
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hgeo : ∀ t ∈ Icc 0 L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    (hstay : ∀ t ∈ Icc 0 L, u t ∈ (extChartAt I x₀).target)
    (hunit : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) (w 0) (w 0) = 1) :
    famEnergy (I := I) x₀ u η w e L 0 = L := by
  rw [famEnergy]
  have hval : ∀ t ∈ Icc (0:ℝ) L, famG (I := I) x₀ u η w e 0 t = 1 := by
    intro t ht
    have hc := chartGram_const_Icc (cov := cov) hmet hL.le hu hw hgeo hstay t ht
    simp only [famG, famCurve, fam, famP, zero_smul, add_zero]
    rw [hc, hunit]
  have h1 : ∫ t in (0:ℝ)..L, famG (I := I) x₀ u η w e 0 t = ∫ t in (0:ℝ)..L, (1:ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    exact hval t ht
  rw [h1, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]


/-! ## The first and second derivatives of the energy of a geodesic variation -/

/-- **The first variation vanishes at a geodesic.**  For a chart geodesic (unit speed is not needed)
the derivative at `s = 0` of the energy of the straight-line variation is zero, because `∇_tγ' = 0`
on the geodesic. -/
lemma famEnergy_deriv_zero [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {L : ℝ} (hL : 0 < L) {u η w e w' e' : ℝ → E}
    {a₁ a₂ : ℝ} (ha₁ : a₁ < 0) (ha₂ : 0 < a₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hwc : ContinuousOn w' (Icc 0 L)) (hec : ContinuousOn e' (Icc 0 L))
    (hη0 : η 0 = 0) (hηL : η L = 0)
    (hgeo : ∀ t ∈ Icc 0 L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (L+2), fam u η s t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s => famEnergy (I := I) x₀ u η w e L s) 0 0 := by
  have h := famEnergy_hasDerivAt (cov := cov) (hmet := hmet) (htor := htor) (x₀ := x₀) (L := L)
    hL.le (hu := hu) (hw := hw) (hη := hη) (he := he) (hwc := hwc) (hec := hec)
    (a₁ := a₁) (a₂ := a₂) (δ₁ := a₁ / 2) (δ₂ := a₂ / 2) (s₀ := 0)
    (by linarith) (by linarith) (by linarith) (by linarith) hη0 hηL hstay
  refine h.congr_deriv ?_
  have hz : ∀ t ∈ Icc (0:ℝ) L, famK cov x₀ u η w e w' e' 0 t = 0 := by
    intro t ht
    rw [famK, covDtP_eq_zero_of_geodesic (cov := cov) (hgeo t ht)]
    exact Submission.Gauss.chartGram_zero_snd (I := I) x₀ _ _
  have h1 : (∫ t in (0:ℝ)..L, famK cov x₀ u η w e w' e' 0 t) = ∫ t in (0:ℝ)..L, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    exact hz t ht
  rw [h1, intervalIntegral.integral_zero, mul_zero]

/-- **The second derivative of the energy of a geodesic variation is the index form.** -/
lemma famEnergy_deriv_second_zero [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {L : ℝ} (hL : 0 < L) {u η w e w' e' : ℝ → E}
    {a₁ a₂ : ℝ} (ha₁ : a₁ < 0) (ha₂ : 0 < a₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hwc : ContinuousOn w' (Icc 0 L)) (hec : ContinuousOn e' (Icc 0 L))
    (hη0 : η 0 = 0) (hηL : η L = 0)
    (hgeo : ∀ t ∈ Icc 0 L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (L+2), fam u η s t ∈ (extChartAt I x₀).target) :
    HasDerivAt (deriv (fun s => famEnergy (I := I) x₀ u η w e L s))
      (-2 * ∫ t in (0:ℝ)..L, indexIntegrand cov x₀ u η w e t) 0 := by
  have hmem : ∀ s ∈ Ioo a₁ a₂,
      deriv (fun s => famEnergy (I := I) x₀ u η w e L s) s
        = famEnergyDeriv cov x₀ u η w e w' e' L s := by
    intro s hs
    have h := famEnergy_hasDerivAt (cov := cov) (hmet := hmet) (htor := htor) (x₀ := x₀) (L := L)
      hL.le (hu := hu) (hw := hw) (hη := hη) (he := he) (hwc := hwc) (hec := hec)
      (a₁ := a₁) (a₂ := a₂) (δ₁ := (a₁ + s) / 2) (δ₂ := (s + a₂) / 2) (s₀ := s)
      (by linarith [hs.1]) (by linarith [hs.2]) (by linarith [hs.1]) (by linarith [hs.2])
      hη0 hηL hstay
    exact h.deriv
  have hev : deriv (fun s => famEnergy (I := I) x₀ u η w e L s)
      =ᶠ[𝓝 (0:ℝ)] famEnergyDeriv cov x₀ u η w e w' e' L :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds ha₁ ha₂) (fun s hs => hmem s hs)
  have h2 := famEnergy_second_deriv_eq (cov := cov) hmet htor x₀ hL ha₁ ha₂ hu hw hη he hwc hec
    hη0 hηL hgeo hstay
  exact hev.hasDerivAt_iff.mpr h2


/-! ## The local minimum, and the main theorem -/

/-- **The energy of the straight-line variation has a local minimum at `s = 0`** when the chart
geodesic is minimising. -/
lemma isLocalMin_famEnergy [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov)
    {x₀ : M} {L : ℝ} (hL : 0 < L) {u η w e w' e' : ℝ → E}
    {a₁ a₂ : ℝ} (ha₁ : a₁ < 0) (ha₂ : 0 < a₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hη0 : η 0 = 0) (hηL : η L = 0)
    (hgeo : ∀ t ∈ Icc 0 L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (L+2), fam u η s t ∈ (extChartAt I x₀).target)
    (hstay_u : ∀ t ∈ Icc 0 L, u t ∈ (extChartAt I x₀).target)
    (hunit : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) (w 0) (w 0) = 1)
    (hmin : Manifold.riemannianEDist I ((extChartAt I x₀).symm (u 0)) ((extChartAt I x₀).symm (u L))
      = ENNReal.ofReal L) :
    IsLocalMin (fun s => famEnergy (I := I) x₀ u η w e L s) 0 := by
  have h0 : famEnergy (I := I) x₀ u η w e L 0 = L :=
    famEnergy_zero_eq (cov := cov) (e' := e') hmet hL hu hw hgeo hstay_u hunit
  refine Filter.eventually_of_mem (Icc_mem_nhds ha₁ ha₂) (fun s hs => ?_)
  show famEnergy (I := I) x₀ u η w e L 0 ≤ famEnergy (I := I) x₀ u η w e L s
  rw [h0]
  exact le_famEnergy_of_minimising hmet hL hu hw hη he hη0 hηL ha₁ ha₂ hstay hmin hs

/-- **Bonnet–Myers, chart-local form.**  A chart geodesic which is unit speed and minimising on
`[0,L]`, and for which a variation field with the sine-test-field property exists (expressed by the
index integral bound `hInt`), satisfies `L ≤ π`. -/
theorem le_pi_of_minimising_chart_geodesic [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x₀ : M} {L : ℝ} (hL : 0 < L) {u η w e w' e' : ℝ → E}
    {a₁ a₂ : ℝ} (ha₁ : a₁ < 0) (ha₂ : 0 < a₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (he : ∀ t ∈ Icc 0 L, HasDerivAt e (e' t) t)
    (hwc : ContinuousOn w' (Icc 0 L)) (hec : ContinuousOn e' (Icc 0 L))
    (hη0 : η 0 = 0) (hηL : η L = 0)
    (hgeo : ∀ t ∈ Icc 0 L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (L+2), fam u η s t ∈ (extChartAt I x₀).target)
    (hstay_u : ∀ t ∈ Icc 0 L, u t ∈ (extChartAt I x₀).target)
    (hunit : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) (w 0) (w 0) = 1)
    (hmin : Manifold.riemannianEDist I ((extChartAt I x₀).symm (u 0)) ((extChartAt I x₀).symm (u L))
      = ENNReal.ofReal L)
    (hInt : (L ^ 2 - Real.pi ^ 2) / (2 * L)
      ≤ ∫ t in (0:ℝ)..L, indexIntegrand cov x₀ u η w e t) :
    L ≤ Real.pi := by
  by_contra hcon
  push Not at hcon
  have hE1 : HasDerivAt (fun s => famEnergy (I := I) x₀ u η w e L s) 0 0 :=
    famEnergy_deriv_zero hmet htor x₀ hL ha₁ ha₂ hu hw hη he hwc hec hη0 hηL hgeo hstay
  have hE2 : HasDerivAt (deriv (fun s => famEnergy (I := I) x₀ u η w e L s))
      (-2 * ∫ t in (0:ℝ)..L, indexIntegrand cov x₀ u η w e t) 0 :=
    famEnergy_deriv_second_zero hmet htor x₀ hL ha₁ ha₂ hu hw hη he hwc hec hη0 hηL hgeo hstay
  have hmin' := isLocalMin_famEnergy (cov := cov) (w' := w') (e' := e') hmet hL ha₁ ha₂ hu hw hη he
    hη0 hηL hgeo hstay hstay_u hunit hmin
  have hnonneg := Commons.Analysis.Calculus.deriv_deriv_nonneg_of_isLocalMin hE1 hE2 hmin'
  have hpos : 0 < (L ^ 2 - Real.pi ^ 2) / (2 * L) := by
    have h1 : Real.pi ^ 2 < L ^ 2 := by
      have hpi := Real.pi_pos
      nlinarith [hcon]
    exact div_pos (by linarith) (by linarith)
  linarith

end

end Submission.BonnetMyers2