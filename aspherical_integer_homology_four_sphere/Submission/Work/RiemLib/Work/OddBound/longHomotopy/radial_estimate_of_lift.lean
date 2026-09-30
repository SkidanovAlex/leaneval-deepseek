import Mathlib
import Submission.Work.RiemLib.RauchK
import Submission.Work.RiemLib.Geodesic
import Submission.Work.RiemLib.GeodesicSpeed
import Submission.Work.RiemLib.Length
import Submission.Work.RiemLib.Distance
import Submission.Work.RiemLib.InjRadius
import Submission.Work.RiemLib.InjBall
import Submission.Work.RiemLib.SegmentDomain
import Submission.Work.RiemLib.XuMain
import Submission.Work.RiemLib.EDist
import Submission.Work.RiemLib.GExpRay2
import Submission.Work.RiemLib.GExpJoint
import Submission.Work.RiemLib.GExpFlow
import Submission.Work.RiemLib.Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt
import Submission.Work.RiemLib.GeodesicGlobal
import Submission.Work.RiemLib.GExpLocalInj
import Submission.Work.RiemLib.CutStep2
import Submission.Work.RiemLib.XuLift
import Submission.Work.RiemLib.ChartPieces
import Submission.Work.RiemLib.ChartIndep
import Submission.Work.RiemLib.CoeffSmooth2
import Submission.Work.RiemLib.JacobiGlobal
import Submission.Work.RiemLib.Commons.Analysis.ODE.exists_linearODE_solution_Icc
import Submission.Work.RiemLib.IndexCorner2
import Submission.Work.RiemLib.InjHalf
import Submission.Work.RiemLib.LensLoop
import Submission.Work.RiemLib.UniformInj
import Submission.Work.RiemLib.ConjRadius
import Submission.Work.RiemLib.ConjCut
import Submission.Work.RiemLib.SingularConj
import Submission.Work.RiemLib.RayConj
import Submission.Work.RiemLib.Gauss
import Submission.Work.RiemLib.ExpBound2
import Submission.Work.RiemLib.JacobiGauss
import Submission.Work.RiemLib.Minimal
import Submission.Work.RiemLib.Work.OddBound.longHomotopy.integrableOn_curveSpeed_of_contMDiffOn_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Auxiliary lemmas for the radial estimate

The proof of `radial_estimate_of_lift` follows the same route as
`Submission.Minimal.pathELength_ge_radial_of_stays`: it integrates the differential inequality
`d/ds ⟪W s, W s⟫ ≤ 2 · speed(GExp p ∘ W)(s) · ⟪W s, W s⟫^{1/2}`, which is Gauss's lemma along a
variation of rays (`hGauss`) together with Cauchy–Schwarz.  As in `Minimal`, the square root is
regularised by `√(g s + δ²)` so that the chain rule applies also at the zeros of `g`.

The auxiliary lemmas below are the ingredients:

* `curveVelocity_GExp_comp_E` — the chain rule identifying the velocity of `GExp p ∘ W` with
  `(d GExp p)_{W s} W'` (stated for an `E`-valued curve, which is what the tangent space is a
  synonym for);
* `inner_tantransport_radial`, `inner_le_norm_mul_radial` — transport of inner products along
  equalities of base points, and Cauchy–Schwarz in the fibre;
* `inner_deriv_le_curveSpeed_mul_radial` — the Gauss bound, which also uses the constancy of the
  speed of `GExp`-rays (`norm_curveVelocity_GExp_smul`);
* `sqrt_le_of_deriv_le_radial` — the one-dimensional comparison (one-sided FTC for `√g`);
* `contDiffOn_coe_of_tangentSpace`, `contMDiffOn_GExp_comp_radial` — smoothness of the image curve,
  needed for the integrability of its speed (`integrableOn_curveSpeed_of_contMDiffOn_one`).
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

noncomputable section

/-- **The chain rule for a curve in the tangent space composed with the exponential map.**  If the
`E`-valued curve `f` has derivative `f'` at `t`, then the velocity of `GExp p ∘ f` at `t` is the
differential of `GExp p` at the *point* `f₀ = f t` applied to `f'`.  Stating the value `f t` as a
separate variable `f₀` (with `ht : f t = f₀`) keeps the differential of `GExp p` at a clean
argument, which the elaborator can handle without unfolding `TangentSpace`. -/
private lemma curveVelocity_GExp_comp_E
    (hmet : IsMetricCompatible cov) (p : M)
    {f : ℝ → E} {t : ℝ} {f' f₀ : E} (hf : HasDerivAt f f' t) (ht : f t = f₀) :
    curveVelocity (I := I)
      (fun u : ℝ => GExp (cov := cov) hmet p (show TangentSpace I p from f u)) t
      = (mfderiv 𝓘(ℝ, E) I
          (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w)) f₀) f' := by
  rw [Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp
    (I := I)
    (f := fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w))
    (σ := f) (σ' := fun _ => f')
    (γ := fun u : ℝ => GExp (cov := cov) hmet p (show TangentSpace I p from f u))
    (t := t) hf
    ((Submission.GExpLocalInj.contMDiffAt_GExp_one (cov := cov) hmet p
      (show TangentSpace I p from f t)).mdifferentiableAt (by simp))
    (Filter.EventuallyEq.of_eq rfl), ht]

/-- Transporting an inner product along equalities of base points does not change it. -/
private lemma inner_tantransport_radial {x₁ x₂ y : M} (h₁ : x₁ = y) (h₂ : x₂ = y)
    (u : TangentSpace I x₁) (v : TangentSpace I x₂) :
    Inner.inner ℝ (Submission.LensLoop.tantransport h₁ u)
        (Submission.LensLoop.tantransport h₂ v)
      = Inner.inner ℝ u (show TangentSpace I x₁ from v) := by
  rw [Submission.LensLoop.tantransport, Submission.LensLoop.tantransport]
  cases h₁
  cases h₂
  rfl

/-- Cauchy–Schwarz for tangent vectors at a common base point. -/
private lemma inner_le_norm_mul_radial {x : M} (a b : TangentSpace I x) :
    Inner.inner ℝ a b ≤ ‖a‖ * ‖b‖ :=
  real_inner_le_norm a b

/-- **The pointwise consequence of Gauss's lemma.**  For a `C¹` curve `W` in the tangent space at
`p` and an interior time `s`, the inner product `⟪W'(s), W(s)⟫` is bounded by the Riemannian speed
of the image curve times `‖W(s)‖`. -/
private lemma inner_deriv_le_curveSpeed_mul_radial
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {W : ℝ → TangentSpace I p} {a b s : ℝ}
    (hW : ContDiffOn ℝ 1 W (Set.Icc a b)) (hs : s ∈ Set.Ioo a b)
    (hGauss : ∀ (v η : TangentSpace I p) (t : ℝ),
      Inner.inner ℝ
        (curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (t • (v + r • η))) 0)
        (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • v)) t)
        = t * Inner.inner ℝ η v) :
    Inner.inner ℝ (deriv W s) (W s)
      ≤ curveSpeed (I := I) (fun u : ℝ => GExp (cov := cov) hmet p (W u)) s * ‖W s‖ := by
  rcases eq_or_ne (W s) 0 with h0 | h0
  · rw [h0]
    simp
  · have honed : (1 : ℝ) • (show E from deriv W s) = (show E from deriv W s) := one_smul ℝ _
    have hzero : (0 : ℝ) • (show E from deriv W s) = (0 : E) := zero_smul ℝ _
    have hWs : HasDerivAt W (deriv W s) s :=
      ((hW.contDiffAt (Icc_mem_nhds hs.1 hs.2)).differentiableAt (by norm_num)).hasDerivAt
    have h3 : curveVelocity (I := I)
          (fun u : ℝ => GExp (cov := cov) hmet p (W u)) s
        = (mfderiv 𝓘(ℝ, E) I
            (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w))
            (show E from W s)) (show E from deriv W s) :=
      curveVelocity_GExp_comp_E (cov := cov) hmet p (f := fun u : ℝ => (show E from W u))
        (t := s) (f' := (show E from deriv W s)) (f₀ := (show E from W s)) hWs rfl
    have h1 : curveVelocity (I := I)
          (fun r : ℝ => GExp (cov := cov) hmet p (W s + r • deriv W s)) 0
        = (mfderiv 𝓘(ℝ, E) I
            (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w))
            (show E from W s)) (show E from deriv W s) := by
      have hder : HasDerivAt (fun r : ℝ => (show E from W s) + r • (show E from deriv W s))
          (show E from deriv W s) 0 := by
        have h := ((hasDerivAt_id (0 : ℝ)).smul_const (show E from deriv W s)).const_add
          (show E from W s)
        rw [honed] at h
        exact h
      have h := curveVelocity_GExp_comp_E (cov := cov) hmet p
        (f := fun r : ℝ => (show E from W s) + r • (show E from deriv W s)) (t := 0)
        (f' := (show E from deriv W s))
        (f₀ := (show E from W s) + (0 : ℝ) • (show E from deriv W s)) hder rfl
      rw [hzero, add_zero] at h
      exact h
    have hcurve : (fun r : ℝ =>
          GExp (cov := cov) hmet p ((1 : ℝ) • (W s + r • deriv W s)))
        = fun r : ℝ => GExp (cov := cov) hmet p (W s + r • deriv W s) := by
      funext r
      congr 1
      exact one_smul ℝ _
    have hptA : GExp (cov := cov) hmet p ((1 : ℝ) • (W s + (0 : ℝ) • deriv W s))
        = GExp (cov := cov) hmet p (W s) := by
      rw [zero_smul, add_zero, one_smul]
    have hptB : GExp (cov := cov) hmet p ((1 : ℝ) • W s)
        = GExp (cov := cov) hmet p (W s) := by
      rw [one_smul]
    have hG := hGauss (W s) (deriv W s) 1
    rw [one_mul] at hG
    have hpair : Inner.inner ℝ (Submission.LensLoop.tantransport (I := I) hptA
          (curveVelocity (I := I) (fun r : ℝ =>
            GExp (cov := cov) hmet p ((1 : ℝ) • (W s + r • deriv W s))) 0))
        (Submission.LensLoop.tantransport (I := I) hptB
          (curveVelocity (I := I) (fun u : ℝ =>
            GExp (cov := cov) hmet p (u • W s)) 1))
        = Inner.inner ℝ (deriv W s) (W s) :=
      (inner_tantransport_radial (I := I) hptA hptB _ _).trans hG
    have hCS := inner_le_norm_mul_radial (I := I)
      (Submission.LensLoop.tantransport (I := I) hptA
        (curveVelocity (I := I) (fun r : ℝ =>
          GExp (cov := cov) hmet p ((1 : ℝ) • (W s + r • deriv W s))) 0))
      (Submission.LensLoop.tantransport (I := I) hptB
        (curveVelocity (I := I) (fun u : ℝ =>
          GExp (cov := cov) hmet p (u • W s)) 1))
    have hAnorm : ‖Submission.LensLoop.tantransport (I := I) hptA
          (curveVelocity (I := I) (fun r : ℝ =>
            GExp (cov := cov) hmet p ((1 : ℝ) • (W s + r • deriv W s))) 0)‖
        = curveSpeed (I := I)
          (fun u : ℝ => GExp (cov := cov) hmet p (W u)) s := by
      rw [Submission.LensLoop.tantransport_eq, hcurve, h1, ← h3]
      exact (Submission.GeodesicSpeed.curveSpeed_eq_norm (I := I)
        (fun u : ℝ => GExp (cov := cov) hmet p (W u)) s).symm
    have hBnorm : ‖Submission.LensLoop.tantransport (I := I) hptB
          (curveVelocity (I := I) (fun u : ℝ =>
            GExp (cov := cov) hmet p (u • W s)) 1)‖ = ‖W s‖ := by
      rw [Submission.LensLoop.norm_tantransport]
      exact Submission.GlobalExp.norm_curveVelocity_GExp_smul (cov := cov) hmet p h0 (t := 1)
        (by norm_num)
    calc Inner.inner ℝ (deriv W s) (W s)
        = Inner.inner ℝ (Submission.LensLoop.tantransport (I := I) hptA
            (curveVelocity (I := I) (fun r : ℝ =>
              GExp (cov := cov) hmet p ((1 : ℝ) • (W s + r • deriv W s))) 0))
          (Submission.LensLoop.tantransport (I := I) hptB
            (curveVelocity (I := I) (fun u : ℝ =>
              GExp (cov := cov) hmet p (u • W s)) 1)) := hpair.symm
      _ ≤ ‖Submission.LensLoop.tantransport (I := I) hptA
            (curveVelocity (I := I) (fun r : ℝ =>
              GExp (cov := cov) hmet p ((1 : ℝ) • (W s + r • deriv W s))) 0)‖
          * ‖Submission.LensLoop.tantransport (I := I) hptB
            (curveVelocity (I := I) (fun u : ℝ =>
              GExp (cov := cov) hmet p (u • W s)) 1)‖ := hCS
      _ = curveSpeed (I := I)
            (fun u : ℝ => GExp (cov := cov) hmet p (W u)) s * ‖W s‖ := by
            rw [hAnorm, hBnorm]

/-- **One-sided FTC for the square root.**  If `g ≥ 0` is continuous on `[a,b]`, differentiable on
the interior with derivative `g'` satisfying the one-sided bound `g' ≤ 2 u √g`, and `u ≥ 0` is
integrable, then `√(g b) ≤ √(g a) + ∫_a^b u`.

The proof regularises: for `δ > 0` the function `R s = √(g s + δ²)` is differentiable on the
interior with derivative `g'/(2 √(g + δ²)) ≤ u`, so the one-sided FTC
`intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le` gives `R b - R a ≤ ∫ u`; letting
`δ → 0` and using `√(g a + δ²) ≤ √(g a) + δ` finishes. -/
private theorem sqrt_le_of_deriv_le_radial {G G' u : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hG : ContinuousOn G (Set.Icc a b))
    (hG0 : ∀ s ∈ Set.Icc a b, 0 ≤ G s)
    (hG' : ∀ s ∈ Set.Ioo a b, HasDerivAt G (G' s) s)
    (hu0 : ∀ s ∈ Set.Icc a b, 0 ≤ u s)
    (hint : IntegrableOn u (Set.Icc a b) volume)
    (hbd : ∀ s ∈ Set.Ioo a b, G' s ≤ 2 * u s * Real.sqrt (G s)) :
    Real.sqrt (G b) ≤ Real.sqrt (G a) + ∫ s in a..b, u s := by
  have hGa : 0 ≤ G a := hG0 a (left_mem_Icc.mpr hab)
  have hGb : 0 ≤ G b := hG0 b (right_mem_Icc.mpr hab)
  have key : ∀ δ : ℝ, 0 < δ →
      Real.sqrt (G b) - Real.sqrt (G a) ≤ (∫ s in a..b, u s) + δ := by
    intro δ hδ
    have hd2 : (0 : ℝ) < δ ^ 2 := by positivity
    set R : ℝ → ℝ := fun s => Real.sqrt (G s + δ ^ 2) with hRdef
    have hRcont : ContinuousOn R (Set.Icc a b) := by
      rw [hRdef]
      exact (hG.add continuousOn_const).sqrt
    have hRderiv : ∀ x ∈ Set.Ioo a b,
        HasDerivWithinAt R (G' x / (2 * Real.sqrt (G x + δ ^ 2))) (Set.Ioi x) x := by
      intro x hx
      have hpos : G x + δ ^ 2 ≠ 0 := by
        have h2 : 0 ≤ G x := hG0 x (Ioo_subset_Icc_self hx)
        linarith
      have hd : HasDerivAt R (G' x / (2 * Real.sqrt (G x + δ ^ 2))) x := by
        rw [hRdef]
        exact ((hG' x hx).add_const (δ ^ 2)).sqrt hpos
      exact hd.hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Ioo a b, G' x / (2 * Real.sqrt (G x + δ ^ 2)) ≤ u x := by
      intro x hx
      have hx' : x ∈ Set.Icc a b := Ioo_subset_Icc_self hx
      have hGx : 0 ≤ G x := hG0 x hx'
      have hux : 0 ≤ u x := hu0 x hx'
      have hpos : 0 < Real.sqrt (G x + δ ^ 2) := Real.sqrt_pos.mpr (by linarith)
      have hden : 0 < 2 * Real.sqrt (G x + δ ^ 2) := by linarith
      have hle := hbd x hx
      have hsq : Real.sqrt (G x) ≤ Real.sqrt (G x + δ ^ 2) := Real.sqrt_le_sqrt (by linarith)
      have hstep : G' x / (2 * Real.sqrt (G x + δ ^ 2))
          ≤ u x * (Real.sqrt (G x) / Real.sqrt (G x + δ ^ 2)) := by
        rw [div_le_iff₀ hden]
        have h3 : u x * (Real.sqrt (G x) / Real.sqrt (G x + δ ^ 2))
              * (2 * Real.sqrt (G x + δ ^ 2)) = 2 * (u x * Real.sqrt (G x)) := by
          field_simp
        rw [h3]
        linarith
      have h2 : Real.sqrt (G x) / Real.sqrt (G x + δ ^ 2) ≤ 1 :=
        div_le_one_of_le₀ hsq (Real.sqrt_nonneg _)
      calc G' x / (2 * Real.sqrt (G x + δ ^ 2))
          ≤ u x * (Real.sqrt (G x) / Real.sqrt (G x + δ ^ 2)) := hstep
        _ ≤ u x * 1 := mul_le_mul_of_nonneg_left h2 hux
        _ = u x := mul_one _
    have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hRcont hRderiv hint
      hbound
    simp only [hRdef] at h
    have h1 : Real.sqrt (G b) ≤ Real.sqrt (G b + δ ^ 2) := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (G a + δ ^ 2) ≤ Real.sqrt (G a) + δ := by
      have h2a : Real.sqrt (G a + δ ^ 2) ^ 2 ≤ (Real.sqrt (G a) + δ) ^ 2 := by
        rw [Real.sq_sqrt (by linarith)]
        nlinarith [Real.sq_sqrt hGa, Real.sqrt_nonneg (G a), hδ.le]
      nlinarith [Real.sqrt_nonneg (G a + δ ^ 2), Real.sqrt_nonneg (G a), hδ.le, h2a]
    linarith
  have hmain : Real.sqrt (G b) - Real.sqrt (G a) ≤ ∫ s in a..b, u s :=
    le_of_forall_pos_le_add key
  linarith

/-- The inverse tangent-bundle trivialisation at its own base point is the canonical
identification `T_pM → E`. -/
private lemma clm_trivializationAt_self_radial {p : M} (w : TangentSpace I p) :
    (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p w = (show E from w) := by
  have hbase : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H p
  have hsym : w = (trivializationAt E (TangentSpace I) p).symmL ℝ p (show E from w) := by
    rw [TangentBundle.symmL_trivializationAt_eq_core (𝕜 := ℝ) (b₀ := p) (b := p)
      (mem_chart_source H p)]
    exact (tangentCoordChange_self (I := I) (x := p) (z := p) (v := (show E from w))
      (mem_extChartAt_source (I := I) p)).symm
  conv_lhs => rw [hsym]
  exact Trivialization.continuousLinearMapAt_symmL (R := ℝ)
    (trivializationAt E (TangentSpace I) p) hbase (show E from w)

/-- **`C¹`-smoothness transfers from the Riemannian tangent space `T_pM` to the model space
`E`**: the trivialisation of the tangent bundle at its base point is a continuous linear map, so
composing with it converts a `T_pM`-valued `C¹` curve into an `E`-valued one. -/
private lemma contDiffOn_coe_of_tangentSpace {p : M} {W : ℝ → TangentSpace I p} {s : Set ℝ}
    (hW : ContDiffOn ℝ 1 W s) :
    ContDiffOn ℝ 1 (fun x : ℝ => (show E from W x)) s := by
  have hcm : ContDiff ℝ 1
      (fun u : TangentSpace I p =>
        (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p u) :=
    ContinuousLinearMap.contDiff ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p)
  have h1 : ContDiffOn ℝ 1
      (fun x : ℝ => (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p (W x)) s :=
    hcm.comp_contDiffOn hW
  refine h1.congr (fun x _ => ?_)
  exact (clm_trivializationAt_self_radial (I := I) (W x)).symm

/-- **The image of a `C¹` lift under the exponential map is `C¹`.** -/
private lemma contMDiffOn_GExp_comp_radial
    (hmet : IsMetricCompatible cov)
    {p : M} {W : ℝ → TangentSpace I p} {a b : ℝ}
    (hW : ContDiffOn ℝ 1 W (Set.Icc a b)) :
    ContMDiffOn 𝓘(ℝ) I 1
      (fun s : ℝ => GExp (cov := cov) hmet p (W s)) (Set.Icc a b) := by
  have hWamb : ContDiffOn ℝ 1 (fun s : ℝ => (show E from W s)) (Set.Icc a b) :=
    contDiffOn_coe_of_tangentSpace hW
  have hWmd : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 (fun s : ℝ => (show E from W s)) (Set.Icc a b) :=
    contMDiffOn_iff_contDiffOn.mpr hWamb
  have hFc : ContMDiff 𝓘(ℝ, E) I 1
      (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w)) :=
    fun v => Submission.GExpLocalInj.contMDiffAt_GExp_one (cov := cov) hmet p v
  have hFcu : ContMDiffOn 𝓘(ℝ, E) I 1
      (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w)) Set.univ :=
    hFc.contMDiffOn
  exact hFcu.comp hWmd (fun x _ => trivial)

/-- **The radial estimate for a `C¹` lift.** If `W : ℝ → T_pM` is `C¹` on `[a,b]`, then the norm of
the lift is at most the length of its image under `GExp p`:
`‖W b‖ ≤ ‖W a‖ + curveLength (GExp p ∘ W) a b`.

ROUTE (suggested). The proof of `Submission.Minimal.pathELength_ge_radial_of_stays` can be copied
almost verbatim, replacing the chart coordinates `σ : ℝ → E` by `W` itself and the chart metric
`chartGram x₀ x₀ (σ s)(σ s)` by the fibre product `Inner.inner ℝ (W s) (W s)`:
* `A s = ⟪W s, W s⟫` and `B s = ⟪W s, W' s⟫` (with `W'` the derivative of `W`), so
  `HasDerivAt A (2 * B s) s` (`HasDerivAt.inner`), then the `δ`-regularised
  `Rδ s = √(A s + δ²)` with `Rδ' s = B s / √(A s + δ²)`;
* the Gauss bound `|B s| ≤ ‖W s‖ * ‖(dGExp p)_{W s}(W' s)‖` is `hGauss` at `t = 1`, `v = W s`,
  `η = W' s` together with Cauchy–Schwarz (`Inner.inner ℝ (W s) (W s) = ‖W s‖²`);
* `‖(dGExp p)_{W s}(W' s)‖ = curveSpeed (GExp p ∘ W) s` by the chain rule
  (`mfderiv_comp`, `Submission.GExpSmooth.exists_contMDiffAt_GExp`, `curveSpeed_eq_norm`);
* integrate with `enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc` (as in `Minimal`), let `δ → 0`,
  and convert `Manifold.pathELength` into `curveLength` via
  `Commons.Geometry.Manifold.pathELength_eq_ofReal_integral_of_enorm_eq_nonneg`.

A parallel agent is proving the same statement under the name `norm_le_curveLength_of_lift`; this is a
deliberate duplicate (both are on the critical path of the long-homotopy argument). -/
theorem radial_estimate_of_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {W : ℝ → TangentSpace I p} {a b : ℝ} (hab : a ≤ b)
    (hW : ContDiffOn ℝ 1 W (Set.Icc a b))
    (hGauss : ∀ (v η : TangentSpace I p) (t : ℝ),
      Inner.inner ℝ
        (curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (t • (v + r • η))) 0)
        (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • v)) t)
        = t * Inner.inner ℝ η v) :
    ‖W b‖ ≤ ‖W a‖ + curveLength (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (W s)) a b := by
  -- The image curve is `C¹`, hence its speed is integrable on `[a,b]`.
  have hγ : ContMDiffOn 𝓘(ℝ) I 1
      (fun s : ℝ => GExp (cov := cov) hmet p (W s)) (Set.Icc a b) :=
    contMDiffOn_GExp_comp_radial (cov := cov) hmet hW
  have hintegrable : IntegrableOn (fun s : ℝ => curveSpeed (I := I)
      (fun u : ℝ => GExp (cov := cov) hmet p (W u)) s) (Set.Icc a b) volume :=
    integrableOn_curveSpeed_of_contMDiffOn_one (I := I) hγ
  -- Gauss's lemma gives the differential inequality at every interior point.
  have hGstep : ∀ s ∈ Set.Ioo a b,
      Inner.inner ℝ (deriv W s) (W s) ≤ curveSpeed (I := I)
        (fun u : ℝ => GExp (cov := cov) hmet p (W u)) s * ‖W s‖ :=
    fun s hs => inner_deriv_le_curveSpeed_mul_radial (I := I) hmet htor hW hs hGauss
  -- The functions of the one-dimensional comparison.
  set g : ℝ → ℝ := fun s => Inner.inner ℝ (W s) (W s) with hgdef
  set g' : ℝ → ℝ := fun s => 2 * Inner.inner ℝ (deriv W s) (W s) with hg'def
  set u : ℝ → ℝ := fun s => curveSpeed (I := I)
    (fun u : ℝ => GExp (cov := cov) hmet p (W u)) s with hudef
  have hgcont : ContinuousOn g (Set.Icc a b) := by
    rw [hgdef]
    exact hW.continuousOn.inner hW.continuousOn
  have hg0 : ∀ s ∈ Set.Icc a b, 0 ≤ g s := by
    intro s _
    show 0 ≤ Inner.inner ℝ (W s) (W s)
    rw [real_inner_self_eq_norm_sq]
    positivity
  have hg' : ∀ s ∈ Set.Ioo a b, HasDerivAt g (g' s) s := by
    intro s hs
    have hWs : HasDerivAt W (deriv W s) s :=
      ((hW.contDiffAt (Icc_mem_nhds hs.1 hs.2)).differentiableAt (by norm_num)).hasDerivAt
    have h := HasDerivAt.inner ℝ hWs hWs
    have hval : 2 * Inner.inner ℝ (deriv W s) (W s)
        = Inner.inner ℝ (W s) (deriv W s) + Inner.inner ℝ (deriv W s) (W s) := by
      rw [real_inner_comm (deriv W s) (W s)]
      ring
    rw [hgdef, hg'def]
    change HasDerivAt (fun s => Inner.inner ℝ (W s) (W s))
      (2 * Inner.inner ℝ (deriv W s) (W s)) s
    rw [hval]
    exact h
  have hbd : ∀ s ∈ Set.Ioo a b, g' s ≤ 2 * u s * Real.sqrt (g s) := by
    intro s hs
    have h1 := hGstep s hs
    have hs2 : Real.sqrt (g s) = ‖W s‖ := by
      show Real.sqrt (Inner.inner ℝ (W s) (W s)) = ‖W s‖
      rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    rw [hg'def]
    change 2 * Inner.inner ℝ (deriv W s) (W s) ≤ 2 * u s * Real.sqrt (g s)
    rw [hs2, hudef]
    linarith
  have hu0 : ∀ s ∈ Set.Icc a b, 0 ≤ u s := by
    intro s _
    rw [hudef]
    exact curveSpeed_nonneg (I := I) _ s
  -- The one-dimensional comparison.
  have hres := sqrt_le_of_deriv_le_radial hab hgcont hg0 hg' hu0 hintegrable hbd
  have hsb : Real.sqrt (g b) = ‖W b‖ := by
    show Real.sqrt (Inner.inner ℝ (W b) (W b)) = ‖W b‖
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hsa : Real.sqrt (g a) = ‖W a‖ := by
    show Real.sqrt (Inner.inner ℝ (W a) (W a)) = ‖W a‖
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [hsb, hsa] at hres
  rw [hudef] at hres
  rw [curveLength_def]
  exact hres

end

end Work.OddBound.longHomotopy
