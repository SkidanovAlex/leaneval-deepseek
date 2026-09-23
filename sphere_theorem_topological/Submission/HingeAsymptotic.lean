import Submission.HingeCompare
import Submission.FirstVariation
import Submission.Commons.Analysis.ODE.sturm_max_principle_right_liminf
import Submission.Commons.Analysis.Calculus.eventually_cos_sub_model_le

/-!
# Toponogov's hinge comparison from the one-sided asymptotics of the distance function

`Submission/HingeCompare.lean` reduces the hinge comparison to

* the first variation formula `ρ'(0) = -cos θ`, and
* the Hessian bound `(cos ∘ ρ)'' ≥ -(cos ∘ ρ)`.

The first variation formula is only available as a *one-sided* statement (see
`Submission/FirstVariation.lean`:  `ρ t ≤ a + t·R + ε·t` for all small `t > 0`), so the two-sided
hypothesis `HasDerivAt ρ (-(cos θ)) 0` of `hinge_of_cos_second_deriv` cannot be fed directly.

Here we prove the corresponding statement with the correct one-sided hypothesis, namely that the
*lower right Dini derivative* of `w = cos ∘ ρ - model` at `0` is `≥ 0`:

  `∀ ε > 0, ∀ᶠ t, -ε * t ≤ cos (ρ t) - model t`.

The Sturm comparison (`Commons.Analysis.ODE.sturm_max_principle_right_liminf`) is stated exactly for
this hypothesis.  The model function is written directly in terms of `R = ⟨V, γ'(L)⟩ = -cos θ`:

  `modelFunR a R t = cos a * cos t - R * sin a * sin t`.

Main results:

* `hinge_of_cos_asymptotic` — the core reduction (Hessian bound + one-sided asymptotics);
* `hinge_of_asymptotic` — the geometric form, where the asymptotics are given as
  `ρ t ≤ a + t·R + ε·t` together with the Lipschitz bound `|ρ t - a| ≤ C·t`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open Set Filter
open scoped Topology ContDiff Manifold
open Bundle
open Submission.HingeCompare
open Submission.FirstVariation
open Submission.Geodesic
open Submission.ChartConnection
open CovariantDerivative
open Submission.GlobalExp

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.HingeAsymptotic

noncomputable section

variable {ρ ρ' G : ℝ → ℝ} {a R T C : ℝ}

/-- The model distance function of the space form of curvature `1`, written in terms of
`R = -cos θ` (where `θ` is the hinge angle):
`cos ⋎(θ; a, t) = cos a cos t - R sin a sin t`. -/
def modelFunR (a R : ℝ) : ℝ → ℝ :=
  (fun t => Real.cos a * Real.cos t) - (fun t => R * Real.sin a * Real.sin t)

/-- The derivative of `modelFunR a R`. -/
def modelFunR' (a R : ℝ) : ℝ → ℝ :=
  (-(fun t => Real.cos a * Real.sin t)) - (fun t => R * Real.sin a * Real.cos t)

lemma hasDerivAt_modelFunR (a R t : ℝ) :
    HasDerivAt (modelFunR a R) (modelFunR' a R t) t := by
  have hfun : modelFunR a R = ((fun y : ℝ => Real.cos a * Real.cos y)
      - (fun y : ℝ => R * Real.sin a * Real.sin y)) := rfl
  have hval : modelFunR' a R t = Real.cos a * -Real.sin t - R * Real.sin a * Real.cos t := by
    simp only [modelFunR', Pi.sub_apply, Pi.neg_apply]
    ring
  rw [hfun, hval]
  exact ((Real.hasDerivAt_cos t).const_mul (Real.cos a)).sub
    ((Real.hasDerivAt_sin t).const_mul (R * Real.sin a))

lemma hasDerivAt_modelFunR' (a R t : ℝ) :
    HasDerivAt (modelFunR' a R) (-(modelFunR a R t)) t := by
  have hfun : modelFunR' a R = ((-(fun y : ℝ => Real.cos a * Real.sin y))
      - (fun y : ℝ => R * Real.sin a * Real.cos y)) := rfl
  have hval : -(modelFunR a R t) = -(Real.cos a * Real.cos t) - R * Real.sin a * -Real.sin t := by
    simp only [modelFunR, Pi.sub_apply]
    ring
  rw [hfun, hval]
  exact (((Real.hasDerivAt_sin t).const_mul (Real.cos a)).neg).sub
    ((Real.hasDerivAt_cos t).const_mul (R * Real.sin a))

/-- **Toponogov's hinge comparison from the one-sided asymptotics.**

Let `ρ 0 = a` with `0 < a`, let `ρ` be continuous on `[0,T]` with values in `[0,π]`, `T < π`, and
suppose that `(cos ∘ ρ)'' + cos ∘ ρ ≥ 0` on `(0,T)` (the Hessian bound, stated through
`DistHessianBound`) together with the one-sided asymptotic bound

  `∀ ε > 0, ∀ᶠ t in 𝓝[>] 0, -ε * t ≤ cos (ρ t) - modelFunR a R t`.

Then `ρ t ≤ arccos (modelFunR a R t)` for `t ∈ [0,T]`. -/
theorem hinge_of_cos_asymptotic
    (ha0 : 0 < a) (hT : 0 < T) (hTπ : T < Real.pi)
    (hρ0 : ρ 0 = a)
    (hρcont : ContinuousOn ρ (Set.Icc 0 T))
    (hρrange : ∀ t ∈ Set.Icc 0 T, ρ t ∈ Set.Icc 0 Real.pi)
    (hlim : ∀ ε > 0, ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      -ε * t ≤ Real.cos (ρ t) - modelFunR a R t)
    (hb : DistHessianBound ρ ρ' G T) :
    ∀ t ∈ Set.Icc 0 T, ρ t ≤ Real.arccos (modelFunR a R t) := by
  obtain ⟨hd1, hd2, hd3⟩ := hb
  set w : ℝ → ℝ := (fun s : ℝ => Real.cos (ρ s)) - modelFunR a R with hwdef
  set w' : ℝ → ℝ := (fun s : ℝ => -(Real.sin (ρ s) * ρ' s)) - modelFunR' a R with hw'def
  set Ff : ℝ → ℝ := G + modelFunR a R with hFfdef
  have hwderiv : ∀ t ∈ Set.Ioo (0:ℝ) T, HasDerivAt w (w' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => Real.cos (ρ s)) (-(Real.sin (ρ t) * ρ' t)) t := by
      have h := (hd1 t ht).cos
      have hv : -(Real.sin (ρ t)) * ρ' t = -(Real.sin (ρ t) * ρ' t) := by ring
      rwa [hv] at h
    have h2 := h1.sub (hasDerivAt_modelFunR a R t)
    rw [hwdef]
    have hv : w' t = -(Real.sin (ρ t) * ρ' t) - modelFunR' a R t := by
      simp only [hw'def, Pi.sub_apply, Pi.neg_apply]
    rw [hv]
    exact h2
  have hw'deriv : ∀ t ∈ Set.Ioo (0:ℝ) T, HasDerivAt w' (Ff t) t := by
    intro t ht
    rw [hw'def]
    have hv : Ff t = G t - -modelFunR a R t := by
      rw [hFfdef]; simp only [Pi.add_apply]; ring
    rw [hv]
    exact (hd2 t ht).sub (hasDerivAt_modelFunR' a R t)
  have hwc : w 0 = 0 := by
    rw [hwdef]
    simp only [Pi.sub_apply, hρ0, modelFunR, Pi.sub_apply, Real.cos_zero, Real.sin_zero, mul_zero,
      mul_one, sub_zero]
    ring
  have hwcont : ContinuousOn w (Set.Icc 0 T) := by
    rw [hwdef]
    refine (Real.continuous_cos.comp_continuousOn hρcont).sub ?_
    rw [show modelFunR a R = ((fun y : ℝ => Real.cos a * Real.cos y)
      - (fun y : ℝ => R * Real.sin a * Real.sin y)) from rfl]
    exact ((continuous_const.mul Real.continuous_cos).sub
      ((continuous_const.mul Real.continuous_sin))).continuousOn
  have hFf : ∀ t ∈ Set.Ioo (0:ℝ) T, 0 ≤ Ff t + (1:ℝ) ^ 2 * w t := by
    intro t ht
    have hh := hd3 t ht
    rw [hFfdef, hwdef]
    simp only [Pi.add_apply, Pi.sub_apply, one_pow, one_mul]
    linarith
  have hlim' : ∀ ε > 0, ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), -ε * (t - 0) ≤ w t := by
    intro ε hε
    have h := hlim ε hε
    refine h.mono fun t ht => ?_
    rw [hwdef]
    simpa using ht
  have hmain := Commons.Analysis.ODE.sturm_max_principle_right_liminf (a := 1) (c := 0) (d := T)
    one_pos hT (by simpa using hTπ) hwcont hwderiv hw'deriv hwc hlim' hFf
  intro t ht
  have hnn : 0 ≤ w t := hmain t ht
  rw [hwdef] at hnn
  simp only [Pi.sub_apply] at hnn
  have hM : modelFunR a R t ≤ Real.cos (ρ t) := by linarith
  have hle : Real.arccos (Real.cos (ρ t)) ≤ Real.arccos (modelFunR a R t) :=
    Real.arccos_le_arccos hM
  rwa [Real.arccos_cos (hρrange t ht).1 (hρrange t ht).2] at hle

/-- **Toponogov's hinge comparison from the geometric asymptotics of the distance function.**

Same conclusion as `hinge_of_cos_asymptotic`, but with the one-sided asymptotics stated in the
geometric form produced by the first variation formula (`Submission/FirstVariation.lean`):

* `ρ t ≤ a + t * R + ε * t` for every `ε > 0` and all small `t > 0` (the first variation), and
* `|ρ t - a| ≤ C * t` (the Lipschitz bound on the distance function).

The conversion into the `cos`-asymptotics used by the Sturm comparison is
`Commons.Analysis.Calculus.eventually_cos_sub_model_le`. -/
theorem hinge_of_asymptotic
    (ha0 : 0 < a) (haπ : a < Real.pi) (hC : 0 ≤ C)
    (hT : 0 < T) (hTπ : T < Real.pi)
    (hρ0 : ρ 0 = a)
    (hρcont : ContinuousOn ρ (Set.Icc 0 T))
    (hρrange : ∀ t ∈ Set.Icc 0 T, ρ t ∈ Set.Icc 0 Real.pi)
    (hbound : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), |ρ t - a| ≤ C * t)
    (hlim : ∀ ε > 0, ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), ρ t ≤ a + t * R + ε * t)
    (hb : DistHessianBound ρ ρ' G T) :
    ∀ t ∈ Set.Icc 0 T, ρ t ≤ Real.arccos (modelFunR a R t) := by
  refine hinge_of_cos_asymptotic (ρ := ρ) (ρ' := ρ') (G := G) (a := a) (R := R) (T := T)
    ha0 hT hTπ hρ0 hρcont hρrange ?_ hb
  intro ε hε
  have h := Commons.Analysis.Calculus.eventually_cos_sub_model_le (a := a) (R := R) (C := C)
    ha0 haπ hC hbound hlim ε hε
  simpa only [modelFunR, Pi.sub_apply] using h

variable [I.Boundaryless] in
/-- The distance function `t ↦ d(q, exp_p (t • V))` along the geodesic variation
`t ↦ exp_p (t • V)`. -/
noncomputable def distAlong {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (q : M) (p : M) (V : E) : ℝ → ℝ :=
  fun t => (Manifold.riemannianEDist I q (expMap cov p (t • V))).toReal

variable [I.Boundaryless] in
/-- **Toponogov's hinge comparison for the variation `t ↦ exp_p (t • V)`, from the first variation
formula and the Hessian bound.**

This is the end-to-end form of the reduction: the first variation formula
(`firstVariation_upper_geodCurve`) supplies the one-sided asymptotics of `distAlong q p V` with slope
`R = ⟨V, c'(L)⟩`, where `c` is the chosen minimising geodesic from `q` to `p = c L`, and
`hinge_of_asymptotic` converts the first variation plus the Hessian bound into the comparison
`d(q, exp_p (t V)) ≤ ⋎(θ; L, t)`.

The remaining geometric input is exactly `DistHessianBound` for `distAlong q p V` (the Hessian
comparison for the distance function). -/
theorem hinge_of_firstVariation [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {q : M} {ξ : TangentSpace I q} (hξ : ‖ξ‖ = 1) {T L : ℝ} (hT : 0 ≤ T) (hL : 0 < L)
    (hLT : L ≤ T) (hLπ : L < Real.pi)
    (hmin : Manifold.riemannianEDist I q
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) = ENNReal.ofReal L)
    (V : E) {C : ℝ} (hC : 0 ≤ C) {ρ' G : ℝ → ℝ}
    (hρcont : ContinuousOn (distAlong (cov := cov) q
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) V) (Set.Icc 0 L))
    (hρrange : ∀ t ∈ Set.Icc 0 L,
      distAlong (cov := cov) q ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) V t
        ∈ Set.Icc 0 Real.pi)
    (hbound : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      |distAlong (cov := cov) q ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) V t - L|
        ≤ C * t)
    (hb : DistHessianBound (distAlong (cov := cov) q
        ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) V) ρ' G L) :
    ∀ t ∈ Set.Icc 0 L,
      distAlong (cov := cov) q ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) V t
        ≤ Real.arccos (modelFunR L (chartGram (I := I)
            ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L)
            ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) V
            (curveVelocity (I := I) (geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L)) t) := by
  have hρ0 : distAlong (cov := cov) q
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) V 0 = L := by
    have h1 : (0:ℝ) • V
        = (0 : TangentSpace I ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L)) := by
      rw [zero_smul]
      exact rfl
    simp only [distAlong]
    rw [h1, expMap_zero, hmin, ENNReal.toReal_ofReal hL.le]
  have hlim : ∀ ε > 0, ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      distAlong (cov := cov) q ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) V t
        ≤ L + t * (chartGram (I := I)
            ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L)
            ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) V
            (curveVelocity (I := I) (geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L))
          + ε * t := by
    intro ε hε
    have h := firstVariation_upper_geodCurve (cov := cov) hmet htor hpinch hξ hT hL hLT hmin V
      ε hε
    refine h.mono fun t ht => ?_
    rw [distAlong]
    calc (Manifold.riemannianEDist I q (expMap cov
          ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) (t • V))).toReal
        ≤ L + t * (chartGram (I := I)
            ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L)
            ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) V
            (curveVelocity (I := I) (geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) + ε) := ht
      _ = L + t * (chartGram (I := I)
            ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L)
            ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) V
            (curveVelocity (I := I) (geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L))
          + ε * t := by ring
  exact hinge_of_asymptotic (a := L) (R := chartGram (I := I)
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L)
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) V
      (curveVelocity (I := I) (geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L))
    (T := L) hL hLπ hC hL hLπ hρ0 hρcont hρrange hbound hlim hb

end

end Submission.HingeAsymptotic
