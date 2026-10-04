import Mathlib
import Submission.Work.OddBound.LiftKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

/-!
# Continuity of the length of a smooth family of curves

`Submission.Length.curveLength γ a b` is the integral `∫ s in a..b, curveSpeed γ s` of the
Riemannian speed of `γ`.  The purpose of this file is to show that for a *jointly* smooth family
of curves `(s, t) ↦ c s t` the length `t ↦ curveLength (c · t) 0 S` depends continuously on the
parameter `t` — the standing hypothesis of the length-minimising argument in
`Work.OddBound.longHomotopy`.

The proof splits into two independent continuity statements:

* `continuous_curveSpeed_family`: the Riemannian speed `(s,t) ↦ curveSpeed (c · t) s` of the
  family is continuous.  The speed is `‖∂_s c (s,t)‖_{c(s,t)}`; the derivative `∂_s c` of the
  family, viewed as a section of the tangent bundle, is `tangentMap` of the family composed with
  the constant unit section of the tangent bundle of the model space `ℝ × ℝ`, hence smooth by
  `ContMDiff.contMDiff_tangentMap`; squaring the Riemannian metric is smooth along smooth
  sections by `ContMDiff.inner_bundle`, and the speed is the square root of that.
* `continuous_intervalIntegral_parameter`: a parameterised interval integral of a continuous
  function is continuous (Mathlib's `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`).

The pointwise identification `curveVelocity (c · t) s = ∂_s c (s,t)` used in the first step is the
chain rule for `(s,t) ↦ c s t` precomposed with `s ↦ (s,t)`, cf. `mfderiv_comp_apply` together
with `mfderiv_eq_fderiv`.
-/

/-- **Continuity of the speed of a smooth two–parameter family of curves.**  For a jointly `C^∞`
family `(s,t) ↦ c s t`, the Riemannian speed `(s,t) ↦ curveSpeed (c · t) s` is continuous. -/
theorem continuous_curveSpeed_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {c : ℝ → ℝ → M}
    (hcsm : ContMDiff (𝓘(ℝ, ℝ × ℝ)) I ∞ (fun u : ℝ × ℝ => c u.1 u.2)) :
    Continuous (fun u : ℝ × ℝ =>
      Submission.Length.curveSpeed (I := I) (fun s : ℝ => c s u.2) u.1) := by
  classical
  set F : ℝ × ℝ → M := fun u => c u.1 u.2 with hFdef
  have hF : ContMDiff (𝓘(ℝ, ℝ × ℝ)) I ∞ F := hcsm
  -- The bundled derivative of the family is smooth as a map of tangent bundles.
  have hT : ContMDiff (𝓘(ℝ, ℝ × ℝ)).tangent I.tangent ∞
      (tangentMap (𝓘(ℝ, ℝ × ℝ)) I F) :=
    hF.contMDiff_tangentMap (m := ∞) (n := ∞) le_rfl
  -- The constant unit section `u ↦ (u, (1,0))` of the tangent bundle of the model space.
  have hκ : ContMDiff (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ × ℝ)).tangent ∞
      (fun u : ℝ × ℝ => (TotalSpace.mk' (ℝ × ℝ) u ((1, 0) : TangentSpace 𝓘(ℝ,ℝ×ℝ) u) :
        TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) :=
    (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (E := (ℝ × ℝ))
      (V := fun u => ((1, 0) : TangentSpace 𝓘(ℝ,ℝ×ℝ) u))).2 contDiff_const
  have hK : ContMDiff (𝓘(ℝ, ℝ × ℝ)) I.tangent ∞
      (fun u : ℝ × ℝ => tangentMap (𝓘(ℝ, ℝ × ℝ)) I F
        (TotalSpace.mk' (ℝ × ℝ) u ((1, 0) : TangentSpace 𝓘(ℝ,ℝ×ℝ) u))) :=
    hT.comp hκ
  -- The partial velocity field `u ↦ ∂_s c u` of the family, as a section of the tangent bundle.
  set sec : (u : ℝ × ℝ) → TangentSpace I (F u) :=
    fun u => (mfderiv (𝓘(ℝ, ℝ × ℝ)) I F u) ((1, 0) : ℝ × ℝ) with hsecdef
  have hsec : ContMDiff (𝓘(ℝ, ℝ × ℝ)) I.tangent ∞
      (fun u : ℝ × ℝ => (⟨F u, sec u⟩ : TangentBundle I M)) := by
    rw [hsecdef]
    exact hK
  -- Squaring the metric along a smooth section is smooth.
  have hinner : ContMDiff (𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun u : ℝ × ℝ => inner ℝ (sec u) (sec u)) :=
    ContMDiff.inner_bundle (b := F) hsec hsec
  have hcont : Continuous (fun u : ℝ × ℝ => Real.sqrt (inner ℝ (sec u) (sec u))) :=
    Real.continuous_sqrt.comp hinner.continuous
  convert hcont using 1
  ext u
  rw [Submission.Length.curveSpeed_def]
  -- The chain rule: the velocity of `c · u.2` at `u.1` is `∂_s c` at `u`.
  have hkey : Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => c s u.2) u.1
      = sec u := by
    have hg : MDifferentiableAt (𝓘(ℝ,ℝ×ℝ)) I (fun u : ℝ × ℝ => c u.1 u.2) u :=
      hcsm.contMDiffAt.mdifferentiableAt (by norm_num)
    have hf : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ,ℝ×ℝ) (fun s : ℝ => (s, u.2)) u.1 :=
      (differentiableAt_id.prodMk (differentiableAt_const u.2)).mdifferentiableAt
    have hid : (mfderiv 𝓘(ℝ) 𝓘(ℝ,ℝ×ℝ) (fun s : ℝ => (s, u.2)) u.1) (1 : ℝ) = (1,0) := by
      rw [mfderiv_eq_fderiv]
      show (fderiv ℝ (fun s : ℝ => (id s, u.2)) u.1) 1 = (1,0)
      rw [differentiableAt_id.fderiv_prodMk (differentiableAt_const u.2), fderiv_id]
      simp
    have hcomp := mfderiv_comp_apply (x := u.1)
      (f := fun s : ℝ => (s, u.2)) (g := fun u : ℝ × ℝ => c u.1 u.2) hg hf (1 : ℝ)
    rw [hid] at hcomp
    rw [Submission.Geodesic.curveVelocity_apply]
    exact hcomp
  rw [hkey]

/-- **Continuity of a parameterised interval integral.**  If `G : ℝ → ℝ → ℝ` is continuous as a
function of both variables, then `t ↦ ∫ s in a..b, G t s` is continuous. -/
theorem continuous_intervalIntegral_parameter
    {G : ℝ → ℝ → ℝ} (hG : Continuous (Function.uncurry G)) (a b : ℝ) :
    Continuous (fun t : ℝ => ∫ s in a..b, G t s) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := G) hG a b

theorem continuousOn_curveLength_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {c : ℝ → ℝ → M} {S : ℝ}
    (hcsm : ContMDiff (𝓘(ℝ, ℝ × ℝ)) I ∞ (fun u : ℝ × ℝ => c u.1 u.2)) :
    ContinuousOn (fun t : ℝ => Submission.Length.curveLength (I := I) (fun s : ℝ => c s t) 0 S)
      (Set.Icc (0 : ℝ) 1) := by
  have hG : Continuous (fun u : ℝ × ℝ =>
      Submission.Length.curveSpeed (I := I) (fun s : ℝ => c s u.2) u.1) :=
    continuous_curveSpeed_family (I := I) hcsm
  -- Swap the two variables so that the parameter is the first argument of the integrand.
  have hG' : Continuous (fun p : ℝ × ℝ =>
      Submission.Length.curveSpeed (I := I) (fun s : ℝ => c s p.1) p.2) :=
    hG.comp (continuous_snd.prodMk continuous_fst)
  have hcont : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..S,
      Submission.Length.curveSpeed (I := I) (fun s' : ℝ => c s' t) s) :=
    continuous_intervalIntegral_parameter
      (G := fun t s => Submission.Length.curveSpeed (I := I) (fun s' : ℝ => c s' t) s) hG' 0 S
  exact hcont.continuousOn

end Work.OddBound.longHomotopy
