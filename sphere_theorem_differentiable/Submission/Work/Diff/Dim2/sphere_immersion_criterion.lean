import Mathlib
import Submission.Work.Diff.Dim2.Ambient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedSectionVars false

/-!
# The immersion criterion for the sphere parametrisation (the `d = 2` branch)

This file proves `Work.Diff.Dim2.sphere_immersion_criterion`: if `ξ : M → ℝ` and
`Az : M → ℝ²` are differentiable at `x`, if `sin (ξ x) ≠ 0`, and if the kernels of `dξ` and of
the angular form `angForm Az x` have trivial intersection, then the differential at `x` of

    G y = sphereAmb (ξ y, Az y) = (sin (ξ y) • Az y, cos (ξ y)) ∈ ℝ³

is injective.

The mathematical content is the explicit computation of the differential of the ambient map
`sphereAmb (r, z) = (sin r · z₀, sin r · z₁, cos r)`: in direction `(a, w)` it is

    (cos r · a · z + sin r · w, -sin r · a),

so with `sin r ≠ 0` the differential of `sphereAmb` at `(r, z)` is injective.  Composing with the
pair map `y ↦ (ξ y, Az y)` yields the claim.

Along the way we need the (well hidden) fact that `TangentSpace` is a *non-reducible* type
synonym for the model space, so that coefficient maps such as `Prod.fst` have to be applied to
`(NormedSpace.fromTangentSpace _) _`; the `set_option backward.isDefEq.respectTransparency.types
false` below is Mathlib's own device for this situation.
-/

private lemma mfderiv_clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) (y : F) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) L y = L := by
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  all_goals first | rfl | (ext v; rfl) | simp

/- Chain rule with a continuous linear map on the left, in a form whose right-hand side is
type-correct (the value of `mfderiv` lives in the *tangent space* of the target, which in
Mathlib is a non-reducible copy of the model space). -/
set_option backward.isDefEq.respectTransparency.types false in
private lemma mfderiv_clm_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {f : M → F} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, F) f x)
    (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, G) (fun y => L (f y)) x v
      = L ((NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, F) f x) v)) := by
  have hL : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, G) L (f x) :=
    ((ContinuousLinearMap.hasFDerivAt L (x := f x)).hasMFDerivAt).mdifferentiableAt
  have h := mfderiv_comp_apply (g := L) (f := f) x hL hf v
  rw [mfderiv_clm L (f x)] at h
  exact h

/-! ## The ambient map `sphereAmb` and its derivative -/

private lemma hasFDerivAt_sA (i : Fin 2) (q : ℝ × EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => Real.sin p.1 * p.2.ofLp i)
      ((Real.sin q.1) • ((EuclideanSpace.proj i).comp
          (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 2))))
        + (q.2.ofLp i) • ((ContinuousLinearMap.toSpanSingleton ℝ (Real.cos q.1)).comp
          (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 2))))) q := by
  have hf : HasFDerivAt (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => Real.sin p.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ (Real.cos q.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 2)))) q := by
    have h1 : HasFDerivAt (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => p.1)
        (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 2))) q := hasFDerivAt_fst
    have h2 : HasFDerivAt Real.sin (ContinuousLinearMap.toSpanSingleton ℝ (Real.cos q.1)) q.1 := by
      rw [← hasDerivAt_iff_hasFDerivAt]
      exact Real.hasDerivAt_sin q.1
    exact h2.comp q h1
  have hg : HasFDerivAt (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => p.2.ofLp i)
      ((EuclideanSpace.proj i).comp
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 2)))) q := by
    have h := ContinuousLinearMap.hasFDerivAt
      ((EuclideanSpace.proj i).comp
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 2)))) (x := q)
    have hfun : (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => (EuclideanSpace.proj i) p.2)
        = fun p : ℝ × EuclideanSpace ℝ (Fin 2) => p.2.ofLp i := by
      funext p
      simp [EuclideanSpace.proj, PiLp.proj_apply]
    change HasFDerivAt (fun p : ℝ × EuclideanSpace ℝ (Fin 2) =>
      (EuclideanSpace.proj i) p.2) _ q at h
    rwa [hfun] at h
  exact hf.mul hg

private lemma hasFDerivAt_sA2 (q : ℝ × EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => Real.cos p.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-Real.sin q.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 2)))) q := by
  have h1 : HasFDerivAt (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => p.1)
      (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 2))) q := hasFDerivAt_fst
  have h2 : HasFDerivAt Real.cos (ContinuousLinearMap.toSpanSingleton ℝ (-Real.sin q.1)) q.1 := by
    rw [← hasDerivAt_iff_hasFDerivAt]
    exact Real.hasDerivAt_cos q.1
  exact h2.comp q h1

private lemma fderiv_sA_apply (i : Fin 2) (q : ℝ × EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (w : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => Real.sin p.1 * p.2.ofLp i) q (a, w)
      = Real.cos q.1 * a * (q.2.ofLp i) + Real.sin q.1 * (w.ofLp i) := by
  rw [(hasFDerivAt_sA i q).fderiv]
  simp [ContinuousLinearMap.toSpanSingleton_apply, EuclideanSpace.proj, PiLp.proj_apply]
  ring

private lemma fderiv_sA2_apply (q : ℝ × EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (w : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => Real.cos p.1) q (a, w)
      = - Real.sin q.1 * a := by
  rw [(hasFDerivAt_sA2 q).fderiv]
  simp [ContinuousLinearMap.toSpanSingleton_apply]
  ring

/-! ## The components of `sphereAmb` -/

private lemma sphereAmbComp_zero (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    sphereAmbComp (0 : Fin 3) p = Real.sin p.1 * p.2.ofLp 0 := by
  rw [sphereAmbComp, Fin.cases_zero]

private lemma sphereAmbComp_one (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    sphereAmbComp (1 : Fin 3) p = Real.sin p.1 * p.2.ofLp 1 := by
  rw [show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl, sphereAmbComp, Fin.cases_succ,
    Fin.cases_zero]

private lemma sphereAmbComp_two (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    sphereAmbComp (2 : Fin 3) p = Real.cos p.1 := by
  rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl, sphereAmbComp, Fin.cases_succ,
    show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl, Fin.cases_succ]

private lemma proj_sphereAmb (i : Fin 3) (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    (EuclideanSpace.proj i) (sphereAmb p) = sphereAmbComp i p := by
  rw [sphereAmb]
  simp [EuclideanSpace.proj, PiLp.proj_apply]

private lemma differentiableAt_sphereAmbComp (i : Fin 3) (q : ℝ × EuclideanSpace ℝ (Fin 2)) :
    DifferentiableAt ℝ (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp i p) q := by
  fin_cases i
  · show DifferentiableAt ℝ (fun p : ℝ × EuclideanSpace ℝ (Fin 2) =>
      sphereAmbComp (0 : Fin 3) p) q
    rw [show (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp (0 : Fin 3) p)
        = (fun p => Real.sin p.1 * p.2.ofLp 0) from funext (fun p => sphereAmbComp_zero p)]
    exact (hasFDerivAt_sA 0 q).differentiableAt
  · show DifferentiableAt ℝ (fun p : ℝ × EuclideanSpace ℝ (Fin 2) =>
      sphereAmbComp (1 : Fin 3) p) q
    rw [show (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp (1 : Fin 3) p)
        = (fun p => Real.sin p.1 * p.2.ofLp 1) from funext (fun p => sphereAmbComp_one p)]
    exact (hasFDerivAt_sA 1 q).differentiableAt
  · show DifferentiableAt ℝ (fun p : ℝ × EuclideanSpace ℝ (Fin 2) =>
      sphereAmbComp (2 : Fin 3) p) q
    rw [show (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp (2 : Fin 3) p)
        = (fun p => Real.cos p.1) from funext (fun p => sphereAmbComp_two p)]
    exact (hasFDerivAt_sA2 q).differentiableAt

private lemma differentiableAt_sphereAmb (q : ℝ × EuclideanSpace ℝ (Fin 2)) :
    DifferentiableAt ℝ sphereAmb q := by
  have hPhi : DifferentiableAt ℝ (fun p : ℝ × EuclideanSpace ℝ (Fin 2) =>
      fun i : Fin 3 => sphereAmbComp i p) q :=
    differentiableAt_pi'' (fun i => differentiableAt_sphereAmbComp i q)
  exact ((ContinuousLinearMap.hasFDerivAt
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm : (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (x := (fun i : Fin 3 => sphereAmbComp i q))).comp q hPhi.hasFDerivAt).differentiableAt

private lemma mdiff_sphereAmb (q : ℝ × EuclideanSpace ℝ (Fin 2)) :
    MDifferentiableAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      sphereAmb q :=
  (differentiableAt_sphereAmb q).hasFDerivAt.hasMFDerivAt.mdifferentiableAt

/-- **The crux**: the differential of `sphereAmb` at `(r, z)` is injective when `sin r ≠ 0`.
The value of `fderiv sphereAmb (r,z)` on `(a, w)` is
`(cos r · a · z₀ + sin r · w₀, cos r · a · z₁ + sin r · w₁, - sin r · a)`, so the third coordinate
gives `a = 0` and then the first two coordinates give `w = 0`. -/
private lemma fderiv_sphereAmb_apply_eq_zero {q : ℝ × EuclideanSpace ℝ (Fin 2)}
    (hsin : Real.sin q.1 ≠ 0) {a : ℝ} {w : EuclideanSpace ℝ (Fin 2)}
    (h : fderiv ℝ sphereAmb q (a, w) = 0) : a = 0 ∧ w = 0 := by
  have hder := (differentiableAt_sphereAmb q).hasFDerivAt
  have hci : ∀ i : Fin 3,
      fderiv ℝ (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp i p) q (a, w) = 0 := by
    intro i
    have hcomp := (ContinuousLinearMap.hasFDerivAt (EuclideanSpace.proj i)
      (x := sphereAmb q)).comp q hder
    have hf : fderiv ℝ (⇑(EuclideanSpace.proj i) ∘ sphereAmb) q
        = (EuclideanSpace.proj i).comp (fderiv ℝ sphereAmb q) := hcomp.fderiv
    have hz : fderiv ℝ (⇑(EuclideanSpace.proj i) ∘ sphereAmb) q (a, w) = 0 := by
      rw [hf, ContinuousLinearMap.comp_apply, h, map_zero]
    rwa [show (⇑(EuclideanSpace.proj i) ∘ sphereAmb)
        = (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp i p) from
      funext (fun p => proj_sphereAmb i p)] at hz
  have hc2 : fderiv ℝ (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp (2 : Fin 3) p)
      q (a, w) = - Real.sin q.1 * a := by
    rw [show (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp (2 : Fin 3) p)
        = (fun p => Real.cos p.1) from funext (fun p => sphereAmbComp_two p)]
    exact fderiv_sA2_apply q a w
  have ha : a = 0 := by
    have h2v := hci 2
    rw [hc2] at h2v
    have hs : Real.sin q.1 * a = 0 := by linarith
    exact (mul_eq_zero.mp hs).resolve_left hsin
  have hc0 : fderiv ℝ (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp (0 : Fin 3) p)
      q (a, w) = Real.cos q.1 * a * (q.2.ofLp 0) + Real.sin q.1 * (w.ofLp 0) := by
    rw [show (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp (0 : Fin 3) p)
        = (fun p => Real.sin p.1 * p.2.ofLp 0) from funext (fun p => sphereAmbComp_zero p)]
    exact fderiv_sA_apply 0 q a w
  have hc1 : fderiv ℝ (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp (1 : Fin 3) p)
      q (a, w) = Real.cos q.1 * a * (q.2.ofLp 1) + Real.sin q.1 * (w.ofLp 1) := by
    rw [show (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp (1 : Fin 3) p)
        = (fun p => Real.sin p.1 * p.2.ofLp 1) from funext (fun p => sphereAmbComp_one p)]
    exact fderiv_sA_apply 1 q a w
  have hw0 : w.ofLp 0 = 0 := by
    have h0v := hci 0
    rw [hc0, ha] at h0v
    simp at h0v
    exact h0v.resolve_left hsin
  have hw1 : w.ofLp 1 = 0 := by
    have h1v := hci 1
    rw [hc1, ha] at h1v
    simp at h1v
    exact h1v.resolve_left hsin
  refine ⟨ha, ?_⟩
  rw [WithLp.ext_iff]
  funext j
  fin_cases j
  · simpa using hw0
  · simpa using hw1

/-! ## The components of the derivative of the pair map `y ↦ (ξ y, Az y)` -/

section Pair

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/- The first component of the derivative of the pair map is the derivative of `ξ`. -/
set_option backward.isDefEq.respectTransparency.types false in
private lemma mfderiv_fst_pair {ξ : M → ℝ} {Az : M → EuclideanSpace ℝ (Fin 2)} {x : M}
    (hξ : MDifferentiableAt I 𝓘(ℝ,ℝ) ξ x)
    (hAz : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) Az x) (v : TangentSpace I x) :
    (NormedSpace.fromTangentSpace (ξ x)) (mfderiv I 𝓘(ℝ,ℝ) ξ x v)
      = ((NormedSpace.fromTangentSpace (ξ x, Az x))
          ((mfderiv I 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2))
            (fun y : M => (ξ y, Az y)) x) v)).1 := by
  have hpair : MDifferentiableAt I 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2))
      (fun y : M => (ξ y, Az y)) x := hξ.prodMk_space hAz
  have hfst := mfderiv_clm_apply (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 2))) hpair v
  rw [show (fun y : M => (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 2))) ((ξ y, Az y)))
      = ξ from funext (fun y => rfl)] at hfst
  exact hfst

/- The second component of the derivative of the pair map is the derivative of `Az`. -/
set_option backward.isDefEq.respectTransparency.types false in
private lemma mfderiv_snd_pair {ξ : M → ℝ} {Az : M → EuclideanSpace ℝ (Fin 2)} {x : M}
    (hξ : MDifferentiableAt I 𝓘(ℝ,ℝ) ξ x)
    (hAz : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) Az x) (v : TangentSpace I x) :
    (NormedSpace.fromTangentSpace (Az x)) (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) Az x v)
      = ((NormedSpace.fromTangentSpace (ξ x, Az x))
          ((mfderiv I 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2))
            (fun y : M => (ξ y, Az y)) x) v)).2 := by
  have hpair : MDifferentiableAt I 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2))
      (fun y : M => (ξ y, Az y)) x := hξ.prodMk_space hAz
  have hsnd := mfderiv_clm_apply (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 2))) hpair v
  rw [show (fun y : M => (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 2))) ((ξ y, Az y)))
      = Az from funext (fun y => rfl)] at hsnd
  exact hsnd

end Pair

theorem sphere_immersion_criterion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ξ : M → ℝ} {Az : M → EuclideanSpace ℝ (Fin 2)} {x : M}
    (hξ : MDifferentiableAt I 𝓘(ℝ,ℝ) ξ x)
    (hAz : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) Az x)
    (hsin : Real.sin (ξ x) ≠ 0)
    (hker : ∀ v : TangentSpace I x,
      mfderiv I 𝓘(ℝ,ℝ) ξ x v = 0 →
      Work.Diff.Dim2.angForm (I := I) (M := M) (Az := Az) x v = 0 → v = 0) :
    Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (fun y : M => Work.Diff.Dim2.sphereAmb (ξ y, Az y)) x) := by
  have hpair : MDifferentiableAt I 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2))
      (fun y : M => (ξ y, Az y)) x := hξ.prodMk_space hAz
  have key : ∀ v : TangentSpace I x,
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        (fun y : M => sphereAmb (ξ y, Az y)) x v = 0 → v = 0 := by
    intro v hv
    have hchain := mfderiv_comp (f := fun y : M => (ξ y, Az y)) (g := sphereAmb) x
      (mdiff_sphereAmb (ξ x, Az x)) hpair
    rw [show mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          (fun y : M => sphereAmb (ξ y, Az y)) x
        = (mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
            sphereAmb (ξ x, Az x)).comp
          (mfderiv I 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2))
            (fun y : M => (ξ y, Az y)) x)
        from hchain, ContinuousLinearMap.comp_apply] at hv
    have hv2 : fderiv ℝ sphereAmb (ξ x, Az x)
        (NormedSpace.fromTangentSpace (ξ x, Az x)
          ((mfderiv I 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2))
            (fun y : M => (ξ y, Az y)) x) v)) = 0 := by
      have h := hv
      rw [mfderiv_eq_fderiv] at h
      exact h
    obtain ⟨hX1, hX2⟩ := fderiv_sphereAmb_apply_eq_zero (q := (ξ x, Az x)) hsin (by
      exact hv2)
    have hξ0 : mfderiv I 𝓘(ℝ,ℝ) ξ x v = 0 := by
      refine (NormedSpace.fromTangentSpace (ξ x)).map_eq_zero_iff.mp ?_
      rw [mfderiv_fst_pair hξ hAz v]
      exact hX1
    have hY : (NormedSpace.fromTangentSpace (Az x))
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) Az x v) = 0 := by
      rw [mfderiv_snd_pair hξ hAz v]
      exact hX2
    have hang : angForm (I := I) (M := M) (Az := Az) x v = 0 := by
      have hthis : angForm (I := I) (M := M) (Az := Az) x v
          = (innerSL ℝ (rot90 (Az x))) ((NormedSpace.fromTangentSpace (Az x))
              (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) Az x v)) := rfl
      rw [hthis, hY, map_zero]
    exact hker v hξ0 hang
  rw [Function.Injective]
  intro v w h
  have hz : v - w = 0 := key (v - w) (by rw [map_sub, h, sub_self])
  exact sub_eq_zero.mp hz

end Work.Diff.Dim2
