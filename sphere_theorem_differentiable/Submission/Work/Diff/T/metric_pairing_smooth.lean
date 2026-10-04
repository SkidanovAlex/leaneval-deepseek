import Mathlib
import Submission.Work.Diff.T.lc_deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.T

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The metric pairing of two smooth vector fields against a jointly smooth family of metrics
is jointly smooth.**

`hJs : JointSmooth G J` says that `p ↦ ⟨p.2, (G p.1).inner p.2⟩` is a smooth section of the
hom-bundle `End(T M)` over `M`, pulled back to `ℝ × M` along `Prod.snd`; i.e. it is
`C^∞` as a map `ℝ × M → TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (fun x ↦ TangentSpace I x →L … →L ℝ)`.
Evaluating such a smooth family of bilinear forms on two smooth sections is smooth: this is
Mathlib's `ContMDiffWithinAt.clm_bundle_apply₂` with

* base `B := M`, base map `b := Prod.snd : ℝ × M → M`,
* bundles `E₁ = E₂ := TangentSpace I` and `E₃ := Bundle.Trivial M ℝ`.

The only bookkeeping needed is (a) the smooth sections `T% Y`, `T% Z` of the tangent bundle,
composed with the projection `Prod.snd` (defeq to `Bundle.Trivial M E`, which is why the tangent
space elaborates at `E : Type*`), and (b) unfolding `ContMDiffWithinAt_totalSpace` at the end:
the trivialization of `Bundle.Trivial M ℝ` is the identity, so the second component *is* the
scalar function. -/
theorem metric_pairing_smooth
    {G : ℝ → SMet I M} {J : Set ℝ} (hJs : JointSmooth G J)
    {Y Z : Π x : M, TangentSpace I x} (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ (G p.1).inner p.2 (Y p.2) (Z p.2)) (J ×ˢ univ) := by
  intro p hp
  -- the projection `(t, x) ↦ x` is smooth
  have hbs : ContMDiffOn (𝓘(ℝ,ℝ).prod I) I ∞ (Prod.snd : ℝ × M → M) (J ×ˢ univ) :=
    contMDiffOn_snd (I := 𝓘(ℝ,ℝ)) (J := I) (M := ℝ) (N := M)
  -- the smooth sections of the tangent bundle, pulled back along `Prod.snd`
  have hYc : ContMDiffOn (𝓘(ℝ,ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      ((T% Y) ∘ (Prod.snd : ℝ × M → M)) (J ×ˢ univ) :=
    ContMDiffOn.comp (t := Set.univ) (hg := hY.contMDiffOn) (hf := hbs) (by intro x hx; trivial)
  have hZc : ContMDiffOn (𝓘(ℝ,ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      ((T% Z) ∘ (Prod.snd : ℝ × M → M)) (J ×ˢ univ) :=
    ContMDiffOn.comp (t := Set.univ) (hg := hZ.contMDiffOn) (hf := hbs) (by intro x hx; trivial)
  -- the family of bilinear forms, as a smooth section of `End(T M)`
  have hψ : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun m : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (Prod.snd m)
        ((G m.1).inner (Prod.snd m))) (J ×ˢ univ) p := hJs p hp
  -- apply the bilinear form to the two sections
  have hmain : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) (I.prod 𝓘(ℝ,ℝ)) ∞
      (fun m : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (Prod.snd m)
        ((G m.1).inner (Prod.snd m) (Y (Prod.snd m)) (Z (Prod.snd m)))) (J ×ˢ univ) p :=
    ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
      (E₃ := Bundle.Trivial M ℝ) (b := fun m : ℝ × M => Prod.snd m)
      (v := fun m : ℝ × M => Y (Prod.snd m)) (w := fun m : ℝ × M => Z (Prod.snd m))
      (ψ := fun m : ℝ × M => (G m.1).inner (Prod.snd m)) (s := J ×ˢ univ) (x := p)
      hψ (hYc p hp) (hZc p hp)
  -- the trivialization of `Bundle.Trivial M ℝ` is the identity, so its second component is
  -- exactly the scalar function we want
  simp only [contMDiffWithinAt_totalSpace] at hmain
  exact hmain.2

end Work.Diff.T
