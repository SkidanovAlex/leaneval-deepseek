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

/-- The metric family `t ↦ (G t).inner x` is a smooth map `ℝ → (TₓM →L TₓM →L ℝ)`.

This is `JointSmooth` composed with the smooth curve `t ↦ (t, x)`, together with the fact that
the scalar product of two `C^n` maps into the fibers of a Riemannian bundle is `C^n`
(`ContMDiffOn.clm_bundle_apply₂` applied to the constant maps `t ↦ u`, `t ↦ v`). -/
theorem metric_family_pairing_smooth
    {G : ℝ → SMet I M} {J : Set ℝ} (hJs : JointSmooth G J) (x : M) (u v : TangentSpace I x) :
    ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun t ↦ (G t).inner x u v) J := by
  have hψ : ContMDiffOn 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun t : ℝ ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x ((G t).inner x)) J := by
    have hc : ContMDiffOn 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ).prod I) ∞ (fun t : ℝ ↦ (t, x)) J :=
      contMDiffOn_id.prodMk contMDiffOn_const
    exact hJs.comp hc (fun t ht => ⟨ht, trivial⟩)
  have hres := ContMDiffOn.clm_bundle_apply₂ (𝕜 := ℝ)
    (F₁ := E) (E₁ := fun y : M ↦ TangentSpace I y)
    (F₂ := E) (E₂ := fun y : M ↦ TangentSpace I y)
    (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
    (b := fun _ : ℝ ↦ x) (ψ := fun t : ℝ ↦ (G t).inner x)
    (v := fun _ : ℝ ↦ u) (w := fun _ : ℝ ↦ v) hψ
    (contMDiffOn_const (c := TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y) x u))
    (contMDiffOn_const (c := TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y) x v))
  have hsrc : MapsTo (fun t : ℝ ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) x
      ((G t).inner x u v)) J (trivializationAt ℝ (Bundle.Trivial M ℝ) x).source :=
    fun _ _ => trivial
  have hiff := (Bundle.Trivialization.contMDiffOn_iff
    (e := trivializationAt ℝ (Bundle.Trivial M ℝ) x)
    (f := fun t : ℝ ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) x ((G t).inner x u v))
    hsrc).mp hres
  refine hiff.2.congr fun t _ => ?_
  rw [Bundle.Trivial.eq_trivialization M ℝ (trivializationAt ℝ (Bundle.Trivial M ℝ) x)]
  simp [Bundle.Trivial.trivialization_apply]

theorem metric_family_deriv
    {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J) {t₀ : ℝ} (hJs : JointSmooth G J)
    (ht₀ : t₀ ∈ J) (x : M) (u v : TangentSpace I x) :
    HasDerivAt (fun t ↦ (G t).inner x u v) (dtMet G t₀ x u v) t₀ := by
  have h1 : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun t : ℝ ↦ (G t).inner x u v) t₀ :=
    (metric_family_pairing_smooth hJs x u v).contMDiffAt (hJ.mem_nhds ht₀)
  have h2 : ContDiffAt ℝ ∞ (fun t : ℝ ↦ (G t).inner x u v) t₀ :=
    contMDiffAt_iff_contDiffAt.mp h1
  have h3 : DifferentiableAt ℝ (fun t : ℝ ↦ (G t).inner x u v) t₀ :=
    h2.differentiableAt (by simp)
  simpa [dtMet] using h3.hasDerivAt

end Work.Diff.T
