import Mathlib
import Submission.Work.Diff.EXT.ricCore

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Local joint smoothness of a metric pairing

If `t ↦ G t` is a jointly smooth family of Riemannian metrics on the open time set `J ∋ t₀`, and
`Y`, `Z` are sections of the tangent bundle that are `C^∞` at `x` (only *at* `x`, which is what the
coordinate frame of a chart provides), then `(t, y) ↦ (G t).inner y (Y y) (Z y)` is jointly `C^∞`
near `(t₀, x)`.

The proof is the local counterpart of `Work.Diff.T.metric_pairing_smooth`: `JointSmooth G J` makes
`(t, y) ↦ (G t).inner y` a smooth section of the bundle of bilinear forms over `M`, pulled back to
`ℝ × M` along `Prod.snd`; Mathlib's `ContMDiffWithinAt.clm_bundle_apply₂` evaluates it against the
two pulled-back sections `Y ∘ Prod.snd`, `Z ∘ Prod.snd`; finally
`contMDiffWithinAt_totalSpace` unfolds the (trivial) bundle `Bundle.Trivial M ℝ` so that the total
space map is the scalar function itself.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

/-- **Joint smoothness of a metric pairing along a jointly smooth family (local form).**  If
`t ↦ G t` is a jointly smooth family of metrics on the open time set `J ∋ t₀` and the sections `Y`,
`Z` are `C^∞` at `x`, then `(t, y) ↦ (G t).inner y (Y y) (Z y)` is jointly `C^∞` near `(t₀, x)`.
The hypotheses on `Y`, `Z` are only local, which is what the coordinate frame of a chart (smooth
only on the chart) requires. -/
theorem contMDiffAt_metric_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) {x : M}
    {Y Z : Π y : M, TangentSpace I y} (hY : SmoothFieldAt I M Y x) (hZ : SmoothFieldAt I M Z x) :
    JointSmoothAt I M (fun p : ℝ × M => (G p.1).inner p.2 (Y p.2) (Z p.2)) t₀ x := by
  -- `(t₀, x)` lies in the interior of the set `J ×ˢ univ` on which `G` is jointly smooth
  have hmem : J ×ˢ (univ : Set M) ∈ 𝓝 (t₀, x) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (hJ.mem_nhds ht₀) Filter.univ_mem
  -- the family of bilinear forms, as a smooth section of the bundle of bilinear forms
  have hψ : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun m : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (Prod.snd m)
        ((G m.1).inner (Prod.snd m))) (t₀, x) := hG.contMDiffAt hmem
  -- the two smooth sections, pulled back along `Prod.snd`
  have hYc : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E)) ∞
      ((T% Y) ∘ (Prod.snd : ℝ × M → M)) (t₀, x) :=
    hY.comp (t₀, x) contMDiffAt_snd
  have hZc : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E)) ∞
      ((T% Z) ∘ (Prod.snd : ℝ × M → M)) (t₀, x) :=
    hZ.comp (t₀, x) contMDiffAt_snd
  -- evaluate the bilinear form on the two sections
  have hmain : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun m : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (Prod.snd m)
        ((G m.1).inner (Prod.snd m) (Y (Prod.snd m)) (Z (Prod.snd m))))
      univ (t₀, x) :=
    ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
      (E₃ := Bundle.Trivial M ℝ) (b := fun m : ℝ × M => Prod.snd m)
      (v := fun m : ℝ × M => Y (Prod.snd m)) (w := fun m : ℝ × M => Z (Prod.snd m))
      (ψ := fun m : ℝ × M => (G m.1).inner (Prod.snd m)) (s := univ) (x := (t₀, x))
      hψ hYc hZc
  -- the trivialization of `Bundle.Trivial M ℝ` is the identity, so the second component of the
  -- total space map is exactly the scalar function we want
  simp only [contMDiffWithinAt_totalSpace] at hmain
  exact hmain.2

end Work.Diff.EXT
