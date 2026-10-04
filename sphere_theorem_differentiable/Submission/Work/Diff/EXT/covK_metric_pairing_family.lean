import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.T.metric_pairing_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The metric pairing of two jointly smooth families of fields

`Work.Diff.EXT.covK_metric_pairing_family`: if `G : ℝ → SMet I M` is jointly smooth on an open
set `V ⊆ ℝ × M` (`JointMet G V`) and `Y`, `Z` are jointly smooth families of tangent fields on `V`
(`JointField`), then `(t,y) ↦ (G t).inner y (Y t y) (Z t y)` is jointly `C^∞` on `V`.

This is the family (time-dependent) version of `Work.Diff.T.metric_pairing_smooth`, which handles
the time-independent *cylinder* `J ×ˢ univ`.  The proof is the same: `hG` is a smooth section of
the bundle of bilinear forms pulled back along `Prod.snd`, and `hY`, `hZ` are smooth sections of
the tangent bundle pulled back along `Prod.snd`; evaluating the bilinear form on the two sections
is `ContMDiffWithinAt.clm_bundle_apply₂`.
-/

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

theorem covK_metric_pairing_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hG : JointMet G V)
    {Y Z : ℝ → TField (I := I) (M := M)} (hY : JointField Y V) (hZ : JointField Z V) :
    ContMDiffOn ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ (G p.1).inner p.2 (Y p.1 p.2) (Z p.1 p.2)) V := by
  intro p hp
  have hψ : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun m : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (Prod.snd m)
        ((G m.1).inner (Prod.snd m))) V p := hG p hp
  have hv : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun m : ℝ × M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x)
        (Prod.snd m) (Y m.1 (Prod.snd m))) V p := hY p hp
  have hw : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun m : ℝ × M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x)
        (Prod.snd m) (Z m.1 (Prod.snd m))) V p := hZ p hp
  have hmain : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod I) (I.prod 𝓘(ℝ,ℝ)) ∞
      (fun m : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (Prod.snd m)
        ((G m.1).inner (Prod.snd m) (Y m.1 (Prod.snd m)) (Z m.1 (Prod.snd m)))) V p :=
    ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
      (E₃ := Bundle.Trivial M ℝ) (b := fun m : ℝ × M => Prod.snd m)
      (v := fun m : ℝ × M => Y m.1 (Prod.snd m))
      (w := fun m : ℝ × M => Z m.1 (Prod.snd m))
      (ψ := fun m : ℝ × M => (G m.1).inner (Prod.snd m)) (s := V) (x := p)
      hψ hv hw
  simp only [contMDiffWithinAt_totalSpace] at hmain
  exact hmain.2

end Work.Diff.EXT
