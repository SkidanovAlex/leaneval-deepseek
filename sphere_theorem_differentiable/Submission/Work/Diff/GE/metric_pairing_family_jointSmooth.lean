import Mathlib
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.EXT.contMDiffAt_metric_pairing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of a metric pairing along a time-dependent family of sections

If `t ↦ G t` is a jointly smooth family of Riemannian metrics on an open time set `J ∋ t₀`, and the
time-dependent sections `(t, y) ↦ V t y`, `(t, y) ↦ Z t y` are `C^∞` at `(t₀, x)`, then
`(t, y) ↦ (G t).inner y (V t y) (Z t y)` is `C^∞` at `(t₀, x)`.

This is the time-dependent counterpart of `Work.Diff.EXT.contMDiffAt_metric_pairing`: there, the two
fields are sections of `TM` pulled back to `ℝ × M` along `Prod.snd` and are smooth at `x`; here they
depend on the time as well, which is exactly the case of the moving frame of the gradient estimate.

The proof is the same in both cases: `JointSmooth G J` makes `(t, y) ↦ (G t).inner y` a smooth
section of the bundle of bilinear forms over `M`, pulled back to `ℝ × M` along `Prod.snd`;
Mathlib's `ContMDiffWithinAt.clm_bundle_apply₂` evaluates it against the two pulled-back sections;
finally `contMDiffWithinAt_totalSpace` unfolds the (trivial) bundle `Bundle.Trivial M ℝ` so that the
total space map is the scalar function itself.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

theorem metric_pairing_family_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) {x : M}
    {V Z : ℝ → Π y : M, TangentSpace I y}
    (hV : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, V p.1 p.2⟩ : TangentBundle I M)) (t₀, x))
    (hZ : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, Z p.1 p.2⟩ : TangentBundle I M)) (t₀, x)) :
    ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M ↦ (G p.1).inner p.2 (V p.1 p.2) (Z p.1 p.2)) (t₀, x) := by
  -- `(t₀, x)` lies in the interior of the set `J ×ˢ univ` on which `G` is jointly smooth
  have hmem : J ×ˢ (univ : Set M) ∈ 𝓝 (t₀, x) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (hJ.mem_nhds ht₀) Filter.univ_mem
  -- the family of bilinear forms, as a smooth section of the bundle of bilinear forms
  have hψ : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun m : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (Prod.snd m)
        ((G m.1).inner (Prod.snd m))) (t₀, x) := hG.contMDiffAt hmem
  -- evaluate the bilinear form of `G` on the two time-dependent sections
  have hmain : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun m : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (Prod.snd m)
        ((G m.1).inner (Prod.snd m) (V m.1 (Prod.snd m)) (Z m.1 (Prod.snd m))))
      univ (t₀, x) :=
    ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
      (E₃ := Bundle.Trivial M ℝ) (b := fun m : ℝ × M => Prod.snd m)
      (v := fun m : ℝ × M => V m.1 (Prod.snd m)) (w := fun m : ℝ × M => Z m.1 (Prod.snd m))
      (ψ := fun m : ℝ × M => (G m.1).inner (Prod.snd m)) (s := univ) (x := (t₀, x))
      hψ hV hZ
  -- the trivialization of `Bundle.Trivial M ℝ` is the identity, so the second component of the
  -- total space map is exactly the scalar function we want
  simp only [contMDiffWithinAt_totalSpace] at hmain
  exact hmain.2

end Work.Diff.GE
