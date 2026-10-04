import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped ContDiff Manifold Bundle
open Bundle

namespace Work.Diff.EXT

/-- **The vertical lift of a section smooth at a point is smooth at that point.**  If `A` is a
section of `TM`, `C^∞` at `x`, then the section `p ↦ (0, A p.2)` of the tangent bundle of the
product manifold `ℝ × M` (model `(modelWithCornersSelf ℝ ℝ).prod I`, so that
`TangentSpace ((modelWithCornersSelf ℝ ℝ).prod I) p` is definitionally `ℝ × TangentSpace I p.2`) is
`C^∞` at `(t₀, x)`.  The second component is the pullback of `A` along `Prod.snd` and the first is
constant; everything is read in the canonical tangent-bundle trivialisation.

Suggested route, entirely with the trivialisation `trivP := trivializationAt (TangentSpace J) (t₀,x)`
of `T(ℝ × M)`:
* `Bundle.Trivialization.contMDiffAt_section_iff` (or `Bundle.contMDiffAt_totalSpace`) reduces the
  goal to smoothness at `(t₀,x)` of `p ↦ (trivP ⟨p, (0, A p.2)⟩).2`.
* On the neighbourhood of `(t₀,x)` where `p ∈ (chartAt (ModelProd ℝ H) (t₀,x)).source` (which holds
  as soon as `p.2 ∈ (chartAt H x).source`) that coordinate equals `(0, (triv_x ⟨p.2, A p.2⟩).2)`,
  where `triv_x := trivializationAt E (TangentSpace I) x`: use
  `Trivialization.continuousLinearMapAt_apply_of_mem`
  (`(e ⟨b, v⟩).2 = (e.continuousLinearMapAt ℝ b) v`), then
  `TangentBundle.continuousLinearMapAt_trivializationAt`
  (`(triv_x).continuousLinearMapAt ℝ b = mfderiv% (extChartAt I x) b`), then `extChartAt_prod`
  together with `mfderiv_prodMap`; note that the first factor is only ever applied to `0`, so it
  need not be identified (`map_zero`).
* Conclude by smoothness at `(t₀,x)` of `p ↦ (0, (triv_x ⟨p.2, A p.2⟩).2)`: the map
  `p ↦ ⟨p.2, A p.2⟩` is `(T% A) ∘ Prod.snd`, hence smooth (`hA.comp _ contMDiffAt_snd`), and
  `z ↦ (triv_x z).2` is smooth at `⟨x, A x⟩` because `triv_x.contMDiffOn` composed with
  `contMDiff_snd` is smooth on `triv_x.source`, which is open and contains `⟨x, A x⟩`
  (`TangentBundle.trivializationAt_baseSet`).

`hA` is the same as `Work.Diff.EXT.SmoothFieldAt I M A x` (`Submission.Work.Diff.EXT.ricCore`), just
written out; `simpa only [Work.Diff.EXT.SmoothFieldAt] using hA` converts between the two forms. -/
theorem contMDiffAt_prod_inr_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {A : Π y : M, TangentSpace I y} {t₀ : ℝ} {x : M}
    (hA : ContMDiffAt I I.tangent (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => (⟨y, A y⟩ : TangentBundle I M)) x) :
    ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) ((modelWithCornersSelf ℝ ℝ).prod I).tangent
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M =>
        (⟨p, (0, A p.2)⟩ : TangentBundle ((modelWithCornersSelf ℝ ℝ).prod I) (ℝ × M)))
      (t₀, x) := by
  -- The vertical lift factors through the canonical identification
  -- `T(ℝ × M) ≃ Tℝ × TM` of `equivTangentBundleProd`, whose inverse is smooth
  -- (`contMDiff_equivTangentBundleProd_symm`), applied to the pair
  -- `(zero section of Tℝ, A)`.
  have h1 : ContMDiffAt 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ)).tangent ∞
      (zeroSection ℝ (TangentSpace 𝓘(ℝ,ℝ))) t₀ :=
    contMDiffAt_zeroSection ℝ (TangentSpace 𝓘(ℝ,ℝ))
  have h2 : ContMDiffAt I I.tangent ∞ (fun y : M => (⟨y, A y⟩ : TangentBundle I M)) x := hA
  have hg := h1.prodMap h2
  have he := (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ,ℝ)) (M := ℝ) (I' := I)
    (M' := M) (n := ∞)).contMDiffAt
    (x := (⟨t₀, (0 : ℝ)⟩, (⟨x, A x⟩ : TangentBundle I M)))
  have hmain : ContMDiffAt (𝓘(ℝ,ℝ).prod I) ((𝓘(ℝ,ℝ).prod I).tangent) ∞
      (fun p : ℝ × M => (equivTangentBundleProd 𝓘(ℝ,ℝ) ℝ I M).symm
        (Prod.map (zeroSection ℝ (TangentSpace 𝓘(ℝ,ℝ)))
          (fun y : M => (⟨y, A y⟩ : TangentBundle I M)) p))
      (t₀, x) := he.comp (t₀, x) hg
  refine hmain.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext p
  rfl

end Work.Diff.EXT
