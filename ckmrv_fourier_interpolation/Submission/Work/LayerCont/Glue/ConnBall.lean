/-
# The intersection of two hyperbolic balls is preconnected

`Work.LayerCont.Glue.exists_glue_two_balls` needs a single geometric input:
`IsPreconnected (B(c₀,ε₀) ∩ B(c₁,ε₁))`.  This file proves it.

The proof is the Euclidean one pushed through the coercion `ℍ → ℂ`:

* hyperbolic balls are *Euclidean* discs (`UpperHalfPlane.image_coe_ball`);
* `coe '' (B₀ ∩ B₁) = (coe '' B₀) ∩ (coe '' B₁)` (injectivity of `coe`, and both sides are images);
* an intersection of two Euclidean discs is **convex** (`convex_ball.inter`), hence preconnected
  (`Convex.isPreconnected`);
* preconnectedness pulls back along the injective, open coercion: given open `u, v ⊆ ℍ` with
  `s ⊆ u ∪ v` and `s ∩ (u ∩ v) = ∅`, their images are open in `ℂ`
  (`Work.LayerCont.FarTail.coe_image_isOpen`), the image of `s` is contained in their union and is
  disjoint from their intersection, so preconnectedness of the image gives `coe '' s ⊆ coe '' u` (or
  `⊆ coe '' v`), and injectivity pulls that back to `s ⊆ u` (or `s ⊆ v`).
-/
import Mathlib
import Submission.Work.LayerCont.Glue.TwoBall

set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.Glue

open Work.Asymptotics Work.LayerCont

/-- **The image of the intersection of two balls is the intersection of the images** (the coercion
`ℍ → ℂ` is injective). -/
lemma coe_image_inter_ball (c₀ c₁ : UpperHalfPlane) (ε₀ ε₁ : ℝ) :
    (fun z : UpperHalfPlane => (z : ℂ)) '' (Metric.ball c₀ ε₀ ∩ Metric.ball c₁ ε₁)
      = ((fun z : UpperHalfPlane => (z : ℂ)) '' Metric.ball c₀ ε₀)
        ∩ ((fun z : UpperHalfPlane => (z : ℂ)) '' Metric.ball c₁ ε₁) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw.1, rfl⟩, ⟨w, hw.2, rfl⟩⟩
  · rintro ⟨⟨w, hw, hwz⟩, ⟨w', hw', hw'z⟩⟩
    have hww : w = w' := UpperHalfPlane.coe_injective (hwz.trans hw'z.symm)
    exact ⟨w, ⟨hw, hww ▸ hw'⟩, hwz⟩

/-- **Preconnectedness pulls back along the coercion**: if the image of `s` is preconnected then so
is `s`.  (The coercion is injective and carries open sets to open sets, which is all the argument
uses.) -/
lemma isPreconnected_of_coe_image {s : Set UpperHalfPlane}
    (h : IsPreconnected ((fun z : UpperHalfPlane => (z : ℂ)) '' s)) : IsPreconnected s := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv huv hdis
  set U : Set ℂ := (fun z : UpperHalfPlane => (z : ℂ)) '' u with hU
  set V : Set ℂ := (fun z : UpperHalfPlane => (z : ℂ)) '' v with hV
  have hUopen : IsOpen U := hU ▸ Work.LayerCont.FarTail.coe_image_isOpen hu
  have hVopen : IsOpen V := hV ▸ Work.LayerCont.FarTail.coe_image_isOpen hv
  have hsub : ((fun z : UpperHalfPlane => (z : ℂ)) '' s) ⊆ U ∪ V := by
    rintro z ⟨w, hws, rfl⟩
    rcases huv hws with hw | hw
    · exact Or.inl ⟨w, hw, rfl⟩
    · exact Or.inr ⟨w, hw, rfl⟩
  have hdis' : ((fun z : UpperHalfPlane => (z : ℂ)) '' s) ∩ (U ∩ V) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨⟨w, hws, rfl⟩, ⟨w₂, hw₂, hw₂eq⟩, ⟨w₃, hw₃, hw₃eq⟩⟩
    have h2 : w₂ = w := UpperHalfPlane.coe_injective hw₂eq
    have h3 : w₃ = w := UpperHalfPlane.coe_injective hw₃eq
    have hmem : w ∈ s ∩ (u ∩ v) := ⟨hws, h2 ▸ hw₂, h3 ▸ hw₃⟩
    rw [hdis] at hmem
    exact hmem
  rcases isPreconnected_iff_subset_of_disjoint.mp h U V hUopen hVopen hsub hdis' with hW | hW
  · refine Or.inl fun x hx => ?_
    obtain ⟨y, hy, hyx⟩ := hW ⟨x, hx, rfl⟩
    rwa [UpperHalfPlane.coe_injective hyx] at hy
  · refine Or.inr fun x hx => ?_
    obtain ⟨y, hy, hyx⟩ := hW ⟨x, hx, rfl⟩
    rwa [UpperHalfPlane.coe_injective hyx] at hy

/-- **The intersection of two hyperbolic balls is preconnected.** -/
theorem isPreconnected_inter_ball (c₀ c₁ : UpperHalfPlane) (ε₀ ε₁ : ℝ) :
    IsPreconnected (Metric.ball c₀ ε₀ ∩ Metric.ball c₁ ε₁) := by
  refine isPreconnected_of_coe_image ?_
  rw [coe_image_inter_ball, UpperHalfPlane.image_coe_ball, UpperHalfPlane.image_coe_ball]
  exact ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected

/-- **The two-ball gluing case, unconditional.** -/
theorem exists_glue_two_balls' {c₀ c₁ : UpperHalfPlane} {ε₀ ε₁ : ℝ} {F G : UpperHalfPlane → ℂ}
    (hF : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F
      (Metric.ball c₀ ε₀))
    (hG : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) G
      (Metric.ball c₁ ε₁))
    {V : Set UpperHalfPlane} (hVsub : V ⊆ Metric.ball c₀ ε₀ ∩ Metric.ball c₁ ε₁)
    (hVopen : IsOpen V) (hVne : V.Nonempty) (hV : Set.EqOn F G V) :
    ∃ K : UpperHalfPlane → ℂ,
      MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) K
        (Metric.ball c₀ ε₀ ∪ Metric.ball c₁ ε₁) ∧
      Set.EqOn K F (Metric.ball c₀ ε₀) ∧ Set.EqOn K G (Metric.ball c₁ ε₁) :=
  exists_glue_two_balls hF hG (isPreconnected_inter_ball c₀ c₁ ε₀ ε₁) hVsub hVopen hVne hV

end Work.LayerCont.Glue
