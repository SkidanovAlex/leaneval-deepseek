import Mathlib
import Submission.Work.Smooth.Jordan.Sphere

/-!
# Transporting a Schoenflies decomposition of a curve along an ambient homeomorphism

`SphereSchoenflies A c` says that the simple closed curve `c` in `A ⊆ ℝ³` is the common boundary
of two embedded closed discs in `A` which cover `A` and meet exactly in the curve
(`Work.Smooth.Jordan.Sphere`).

The present file shows that this datum is transported by any homeomorphism `φ : ℝ³ ≃ₜ ℝ³`: the
curve `t ↦ φ (c t)` in `φ '' A` is again the common boundary of two embedded discs.  Concretely,
the images under `φ` of the two discs of `h` are the two discs of the transported datum; this uses
only that `φ` is a bijection (`φ '' (B ∩ B') = φ '' B ∩ φ '' B'`) and that images commute with
unions and preserve `Set.range` (`Set.range_comp`).

This is the functoriality of the Schoenflies input used to move the round-sphere statement to any
embedded `2`-sphere (e.g. the boundary of Pardon's box) along an explicit ambient homeomorphism.
-/

open Set
open Classical
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.Jordan

noncomputable section

/-- A simple closed curve in `A ⊆ ℝ³` remains a simple closed curve in `φ '' A` when composed with
an ambient homeomorphism `φ`: membership, continuity and `2π`-periodicity are immediate, and
simplicity is inherited because `φ` is injective. -/
private lemma isSimpleClosedCurveOn_image_homeomorph {A : Set R3} {c : ℝ → R3}
    (h : IsSimpleClosedCurveOn A c) (φ : R3 ≃ₜ R3) :
    IsSimpleClosedCurveOn (φ '' A) (fun t => φ (c t)) :=
  ⟨fun t => ⟨c t, h.1 t, rfl⟩,
   φ.continuous.comp h.2.1,
   fun t => congrArg φ (h.2.2.1 t),
   fun _s hs _t ht hst => h.2.2.2 hs ht (φ.injective hst)⟩

/-- **Jordan–Schoenflies is natural under ambient homeomorphisms**: if `c` in `A` is the common
boundary of two embedded discs covering `A`, then `t ↦ φ (c t)` in `φ '' A` is the common boundary
of the images of the two discs under `φ`. -/
theorem sphere_schoenflies_map_homeomorph {A : Set LeanEval.KnotTheory.PardonDistortion.R3} {c : ℝ → LeanEval.KnotTheory.PardonDistortion.R3} (h : SphereSchoenflies A c) (φ : LeanEval.KnotTheory.PardonDistortion.R3 ≃ₜ LeanEval.KnotTheory.PardonDistortion.R3) : Nonempty (SphereSchoenflies (φ '' A) (fun t => φ (c t))) := by
  classical
  -- `φ` as a bundled continuous map, so that the discs of `h` can be post-composed with it.
  let ψ : C(R3, R3) := ⟨φ, φ.continuous⟩
  have hψ : ⇑ψ = ⇑φ := rfl
  have hrange₁ : Set.range ⇑(ψ.comp h.e) = φ '' Set.range ⇑h.e := by
    rw [ContinuousMap.coe_comp, Set.range_comp, hψ]
  have hrange₂ : Set.range ⇑(ψ.comp h.e') = φ '' Set.range ⇑h.e' := by
    rw [ContinuousMap.coe_comp, Set.range_comp, hψ]
  refine ⟨{ simple := isSimpleClosedCurveOn_image_homeomorph h.simple φ
            e := ψ.comp h.e
            e' := ψ.comp h.e'
            inj := ?_
            inj' := ?_
            boundary := ?_
            boundary' := ?_
            mem := ?_
            mem' := ?_
            cover := ?_
            meet := ?_ }⟩
  · -- injectivity of `φ ∘ e`
    rw [ContinuousMap.coe_comp]
    exact φ.injective.comp h.inj
  · rw [ContinuousMap.coe_comp]
    exact φ.injective.comp h.inj'
  · -- the boundary of the first transported disc is `φ ∘ c`
    intro θ
    show ψ (h.e (circlePoint θ)) = φ (c θ)
    rw [h.boundary θ]
    rfl
  · intro θ
    show ψ (h.e' (circlePoint θ)) = φ (c θ)
    rw [h.boundary' θ]
    rfl
  · -- the transported discs still lie in the image of the surface
    intro z
    exact ⟨h.e z, h.mem z, rfl⟩
  · intro z
    exact ⟨h.e' z, h.mem' z, rfl⟩
  · -- the two transported discs cover `φ '' A`
    rw [hrange₁, hrange₂, ← Set.image_union, h.cover]
  · -- and they meet exactly in the transported curve
    rw [hrange₁, hrange₂, ← Set.image_inter φ.injective, h.meet]
    rw [← Set.range_comp]
    congr 1

end

end Work.Smooth.Jordan
