import Mathlib
import Submission.Work.PlanarSC.exists_circleMap_of_loop

/-!
# The circle map of a simple closed path in `ℂ`

`Work.PlanarSC.exists_circleMap_of_path`: a closed path `p : Path x x` in `ℂ` which is injective
on the parametrising interval up to the identification of its two endpoints (i.e. `p` is a *simple
closed curve*, a Jordan curve) factors through the standard parametrisation
`t ↦ Circle.exp (2 π i t)` of the circle by an injective continuous map `γ : C(Circle, ℂ)`; and the
image of `γ` is exactly the image of `p`.

This is the `ℂ`-valued, `Set.range`-augmented form of the general topological statement
`Work.PlanarSC.exists_circleMap_of_loop`, which descends `p` along the quotient map `circlePt`
(`circlePt s = circlePt t` iff `s = t` or `{s, t} = {0, 1}`), using
* well-definedness: `circlePt s = circlePt t` forces `p s = p t` (via `p 0 = p 1`);
* continuity: `circlePt` is a continuous surjection from the compact `unitInterval` onto the
  Hausdorff `Circle`, hence a quotient map;
* injectivity: the hypothesis on `p`, which is precisely `IsSimpleLoop p`.

The extra information here is that `Set.range γ = Set.range p`, which follows from the pointwise
identity `γ (circlePt t) = p t` together with surjectivity of `circlePt`.
-/

namespace Work.PlanarSC

open Set

noncomputable section

theorem exists_circleMap_of_path {x : ℂ} (p : Path x x)
    (hp : ∀ s t : unitInterval, p s = p t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    ∃ γ : C(Circle, ℂ), Function.Injective γ ∧
      (∀ t : unitInterval, γ (Circle.exp (2 * Real.pi * (t : ℝ))) = p t) ∧
      Set.range γ = Set.range p := by
  obtain ⟨γ, hγinj, hγval⟩ := exists_circleMap_of_loop p hp
  have hγval' : ∀ t : unitInterval, γ (Circle.exp (2 * Real.pi * (t : ℝ))) = p t :=
    fun t => by simpa [circlePt] using hγval t
  refine ⟨γ, hγinj, hγval', ?_⟩
  ext z
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨t, ht⟩ := circlePt_surjective a
    exact ⟨t, by rw [← ha, ← ht, ← hγval t]⟩
  · rintro ⟨t, ht⟩
    exact ⟨Circle.exp (2 * Real.pi * (t : ℝ)), by rw [hγval', ht]⟩

end

end Work.PlanarSC
