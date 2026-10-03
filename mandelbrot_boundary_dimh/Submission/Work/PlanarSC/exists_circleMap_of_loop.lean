import Mathlib
import Submission.Work.PlanarSC.GridWalk

/-!
# A simple loop is the restriction of an injective map defined on the circle

`Work.PlanarSC.exists_circleMap_of_loop`: a path `p : Path x x` which is injective on the
parametrising interval up to the identification of its two endpoints (`IsSimpleLoop p`) factors
through the standard parametrisation `circlePt : unitInterval → Circle` by an *injective*
continuous map `γ : C(Circle, X)`.

The proof is a descent along the quotient map `circlePt`:

* `circlePt` is a continuous surjection from the compact space `unitInterval` onto the Hausdorff
  space `Circle`, hence a quotient map (`IsClosedMap.isQuotientMap` + `IsQuotientMap.continuous_iff`);
* the well-definedness required to descend `p` to `Circle` is exactly the description of the
  fibres of `circlePt` (`circlePt_eq_iff`: `circlePt s = circlePt t` iff `s = t` or
  `{s, t} = {0, 1}`), together with `p 0 = p 1`;
* injectivity of the descended map is `IsSimpleLoop` plus surjectivity of `circlePt`.
-/

open Set
open scoped unitInterval Topology

namespace Work.PlanarSC

noncomputable section

/-- The fibres of the standard parametrisation `t ↦ exp (2 π i t)` of the circle: two parameters
have the same image exactly when they are equal, or when they are the two endpoints of
`unitInterval` in either order. -/
theorem circlePt_eq_iff {s t : unitInterval} :
    circlePt s = circlePt t ↔ s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  refine ⟨fun h => ?_, ?_⟩
  · have himg : Circle.exp (2 * Real.pi * (s : ℝ)) = Circle.exp (2 * Real.pi * (t : ℝ)) := h
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp himg
    have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hs : (s : ℝ) = (t : ℝ) + m := by
      refine mul_left_cancel₀ h2π ?_
      rw [hm]; ring
    obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg m
    · rw [hn] at hs
      push_cast at hs
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · left
        exact Subtype.ext (by simpa [hn0] using hs)
      · right; right
        have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
        have hs1 : (s : ℝ) = 1 := by linarith [s.2.1, s.2.2, t.2.1, hn']
        have ht0 : (t : ℝ) = 0 := by linarith [s.2.1, s.2.2, t.2.1, hn']
        exact ⟨Set.Icc.coe_eq_one.mp hs1, Set.Icc.coe_eq_zero.mp ht0⟩
    · rw [hn] at hs
      push_cast at hs
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · left
        exact Subtype.ext (by simpa [hn0] using hs)
      · right; left
        have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
        have ht1 : (t : ℝ) = 1 := by linarith [s.2.1, s.2.2, t.2.1, t.2.2, hn']
        have hs0 : (s : ℝ) = 0 := by linarith [s.2.1, s.2.2, t.2.1, t.2.2, hn']
        exact ⟨Set.Icc.coe_eq_zero.mp hs0, Set.Icc.coe_eq_one.mp ht1⟩
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · simp
    · simp

theorem exists_circleMap_of_loop {X : Type*} [TopologicalSpace X] {x : X} (p : Path x x)
    (hp : IsSimpleLoop p) :
    ∃ γ : C(Circle, X), Function.Injective γ ∧ ∀ t : unitInterval, γ (circlePt t) = p t := by
  -- `p` is well defined on the fibres of `circlePt`
  have hker : ∀ s t : unitInterval, circlePt s = circlePt t → p s = p t := by
    intro s t h
    rcases circlePt_eq_iff.mp h with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]
    · rw [h1, h2, p.source, p.target]
    · rw [h1, h2, p.source, p.target]
  -- descend `p` along `circlePt`
  obtain ⟨γfun, hγfun⟩ : ∃ g : Circle → X, ∀ t : unitInterval, g (circlePt t) = p t :=
    ⟨fun z => p (Function.surjInv circlePt_surjective z),
      fun t => hker _ t (Function.surjInv_eq circlePt_surjective (circlePt t))⟩
  -- `circlePt` is a quotient map: a continuous surjection from a compact space onto a Hausdorff
  -- space
  have hcl : IsClosedMap circlePt := fun s hs => (hs.isCompact.image continuous_circlePt).isClosed
  have hq : Topology.IsQuotientMap circlePt :=
    hcl.isQuotientMap continuous_circlePt circlePt_surjective
  -- hence continuity descends
  have hcomp : γfun ∘ circlePt = p := funext hγfun
  have hcont : Continuous γfun := (hq.continuous_iff).2 (hcomp ▸ p.continuous)
  refine ⟨⟨γfun, hcont⟩, ?_, hγfun⟩
  -- and injectivity of the descended map is `IsSimpleLoop`
  intro z w hzw
  change γfun z = γfun w at hzw
  obtain ⟨s, hs⟩ := circlePt_surjective z
  obtain ⟨t, ht⟩ := circlePt_surjective w
  have hst : p s = p t := by rw [← hγfun s, ← hγfun t, hs, ht, hzw]
  rcases hp s t hst with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← hs, ← ht, h1]
  · rw [← hs, ← ht, h1, h2]; simp
  · rw [← hs, ← ht, h1, h2]; simp

end

end Work.PlanarSC
