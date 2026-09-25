import Mathlib

/-!
# `Work.ShafarevichKoch.smul_zmodTwo_eq` -- every action on `𝔽₂` is trivial

Any `DistribMulAction` of a group `G` on the additive group `ℤ/2` is **trivial**: `G` acts by
additive automorphisms, `Aut(ℤ/2) = 1`.  This is the reason the hypotheses `hcompN`/`hcompG`
("the action is trivial / factors through `q`") that occur in the Shafarevich--Koch counting
lemmas of this chapter are *not* restrictions at all: for `𝔽₂`-coefficients they are automatic.

`Work.ShafarevichKoch.isLocallyConstant_of_isOpenMap` is the second general-purpose tool used by
the section-free counting engine of `README.md` §16.2: local constancy descends along an open
surjection.
-/

set_option linter.unusedVariables false

namespace Work.ShafarevichKoch

/-- **Every `DistribMulAction` of a group on `ℤ/2` is trivial.** -/
theorem smul_zmodTwo_eq {G : Type*} [Group G] [DistribMulAction G (ZMod 2)] (g : G)
    (m : ZMod 2) : g • m = m := by
  have hcases : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  have hone : g • (1 : ZMod 2) = 1 := by
    rcases hcases (g • (1 : ZMod 2)) with h | h
    · exfalso
      have h' := congrArg (fun z => g⁻¹ • z) h
      simp only [smul_zero] at h'
      simpa using h'
    · exact h
  rcases hcases m with h | h
  · rw [h, smul_zero]
  · rw [h, hone]

/-- **Descent of local constancy along an open surjection.** -/
theorem isLocallyConstant_of_isOpenMap {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {q : X → Y} (hq : IsOpenMap q) (hsurj : Function.Surjective q) {f : Y → Z}
    (hf : IsLocallyConstant (f ∘ q)) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open] at hf ⊢
  intro a
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨U, hU, hxU, hUc⟩ := hf x
  exact ⟨q '' U, hq U hU, ⟨x, hxU, rfl⟩, fun b hb => by
    obtain ⟨u, huU, rfl⟩ := hb
    exact hUc u huU⟩

end Work.ShafarevichKoch
