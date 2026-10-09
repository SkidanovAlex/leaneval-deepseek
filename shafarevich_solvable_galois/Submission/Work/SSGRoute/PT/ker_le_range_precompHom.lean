import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Factoring an additive map through `g` along a retraction of `range g`

If `f.range = g.ker` and `χ : B →+ X` kills `f.range`, then `χ` factors through `g` provided the
inclusion `range g ↪ C` admits an additive retraction.  This is the exactness input `hbot` of the
`α²`-dévissage (`PT/AlphaTwoAssembly.lean`): it says
`(precompHom g).range ⊇ (precompHom f).ker`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute.PT

theorem ker_le_range_precompHom {A B C X : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup X]
    (f : A →+ B) (g : B →+ C) (hgk : f.range = g.ker)
    (r : C →+ ↥(g.range)) (hr : ∀ x : ↥(g.range), r (x : C) = x)
    (χ : B →+ X) (hχ : ∀ a : A, χ (f a) = 0) :
    ∃ θ : C →+ X, θ.comp g = χ := by
  have hker : g.ker ≤ χ.ker := by
    intro b hb
    rw [← hgk] at hb
    obtain ⟨a, rfl⟩ := hb
    exact AddMonoidHom.mem_ker.mpr (hχ a)
  have hsurj : Function.Surjective g.rangeRestrict := by
    intro y
    obtain ⟨b, hb⟩ := y.2
    exact ⟨b, Subtype.ext hb⟩
  have hle : (g.rangeRestrict).ker ≤ χ.ker := by
    intro b hb
    have hgb : g b = 0 := by
      have h := congrArg (fun t : ↥(g.range) => (t : C)) hb
      change g b = 0 at h
      exact h
    exact hker (AddMonoidHom.mem_ker.mpr hgb)
  let ψ : ↥(g.range) →+ X :=
    (AddMonoidHom.liftOfSurjective g.rangeRestrict hsurj) ⟨χ, hle⟩
  have hψ : ∀ b : B, ψ (g.rangeRestrict b) = χ b := fun b =>
    AddMonoidHom.liftOfRightInverse_comp_apply g.rangeRestrict
      (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨χ, hle⟩ b
  refine ⟨ψ.comp r, ?_⟩
  ext b
  show ψ (r (g b)) = χ b
  have hr' : r (g b) = g.rangeRestrict b := hr (g.rangeRestrict b)
  rw [hr', hψ]

end Work.SSGRoute.PT
