import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.Nodes.UEPR

/-
**Strict inequality at `1` is detected by `≤ 1`.**  If two valuations `v` (on `F`) and `w` (on `Ω`,
transported along `algebraMap F Ω`) have the same "unit ball" `{x | · ≤ 1}`, then they have the same
"maximal ideal" `{x | · < 1}` as well.  The point is that `x` is a unit for a valuation (`v x = 1`)
iff both `v x ≤ 1` and `v x⁻¹ ≤ 1`, so the unit groups of the two valuation rings coincide; then
`a < 1 ↔ a ≤ 1 ∧ a ≠ 1` finishes.  No discreteness of the value group of `v`, and no further
hypothesis, is needed.
-/
theorem lt_one_iff {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation F (WithZero (Multiplicative ℤ))) (w : Valuation Ω Γ) (hsub : ∀ x : F, w (algebraMap F Ω x) ≤ 1 ↔ v x ≤ 1) (x : F) : w (algebraMap F Ω x) < 1 ↔ v x < 1 := by
  -- `w` does not vanish on `algebraMap y` for `y ≠ 0` (directly from `y * y⁻¹ = 1`).
  have hmapne : ∀ y : F, y ≠ 0 → w (algebraMap F Ω y) ≠ 0 := by
    intro y hy h0
    have h1 : w (algebraMap F Ω (y * y⁻¹)) = 0 := by
      rw [map_mul, Valuation.map_mul, h0, zero_mul]
    rw [mul_inv_cancel₀ hy, map_one, Valuation.map_one] at h1
    exact one_ne_zero h1
  -- The unit groups of the two valuation rings agree: `v y = 1 ↔ w (algebraMap y) = 1`.
  have key : ∀ y : F, y ≠ 0 → (v y = 1 ↔ w (algebraMap F Ω y) = 1) := by
    intro y hy
    have hvy : v y ≠ 0 := v.ne_zero_iff.mpr hy
    have hby : w (algebraMap F Ω y) ≠ 0 := hmapne y hy
    -- the `≤ 1` conditions on the inverses also correspond
    have hinv : (v y)⁻¹ ≤ 1 ↔ (w (algebraMap F Ω y))⁻¹ ≤ 1 := by
      have e : (v y)⁻¹ = v y⁻¹ := (Valuation.map_inv v y).symm
      have e2 : w (algebraMap F Ω y⁻¹) = (w (algebraMap F Ω y))⁻¹ := by
        rw [show algebraMap F Ω y⁻¹ = (algebraMap F Ω y)⁻¹ by simp [map_inv₀],
            Valuation.map_inv w (algebraMap F Ω y)]
      rw [e, ← hsub y⁻¹, e2]
    -- and `a = 1 ↔ a ≤ 1 ∧ a⁻¹ ≤ 1` on both sides
    have hv1 : v y = 1 ↔ v y ≤ 1 ∧ (v y)⁻¹ ≤ 1 :=
      ⟨fun h => by rw [h]; simp,
        fun h => le_antisymm h.1 ((inv_le_one₀ (zero_lt_iff.mpr hvy)).mp h.2)⟩
    have hw1 : w (algebraMap F Ω y) = 1 ↔
        w (algebraMap F Ω y) ≤ 1 ∧ (w (algebraMap F Ω y))⁻¹ ≤ 1 :=
      ⟨fun h => by rw [h]; simp,
        fun h => le_antisymm h.1 ((inv_le_one₀ (zero_lt_iff.mpr hby)).mp h.2)⟩
    rw [hv1, hw1]
    exact ⟨fun h => ⟨(hsub y).mpr h.1, hinv.mp h.2⟩,
           fun h => ⟨(hsub y).mp h.1, hinv.mpr h.2⟩⟩
  by_cases hx : x = 0
  · subst hx
    simp [Valuation.map_zero]
  · rw [lt_iff_le_and_ne, lt_iff_le_and_ne, hsub x]
    exact ⟨fun h => ⟨h.1, fun hv => h.2 ((key x hx).mp hv)⟩,
           fun h => ⟨h.1, fun hw => h.2 ((key x hx).mpr hw)⟩⟩

end Work.MotV5.Nodes.UEPR
