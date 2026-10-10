import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Ring.Aut
import Mathlib.Tactic.Ring.RingNF
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.P2Close

/-- Norm-one elements of a field with an involution are squares, granted that fixed elements are: for `σ : E ≃+* E` with `σ ^ 2 = 1` on a field `E`, if every `σ`-fixed element is a square, then every `x` with `x * σ x = 1` is a square. Proof sketch: if `x = -1` use `hfix` (as `σ (-1) = -1`); otherwise put `y := 1 + x` (so `y ≠ 0`) and check `x * σ y = x * σ 1 + (x * σ x) * 1 = x + 1 = y`, `σ (y * σ y) = σ y * y = y * σ y`, so `hfix` gives `y * σ y = z * z`; then `x * (σ y)^2 = (x * σ y) * σ y = y * σ y = z * z` and `σ y ≠ 0`, so `x = (z / σ y)^2`. More generally any `a` with `y := a + x * σ a ≠ 0` works. -/
theorem isSquare_of_mul_aut_eq_one {E : Type*} [Field E] (σ : E ≃+* E) (hσ2 : σ ^ 2 = 1)
    (hfix : ∀ y : E, σ y = y → IsSquare y) :
    ∀ x : E, x * σ x = 1 → IsSquare x := by
  -- `σ` is an involution
  have hσ : ∀ y : E, σ (σ y) = y := fun y => by
    have h := congrArg (fun f : E ≃+* E => f y) hσ2
    simpa using h
  intro x hx
  by_cases hx1 : x = -1
  · -- `x = -1` is `σ`-fixed, hence a square by hypothesis
    rw [hx1]
    exact hfix (-1) (by simp)
  · -- general case: take `y := 1 + x`, which is nonzero and satisfies `x * σ y = y`
    set y : E := 1 + x with hy_def
    have hy : y ≠ 0 := by
      rw [hy_def]
      intro h
      apply hx1
      linear_combination h
    have hxy : x * σ y = y := by
      rw [hy_def, map_add, map_one, mul_add, mul_one, hx]
      ring
    -- `y * σ y` is `σ`-fixed, hence a square
    have hfixy : σ (y * σ y) = y * σ y := by
      rw [map_mul, hσ]
      ring
    obtain ⟨z, hz⟩ := hfix (y * σ y) hfixy
    have hσy : σ y ≠ 0 := fun h => hy (σ.injective (by rw [h, map_zero]))
    refine ⟨z / σ y, ?_⟩
    have hsq : x * σ y ^ 2 = z ^ 2 := by
      have e : x * σ y ^ 2 = (x * σ y) * σ y := by ring
      rw [e, hxy, hz]; ring
    field_simp
    exact hsq

end Work.SSGRoute.P2Close
