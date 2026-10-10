import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.ASZGC

set_option maxHeartbeats 1000000

theorem Lc0_ne_zero (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) (hg : ¬ ∃ c : K, c ^(5:ℕ) - c = g) :
    a ^(5:ℕ) * g ^(2:ℕ) - a ^(3:ℕ) * b ^(2:ℕ) + 2 * a ^(2:ℕ) * b ^(3:ℕ) + 2 * b ^(5:ℕ) * g ^(2:ℕ) ≠ 0 := by
  intro hL
  -- In characteristic 5, `a ^ 2 - a * b - b ^ 2 = (a + 2 * b) ^ 2`, so `a + 2 * b ≠ 0`.
  have hs : a + 2 * b ≠ 0 := by
    intro h0
    apply ha
    have h1 : a ^(2:ℕ) - a * b - b ^(2:ℕ) = (a + 2 * b) ^(2:ℕ) := by
      ring_nf
      reduce_mod_char! <;> ring_nf
    rw [h1, h0]
    first | refl_ring1 | ring
  have hg0 : g ≠ 0 := by
    intro h0
    exact hg ⟨0, by rw [h0]; ring⟩
  -- Key rewriting of `Lc0` as `(a + 2b)^5 g^2 - a^2 b^2 (a - 2b)` (characteristic 5).
  have hkey : a ^(5:ℕ) * g ^(2:ℕ) - a ^(3:ℕ) * b ^(2:ℕ) + 2 * a ^(2:ℕ) * b ^(3:ℕ) + 2 * b ^(5:ℕ) * g ^(2:ℕ)
      = (a + 2 * b) ^(5:ℕ) * g ^(2:ℕ) - a ^(2:ℕ) * b ^(2:ℕ) * (a - 2 * b) := by
    ring_nf
    reduce_mod_char! <;> ring_nf
  rw [hkey] at hL
  have hrel : (a + 2 * b) ^(5:ℕ) * g ^(2:ℕ) = a ^(2:ℕ) * b ^(2:ℕ) * (a - 2 * b) := sub_eq_zero.mp hL
  by_cases habd : a * b * (a - 2 * b) = 0
  · -- Degenerate case: `a ^ 2 * b ^ 2 * (a - 2b) = 0`, so `(a + 2b)^5 * g^2 = 0`, impossible.
    have hprod : a ^(2:ℕ) * b ^(2:ℕ) * (a - 2 * b) = 0 := by
      have h : a ^(2:ℕ) * b ^(2:ℕ) * (a - 2 * b) = a * (a * b * (a - 2 * b)) * b := by ring
      rw [h, habd]
      first | refl_ring1 | ring
    have h0 : (a + 2 * b) ^(5:ℕ) * g ^(2:ℕ) = 0 := by rw [hrel, hprod]
    exact (mul_ne_zero (pow_ne_zero 5 hs) (pow_ne_zero 2 hg0)) h0
  · -- Generic case: exhibit an explicit Artin–Schreier solution `c = -2 g (a + 2b)^2 / (a b)`.
    have hab : a * b ≠ 0 := fun h => habd (by rw [h]; ring)
    have ha0 : a ≠ 0 := fun h => hab (by rw [h]; ring)
    have hb0 : b ≠ 0 := fun h => hab (by rw [h]; ring)
    have hsq : g ^(2:ℕ) * (a + 2 * b) ^(5:ℕ) = a ^(2:ℕ) * b ^(2:ℕ) * (a - 2 * b) := by
      rw [mul_comm]; exact hrel
    have h5 : g ^(5:ℕ) * (a + 2 * b) ^(10:ℕ) = g * (a ^(4:ℕ) * b ^(4:ℕ) * (a - 2 * b) ^(2:ℕ)) := by
      calc g ^(5:ℕ) * (a + 2 * b) ^(10:ℕ) = (g ^(2:ℕ) * (a + 2 * b) ^(5:ℕ)) ^(2:ℕ) * g := by ring
        _ = (a ^(2:ℕ) * b ^(2:ℕ) * (a - 2 * b)) ^(2:ℕ) * g := by rw [hsq]
        _ = g * (a ^(4:ℕ) * b ^(4:ℕ) * (a - 2 * b) ^(2:ℕ)) := by ring
    have hchar : -32 * (a - 2 * b) ^(2:ℕ) + 2 * (a + 2 * b) ^(2:ℕ) - a * b = 0 := by
      ring_nf
      reduce_mod_char! <;> ring_nf
    refine hg ⟨-2 * g * (a + 2 * b) ^(2:ℕ) / (a * b), ?_⟩
    field_simp
    -- `field_simp` clears denominators and cancels the common factor `g` (using `hg0`).
    have h5' : g ^(4:ℕ) * (a + 2 * b) ^(10:ℕ) = a ^(4:ℕ) * b ^(4:ℕ) * (a - 2 * b) ^(2:ℕ) := by
      have h := h5
      rw [show g ^(5:ℕ) * (a + 2 * b) ^(10:ℕ) = g * (g ^(4:ℕ) * (a + 2 * b) ^(10:ℕ)) by ring] at h
      exact mul_left_cancel₀ hg0 h
    rw [show 2 * (a + 2 * b) ^(2:ℕ) * (-(2 ^(4:ℕ) * g ^(4:ℕ) * (a + 2 * b) ^(8:ℕ)) - -(a ^(4:ℕ) * b ^(4:ℕ)))
        = -32 * (g ^(4:ℕ) * (a + 2 * b) ^(10:ℕ)) + 2 * (a + 2 * b) ^(2:ℕ) * a ^(4:ℕ) * b ^(4:ℕ) by ring]
    rw [h5']
    rw [show -32 * (a ^(4:ℕ) * b ^(4:ℕ) * (a - 2 * b) ^(2:ℕ)) + 2 * (a + 2 * b) ^(2:ℕ) * a ^(4:ℕ) * b ^(4:ℕ)
        = a ^(4:ℕ) * b ^(4:ℕ) * (-32 * (a - 2 * b) ^(2:ℕ) + 2 * (a + 2 * b) ^(2:ℕ)) by ring]
    rw [sub_eq_zero.mp hchar]
    first | refl_ring1 | ring

end Work.MotAS.ASZGC
