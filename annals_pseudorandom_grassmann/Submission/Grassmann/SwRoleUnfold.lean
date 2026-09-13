import Submission.Grassmann.ReindexMain

/-!
# Unfolding the role-space switching sum

`inv_mul_swRoleSum` turns

`c⁻¹ * (b * SwRoleSum t f d)`   (`c = 2 ^ (dim WrOf t * codim (VrOf t))`, `b = 2 ^ (3 d·rank X)`, `X = t.2.2`)

into a sum over `p : QPair m n t` of `b * G V₃ W₃ (XsOf t p) f`, guarded by `ReindexGood`,
which is exactly the shape in which the reindexing `Φ₃` and the weighted fibre bound apply.

The unfolding of `SwTermRole` is expensive, so this file is deliberately kept separate and
compiled with a large heartbeat budget.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 100000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-- `SwTermRole` written with `G`. -/
theorem SwTermRole_eq_G (t : Triple m n) (p : QPair m n t)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    SwTermRole t p f =
      (2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
        ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))) *
        G (liftV t.1 p.1) (liftW t.2.1 p.2) (XsOf t p) f := by
  unfold SwTermRole G
  rfl

/-- `SwRoleSum` written as a sum of `G`-terms. -/
theorem SwRoleSum_eq (t : Triple m n) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (d : ℕ) :
    SwRoleSum t f d = ∑ p : QPair m n t,
      (if ReindexGood d ⟨t, p⟩ then
        (2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
          ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))) *
          G (liftV t.1 p.1) (liftW t.2.1 p.2) (XsOf t p) f else 0) := by
  rw [SwRoleSum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h1 : p.1 ⊓ VrOf t = ⊥ ∧ p.2 ⊔ WrOf t = ⊤
  · rw [if_pos h1]
    by_cases h2 : SwGuard t d (pV t p) (pW t p)
    · rw [if_pos h2, if_pos (show ReindexGood d (⟨t, p⟩ : Σ t : Triple m n, QPair m n t)
          from ⟨h1, h2⟩), SwTermRole_eq_G]
    · rw [if_neg h2, if_neg (fun h => h2 h.2)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]

/-- **The role-space switching sum in `G`-form.**  The factor `c⁻¹` cancels the factor `c` of
`SwTermRole`. -/
theorem inv_mul_swRoleSum (t : Triple m n) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (d : ℕ) :
    ((2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
        ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))))⁻¹ *
      ((2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) * SwRoleSum t f d)
    = ∑ p : QPair m n t,
        (if ReindexGood d ⟨t, p⟩ then
          (2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) *
            G (liftV t.1 p.1) (liftW t.2.1 p.2) (XsOf t p) f else 0) := by
  set c : ℝ := (2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
    ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))) with hc
  set b : ℝ := (2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) with hb
  have hc0 : c ≠ 0 := by rw [hc]; positivity
  rw [SwRoleSum_eq, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : ReindexGood d ⟨t, p⟩
  · rw [if_pos h, if_pos h]
    show c⁻¹ * (b * (c * G (liftV t.1 p.1) (liftW t.2.1 p.2) (XsOf t p) f))
      = b * G (liftV t.1 p.1) (liftW t.2.1 p.2) (XsOf t p) f
    calc c⁻¹ * (b * (c * G (liftV t.1 p.1) (liftW t.2.1 p.2) (XsOf t p) f))
        = (c⁻¹ * c) * (b * G (liftV t.1 p.1) (liftW t.2.1 p.2) (XsOf t p) f) := by ring
      _ = b * G (liftV t.1 p.1) (liftW t.2.1 p.2) (XsOf t p) f := by
            rw [inv_mul_cancel₀ hc0, one_mul]
  · rw [if_neg h, if_neg h]; ring

end
end Submission.Grassmann
