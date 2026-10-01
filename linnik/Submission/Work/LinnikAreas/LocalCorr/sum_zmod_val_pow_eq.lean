import Mathlib

namespace Work.LinnikAreas.LocalCorr

/-- **Complete character sum over `ZMod N`.**  For `N ≥ 1`, a primitive `N`-th root of unity
`θ` and any `D : ZMod N`, the sum `∑_{w : ZMod N} θ^{(D*w).val}` equals `N` when `D = 0` and
vanishes otherwise.  Indeed `w ↦ θ^{(D*w).val}` is an additive character of `ZMod N` (using
`θ^N = 1`) which is non-trivial when `D ≠ 0` (its value at `w = 1` is `θ^{D.val} ≠ 1`), and a
non-trivial character of a finite group sums to zero by the shift argument `w ↦ w + 1`. -/
theorem sum_zmod_val_pow_eq (N : ℕ) [NeZero N] {θ : ℂ} (hθ : IsPrimitiveRoot θ N) (D : ZMod N) :
    (∑ w : ZMod N, θ ^ ((D * w).val)) = if D = 0 then (N : ℂ) else 0 := by
  classical
  -- `w ↦ θ^{((D*w).val)}` is an additive character of `ZMod N`.
  have hmap : ∀ a b : ZMod N,
      θ ^ ((D * (a + b)).val) = θ ^ ((D * a).val) * θ ^ ((D * b).val) := by
    intro a b
    rw [mul_add, ZMod.val_add, ZMod.val_mul, ZMod.val_mul,
      pow_eq_pow_of_modEq (Nat.mod_modEq _ _) hθ.pow_eq_one, pow_add]
  have hz : θ ^ ((D * 0).val) = 1 := by
    rw [mul_zero, ZMod.val_zero, pow_zero]
  let ψ : AddChar (ZMod N) ℂ := AddChar.mk (fun w => θ ^ ((D * w).val)) hz hmap
  have hψ : ψ = 0 ↔ D = 0 := by
    rw [AddChar.eq_zero_iff]
    constructor
    · intro h
      by_contra hD
      have hval : D.val ≠ 0 := fun h0 => hD ((ZMod.val_eq_zero D).mp h0)
      have hlt : D.val < N := ZMod.val_lt D
      have h1 : θ ^ D.val = 1 := by
        have := h 1
        simpa [ψ, mul_one] using this
      exact (hθ.pow_ne_one_of_pos_of_lt hval hlt) h1
    · intro hD w
      simp [ψ, hD]
  have hsum : (∑ w : ZMod N, ψ w) = if D = 0 then (N : ℂ) else 0 := by
    rw [AddChar.sum_eq_ite ψ, ZMod.card N]
    by_cases h : D = 0
    · rw [if_pos h, if_pos (hψ.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (hψ.mp hh))]
  simpa [ψ] using hsum

end Work.LinnikAreas.LocalCorr
