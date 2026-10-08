import Mathlib

namespace Work.DSTR.M110.twistAux

/-- Hilbert 90 for an order-two automorphism of a field, in the form needed here:
if `a * σ a = 1` (norm one) then there is a nonzero `d` with `a * σ d = d`.

The element is produced by the usual twisted-trace trick: for any `c` the element
`d = c + a * σ c` is a solution (since `a * σ (c + a*σ c) = a*σ c + a*σ a*c = a*σ c + c`),
and it can only vanish for *every* `c` if `a = -1` and `σ = 1`, which is excluded. -/
theorem twistAuxExistsFixedOfNormOne (F : Type*) [Field F]
    (σ : F ≃+* F) (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) (a : F) (ha : a * σ a = 1) :
    ∃ d : F, d ≠ 0 ∧ a * σ d = d := by
  -- `σ` is an involution pointwise.
  have hσ2' : ∀ x : F, σ (σ x) = x := by
    intro x
    have h := DFunLike.congr_fun hσ2 x
    simpa using h
  -- Some `c` gives the nonzero twisted trace `c + a * σ c`.
  have hex : ∃ c : F, c + a * σ c ≠ 0 := by
    by_contra h
    push Not at h
    -- If every twisted trace vanishes, then taking `c = 1` gives `a = -1`, ...
    have ha1 : a = -1 := by
      have h1 : (1 : F) + a = 0 := by have := h 1; simpa using this
      linear_combination h1
    -- ... and then `c + (-1) * σ c = 0` forces `σ c = c` for all `c`, i.e. `σ = 1`.
    refine hσ1 (RingEquiv.ext fun c => ?_)
    have hc := h c
    rw [ha1] at hc
    have : σ c = c := by linear_combination -hc
    simpa using this
  obtain ⟨c, hc⟩ := hex
  -- The twisted trace is a solution.
  refine ⟨c + a * σ c, hc, ?_⟩
  have key : a * σ (c + a * σ c) = c + a * σ c := by
    rw [map_add, map_mul, hσ2' c]
    rw [mul_add, ← mul_assoc a (σ a) c, ha, one_mul]
    ring
  exact key

end Work.DSTR.M110.twistAux
