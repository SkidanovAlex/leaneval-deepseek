import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep4

set_option linter.unusedSimpArgs false in
theorem step4_rel9 {K : Type} [Field K] [CharP K 2] (μ : K ≃+* K) {c w τ v Y : K}
    (hc : μ c = c) (hw : μ w = w) (hc0 : c ≠ 0) (hw0 : w ≠ 0)
    (e1 : c * Y = τ * μ Y + w) (e2 : v * Y = c⁻¹ * μ Y + w) :
    (v + c) * (1 + μ τ * μ v) = (μ τ + c⁻¹) * (1 + τ * v) := by
  -- From `e2` we get `c⁻¹ * μ Y = v * Y + w`, hence `μ Y = c * (v * Y + w)`.
  have h1 : c⁻¹ * μ Y = v * Y + w := (CharTwo.add_eq_iff_eq_add).mp e2.symm
  have hX : μ Y = c * (v * Y + w) := by
    rw [← h1, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  -- Additive ("= 0") forms of the two given relations.
  have hz_e1 : c * Y + τ * (μ Y) + w = 0 := by
    rw [add_assoc]; exact CharTwo.add_eq_zero.mpr e1
  have hz_e2 : μ Y + c * (v * Y + w) = 0 := CharTwo.add_eq_zero.mpr hX
  -- First key relation: `(μ Y) * (1 + τ*v) = w * (v + c)`.
  have hC : μ Y * (1 + τ * v) = w * (v + c) := by
    have hz : μ Y * (1 + τ * v) + w * (v + c) = 0 := by
      linear_combination
        (norm := (ring_nf; try simp only [Nat.reduceMod, CharTwo.ofNat_eq_mod, Nat.cast_zero,
          mul_zero, neg_zero]))
        hz_e2 + v * hz_e1
    exact CharTwo.add_eq_zero.mp hz
  -- The relation `c * Y = τ * (c * (v * Y + w)) + w` in additive form.
  have he1sub : c * Y + τ * (c * (v * Y + w)) + w = 0 := by
    rw [add_assoc]; exact CharTwo.add_eq_zero.mpr (by rw [← hX]; exact e1)
  -- Second key relation: `c * Y * (1 + τ*v) = w * (1 + τ*c)`.
  have hA : c * Y * (1 + τ * v) = w * (1 + τ * c) := by
    have hz : c * Y * (1 + τ * v) + w * (1 + τ * c) = 0 := by
      linear_combination
        (norm := (ring_nf; try simp only [Nat.reduceMod, CharTwo.ofNat_eq_mod, Nat.cast_zero,
          mul_zero, neg_zero]))
        he1sub
    exact CharTwo.add_eq_zero.mp hz
  -- Apply `μ` to `hA` to get the relation involving `μ τ`, `μ v`.
  have hB : c * (μ Y) * (1 + μ τ * μ v) = w * (1 + μ τ * c) := by
    have := congrArg μ hA
    simpa [map_mul, map_add, map_one, hc, hw] using this
  -- Combine `hC` and `hB`, then cancel `w`.
  have key : w * (c * ((v + c) * (1 + μ τ * μ v)))
      = w * ((1 + μ τ * c) * (1 + τ * v)) := by
    calc w * (c * ((v + c) * (1 + μ τ * μ v)))
        = c * (w * (v + c)) * (1 + μ τ * μ v) := by ring
      _ = c * (μ Y * (1 + τ * v)) * (1 + μ τ * μ v) := by rw [← hC]
      _ = c * (μ Y) * (1 + μ τ * μ v) * (1 + τ * v) := by ring
      _ = w * (1 + μ τ * c) * (1 + τ * v) := by rw [hB]
      _ = w * ((1 + μ τ * c) * (1 + τ * v)) := by ring
  have hfin : c * ((v + c) * (1 + μ τ * μ v)) = (1 + μ τ * c) * (1 + τ * v) :=
    mul_left_cancel₀ hw0 key
  -- Rewrite the right-hand side and cancel `c`.
  have h2 : c * ((v + c) * (1 + μ τ * μ v)) = c * ((μ τ + c⁻¹) * (1 + τ * v)) := by
    rw [hfin]
    field_simp
    ring
  exact mul_left_cancel₀ hc0 h2

end Work.PSU3.StageB.NotFpfStep4
