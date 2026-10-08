import Mathlib

namespace Work.BSW.Cases.K4

set_option linter.unusedVariables false

/-- The map `h ↦ h * u` is a bijection from the set of `h ∈ H` which are inverted
by conjugation with `u` (i.e. `u * h * u = h⁻¹`) onto the set of involutions `y`
lying in the coset `H * u`.  Consequently those two sets have the same cardinality.
(Note: the hypothesis `orderOf u = 2` is not needed for this counting argument,
only `u ∉ H` is used.) -/
theorem ncard_involutions_coset_eq {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (u : G) (hu : orderOf u = 2) (huH : u ∉ H) :
    ({y : G | orderOf y = 2 ∧ ∃ h ∈ H, y = h * u} : Set G).ncard =
      ({h : G | h ∈ H ∧ u * h * u = h⁻¹} : Set G).ncard := by
  -- The two sets are related by the injective map `h ↦ h * u`.
  have hS : ({y : G | orderOf y = 2 ∧ ∃ h ∈ H, y = h * u} : Set G)
      = (fun h : G => h * u) '' {h : G | h ∈ H ∧ u * h * u = h⁻¹} := by
    ext y
    constructor
    · -- Forward: `y = h * u` an involution forces `u * h * u = h⁻¹`.
      rintro ⟨hord, h, hhH, hyh⟩
      refine ⟨h, ⟨hhH, ?_⟩, hyh.symm⟩
      have hord' : orderOf (h * u) = 2 := by rw [← hyh]; exact hord
      have hsq : (h * u) ^ 2 = 1 := (orderOf_eq_prime_iff.mp hord').1
      have h1 : h * u * h * u = 1 := by
        have := hsq; rw [pow_two] at this
        simpa only [mul_assoc] using this
      calc u * h * u = h⁻¹ * (h * u * h * u) := by group
        _ = h⁻¹ * 1 := by rw [h1]
        _ = h⁻¹ := by simp
    · -- Backward: if `u * h * u = h⁻¹` then `h * u` is an involution, and it is
      -- not `1` because `u ∉ H`.
      rintro ⟨h, ⟨hhH, hconj⟩, hyh⟩
      have hy_eq : y = h * u := hyh.symm
      refine ⟨?_, h, hhH, hy_eq⟩
      rw [hy_eq]
      apply orderOf_eq_prime_iff.mpr
      refine ⟨?_, ?_⟩
      · rw [pow_two]
        calc (h * u) * (h * u) = h * (u * h * u) := by group
          _ = h * h⁻¹ := by rw [hconj]
          _ = 1 := by rw [mul_inv_cancel]
      · intro hh
        apply huH
        have hu_eq : u = h⁻¹ := by
          have htmp : h⁻¹ * (h * u) = h⁻¹ * 1 := by rw [hh]
          rwa [inv_mul_cancel_left, mul_one] at htmp
        rw [hu_eq]
        exact H.inv_mem hhH
  rw [hS]
  exact Set.ncard_image_of_injective _ (fun a b hab => mul_right_cancel hab)

end Work.BSW.Cases.K4
