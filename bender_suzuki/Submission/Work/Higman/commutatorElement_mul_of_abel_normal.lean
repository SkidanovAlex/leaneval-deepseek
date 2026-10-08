import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

open scoped commutatorElement

/-- If `A` is an abelian normal subgroup of a group `G` and `A ≤ C`, then for every `c ∈ C`
the map `a ↦ ⁅a, c⁆` is multiplicative on `A`. -/
theorem commutatorElement_mul_of_abel_normal {G : Type} [Group G] {A C : Subgroup G}
    (hAn : A.Normal) (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) {c : G} (hc : c ∈ C) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  -- The commutator of an element of the normal subgroup `A` with any `c` again lies in `A`:
  -- `⁅a, c⁆ = a * (c * a⁻¹ * c⁻¹)` is a product of `a ∈ A` with a conjugate of `a⁻¹ ∈ A`.
  have hmem_a : ⁅a, c⁆ ∈ A := by
    rw [commutatorElement_def]
    simpa only [mul_assoc] using A.mul_mem ha (hAn.conj_mem a⁻¹ (A.inv_mem ha) c)
  have hmem_b : ⁅b, c⁆ ∈ A := by
    rw [commutatorElement_def]
    simpa only [mul_assoc] using A.mul_mem hb (hAn.conj_mem b⁻¹ (A.inv_mem hb) c)
  -- Since `A` is abelian, `a` commutes with `⁅b, c⁆`, and the two commutators commute.
  have h1 : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ := by
    rw [hAb a ha ⁅b, c⁆ hmem_b, mul_assoc, mul_inv_cancel, mul_one]
  rw [commutatorElement_mul_left_eq_conj_mul, h1, hAb ⁅b, c⁆ hmem_b ⁅a, c⁆ hmem_a]

end Work.Higman
