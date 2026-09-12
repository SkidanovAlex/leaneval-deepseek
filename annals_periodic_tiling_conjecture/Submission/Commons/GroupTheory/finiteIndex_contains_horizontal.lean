import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.GroupTheory

/-- If `L` is a finite-index additive subgroup of `(ℤ × ℤ) × G` with `G` finite, then some
positive multiple of the horizontal element `(((1, 0)), 0)` lies in `L`. -/
theorem finiteIndex_contains_horizontal {G : Type} [AddCommGroup G] [Finite G]
    (L : AddSubgroup ((ℤ × ℤ) × G)) (hL : L.FiniteIndex) :
    ∃ n : ℕ, 0 < n ∧ ((((n : ℤ), (0 : ℤ)), (0 : G)) : (ℤ × ℤ) × G) ∈ L := by
  haveI : L.FiniteIndex := hL
  letI : Fintype (((ℤ × ℤ) × G) ⧸ L) := AddSubgroup.fintypeQuotientOfFiniteIndex (H := L)
  -- In the finite quotient group, the class of the horizontal element has finite additive order.
  let x0 : (ℤ × ℤ) × G := (((1 : ℤ), (0 : ℤ)), (0 : G))
  have hq : IsOfFinAddOrder (x0 : ((ℤ × ℤ) × G) ⧸ L) :=
    isOfFinAddOrder_of_finite _
  rcases (isOfFinAddOrder_iff_nsmul_eq_zero.mp hq) with ⟨n, hnpos, hnzero⟩
  refine ⟨n, hnpos, ?_⟩
  -- hnzero : n • (class x0) = 0 in the quotient, i.e. class (n • x0) = class 0.
  have hcl : (n • x0 : (ℤ × ℤ) × G) = ((((n : ℤ), (0 : ℤ)), (0 : G)) : (ℤ × ℤ) × G) := by
    simp [x0]
  have hclass : ((n • x0 : (ℤ × ℤ) × G) : ((ℤ × ℤ) × G) ⧸ L) =
      ((0 : (ℤ × ℤ) × G) : ((ℤ × ℤ) × G) ⧸ L) := by
    simpa using hnzero
  have hmemb : -((((n : ℤ), (0 : ℤ)), (0 : G)) : (ℤ × ℤ) × G) +
      (0 : (ℤ × ℤ) × G) ∈ L := by
    -- QuotientAddGroup.eq : ↑a = ↑b ↔ -a + b ∈ L
    rw [← hcl]
    exact QuotientAddGroup.eq.mp hclass
  have hmemb' : -((((n : ℤ), (0 : ℤ)), (0 : G)) : (ℤ × ℤ) × G) ∈ L := by
    simpa using hmemb
  simpa using (L.neg_mem hmemb')

end Commons.GroupTheory