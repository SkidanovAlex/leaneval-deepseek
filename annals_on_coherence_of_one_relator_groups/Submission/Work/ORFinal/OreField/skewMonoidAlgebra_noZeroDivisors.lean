import Mathlib

namespace Work.ORFinal.OreField

open SkewMonoidAlgebra

/-- The skew monoid algebra of the group `Multiplicative ℤ` (i.e. the skew Laurent
polynomial ring `D[t, t⁻¹; σ]`) over a division ring `D` has no zero divisors.

Proof: take the largest elements `a`, `b` (for the image of the order of `ℤ`) of the
supports of `f` and `g`; the coefficient of `f * g` at `a * b` is `f.coeff a * a • g.coeff b`,
which is nonzero because (i) `a * b` can only be written as a product of an element of
`f.support` and an element of `g.support` in the single way `a * b` (the order on `ℤ` is
cancellative), and (ii) `f.coeff a ≠ 0`, `g.coeff b ≠ 0` and the action of a group element
is injective. -/
theorem skewMonoidAlgebra_noZeroDivisors {D : Type*} [DivisionRing D]
    [MulSemiringAction (Multiplicative ℤ) D]
    (f g : SkewMonoidAlgebra D (Multiplicative ℤ)) (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 := by
  classical
  have hfne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; exact hf (support_eq_empty.mp h)
  have hgne : g.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; exact hg (support_eq_empty.mp h)
  -- the largest terms of `f` and `g`
  set a := f.support.max' hfne with ha_eq
  set b := g.support.max' hgne with hb_eq
  have ha : a ∈ f.support := ha_eq ▸ Finset.max'_mem _ _
  have hb : b ∈ g.support := hb_eq ▸ Finset.max'_mem _ _
  have hfa : f.coeff a ≠ 0 := mem_support_iff.mp ha
  have hgb : g.coeff b ≠ 0 := mem_support_iff.mp hb
  have hle_f : ∀ x ∈ f.support, x ≤ a := by
    intro x hx; rw [ha_eq]; exact Finset.le_max' _ _ hx
  have hle_g : ∀ x ∈ g.support, x ≤ b := by
    intro x hx; rw [hb_eq]; exact Finset.le_max' _ _ hx
  have hab : (a * b) * b⁻¹ = a := by rw [mul_assoc, mul_inv_cancel, mul_one]
  -- the coefficient of `f * g` at the top position `a * b`
  have hcoeff : (f * g).coeff (a * b) = f.coeff a * a • g.coeff b := by
    rw [coeff_mul_right, Finsupp.sum]
    rw [Finset.sum_eq_single b]
    · rw [hab]
    · intro b' hb' hne
      have hlt : b' < b := lt_of_le_of_ne (hle_g b' hb') hne
      have hmem : (a * b) * b'⁻¹ ∉ f.support := by
        intro hmem
        have h1 : a.toAdd + b.toAdd - b'.toAdd ≤ a.toAdd := hle_f _ hmem
        have h2 : b'.toAdd < b.toAdd := hlt
        have h3 : b ≤ b' := by
          have : b.toAdd ≤ b'.toAdd := by linarith
          exact this
        exact hne (le_antisymm (hle_g b' hb') h3)
      rw [notMem_support_iff.mp hmem, zero_mul]
    · intro hbnot; exact absurd hb hbnot
  -- the group action is injective, so the top coefficient is nonzero
  have haction : a • g.coeff b ≠ 0 := by
    intro hzero
    have : g.coeff b = 0 := by
      calc g.coeff b = (1 : Multiplicative ℤ) • g.coeff b := (one_smul _ _).symm
        _ = (a⁻¹ * a) • g.coeff b := by rw [inv_mul_cancel]
        _ = a⁻¹ • (a • g.coeff b) := mul_smul a⁻¹ a _
        _ = a⁻¹ • (0 : D) := by rw [hzero]
        _ = 0 := smul_zero _
    exact hgb this
  intro hzero
  have hc0 : (f * g).coeff (a * b) = 0 := by rw [hzero]; simp
  rw [hcoeff] at hc0
  exact mul_ne_zero hfa haction hc0

end Work.ORFinal.OreField
