import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.vchar_norm_one
import Submission.Work.CharCore.isVChar_iff_exists_int_coeffs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore.cfInner_self_vchar_nat`

The self-inner-product of a virtual character is a natural number.

A virtual character is an integral linear combination `f = ∑_{χ ∈ Irr G} c χ • χ` of the
irreducible characters (`Work.CharCore.isVChar_iff_exists_int_coeffs`).  Orthonormality of
`Irr G` for `cfInner` (`Work.CharCore.irr_orthonormal`) makes the self-inner-product the
sum of the squares of the integer coefficients,

`cfInner f f = ∑_{χ ∈ Irr G} (c χ)^2`

(`Work.CharCore.cfInner_eq_sum_sq`).  A sum of squares of integers is a nonnegative integer,
and casting a nonnegative integer to `ℂ` is its image under `ℕ → ℂ`, so `cfInner f f` is a
natural number.
-/

noncomputable section

open Classical Finset

namespace Work.CharCore

theorem cfInner_self_vchar_nat {G : Type*} [Group G] [Fintype G] {f : G → ℂ} (hf : IsVChar f) :
    ∃ n : ℕ, cfInner f f = n := by
  obtain ⟨c, hc⟩ := (isVChar_iff_exists_int_coeffs (G := G)).mp hf
  -- the norm is the sum of the squares of the integer coefficients
  have hsq : cfInner f f = ∑ x : ↥(Irr G), ((c x : ℤ) : ℂ) ^ 2 := by
    rw [hc]
    exact cfInner_eq_sum_sq (s := Irr G) (fun _ hx => hx) c
  -- that integer sum of squares is nonnegative, so it is the image of its `toNat`
  refine ⟨(∑ x : ↥(Irr G), (c x) ^ 2).toNat, ?_⟩
  rw [hsq]
  have hS : 0 ≤ (∑ x : ↥(Irr G), (c x) ^ 2) := Finset.sum_nonneg (fun x _ => sq_nonneg (c x))
  have hcast : ((∑ x : ↥(Irr G), (c x) ^ 2).toNat : ℂ)
      = ((∑ x : ↥(Irr G), (c x) ^ 2 : ℤ) : ℂ) := by
    have := Int.toNat_of_nonneg hS
    exact_mod_cast this
  rw [hcast]
  simp only [Int.cast_sum, Int.cast_pow]

end Work.CharCore
