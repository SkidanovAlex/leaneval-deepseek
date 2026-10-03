import Mathlib

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

open scoped BigOperators

/-- The bijection `ZMod Q × ℤ ≃ ℤ`, `(z, m) ↦ m * Q + z.val`, exhibiting `ℤ` as `Q` disjoint
copies of itself indexed by the residues mod `Q`.  (Its inverse sends `n` to
`((n : ZMod Q), n / Q)`.) -/
private def zmodMulEquiv (Q : ℕ) [NeZero Q] : ZMod Q × ℤ ≃ ℤ where
  toFun p := p.2 * (Q : ℤ) + (p.1.val : ℤ)
  invFun n := ((n : ZMod Q), n / (Q : ℤ))
  left_inv := by
    rintro ⟨z, m⟩
    ext
    · show (((m * (Q : ℤ) + (z.val : ℤ) : ℤ)) : ZMod Q) = z
      push_cast
      rw [ZMod.natCast_self, mul_zero, zero_add, ZMod.natCast_zmod_val]
    · show (m * (Q : ℤ) + (z.val : ℤ)) / (Q : ℤ) = m
      rw [add_comm, Int.add_mul_ediv_right (z.val : ℤ) m (by exact_mod_cast (NeZero.ne Q)),
        Int.ediv_eq_zero_of_lt (Int.natCast_nonneg z.val) (by exact_mod_cast ZMod.val_lt z),
        zero_add]
  right_inv := by
    intro n
    show (n / (Q : ℤ)) * (Q : ℤ) + (((n : ZMod Q)).val : ℤ) = n
    rw [ZMod.val_intCast]
    linarith [Int.emod_add_mul_ediv n (Q : ℤ)]

theorem sum_int_eq_sum_zmod_mul (Q : ℕ) [NeZero Q] (F : ℤ → ℝ) (hF : Summable F) :
    ∑' n : ℤ, F n = ∑ z : ZMod Q, ∑' m : ℤ, F ((m : ℤ) * Q + z.val) := by
  let e : ZMod Q × ℤ ≃ ℤ := zmodMulEquiv Q
  have hsum : Summable (fun p : ZMod Q × ℤ => F (e p)) := hF.comp_injective e.injective
  have hfib : ∀ z : ZMod Q, Summable (fun m : ℤ => F (e (z, m))) := by
    intro z
    refine hF.comp_injective ?_
    intro m₁ m₂ h
    have : m₁ * (Q : ℤ) = m₂ * (Q : ℤ) := add_right_cancel h
    exact mul_right_cancel₀ (by exact_mod_cast (NeZero.ne Q)) this
  have hprod : ∑' p : ZMod Q × ℤ, F (e p) = ∑' z : ZMod Q, ∑' m : ℤ, F (e (z, m)) :=
    hsum.tsum_prod' hfib
  have heq : ∑' p : ZMod Q × ℤ, F (e p) = ∑' n : ℤ, F n := Equiv.tsum_eq e F
  have hfin : (∑' z : ZMod Q, ∑' m : ℤ, F (e (z, m))) = ∑ z : ZMod Q, ∑' m : ℤ, F (e (z, m)) :=
    tsum_fintype _
  exact heq.symm.trans (hprod.trans hfin)

end Work.KMTPlan.A6
