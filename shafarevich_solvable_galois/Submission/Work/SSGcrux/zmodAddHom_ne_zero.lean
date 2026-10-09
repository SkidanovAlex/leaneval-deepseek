import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGcrux

/-- **An additive homomorphism out of `ℤ/p` (`p` prime) with non-zero value at `1` is non-zero
everywhere off `0`**: the kernel of an additive map on `ℤ/p` is an additive subgroup, hence `⊥` or
`⊤`, and `⊤` would force `f 1 = 0`. -/
theorem zmodAddHom_ne_zero {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]
    (f : ZMod p →+ M) (h : f 1 ≠ 0) : ∀ a : ZMod p, a ≠ 0 → f a ≠ 0 := by
  intro a ha
  -- `ℤ/p` is a field (as `p` is prime), so `a ≠ 0` has a multiplicative inverse `b`.
  set b := a⁻¹ with hbdef
  have hb : b * a = 1 := by rw [hbdef]; exact inv_mul_cancel₀ ha
  -- write `b` as the image of its natural representative `n = b.val`
  let n := b.val
  have hn : (n : ZMod p) = b := ZMod.natCast_zmod_val b
  -- hence `f 1 = f (b * a) = f (n • a) = n • f a`
  have key : f 1 = n • f a := by
    rw [← hb]
    have h1 : b * a = n • a := by rw [hn.symm, nsmul_eq_mul]
    rw [h1, map_nsmul]
  -- so `f a = 0` would force `f 1 = n • f a = 0`, contradicting the hypothesis
  intro hfa
  rw [key, hfa, nsmul_zero] at h
  exact h rfl

end Work.SSGcrux
