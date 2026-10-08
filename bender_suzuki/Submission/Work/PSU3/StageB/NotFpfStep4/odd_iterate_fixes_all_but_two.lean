import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep4

/-- If a self-map `f` of a type is fixed pointwise outside the (at most) two points
`a`, `b`, and some odd iterate `f^[m]` (`m` odd) is the identity, then `f` is the
identity everywhere.  The point is that the non-fixed points of `f` form a union of
nontrivial cycles, hence the only possible non-identity behaviour is a transposition
of `a` and `b`, whose order `2` cannot divide the odd number `m`. -/
theorem odd_iterate_fixes_all_but_two {α : Type*} (f : α → α) (m : ℕ) (hm : Odd m)
    (hf : ∀ x, f^[m] x = x) {a b : α}
    (h : ∀ x, x ≠ a → x ≠ b → f x = x) :
    ∀ x, f x = x := by
  obtain ⟨k, hk⟩ := hm
  have hm1 : 1 ≤ m := by omega
  -- `f` is injective because `f^[m-1]` is a left inverse of `f`.
  have hinj : Function.Injective f := by
    apply Function.LeftInverse.injective (g := f^[m - 1])
    intro x
    have hstep : f^[m - 1 + 1] x = f^[m - 1] (f x) :=
      Function.iterate_succ_apply f (m - 1) x
    rw [Nat.sub_add_cancel hm1] at hstep
    rw [← hstep, hf x]
  -- Injectivity forces `f` to preserve the two exceptional points.
  have ha : f a = a ∨ f a = b := by
    rcases eq_or_ne (f a) a with h1 | h1
    · exact Or.inl h1
    · rcases eq_or_ne (f a) b with h2 | h2
      · exact Or.inr h2
      · exact absurd (hinj (h (f a) h1 h2)) h1
  have hb : f b = b ∨ f b = a := by
    rcases eq_or_ne (f b) b with h1 | h1
    · exact Or.inl h1
    · rcases eq_or_ne (f b) a with h2 | h2
      · exact Or.inr h2
      · exact absurd (hinj (h (f b) h2 h1)) h1
  -- `f^[2] z = f (f z)`.
  have h2apply : ∀ z, f^[2] z = f (f z) := by
    intro z
    rw [Function.iterate_succ_apply' f 1 z, Function.iterate_one]
  -- `f` has order dividing `2` (it is either the identity or the transposition of `a`,`b`).
  have hf2 : ∀ y, f^[2] y = y := by
    intro y
    rw [h2apply]
    rcases eq_or_ne y a with hyA | hya
    · rw [hyA]
      rcases ha with h1 | h1
      · rw [h1, h1]
      · rw [h1]
        rcases hb with h2 | h2
        · have hab : a = b := hinj (h1.trans h2.symm)
          rw [h2]; exact hab.symm
        · rw [h2]
    · rcases eq_or_ne y b with hyB | hyb
      · rw [hyB]
        rcases hb with h1 | h1
        · rw [h1, h1]
        · rw [h1]
          rcases ha with h2 | h2
          · rw [h2]; exact (hinj (h1.trans h2.symm)).symm
          · rw [h2]
      · have hy : f y = y := h y hya hyb
        rw [hy, hy]
  -- Since `m` is odd, `f^[m] = f`, and `f^[m]` is the identity.
  intro x
  have hstep : f^[m] x = f x := by
    rw [hk, Function.iterate_add_apply, Function.iterate_one]
    rw [Function.iterate_mul]
    exact Function.iterate_fixed (hf2 (f x)) k
  rw [← hstep]
  exact hf x

end Work.PSU3.StageB.NotFpfStep4
