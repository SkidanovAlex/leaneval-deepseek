import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.InvAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.InvAux

/--
Two non-trivial involutions `c`, `d` of a field `Ω` of characteristic zero are equal as soon
as every element fixed by `c` is fixed by `d`.

Indeed, pick `y = x - c x ≠ 0` with `c y = -y`.  Then `c` fixes `y * y`, hence so does `d`,
so `(d y)² = y²` and therefore `d y = y` or `d y = -y`.  In both cases one has a closed formula
for `d t` (`2 * d t = (t + c t) + ((t - c t) / y) * d y`), obtained from the fact that
`(t + c t)` and `(t - c t) / y` lie in the fixed field of `c`, whence of `d` as well.  When
`d y = y` this formula gives `d = 1`, contradicting the non-triviality of `d`; hence
`d y = -y = c y`, and the same formula gives `d t = c t` for every `t`.
-/
theorem eq_of_fixes_fixSub {Ω : Type*} [Field Ω] [CharZero Ω] {c d : Ω ≃+* Ω}
    (hc : c * c = 1) (hc1 : c ≠ 1) (hd : d * d = 1) (hd1 : d ≠ 1)
    (hfix : ∀ x : Ω, c x = x → d x = x) : d = c := by
  -- `c` is an involution.
  have hcc : ∀ z, c (c z) = z := by
    intro z
    have := congrArg (fun e : Ω ≃+* Ω => e z) hc
    simpa using this
  -- Non-triviality of `c` supplies some `x` with `c x ≠ x`.
  obtain ⟨x, hx⟩ : ∃ x, c x ≠ x := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hc1 (by ext z; exact h z)
  -- `y = x - c x` is nonzero and satisfies `c y = -y`.
  set y : Ω := x - c x with hydef
  have hy : y ≠ 0 := by
    rw [hydef]
    exact sub_ne_zero.mpr (fun h => hx h.symm)
  have hcy : c y = -y := by
    rw [hydef, map_sub, hcc x]
    ring
  -- `(t - c t) / y` is fixed by `c`.
  have hQfix : ∀ t, c ((t - c t) / y) = (t - c t) / y := by
    intro t
    have h1 : c (t - c t) = -(t - c t) := by
      rw [map_sub, hcc t]; ring
    rw [map_div₀, h1, hcy, neg_div_neg_eq]
  -- `d` fixes `t + c t`, since `c` does.
  have hA : ∀ t, d (t + c t) = t + c t := by
    intro t
    have : c (t + c t) = t + c t := by
      rw [map_add, hcc t]; ring
    exact hfix _ this
  -- `d (t - c t) = ((t - c t) / y) * d y`.
  have hB : ∀ t, d (t - c t) = ((t - c t) / y) * d y := by
    intro t
    have hq := hfix _ (hQfix t)
    have hty : ((t - c t) / y) * y = t - c t := div_mul_cancel₀ (t - c t) hy
    conv_lhs => rw [← hty]
    rw [map_mul, hq]
  -- The key closed formula for `d t`.
  have h2d : ∀ t, (2 : Ω) * d t = (t + c t) + ((t - c t) / y) * (d y) := by
    intro t
    have h2 : d ((2 : Ω) * t) = (2 : Ω) * d t := by rw [map_mul, map_ofNat]
    have h1 : (2 : Ω) * t = (t + c t) + (t - c t) := by ring
    rw [h1, map_add, hA t, hB t] at h2
    exact h2.symm
  -- `(d y)² = y²`.
  have hsq : c (y * y) = y * y := by rw [map_mul, hcy]; ring
  have hsq' : d y * d y = y * y := by
    rw [← map_mul, hfix _ hsq]
  -- Hence `d y = y` or `d y = -y`.
  have hcases : d y = y ∨ d y = -y := by
    have hfac : (d y - y) * (d y + y) = 0 := by
      have : (d y - y) * (d y + y) = d y * d y - y * y := by ring
      rw [this, hsq', sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · left; exact sub_eq_zero.mp h
    · right; exact eq_neg_of_add_eq_zero_left h
  have h2ne : (2 : Ω) ≠ 0 := by norm_num
  rcases hcases with hdy | hdy
  · -- `d y = y` forces `d = 1`, contradicting non-triviality.
    exfalso
    apply hd1
    ext t
    show d t = t
    have key := h2d t
    rw [hdy, div_mul_cancel₀ _ hy] at key
    have : (2 : Ω) * d t = (2 : Ω) * t := by rw [key]; ring
    exact mul_left_cancel₀ h2ne this
  · -- `d y = -y = c y`, and the formula gives `d t = c t`.
    ext t
    show d t = c t
    have key := h2d t
    rw [hdy, mul_neg, div_mul_cancel₀ _ hy] at key
    have : (2 : Ω) * d t = (2 : Ω) * c t := by rw [key]; ring
    exact mul_left_cancel₀ h2ne this

end Work.SSGRoute.InvAux
