import Mathlib

namespace Work.LinnikAreas

/-- If `f : ℤ → ℝ` vanishes below `t` and its restriction to the ray `{t, t+1, t+2, …}`
(viewed as an `ℕ`-indexed sequence) is summable, then `f` itself is summable over `ℤ`. -/
theorem summable_int_of_ray {f : ℤ → ℝ} (t : ℤ) (h0 : ∀ p, p < t → f p = 0)
    (h : Summable fun n : ℕ => f (t + (n:ℤ))) : Summable f := by
  -- `f` is supported on the right ray `{p | t ≤ p}`.
  have hsupp : Function.support f ⊆ {p : ℤ | t ≤ p} := by
    intro p hp
    by_contra hlt
    exact hp (h0 p (not_le.mp hlt))
  -- on that ray the indicator of the ray agrees with `f`.
  have hind : ({p : ℤ | t ≤ p} : Set ℤ).indicator f = f := by
    funext p
    by_cases hp : p ∈ ({p : ℤ | t ≤ p} : Set ℤ)
    · rw [Set.indicator_of_mem hp]
    · have hz : f p = 0 := by
        by_contra hne
        exact hp (hsupp (Function.mem_support.mpr hne))
      rw [Set.indicator_of_notMem hp, hz]
  -- the ray is order-isomorphic to `ℕ` via `n ↦ t + n`.
  let e : ℕ ≃ {p : ℤ // t ≤ p} :=
    { toFun := fun n => ⟨t + (n : ℤ), by omega⟩
      invFun := fun p => ((p : ℤ) - t).toNat
      left_inv := by intro n; simp
      right_inv := by
        rintro ⟨p, hp⟩
        simp only [Subtype.mk.injEq]
        have hz : ((p - t).toNat : ℤ) = p - t := Int.toNat_of_nonneg (by omega)
        rw [hz]; ring }
  have hcomp : Summable ((fun p : {p : ℤ // t ≤ p} => f (p : ℤ)) ∘ e) := by
    rw [show ((fun p : {p : ℤ // t ≤ p} => f (p : ℤ)) ∘ e)
          = (fun n : ℕ => f (t + (n:ℤ))) from rfl]
    exact h
  have hg : Summable (fun p : {p : ℤ // t ≤ p} => f (p : ℤ)) := (e.summable_iff).mp hcomp
  rw [← hind]
  exact (summable_subtype_iff_indicator (s := {p : ℤ | t ≤ p})).mp hg

end Work.LinnikAreas
