import Mathlib

namespace Work.LinnikAreas

/-- A `ℤ`-indexed sum whose terms vanish below `N` equals the `ℕ`-indexed sum of the shifted
sequence `n ↦ f (N + n)`. -/
theorem tsum_int_eq_tsum_nat_add (f : ℤ → ℝ) (N : ℤ) (h : ∀ p : ℤ, p < N → f p = 0) :
    (∑' p : ℤ, f p) = ∑' n : ℕ, f (N + (n : ℤ)) := by
  have hsupp : Function.support f ⊆ Set.Ici N := by
    intro p hp
    simp only [Set.mem_Ici]
    by_contra hlt
    exact hp (h p (not_le.mp hlt))
  rw [← tsum_subtype_eq_of_support_subset (s := Set.Ici N) hsupp]
  change (∑' p : {p : ℤ // N ≤ p}, f (p : ℤ)) = ∑' n : ℕ, f (N + (n : ℤ))
  let e : ℕ ≃ {p : ℤ // N ≤ p} :=
    { toFun := fun n => ⟨N + (n : ℤ), by omega⟩
      invFun := fun p => ((p : ℤ) - N).toNat
      left_inv := by intro n; simp
      right_inv := by
        rintro ⟨p, hp⟩
        simp only [Subtype.mk.injEq]
        have hz : ((p - N).toNat : ℤ) = p - N := Int.toNat_of_nonneg (by omega)
        rw [hz]; ring }
  rw [← e.tsum_eq (fun p : {p : ℤ // N ≤ p} => f (p : ℤ))]
  rfl

end Work.LinnikAreas
