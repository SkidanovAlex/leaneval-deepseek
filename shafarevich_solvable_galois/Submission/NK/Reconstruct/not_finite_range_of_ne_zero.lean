import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

/-- A nonzero linear map into a torsion-free `ℤ_[ℓ]`-module has infinite range:
the `ℤ_[ℓ]`-multiples of the image of any vector on which `f` does not vanish
already give infinitely many elements of the range. -/
theorem not_finite_range_of_ne_zero {ℓ : ℕ} [Fact ℓ.Prime] {A B : Type*} [AddCommGroup A]
    [Module (PadicInt ℓ) A] [AddCommGroup B] [Module (PadicInt ℓ) B]
    [Module.IsTorsionFree (PadicInt ℓ) B] (f : A →ₗ[PadicInt ℓ] B) (hf : f ≠ 0) :
    ¬ Finite (LinearMap.range f) := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hf
  simp only [LinearMap.zero_apply] at hx
  have hg : Function.Injective (fun n : ℤ => (n : PadicInt ℓ) • f x) := by
    intro n m hnm
    change ((n : PadicInt ℓ) • f x) = ((m : PadicInt ℓ) • f x) at hnm
    have h : (((n - m : ℤ)) : PadicInt ℓ) • f x = 0 := by
      rw [Int.cast_sub, sub_smul, hnm, sub_self]
    have h2 : (((n - m : ℤ)) : PadicInt ℓ) = 0 := by
      rcases smul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hx
    exact sub_eq_zero.mp (Int.cast_injective h2)
  have hinf : (Set.range (fun n : ℤ => (n : PadicInt ℓ) • f x)).Infinite :=
    Set.infinite_range_of_injective hg
  have hsub : Set.range (fun n : ℤ => (n : PadicInt ℓ) • f x) ⊆ LinearMap.range f := by
    rintro _ ⟨n, rfl⟩
    exact ⟨(n : PadicInt ℓ) • x, map_smul f _ x⟩
  have := Set.Infinite.mono hsub hinf
  simpa [Set.Infinite, Set.Finite] using this

end NK.Reconstruct
