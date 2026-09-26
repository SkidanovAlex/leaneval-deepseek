import Mathlib
import Submission.Work.FunctionalEquations.Basic

namespace Work.FunctionalEquations

/-- A function on the upper half-plane that is invariant under translation by `1`
is invariant under translation by any integer.  The imaginary part is unchanged
by real translations, so the periodicity hypothesis applies at every intermediate
point. -/
theorem PeriodicIntTranslate {f : ℂ → ℂ} (hper : ∀ τ : ℂ, 0 < τ.im → f (τ + 1) = f τ) :
    ∀ (k : ℤ) (τ : ℂ), 0 < τ.im → f (τ + k) = f τ := by
  -- Invariance under translation by a natural number.
  have hnat : ∀ n : ℕ, ∀ τ : ℂ, 0 < τ.im → f (τ + (n : ℂ)) = f τ := by
    intro n
    induction n with
    | zero => intro τ _; simp
    | succ n ih =>
      intro τ h
      have hcast : τ + ((n + 1 : ℕ) : ℂ) = (τ + (n : ℂ)) + 1 := by
        push_cast; ring
      rw [hcast, hper (τ + (n : ℂ)) (by simpa using h), ih τ h]
  intro k τ h
  by_cases hk : 0 ≤ k
  · -- Nonnegative case: write `k` as a natural number.
    have hk' : k = (k.toNat : ℤ) := (Int.toNat_of_nonneg hk).symm
    rw [hk']
    push_cast
    exact hnat k.toNat τ h
  · -- Negative case: translate the point up by `-k` to reduce to the natural case.
    have hklt : k < 0 := not_le.mp hk
    set n : ℕ := (-k).toNat with hn
    have hk' : k = -(n : ℤ) := by
      have : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      omega
    have him : 0 < (τ + (k : ℂ)).im := by
      rw [show (τ + (k : ℂ)).im = τ.im by simp]; exact h
    have hkey := hnat n (τ + (k : ℂ)) him
    have hsum : (τ + (k : ℂ)) + (n : ℂ) = τ := by
      rw [hk']; push_cast; ring
    rw [hsum] at hkey
    exact hkey.symm

end Work.FunctionalEquations
