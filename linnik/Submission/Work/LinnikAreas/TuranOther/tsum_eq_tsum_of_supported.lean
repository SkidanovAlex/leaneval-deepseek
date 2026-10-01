import Mathlib

namespace Work.LinnikAreas.TuranOther

/-- If `f : ℂ → ℂ` is supported on the range of an injective `φ : ℤ → ℂ` and the
sum of `f ∘ φ` over `ℤ` converges, then `f` is summable over `ℂ` with the same
total sum. -/
theorem tsum_eq_tsum_of_supported {f : ℂ → ℂ} {φ : ℤ → ℂ} (hφ : Function.Injective φ)
    (hsupp : ∀ u : ℂ, (∀ n : ℤ, u ≠ φ n) → f u = 0)
    (hf : Summable fun n : ℤ => f (φ n)) :
    Summable f ∧ (∑' u : ℂ, f u) = ∑' n : ℤ, f (φ n) := by
  have hsupp' : ∀ u : ℂ, u ∉ Set.range φ → f u = 0 := by
    intro u hu
    exact hsupp u fun n h => hu ⟨n, h.symm⟩
  have hsupp'' : Function.support f ⊆ Set.range φ := fun u hu =>
    by_contra fun h => hu (hsupp' u h)
  exact ⟨(hφ.summable_iff hsupp').mp hf, (hφ.tsum_eq hsupp'').symm⟩

end Work.LinnikAreas.TuranOther
