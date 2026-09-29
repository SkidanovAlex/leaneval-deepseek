import Mathlib
import Submission.Work.Resample.auTailDefs

namespace Work.Resample

open HvdH

/-- The per-term identity: the ideal fixed-point weight `auWi` is exactly `1/(2α)` times the
Gaussian weight `auGauss` at the (unwrapped) window index `auW0 + i`, since the exponent
`π (n-ζ)²/α²` with `ζ = s k/t` equals `π N²/(α² t²)` where `N = t(K+i-m) - s k`. -/
theorem auWi_eq_gauss (p α s t k i : ℕ) (hst : s < t) :
    auWi p α s t k i
      = (1 / (2 * (α : ℝ))) * auGauss α (auZeta s t k) (auW0 p α s t k + (i : ℤ)) := by
  have ht : (t : ℝ) ≠ 0 := by
    have : t ≠ 0 := by omega
    exact_mod_cast this
  have hnt : ((auW0 p α s t k + (i : ℤ) : ℤ) : ℝ) - auZeta s t k
      = (auN p α s t k i : ℝ) / (t : ℝ) := by
    rw [auW0, auZeta, auN]; push_cast; field_simp; ring
  have harg : Real.pi * (((auW0 p α s t k + (i : ℤ) : ℤ) : ℝ) - auZeta s t k) ^ 2 / (α : ℝ) ^ 2
      = Real.pi * (auNsq p α s t k i : ℝ) / ((α : ℝ) ^ 2 * (t : ℝ) ^ 2) := by
    rw [hnt, auNsq]; push_cast
    rcases eq_or_ne α 0 with h0 | hα
    · subst h0; simp
    · field_simp
  rw [auWi, auGauss]
  rw [harg]

theorem auTailWin (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t)
    (u : Fin s → ℂ) (k : Fin t) :
    (∑ i ∈ Finset.range (auL p α),
        ((auWi p α s t (k : ℕ) i : ℝ) : ℂ) *
          u ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩)
      = (1 / (2 * (α : ℝ)) : ℂ) *
        ∑ i ∈ Finset.range (auL p α),
          auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u
            (auW0 p α s t (k : ℕ) + (i : ℤ)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hJ : finMod s (by omega) (auW0 p α s t (k : ℕ) + (i : ℤ))
      = (⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩ : Fin s) := by
    rw [auW0_add]
    exact (auJ_eq_finMod p α s t (k : ℕ) i hs).symm
  rw [auWi_eq_gauss p α s t (k : ℕ) i hst]
  simp only [auHf]
  rw [hJ]
  push_cast
  ring

end Work.Resample
