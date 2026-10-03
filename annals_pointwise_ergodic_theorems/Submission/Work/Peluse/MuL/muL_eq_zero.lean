import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.MuL

/-- `μ_L` is supported in `(-L, L)`: for `|h| ≥ L` the pair count `#{h₁,h₂ ∈ [L] : h₁ - h₂ = h}`
is empty because `|h₁ - h₂| ≤ L - 1 < L`. -/
theorem muL_eq_zero {L : ℕ} {h : ℤ} (hh : L ≤ |h|) : Work.Peluse.muL L h = 0 := by
  unfold Work.Peluse.muL
  have hempty : (((Finset.Icc 1 L).product (Finset.Icc 1 L)).filter
      (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = h)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro p hp hpeq
    obtain ⟨hm1, hm2⟩ := Finset.mem_product.mp hp
    obtain ⟨h1a, h1b⟩ := Finset.mem_Icc.mp hm1
    obtain ⟨h2a, h2b⟩ := Finset.mem_Icc.mp hm2
    have hp1' : (p.1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast h1b
    have hp2 : (1 : ℤ) ≤ (p.2 : ℤ) := by exact_mod_cast h2a
    have hle1 : |(p.1 : ℤ) - (p.2 : ℤ)| ≤ (L : ℤ) - 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hlt : |h| < (L : ℤ) := by
      rw [← hpeq]
      linarith
    linarith
  rw [hempty, Finset.card_empty, Nat.cast_zero, mul_zero]

end Work.Peluse.MuL
