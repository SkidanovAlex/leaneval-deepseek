import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmTermDefs

open DirichletCharacter Complex
noncomputable section

namespace Work.LinnikAreas.Density4

/-- For `n ≥ 1` and `X > 0` the two `cpow` factors of the `n`-th summand rearrange:
`n^{-ρ}·(n/X)^{-s} = X^s·n^{-(ρ+s)}`. -/
lemma cpow_div_mul_of_pos (ρ s : ℂ) {n : ℕ} (hn : 0 < n) {X : ℝ} (hX : 0 < X) :
    (n : ℂ) ^ (-ρ) * (((n : ℂ) / (X : ℂ)) ^ (-s))
      = (X : ℂ) ^ s * (n : ℂ) ^ (-(ρ + s)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast]; exact Complex.ofReal_ne_zero.mpr hn0.ne'
  have h1 : ((n : ℂ) / (X : ℂ)) ^ (-s) = (n : ℂ) ^ (-s) * (X : ℂ) ^ s := by
    have h := Complex.div_cpow_ofReal_nonneg (a := (n : ℝ)) (b := X) hn0.le hX.le (-s)
    simp only [Complex.ofReal_natCast] at h
    rw [h, Complex.cpow_neg (X : ℂ) s, div_eq_mul_inv, inv_inv]
  have hcp : (n : ℂ) ^ (-ρ) * (n : ℂ) ^ (-s) = (n : ℂ) ^ (-(ρ + s)) := by
    rw [← Complex.cpow_add (-ρ) (-s) hnne, show -ρ + -s = -(ρ + s) by ring]
  rw [h1, ← hcp]
  ring

theorem SsmTerm_tsum_eq (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hX : 0 < X) (t : ℝ) :
    (∑' n : ℕ, Work.LinnikAreas.Density4.SsmTerm q U V W X χ ρ n t)
      = Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)
          * (X : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
          * Work.LinnikAreas.Density4.mollSeries q U V W χ (ρ + ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
  set s : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I with hs
  have hpt : ∀ n : ℕ, SsmTerm q U V W X χ ρ n t
      = (Complex.Gamma s * (X : ℂ) ^ s) * (mollCoeff q U V W χ n * (n : ℂ) ^ (-(ρ + s))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [SsmTerm, mollCoeff_zero]
    · have hdiv : ((((n : ℝ) / X : ℝ)) : ℂ) = (n : ℂ) / (X : ℂ) := by
        rw [Complex.ofReal_div, Complex.ofReal_natCast]
      have h2 : mollCoeff q U V W χ n * (n : ℂ) ^ (-ρ) * ((n : ℂ) / (X : ℂ)) ^ (-s)
          = (X : ℂ) ^ s * (mollCoeff q U V W χ n * (n : ℂ) ^ (-(ρ + s))) := by
        have key := cpow_div_mul_of_pos ρ s hn hX
        calc mollCoeff q U V W χ n * (n : ℂ) ^ (-ρ) * ((n : ℂ) / (X : ℂ)) ^ (-s)
            = mollCoeff q U V W χ n
                * ((n : ℂ) ^ (-ρ) * ((n : ℂ) / (X : ℂ)) ^ (-s)) := by ring
          _ = mollCoeff q U V W χ n * ((X : ℂ) ^ s * (n : ℂ) ^ (-(ρ + s))) := by rw [key]
          _ = (X : ℂ) ^ s * (mollCoeff q U V W χ n * (n : ℂ) ^ (-(ρ + s))) := by ring
      calc SsmTerm q U V W X χ ρ n t
          = (mollCoeff q U V W χ n * (n : ℂ) ^ (-ρ) * ((n : ℂ) / (X : ℂ)) ^ (-s))
              * Complex.Gamma s := by
            rw [SsmTerm, ← hs, hdiv]; ring
        _ = ((X : ℂ) ^ s * (mollCoeff q U V W χ n * (n : ℂ) ^ (-(ρ + s))))
              * Complex.Gamma s := by rw [h2]
        _ = (Complex.Gamma s * (X : ℂ) ^ s)
              * (mollCoeff q U V W χ n * (n : ℂ) ^ (-(ρ + s))) := by ring
  rw [mollSeries, ← tsum_mul_left]
  exact tsum_congr hpt

end Work.LinnikAreas.Density4
