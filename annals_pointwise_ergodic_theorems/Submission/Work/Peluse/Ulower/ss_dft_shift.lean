import Mathlib
import Submission.Work.Peluse.Fourier.dftOrthogonality

namespace Work.Peluse.Ulower

/-- **The shifted discrete Fourier orthogonality.**  For `n ≥ 1`, `r : ℕ`, `θ : ℝ` and `x : ℤ`,

`∑_{j<n} e(−j r/n) · e((θ + j/n) x) = if n ∣ (x − r) then n · e(θ x) else 0`,

where `e(t) = Work.Peluse.ee t = exp(2πi t)`.

Proof: the product of the two characters is `e(θ x) · e(j (x − r)/n)`, so the sum is
`e(θx) ∑_{j<n} e(j (x−r)/n)`, and the root-of-unity orthogonality
`Work.Peluse.Fourier.dftOrthogonality` gives the stated value.  This is the inverse-DFT identity by
which a Fourier coefficient of a *decimated* function `z ↦ F (c z + r)` is expressed through the
Fourier coefficients of `F` at the `|c|` frequencies `ξ_j = (β + j)/c` (Peluse's
`U²`-inverse entry). -/
theorem ss_dft_shift {n : ℕ} (hn : 1 ≤ n) (r : ℕ) (θ : ℝ) (x : ℤ) :
    (∑ j ∈ Finset.range n,
        Work.Peluse.ee (-(j : ℝ) * (r : ℝ) / (n : ℝ))
          * Work.Peluse.ee ((θ + (j : ℝ) / (n : ℝ)) * (x : ℝ)))
      = if (n : ℤ) ∣ (x - (r : ℤ)) then (n : ℂ) * Work.Peluse.ee (θ * (x : ℝ)) else 0 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnR : (n : ℝ) ≠ 0 := ne_of_gt hn0
  -- (1) the product of the two characters is `e (θ x) · e (j (x - r) / n)`
  have key : ∀ j : ℕ,
      Work.Peluse.ee (-(j : ℝ) * (r : ℝ) / (n : ℝ))
          * Work.Peluse.ee ((θ + (j : ℝ) / (n : ℝ)) * (x : ℝ))
        = Work.Peluse.ee (θ * (x : ℝ))
          * Work.Peluse.ee ((j : ℝ) * ((x : ℝ) - (r : ℝ)) / (n : ℝ)) := by
    intro j
    have harg : -(j : ℝ) * (r : ℝ) / (n : ℝ) + (θ + (j : ℝ) / (n : ℝ)) * (x : ℝ)
        = θ * (x : ℝ) + (j : ℝ) * ((x : ℝ) - (r : ℝ)) / (n : ℝ) := by
      field_simp
      ring
    rw [← Work.Peluse.ee_add, harg, Work.Peluse.ee_add]
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  -- (2) root-of-unity orthogonality
  have hcast : ((x - (r : ℤ) : ℤ) : ℝ) = (x : ℝ) - (r : ℝ) := by push_cast; ring
  have horth : (∑ j ∈ Finset.range n,
        Work.Peluse.ee ((j : ℝ) * ((x : ℝ) - (r : ℝ)) / (n : ℝ)))
      = if (n : ℤ) ∣ (x - (r : ℤ)) then (n : ℂ) else 0 := by
    have h := Work.Peluse.Fourier.dftOrthogonality n hn (x - (r : ℤ))
    rw [hcast] at h
    exact h
  rw [horth]
  by_cases h : (n : ℤ) ∣ (x - (r : ℤ))
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; simp

end Work.Peluse.Ulower
