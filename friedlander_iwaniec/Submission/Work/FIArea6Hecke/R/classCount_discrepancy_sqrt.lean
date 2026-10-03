import Mathlib
import Submission.Work.FIArea6Hecke.R.classCount_eq_shiftCount
import Submission.Commons.NumberTheory.Diophantine.lattice_disk_count_bound

namespace Work.FIArea6Hecke.R

/-- **Elementary Gauss-circle discrepancy for a residue class mod `4d`.** For `X ≥ 16d²` (so that `R = √X/(4d) ≥ 1`) the number of Gaussian integers `z ≡ p (mod 4d)` with `|z|² ≤ X` differs from `πR²` by `O(R)`, with an absolute constant: this is the classical elementary bound for a shifted lattice disc, `Commons.NumberTheory.Diophantine.lattice_disk_count_bound` (imported by `Work.FIArea6Hecke.R.LatticeCountBridge`), transported across the change of variable `z = p + 4d·w` (`Work.FIArea6Hecke.R.classCount_eq_shiftCount`). -/
theorem classCount_discrepancy_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (p : GaussianInt) (X : ℝ),
      16 * (d : ℝ) ^ 2 ≤ X →
      |(Work.FIArea6Hecke.R.classCount d p X : ℝ) - Real.pi * (X / (16 * (d : ℝ) ^ 2))|
        ≤ C * (Real.sqrt X / (4 * (d : ℝ))) := by
  obtain ⟨C₀, hC₀pos, hbound⟩ :=
    Commons.NumberTheory.Diophantine.lattice_disk_count_bound
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro d hd p X hX
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hXpos : (0 : ℝ) < X := by
    have : (0 : ℝ) < 16 * (d : ℝ) ^ 2 := by positivity
    linarith
  set R : ℝ := Real.sqrt X / (4 * (d : ℝ)) with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hR1 : 1 ≤ R := by
    rw [hR, le_div_iff₀ (by positivity), one_mul]
    have hX' : (4 * (d : ℝ)) ^ 2 ≤ X := by
      rw [show (4 * (d : ℝ)) ^ 2 = 16 * (d : ℝ) ^ 2 from by ring]; exact hX
    calc 4 * (d : ℝ) = Real.sqrt ((4 * (d : ℝ)) ^ 2) :=
          (Real.sqrt_sq (show (0 : ℝ) ≤ 4 * (d : ℝ) from by positivity)).symm
      _ ≤ Real.sqrt X := Real.sqrt_le_sqrt hX'
  have hRsq : R ^ 2 = X / (16 * (d : ℝ) ^ 2) := by
    rw [hR, div_pow, Real.sq_sqrt (le_of_lt hXpos),
      show (4 * (d : ℝ)) ^ 2 = 16 * (d : ℝ) ^ 2 from by ring]
  set c : ℝ × ℝ :=
    (-((p.re : ℝ) / (4 * (d : ℝ))), -((p.im : ℝ) / (4 * (d : ℝ)))) with hc
  have hc1 : c.1 = -((p.re : ℝ) / (4 * (d : ℝ))) := by rw [hc]
  have hc2 : c.2 = -((p.im : ℝ) / (4 * (d : ℝ))) := by rw [hc]
  have hkey : ∀ z : ℤ × ℤ,
      (z.1 - c.1) ^ 2 + (z.2 - c.2) ^ 2
        = ((z.1 : ℝ) + (p.re : ℝ) / (4 * (d : ℝ))) ^ 2
          + ((z.2 : ℝ) + (p.im : ℝ) / (4 * (d : ℝ))) ^ 2 := by
    intro z
    rw [hc1, hc2]
    push_cast
    ring
  have hset : ({z : ℤ × ℤ | (z.1 - c.1) ^ 2 + (z.2 - c.2) ^ 2 ≤ R ^ 2} : Set (ℤ × ℤ))
      = {w : ℤ × ℤ | ((w.1 : ℝ) + (p.re : ℝ) / (4 * (d : ℝ))) ^ 2
          + ((w.2 : ℝ) + (p.im : ℝ) / (4 * (d : ℝ))) ^ 2 ≤ X / (16 * (d : ℝ) ^ 2)} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    rw [hkey z, ← hRsq]
  have hcount : (Work.FIArea6Hecke.R.classCount d p X : ℝ)
      = (({z : ℤ × ℤ | (z.1 - c.1) ^ 2 + (z.2 - c.2) ^ 2 ≤ R ^ 2} : Set (ℤ × ℤ)).ncard : ℝ) := by
    rw [Work.FIArea6Hecke.R.classCount_eq_shiftCount hd p X]
    show (({w : ℤ × ℤ | ((w.1 : ℝ) + (p.re : ℝ) / (4 * (d : ℝ))) ^ 2
        + ((w.2 : ℝ) + (p.im : ℝ) / (4 * (d : ℝ))) ^ 2
        ≤ X / (16 * (d : ℝ) ^ 2)} : Set (ℤ × ℤ)).ncard : ℝ) = _
    rw [← hset]
  have hbd := hbound R c hR0
  rw [← hcount, show Real.pi * R ^ 2 = Real.pi * (X / (16 * (d : ℝ) ^ 2)) from by
    rw [hRsq]] at hbd
  calc |(Work.FIArea6Hecke.R.classCount d p X : ℝ)
        - Real.pi * (X / (16 * (d : ℝ) ^ 2))|
      ≤ C₀ * (R + 1) := hbd
    _ ≤ (2 * C₀) * R := by nlinarith [hR1, hC₀pos]
    _ = (2 * C₀) * (Real.sqrt X / (4 * (d : ℝ))) := by rw [hR]

end Work.FIArea6Hecke.R
