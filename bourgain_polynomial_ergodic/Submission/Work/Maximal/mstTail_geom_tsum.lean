import Mathlib

set_option linter.unusedVariables false

namespace Work.Maximal

/-- The individual term of the kernel tail is the general term of a geometric series:
`(b * 2 ^ (-((K+j)/(2d)))) ^ θ = b ^ θ * 2 ^ (-(θ K /(2d))) * (2 ^ (-(θ/(2d)))) ^ j`. -/
theorem mstTail_geom_term (θ : ℝ) (d : ℕ) (K : ℕ) (b : ℝ) (hb : 0 ≤ b) (j : ℕ) :
    (b * (2 : ℝ) ^ (-(((K : ℝ) + (j : ℝ)) / (2 * (d : ℝ))))) ^ θ
      = b ^ θ * (2 : ℝ) ^ (-(θ * (K : ℝ) / (2 * (d : ℝ))))
          * ((2 : ℝ) ^ (-(θ / (2 * (d : ℝ))))) ^ j := by
  rw [Real.mul_rpow hb (Real.rpow_nonneg (by norm_num) _)]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring_nf

theorem mstTail_geom_tsum (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (d : ℕ) (hd : 1 ≤ d) (K : ℕ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Summable (fun j : ℕ =>
        a * (b * (2 : ℝ) ^ (-(((K : ℝ) + (j : ℝ)) / (2 * (d : ℝ))))) ^ θ)
      ∧ (∑' j : ℕ, a * (b * (2 : ℝ) ^ (-(((K : ℝ) + (j : ℝ)) / (2 * (d : ℝ))))) ^ θ)
        = a * b ^ θ * (2 : ℝ) ^ (-(θ * (K : ℝ) / (2 * (d : ℝ))))
            * (1 - (2 : ℝ) ^ (-(θ / (2 * (d : ℝ)))))⁻¹ := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hden : (0 : ℝ) < 2 * (d : ℝ) := by positivity
  set r : ℝ := (2 : ℝ) ^ (-(θ / (2 * (d : ℝ)))) with hrdef
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hrdef]
    exact (Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 2)).mpr
      (Or.inl ⟨by norm_num, by
        have h : 0 < θ / (2 * (d : ℝ)) := div_pos hθ0 hden
        linarith⟩)
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_of_nonneg (le_of_lt hrpos)]; exact hr1
  set C : ℝ := a * b ^ θ * (2 : ℝ) ^ (-(θ * (K : ℝ) / (2 * (d : ℝ)))) with hCdef
  have hkey : ∀ j : ℕ, a * (b * (2 : ℝ) ^ (-(((K : ℝ) + (j : ℝ)) / (2 * (d : ℝ))))) ^ θ
      = C * r ^ j := by
    intro j
    have h1 : (b * (2 : ℝ) ^ (-(((K : ℝ) + (j : ℝ)) / (2 * (d : ℝ))))) ^ θ
        = b ^ θ * (2 : ℝ) ^ (-(θ * (K : ℝ) / (2 * (d : ℝ)))) * r ^ j := by
      simp only [hrdef]
      exact mstTail_geom_term θ d K b hb j
    rw [h1, hCdef]
    ring
  constructor
  · exact ((summable_geometric_of_norm_lt_one hnorm).mul_left C).congr (fun j => (hkey j).symm)
  · rw [tsum_congr hkey, tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm]

end Work.Maximal
