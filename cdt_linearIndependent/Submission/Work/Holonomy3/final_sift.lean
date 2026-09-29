import Mathlib
import Submission.Work.Holonomy3.comp_defs

namespace Work.Holonomy3

/-- **The arithmetic core of the final sift.**

With `A > 0`, `m > 0` we have, from the four error estimates
`lnu₀ + lnβ + T ≤ I`, `I ≤ A·(1/m)·rearr + errC`, `-A(τ+η) ≤ lnβ`,
`A(x - (1/m²)S) - errE ≤ T` and `-lnu₀ ≤ errU`:

  `m(x - τ) ≤ rearr + (1/m)·S + (m/A)·(errC + errE + errU + A·η)`.

Indeed, chaining the estimates gives
`A(x - τ) ≤ A·(1/m)·rearr + A·(1/m²)·S + (errC + errE + errU + A·η)`,
and multiplying by the positive factor `m/A` yields the claim. -/
theorem final_sift_arith {A m rearr S x τ η errC errE errU lnu₀ lnβ T I : ℝ}
    (hm : 0 < m) (hA : 0 < A)
    (h1 : lnu₀ + lnβ + T ≤ I)
    (h2 : I ≤ A * (1 / m) * rearr + errC)
    (h3 : -(A * (τ + η)) ≤ lnβ)
    (h4 : A * (x - (1 / m ^ 2) * S) - errE ≤ T)
    (h5 : -lnu₀ ≤ errU) :
    m * (x - τ) ≤ rearr + (1 / m) * S
      + (m / A) * (errC + errE + errU + A * η) := by
  have hkey : A * (x - τ) ≤ A * (1 / m) * rearr + A * (1 / m ^ 2) * S
      + (errC + errE + errU + A * η) := by
    linarith
  have hAne : A ≠ 0 := ne_of_gt hA
  have hstep := mul_le_mul_of_nonneg_left hkey (le_of_lt (div_pos hm hA))
  rw [mul_add, mul_add] at hstep
  have e1 : (m / A) * (A * (x - τ)) = m * (x - τ) := by field_simp
  have e2 : (m / A) * (A * (1 / m) * rearr) = rearr := by field_simp
  have e3 : (m / A) * (A * (1 / m ^ 2) * S) = (1 / m) * S := by field_simp
  rw [e1, e2, e3] at hstep
  exact hstep

theorem final_sift {l m d D : ℕ} (hm : 0 < m) (hd : 0 < d) (hD : 0 < D)
    (γ : Fin (l + 2) → ℝ) (L : Fin (l + 1) → ℝ) (rearr I T lnu₀ lnβ τ η errC errE errU : ℝ)
    (h1 : lnu₀ + lnβ + T ≤ I)
    (h2 : I ≤ ((m : ℝ) * d * D / 2) * (1 / (m : ℝ)) * rearr + errC)
    (h3 : -(((m : ℝ) * d * D / 2) * (τ + η)) ≤ lnβ)
    (h4 : ((m : ℝ) * d * D / 2) * (L (Fin.last l) -
        (1 / (m : ℝ) ^ 2) * ∑ k : Fin l,
          (γ k.succ.castSucc) ^ 2 * (L k.succ - L k.castSucc)) - errE ≤ T)
    (h5 : -lnu₀ ≤ errU) (hη : 0 ≤ η) :
    (m : ℝ) * (L (Fin.last l) - τ) ≤ rearr +
      (1 / (m : ℝ)) * ∑ k : Fin l,
        (γ k.succ.castSucc) ^ 2 * (L k.succ - L k.castSucc) +
      (m : ℝ) / ((m : ℝ) * d * D / 2) *
        (errC + errE + errU + ((m : ℝ) * d * D / 2) * η) := by
  have hA : (0 : ℝ) < (m : ℝ) * d * D / 2 := by positivity
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  exact final_sift_arith hm' hA h1 h2 h3 h4 h5

end Work.Holonomy3
