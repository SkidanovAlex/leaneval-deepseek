import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Curl

open scoped Real

/-- **The polar coordinates on `Uax` are surjective onto `(0,∞) × (0,π/2)`** (with the radial
scaling `ρ^p/b`): for every `p, b, w > 0` and every `θ ∈ (0, π/2)` there is a point `x ∈ Uax`
with `ρ(x)^p / b = w` and `θ(x) = θ`.

The witness is the point of `ℝ³` with cylindrical coordinates `r = A cos θ`, `x₃ = A sin θ`,
where `A := (w b)^{1/p}`: then `r > 0`, `x₃ > 0` (so `x ∈ Uax`), `ρ = √(r²+x₃²) = A`, and
`θ(x) = arctan(x₃/r) = arctan(tan θ) = θ`. -/
theorem exists_mem_Uax_rho_theta {p b w θ : ℝ} (hp : 0 < p) (hb : 0 < b) (hw : 0 < w)
    (hθ : 0 < θ) (hθlt : θ < Real.pi / 2) :
    ∃ x ∈ Work.FTS.BSIdent.Uax,
      Work.Cyl.rho x ^ p / b = w ∧ Work.Cyl.theta x = θ := by
  set A : ℝ := (w * b) ^ (1 / p) with hAdef
  have hwb : 0 < w * b := mul_pos hw hb
  have hA : 0 < A := by rw [hAdef]; exact Real.rpow_pos_of_pos hwb _
  have hAp : A ^ p = w * b := by
    rw [hAdef, ← Real.rpow_mul (le_of_lt hwb) (1 / p) p,
      one_div_mul_cancel (ne_of_gt hp), Real.rpow_one]
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθlt⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos])
  have hAc : 0 < A * Real.cos θ := mul_pos hA hcos
  set x : Work.FTS.BSIdent.R3 := !₂[A * Real.cos θ, 0, A * Real.sin θ] with hxdef
  have hx0 : x 0 = A * Real.cos θ := by rw [hxdef]; simp
  have hx1 : x 1 = 0 := by rw [hxdef]; simp
  have hx2 : x 2 = A * Real.sin θ := by rw [hxdef]; simp
  refine ⟨x, ?_, ?_, ?_⟩
  · -- `x ∈ Uax`
    constructor
    · rw [hx2]; exact ne_of_gt (mul_pos hA hsin)
    · rw [hx0, hx1]
      have hpos : (0 : ℝ) < (A * Real.cos θ) ^ 2 := pow_pos hAc 2
      simpa using ne_of_gt hpos
  · -- `ρ(x) = A`
    have hρ : Work.Cyl.rho x = A := by
      rw [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial, hx0, hx1, hx2]
      rw [show (A * Real.cos θ) ^ 2 + (0 : ℝ) ^ 2 + (A * Real.sin θ) ^ 2 = A ^ 2 by
            rw [show (A * Real.cos θ) ^ 2 + (0 : ℝ) ^ 2 = (A * Real.cos θ) ^ 2 by ring,
              mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one],
          Real.sqrt_sq (le_of_lt hA)]
    rw [hρ, hAp]
    exact mul_div_cancel_right₀ w (ne_of_gt hb)
  · -- `θ(x) = θ`
    rw [Work.Cyl.theta, Work.Cyl.axial, Work.Cyl.radial, Work.Cyl.radSq, hx0, hx1, hx2]
    rw [show A * Real.sin θ / Real.sqrt ((A * Real.cos θ) ^ 2 + (0 : ℝ) ^ 2) = Real.tan θ by
          rw [Real.tan_eq_sin_div_cos,
            show (A * Real.cos θ) ^ 2 + (0 : ℝ) ^ 2 = (A * Real.cos θ) ^ 2 by ring,
            Real.sqrt_sq (mul_nonneg (le_of_lt hA) (le_of_lt hcos))]
          field_simp]
    exact Real.arctan_tan (by linarith) hθlt

end Work.FTS.BSIdent.Curl
