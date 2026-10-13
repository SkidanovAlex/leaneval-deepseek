import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.CrossProduct

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LWP.BiotSavart

open Matrix

/-- The self dot product of a nonzero vector of `Fin 3 → ℝ` is nonzero: it is a sum of
squares of the coordinates. -/
lemma dotProduct_self_ne_zero_three {v : Fin 3 → ℝ} (hv : v ≠ 0) : v ⬝ᵥ v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ v j * v j :=
    fun j _ => mul_self_nonneg _
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
  exact mul_self_eq_zero.mp (hz i (Finset.mem_univ i))

theorem crossRecover (x a d : Fin 3 → ℝ) (hd : d ≠ 0) (hda : crossProduct d a ≠ 0) :
    x = (d ⬝ᵥ d)⁻¹ • crossProduct d (crossProduct x d)
        + (((((crossProduct (crossProduct x a) d) ⬝ᵥ a) * (d ⬝ᵥ d) + (d ⬝ᵥ a) * ((crossProduct (crossProduct x d) a) ⬝ᵥ d))
            / ((d ⬝ᵥ d) * (a ⬝ᵥ a) - (d ⬝ᵥ a) * (d ⬝ᵥ a))) * (d ⬝ᵥ d)⁻¹) • d := by
  -- The self dot product of `d` is nonzero.
  have hdd : (d ⬝ᵥ d) ≠ 0 := dotProduct_self_ne_zero_three hd
  -- The Binet–Cauchy denominator is the square of `d ⨯₃ a`, hence nonzero.
  have hD : ((d ⬝ᵥ d) * (a ⬝ᵥ a) - (d ⬝ᵥ a) * (d ⬝ᵥ a)) ≠ 0 := by
    rw [show (d ⬝ᵥ d) * (a ⬝ᵥ a) - (d ⬝ᵥ a) * (d ⬝ᵥ a)
          = (crossProduct d a) ⬝ᵥ (crossProduct d a) by
        rw [cross_dot_cross, dotProduct_comm a d]]
    exact dotProduct_self_ne_zero_three hda
  -- The numerator equals `(x ⬝ᵥ d)` times the denominator.
  have hN : ((crossProduct (crossProduct x a) d) ⬝ᵥ a) * (d ⬝ᵥ d)
        + (d ⬝ᵥ a) * ((crossProduct (crossProduct x d) a) ⬝ᵥ d)
      = (x ⬝ᵥ d) * ((d ⬝ᵥ d) * (a ⬝ᵥ a) - (d ⬝ᵥ a) * (d ⬝ᵥ a)) := by
    simp_rw [cross_apply, vec3_dotProduct]
    dsimp only [Matrix.cons_val]
    ring
  -- Hence the scalar coefficient is `(x ⬝ᵥ d) * (d ⬝ᵥ d)⁻¹`.
  have hc : ((((crossProduct (crossProduct x a) d) ⬝ᵥ a) * (d ⬝ᵥ d)
        + (d ⬝ᵥ a) * ((crossProduct (crossProduct x d) a) ⬝ᵥ d))
        / ((d ⬝ᵥ d) * (a ⬝ᵥ a) - (d ⬝ᵥ a) * (d ⬝ᵥ a))) = (x ⬝ᵥ d) := by
    rw [hN]
    exact mul_div_cancel_right₀ (x ⬝ᵥ d) hD
  rw [hc, cross_cross_eq_smul_sub_smul']
  rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hdd, one_smul]
  rw [mul_comm (d ⬝ᵥ d)⁻¹ (x ⬝ᵥ d), sub_add_cancel]

end Work.LWP.BiotSavart
