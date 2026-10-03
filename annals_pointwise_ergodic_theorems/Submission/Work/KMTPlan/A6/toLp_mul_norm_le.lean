import Mathlib

namespace Work.KMTPlan.A6

open scoped ENNReal

set_option linter.style.haveILetI false

/-- **Pointwise multiplication against a bounded factor is bounded in `ℓ^r`.**

For `1 ≤ r`, a finite family `g` and an arbitrary finite family `u` of complex numbers,
the `ℓ^r` norm of the pointwise product `i ↦ u i * g i` is at most
`‖g‖_∞ · ‖u‖_r`, where `‖g‖_∞ = ⨆ i, ‖g i‖` is the sup norm of `g`.

This is the multiplicative form of the monotonicity of the counting measure: for every `i`
one has `‖u i * g i‖ = ‖u i‖ · ‖g i‖ ≤ ‖u i‖ · ‖g‖_∞`, and raising to the `r`-th power and
summing gives `∑ i ‖u i * g i‖^r ≤ ‖g‖_∞^r ∑ i ‖u i‖^r`.

The statement is phrased for the `WithLp` (= `PiLp`) model of the finite dimensional `ℓ^r`
space, so that it can be applied to the vectors occurring in `varpCol`. -/
theorem toLp_mul_norm_le {J : ℕ} {r : NNReal} (hr : 1 ≤ r) (u g : Fin J → ℂ) :
    ENNReal.ofReal (norm (WithLp.toLp (r : ENNReal) (fun i : Fin J => u i * g i)))
      ≤ (⨆ i, ENNReal.ofReal (norm (g i))) *
        ENNReal.ofReal (norm (WithLp.toLp (r : ENNReal) u)) := by
  classical
  haveI : Fact (1 ≤ (r : ENNReal)) := ⟨by exact_mod_cast hr⟩
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hr)
  have hrnn : (0 : ℝ) ≤ (r : ℝ) := le_of_lt hrpos
  have hinv : (0 : ℝ) ≤ 1 / (r : ℝ) := by positivity
  have hrr : (r : ℝ) * (1 / (r : ℝ)) = 1 := by field_simp
  -- the `ℓ^r` norm of an element of `WithLp` as a sum of `r`-th powers of norms
  have hnorm : ∀ v : Fin J → ℂ,
      ‖WithLp.toLp (r : ENNReal) v‖ₑ = (∑ i : Fin J, ‖v i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
    intro v
    rw [enorm_eq_nnnorm,
      PiLp.nnnorm_eq_sum (p := (r : ENNReal)) (by simp) (WithLp.toLp (r : ENNReal) v)]
    rw [WithLp.ofLp_toLp, ENNReal.coe_toReal, ENNReal.coe_rpow_of_nonneg _ hinv]
    congr 1
    simp only [ENNReal.ofNNReal_finsetSum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [ENNReal.coe_rpow_of_nonneg _ hrnn, ← enorm_eq_nnnorm (v i)]
  -- pass to extended non-negative norm notation
  simp only [ofReal_norm]
  set M := ⨆ i : Fin J, ‖g i‖ₑ with hM
  have hgi : ∀ i, ‖g i‖ₑ ≤ M := fun i => le_iSup (fun i => ‖g i‖ₑ) i
  calc ‖WithLp.toLp (r : ENNReal) (fun i => u i * g i)‖ₑ
      = (∑ i : Fin J, ‖u i * g i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) := hnorm _
    _ ≤ (∑ i : Fin J, (‖u i‖ₑ * M) ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
        refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun i _ => ?_) hinv
        rw [enorm_mul]
        exact ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left (hgi i) zero_le) hrnn
    _ = (∑ i : Fin J, ‖u i‖ₑ ^ (r : ℝ) * M ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => ENNReal.mul_rpow_of_nonneg _ _ hrnn
    _ = ((∑ i : Fin J, ‖u i‖ₑ ^ (r : ℝ)) * M ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
        rw [Finset.sum_mul]
    _ = (∑ i : Fin J, ‖u i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) * M := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hinv]
        congr 1
        rw [← ENNReal.rpow_mul, hrr, ENNReal.rpow_one]
    _ = M * ‖WithLp.toLp (r : ENNReal) u‖ₑ := by
        rw [hnorm u, mul_comm]

end Work.KMTPlan.A6
