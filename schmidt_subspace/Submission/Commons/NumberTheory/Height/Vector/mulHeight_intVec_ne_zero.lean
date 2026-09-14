import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Height.NumberField
import Submission.Commons.Data.IntVec.primitive_factor

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.Height.Vector

open scoped BigOperators

/-- For a nonzero integer vector `x`, the multiplicative height of `x` viewed as a tuple of
rational numbers equals the sup norm of `x` divided by the content `gcd x`.

Writing `x = d • y` with `d = gcd x ≥ 1` and `y = x / d` primitive, the height is invariant
under the rational scaling by `d`, so it equals the height of the primitive vector `y`, which by
`Rat.mulHeight_eq_max_abs_of_gcd_eq_one` is the sup norm `‖y‖`; and `‖x‖ = d * ‖y‖`. -/
theorem mulHeight_intVec_ne_zero {σ : Type*} [Fintype σ] (x : σ → ℤ) (hx : x ≠ 0) :
    Height.mulHeight (fun i => (x i : ℚ)) = ‖x‖ / ((Finset.univ.gcd x : ℤ) : ℝ) := by
  classical
  obtain ⟨d, hd1, y, hgcd, hxy, _, _⟩ :=
    Commons.Data.IntVec.primitive_factor x hx
  -- `σ` is nonempty, as `x ≠ 0`
  have hne : Nonempty σ := by
    by_contra h
    apply hx
    funext i
    exact (h ⟨i⟩).elim
  haveI := hne
  -- `d > 0`
  have hdnonneg : (0 : ℤ) ≤ d := by omega
  have hdpos : (0 : ℤ) < d := by omega
  have hd0z : d ≠ 0 := hdpos.ne'
  have hd0q : (d : ℚ) ≠ 0 := by exact_mod_cast hd0z
  have hd0r : (d : ℝ) ≠ 0 := by exact_mod_cast hd0z
  have hdnonnegr : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdnonneg
  -- pointwise form of `x = d • y`
  have hpoint : ∀ i, x i = d * y i := by
    intro i
    rw [hxy]
    simp [Pi.smul_apply]
  have h1 : x = fun i => d * y i := funext hpoint
  -- the content of `x` is `d`
  have hgcdx : Finset.univ.gcd x = d := by
    rw [h1, Finset.gcd_mul_left, hgcd, mul_one, Int.normalize_of_nonneg hdnonneg]
  -- the rational tuple of `x` is the rational scaling of that of `y`
  have hcast : (fun i => (x i : ℚ)) = (d : ℚ) • (fun i => (y i : ℚ)) := by
    funext i
    rw [hpoint i]
    simp [Pi.smul_apply]
  -- the height of the primitive vector is its sup norm
  have hhy : Height.mulHeight (fun i => (y i : ℚ)) = ‖y‖ := by
    have hmax := Rat.mulHeight_eq_max_abs_of_gcd_eq_one (x := y) hgcd
    rw [show (fun i => (y i : ℚ)) = ((↑) : ℤ → ℚ) ∘ y from rfl, hmax]
    rw [show ((⨆ i, |y i| : ℤ) : ℝ) = ⨆ i, ((|y i| : ℤ) : ℝ) from
      Finite.map_iSup_of_monotone (fun i => |y i|) Int.cast_mono]
    have hbridge : ∀ i, ((|y i| : ℤ) : ℝ) = ‖y i‖ := by
      intro i
      simp only [Int.cast_abs, Int.norm_eq_abs]
    simp only [hbridge]
    apply le_antisymm
    · exact ciSup_le fun i => norm_le_pi_norm y i
    · refine (pi_norm_le_iff_of_nonneg ?_).2 fun i => Finite.le_ciSup_of_le i le_rfl
      exact Real.iSup_nonneg' ⟨Classical.arbitrary σ, norm_nonneg _⟩
  -- the norm of `x` is `d` times the norm of `y`
  have hnormpoint : ∀ i, ‖x i‖ = (d : ℝ) * ‖y i‖ := by
    intro i
    rw [hpoint i, norm_mul, Int.norm_eq_abs, abs_of_nonneg hdnonnegr]
  have hnorm : ‖x‖ = (d : ℝ) * ‖y‖ := by
    apply le_antisymm
    · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      rw [hnormpoint i]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm y i) hdnonnegr
    · have hyx : ‖y‖ ≤ ‖x‖ / (d : ℝ) := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
        have hyt : ‖y i‖ = ‖x i‖ / (d : ℝ) := by
          rw [hnormpoint i, mul_div_cancel_left₀ ‖y i‖ hd0r]
        rw [hyt]
        exact div_le_div_of_nonneg_right (norm_le_pi_norm x i) hdnonnegr
      calc (d : ℝ) * ‖y‖ ≤ (d : ℝ) * (‖x‖ / (d : ℝ)) :=
            mul_le_mul_of_nonneg_left hyx hdnonnegr
        _ = ‖x‖ := by rw [← mul_div_assoc, mul_div_cancel_left₀ ‖x‖ hd0r]
  rw [hcast, Height.mulHeight_smul_eq_mulHeight _ hd0q, hhy, hgcdx, hnorm,
    mul_div_cancel_left₀ ‖y‖ hd0r]

end Commons.NumberTheory.Height.Vector