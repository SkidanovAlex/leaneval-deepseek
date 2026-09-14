import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.Normed.Ring.Lemmas

namespace Commons.Data.IntVec

/-- Every nonzero integer vector `x` is a positive multiple `d • y` of a
*primitive* integer vector `y` (one with `gcd y = 1`), with `d ≥ 1`, and the
coordinates of `y` are coordinatewise no larger in absolute value than those of
`x` (hence `‖y‖ ≤ ‖x‖` in the sup norm).

The multiple is `d = gcd x` and `y = x / d`. -/
theorem primitive_factor {σ : Type*} [Fintype σ] (x : σ → ℤ) (hx : x ≠ 0) :
    ∃ d : ℤ, 1 ≤ d ∧ ∃ y : σ → ℤ, (Finset.univ : Finset σ).gcd y = 1 ∧ x = d • y ∧
      (∀ i : σ, ‖y i‖ ≤ ‖x i‖) ∧ ‖y‖ ≤ ‖x‖ := by
  classical
  -- some coordinate of `x` is nonzero
  have hex : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext fun i => by simp [h i])
  obtain ⟨i0, hi0⟩ := hex
  -- the gcd of all coordinates
  let g : ℤ := (Finset.univ : Finset σ).gcd x
  have hg_eq : g = (Finset.univ : Finset σ).gcd x := rfl
  have hgne : g ≠ 0 := by
    rw [hg_eq]
    exact Finset.gcd_ne_zero_iff.2 ⟨i0, Finset.mem_univ i0, hi0⟩
  have hgnn : 0 ≤ g := by
    have h1 : |g| = g := by rw [Int.abs_eq_normalize, hg_eq, Finset.normalize_gcd]
    rw [← h1]
    exact abs_nonneg g
  have hg1 : 1 ≤ g := by omega
  -- the primitive vector
  let y : σ → ℤ := fun i => x i / g
  have hgcd : (Finset.univ : Finset σ).gcd y = 1 := by
    have hy : y = fun i => x i / (Finset.univ : Finset σ).gcd x := by
      funext i
      simp only [y, hg_eq]
    rw [hy]
    exact Finset.gcd_div_eq_one (f := x) (i := i0) (Finset.mem_univ i0) hi0
  have hxy : x = g • y := by
    funext i
    have hdvd : g ∣ x i := by
      rw [hg_eq]
      exact Finset.gcd_dvd (Finset.mem_univ i)
    show x i = (g • y) i
    rw [Pi.smul_apply, zsmul_eq_mul, Int.cast_id]
    exact (Int.mul_ediv_cancel' hdvd).symm
  have hy_le : ∀ i : σ, ‖y i‖ ≤ ‖x i‖ := by
    intro i
    have hdvd : g ∣ x i := by
      rw [hg_eq]
      exact Finset.gcd_dvd (Finset.mem_univ i)
    have hxi : x i = g * (x i / g) := (Int.mul_ediv_cancel' hdvd).symm
    have hyi : y i = x i / g := rfl
    have hgd : (1 : ℝ) ≤ ‖g‖ := by
      rw [Int.norm_eq_abs, abs_of_nonneg (by exact_mod_cast hgnn)]
      exact_mod_cast hg1
    have habs : ‖x i‖ = ‖g‖ * ‖x i / g‖ := by
      conv_lhs => rw [hxi]
      simp only [Int.norm_eq_abs, Int.cast_mul, abs_mul]
    rw [hyi, habs]
    calc ‖x i / g‖ = 1 * ‖x i / g‖ := (one_mul _).symm
      _ ≤ ‖g‖ * ‖x i / g‖ := mul_le_mul_of_nonneg_right hgd (norm_nonneg _)
  have hy_norm : ‖y‖ ≤ ‖x‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 (fun i => ?_)
    exact (hy_le i).trans (norm_le_pi_norm x i)
  exact ⟨g, hg1, y, hgcd, hxy, hy_le, hy_norm⟩

end Commons.Data.IntVec