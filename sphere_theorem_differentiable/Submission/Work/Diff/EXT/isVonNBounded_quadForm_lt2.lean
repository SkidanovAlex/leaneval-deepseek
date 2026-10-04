/-
# Sublevel sets of a positive definite quadratic form are von Neumann bounded

For a matrix `A : Fin n → Fin n → ℝ` whose associated quadratic form

  `Q v = ∑ i, ∑ j, v i * v j * A i j`

is strictly positive away from the origin, the sublevel set `{v | Q v < r}` (`r > 0`) is von
Neumann bounded.

The argument is the standard one: `Q` is a continuous function which is homogeneous of degree
two, so on the compact unit sphere it attains a minimum `c > 0`; hence `c * ‖v‖ ^ 2 ≤ Q v` for
every `v`, and the sublevel set is contained in the ball of radius `√(r / c)`.

No symmetry of `A` is needed: `Q` depends only on the symmetric part `(A + Aᵀ) / 2` of `A`.  The
hypothesis `0 < r` is not actually used by the proof (for `r ≤ 0` the set is empty, because
`0 ≤ Q v`), but it is part of the requested statement.
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Diff.EXT

/-- The quadratic form `v ↦ ∑ i, ∑ j, v i * v j * A i j` is homogeneous of degree two. -/
lemma quadForm_smul (n : ℕ) (A : Fin n → Fin n → ℝ) (c : ℝ) (v : Fin n → ℝ) :
    ∑ i, ∑ j, (c • v) i * (c • v) j * A i j = c ^ 2 * ∑ i, ∑ j, v i * v j * A i j := by
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- A quadratic form which is strictly positive away from the origin dominates `c * ‖v‖ ^ 2`
for some `c > 0`.  (The constant is the minimum of the form on the compact unit sphere.) -/
lemma exists_pos_le_quadForm (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hA : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * v j * A i j) :
    ∃ c > 0, ∀ v : Fin n → ℝ, c * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, v i * v j * A i j := by
  have hcont : Continuous fun v : Fin n → ℝ => ∑ i, ∑ j, v i * v j * A i j := by fun_prop
  have hmin : ∃ c > 0, ∀ v : Fin n → ℝ, ‖v‖ = 1 → c ≤ ∑ i, ∑ j, v i * v j * A i j := by
    rcases subsingleton_or_nontrivial (Fin n → ℝ) with hsub | hnt
    · -- the space is trivial: the sphere is empty and any `c > 0` works
      refine ⟨1, one_pos, fun v hv => ?_⟩
      have hv0 : v = 0 := Subsingleton.elim v 0
      rw [hv0] at hv
      simp at hv
    · haveI := hnt
      -- the unit sphere is compact and nonempty, so the form attains a minimum there
      have hne : (Metric.sphere (0 : Fin n → ℝ) (1 : ℝ)).Nonempty := by
        obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → ℝ)
        refine ⟨‖v‖⁻¹ • v, ?_⟩
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
      obtain ⟨v, hv, hminv⟩ :=
        (isCompact_sphere (0 : Fin n → ℝ) (1 : ℝ)).exists_isMinOn hne hcont.continuousOn
      have hvnorm : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hv
      exact ⟨_, hA v (by intro h; rw [h] at hvnorm; norm_num at hvnorm),
        fun w hw => hminv (by simpa [Metric.mem_sphere, dist_eq_norm] using hw)⟩
  obtain ⟨c, hcpos, hc⟩ := hmin
  refine ⟨c, hcpos, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    -- scale `v` to the unit sphere
    have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
        inv_mul_cancel₀ hnorm]
    have h1 : c ≤ (‖v‖⁻¹) ^ 2 * ∑ i, ∑ j, v i * v j * A i j := by
      have h2 := hc _ hu
      rwa [quadForm_smul] at h2
    have hsq : (‖v‖⁻¹) ^ 2 * ‖v‖ ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hnorm, one_pow]
    have hpos : 0 < ‖v‖ ^ 2 := by positivity
    calc c * ‖v‖ ^ 2
        ≤ ((‖v‖⁻¹) ^ 2 * ∑ i, ∑ j, v i * v j * A i j) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
      _ = (∑ i, ∑ j, v i * v j * A i j) * ((‖v‖⁻¹) ^ 2 * ‖v‖ ^ 2) := by ring
      _ = ∑ i, ∑ j, v i * v j * A i j := by rw [hsq, mul_one]

theorem isVonNBounded_quadForm_lt2 (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hA : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * v j * A i j)
    {r : ℝ} (hr : 0 < r) :
    Bornology.IsVonNBounded ℝ {v : Fin n → ℝ | ∑ i, ∑ j, v i * v j * A i j < r} := by
  obtain ⟨c, hcpos, hc⟩ := exists_pos_le_quadForm n A hA
  refine Bornology.IsVonNBounded.subset ?_
    (NormedSpace.isVonNBounded_ball ℝ (Fin n → ℝ) (Real.sqrt (r / c)))
  intro v hv
  have hcr : c * ‖v‖ ^ 2 < r := lt_of_le_of_lt (hc v) hv
  have hd : ‖v‖ ^ 2 < r / c := by rw [lt_div_iff₀ hcpos]; linarith
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  calc ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
    _ < Real.sqrt (r / c) := Real.sqrt_lt_sqrt (by positivity) hd

end Work.Diff.EXT
