import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFock.KinRowQuant
import Submission.Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.summable_vec_inv_one_add_norm_sq`

The lattice series `Σ_{n ∈ ℤ³} (1 + ‖vec n‖²)^{-k}` converges for every `k ≥ 2`,
where `vec n = 2π n` is the dual-lattice momentum vector
(`Work.BoseB4.vec`).

The arithmetic content is again three-dimensionality, but the exponent may now be
as small as `2` (above the critical `3/2` for the radial integral in dimension
`3`) because the lattice vector `vec n` grows *linearly* in `n`: it is the
`2π`-multiple of the primitive integer lattice vector `latVec n`.  Concretely
`‖vec n‖ = 2π‖latVec n‖`, so for `n ≠ 0` (where `‖latVec n‖ ≥ 1`)

`1 + ‖vec n‖² = 1 + 4π²‖latVec n‖² ≥ (1 + ‖latVec n‖)²`,

and hence `(1 + ‖vec n‖²)^{-k} ≤ (1 + ‖latVec n‖)^{-2k}`, which is summable since
`2k ≥ 4` (`Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv`).  The single
point `n = 0`, where both sides equal `1`, is harmless.
-/

namespace Work.BoseBoxFock

noncomputable section

/-- A non-zero integer lattice vector has Euclidean norm at least `1`: some
coordinate is a non-zero integer.  (Local copy of the private helper of
`summable_one_add_norm_latVec_pow_inv`.) -/
private lemma one_le_norm_latVec_inv_one_add_norm_sq {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    1 ≤ ‖latVec n‖ := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := Function.ne_iff.mp hn
  have h1 : (1 : ℝ) ≤ |((n i : ℤ) : ℝ)| := by
    have h2 : (1 : ℤ) ≤ |n i| := Int.one_le_abs hi
    exact_mod_cast h2
  have h2 : ‖(latVec n).ofLp i‖ = |((n i : ℤ) : ℝ)| := by
    have h3 : (latVec n).ofLp i = ((n i : ℤ) : ℝ) := by
      simp [latVec, WithLp.ofLp_toLp]
    rw [h3, Real.norm_eq_abs]
  calc (1 : ℝ) ≤ ‖(latVec n).ofLp i‖ := by rw [h2]; exact h1
    _ ≤ ‖latVec n‖ := PiLp.norm_apply_le (latVec n) i

/-- The dual-lattice momentum `vec n = 2π n` is the `2π`-multiple of the primitive
integer vector `latVec n`. -/
private lemma vec_eq_smul_latVec (n : Fin 3 → ℤ) :
    Work.BoseB4.vec n = (2 * Real.pi) • latVec n := by
  ext i
  simp [Work.BoseB4.vec, latVec]

/-- `vec` scales the norm of `latVec` by `2π`. -/
private lemma norm_vec_eq (n : Fin 3 → ℤ) :
    ‖Work.BoseB4.vec n‖ = 2 * Real.pi * ‖latVec n‖ := by
  rw [vec_eq_smul_latVec, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

/-- The pointwise comparison `(1 + ‖vec n‖²)^{-k} ≤ (1 + ‖latVec n‖)^{-2k}` for
`n ≠ 0`. -/
private lemma inv_one_add_norm_vec_pow_le {k : ℕ} {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ k)⁻¹ ≤ ((1 + ‖latVec n‖) ^ (2 * k))⁻¹ := by
  have hb1 : 1 ≤ ‖latVec n‖ := one_le_norm_latVec_inv_one_add_norm_sq hn
  have key : 2 * ‖latVec n‖ + ‖latVec n‖ ^ 2 ≤ 4 * Real.pi ^ 2 * ‖latVec n‖ ^ 2 := by
    have h4 : (3 : ℝ) ≤ 4 * Real.pi ^ 2 - 1 := by nlinarith [Real.pi_gt_three]
    have h1 : 2 * ‖latVec n‖ ≤ 2 * ‖latVec n‖ ^ 2 := by nlinarith [hb1]
    have h2 : 3 * ‖latVec n‖ ^ 2 ≤ (4 * Real.pi ^ 2 - 1) * ‖latVec n‖ ^ 2 := by
      nlinarith [h4, sq_nonneg ‖latVec n‖]
    nlinarith [h1, h2]
  have hsq : (1 + ‖latVec n‖) ^ 2 ≤ 1 + ‖Work.BoseB4.vec n‖ ^ 2 := by
    rw [norm_vec_eq]
    nlinarith [key]
  have hpow : (1 + ‖latVec n‖) ^ (2 * k) ≤ (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ k := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hsq k
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hpow

theorem summable_vec_inv_one_add_norm_sq {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun n : Fin 3 → ℤ => ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ k)⁻¹) := by
  refine Summable.of_nonneg_of_le
    (f := fun n : Fin 3 → ℤ => ((1 + ‖latVec n‖) ^ (2 * k))⁻¹)
    (g := fun n : Fin 3 → ℤ => ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ k)⁻¹)
    (fun n => by positivity) (fun n => ?_)
    (summable_one_add_norm_latVec_pow_inv (by omega : 4 ≤ 2 * k))
  rcases eq_or_ne n 0 with hn0 | hn
  · subst hn0
    have hl : latVec (0 : Fin 3 → ℤ) = 0 := by ext i; simp [latVec]
    have hv : Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 := by ext i; simp [Work.BoseB4.vec]
    simp [hl, hv]
  · exact inv_one_add_norm_vec_pow_le hn

end

end Work.BoseBoxFock
