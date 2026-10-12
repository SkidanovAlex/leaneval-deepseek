import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.LatSamplingAux.ftLatticeSummable`

The series of Fourier coefficients of `F` sampled on the dual lattice
`k_m = (2π/ℓ) • latVec m` is **summable** (unconditionally, i.e. absolutely) as soon as the
Fourier transform `FT(F)(p) = ∫ e^{-i⟪p,y⟫} F y dy` of `F` decays faster than any polynomial.

This is the *convergence* half of the Poisson sampling identity
(`Work.BoseBoxFock.latSampling_decay`): the identity itself needs the additional input that the
periodisation `∑_d F(z + ℓ d)` converges, but the left-hand side of the identity is summable on
the strength of the momentum-space decay alone.

**Proof.** The exp factor has modulus `1`, so the summand is bounded by
`‖FT(F)(k_m)‖ ≤ C (1 + ‖k_m‖)^{-4}` with `C` the constant supplied by the hypothesis at `n = 4`.
Since `‖k_m‖ = (2π/ℓ)·‖latVec m‖` and `2π/ℓ > 0`, this is at most a *constant* multiple of
`(1 + ‖latVec m‖)^{-4}` (the constant absorbs the case `2π/ℓ < 1`: `1 + a v ≥ min(1,a)(1 + v)`),
and `m ↦ (1 + ‖latVec m‖)^{-4}` is summable by
`Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv` — three-dimensionality of the lattice.
-/

namespace Work.BoseBoxFock.LatSamplingAux

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The elementary comparison used to pass from the dual-lattice spacing to the lattice itself:
for `a > 0` and `v ≥ 0`, `(1 + a*v)^{-m} ≤ (max 1 a^{-1})^m (1 + v)^{-m}`.

Indeed `a ≥ 1` gives `1 + a*v ≥ 1 + v`, while `a ≤ 1` gives `1 + a*v ≥ a + a*v = a(1 + v)`. -/
private lemma inv_zpow_le {a : ℝ} (ha : 0 < a) (m : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    (1 + a * v) ^ (-(m:ℤ)) ≤ (max 1 a⁻¹)^m * (1 + v) ^ (-(m:ℤ)) := by
  have hw : 0 < 1 + v := by linarith
  have hu : 0 < 1 + a * v := by nlinarith [mul_nonneg ha.le hv]
  have hkey : 1 + v ≤ max 1 a⁻¹ * (1 + a * v) := by
    rcases lt_or_ge 1 a with h | h
    · rw [max_eq_left (inv_le_one_of_one_le₀ h.le), one_mul]; nlinarith
    · rw [max_eq_right ((one_le_inv₀ ha).mpr h)]
      have h2 : 1 ≤ a⁻¹ := (one_le_inv₀ ha).mpr h
      have h3 : a * a⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt ha)
      nlinarith [h2, h3, hv]
  have hle : (1 + a * v)⁻¹ ≤ (max 1 a⁻¹) * (1 + v)⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ hu, ← div_eq_mul_inv, div_mul_eq_mul_div, one_le_div₀ hw]
    exact hkey
  calc (1 + a * v) ^ (-(m:ℤ)) = (1 + a * v)⁻¹ ^ m := by rw [zpow_neg, zpow_natCast, ← inv_pow]
    _ ≤ ((max 1 a⁻¹) * (1 + v)⁻¹) ^ m := pow_le_pow_left₀ (inv_nonneg.mpr hu.le) hle m
    _ = (max 1 a⁻¹)^m * (1 + v) ^ (-(m:ℤ)) := by rw [mul_pow, zpow_neg, zpow_natCast, ← inv_pow]

theorem ftLatticeSummable {ℓ : ℝ} (hℓ : 0 < ℓ) {F : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hFTdec : ∀ n : ℕ, ∃ C : ℝ, ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖∫ y : EuclideanSpace ℝ (Fin 3), Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * F y‖
        ≤ C * (1 + ‖p‖) ^ (-(n : ℤ)))
    (z : EuclideanSpace ℝ (Fin 3)) :
    Summable (fun m : Fin 3 → ℤ =>
      (∫ y : EuclideanSpace ℝ (Fin 3),
          Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) y : ℂ))) * F y)
        * Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) z : ℂ))) := by
  obtain ⟨C, hC⟩ := hFTdec 4
  have ha : 0 < 2 * Real.pi / ℓ := by positivity
  have hsum0 : Summable (fun m : Fin 3 → ℤ =>
      (1 + ‖Work.BoseBoxFock.latVec m‖) ^ (-(↑(4:ℕ) : ℤ))) := by
    have h := Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv (N := 4) le_rfl
    simpa only [zpow_neg, zpow_natCast] using h
  refine Summable.of_norm_bounded
    (g := fun m : Fin 3 → ℤ => max C 0 * (max 1 (2 * Real.pi / ℓ)⁻¹)^4 *
      (1 + ‖Work.BoseBoxFock.latVec m‖) ^ (-(↑(4:ℕ) : ℤ)))
    (hsum0.mul_left _) ?_
  intro m
  have hmul : ‖(2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m‖
      = (2 * Real.pi / ℓ) * ‖Work.BoseBoxFock.latVec m‖ := by
    rw [norm_smul, Real.norm_of_nonneg ha.le]
  have hA : ‖∫ y : E3,
      Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) y : ℂ))) * F y‖
      ≤ max C 0 * (1 + ‖(2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m‖) ^ (-(↑(4:ℕ) : ℤ)) := by
    refine (hC ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m)).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)
  have hB : ‖Complex.exp (Complex.I *
      (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) z : ℂ))‖ = 1 := by
    rw [mul_comm Complex.I (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) z : ℂ),
      Complex.norm_exp_ofReal_mul_I]
  calc ‖(∫ y : E3,
        Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) y : ℂ))) * F y)
        * Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) z : ℂ))‖
      = _ * ‖Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) z : ℂ))‖ :=
        norm_mul _ _
    _ = _ := by rw [hB, mul_one]
    _ ≤ max C 0 * (1 + ‖(2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m‖) ^ (-(↑(4:ℕ) : ℤ)) := hA
    _ = max C 0 * (1 + (2 * Real.pi / ℓ) * ‖Work.BoseBoxFock.latVec m‖) ^ (-(↑(4:ℕ) : ℤ)) := by
        rw [hmul]
    _ ≤ max C 0 * ((max 1 (2 * Real.pi / ℓ)⁻¹)^4 *
          (1 + ‖Work.BoseBoxFock.latVec m‖) ^ (-(↑(4:ℕ) : ℤ))) :=
        mul_le_mul_of_nonneg_left (inv_zpow_le ha 4 (norm_nonneg _)) (le_max_right C 0)
    _ = max C 0 * (max 1 (2 * Real.pi / ℓ)⁻¹)^4 *
          (1 + ‖Work.BoseBoxFock.latVec m‖) ^ (-(↑(4:ℕ) : ℤ)) := by ring

end Work.BoseBoxFock.LatSamplingAux
