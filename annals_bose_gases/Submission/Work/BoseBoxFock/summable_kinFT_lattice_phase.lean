import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.KinRowQuant
import Submission.Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.summable_kinFT_lattice_phase`

Summability of the **lattice sampling of the phase-twisted Fourier transform** of a smooth
compactly supported function: for `ℓ > 0`, `W : ℝ³ → ℂ` smooth with compact support and every
`z ∈ ℝ³`,

    `Σ_n Ŵ(k_n)·e^{i⟪k_n,z⟫} < ∞` absolutely,   `k_n = kmomInt ℓ n = (2π/ℓ)·latVec n`.

This is the summability input of the lattice Poisson (aliasing) identity
`Work.BoseBoxFock.latticePoisson_kernel`, where the phase factors `e^{i⟪k_n,z⟫}` are exactly the
Fourier covariance of the translation `W ↦ W(· + z)`.

## Proof

`W` smooth with compact support makes `Ŵ = kinFT W` Schwartz, hence polynomially decaying:
`‖Ŵ(p)‖ ≤ C (1 + ‖p‖)^{-4}` (`Work.OneBodyKin.kinFT_decay_le` at order `4`).  The phase factor has
modulus `1` (`Complex.norm_exp_ofReal_mul_I`), so the terms are dominated in absolute value by
`C (1 + (2π/ℓ)‖latVec n‖)^{-4}`, and the lattice series
`Σ_n (1 + ‖latVec n‖)^{-4}` converges (`Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv`).
The only bookkeeping is the scalar rescaling `(1 + c‖v‖)^{-4} ≤ (min 1 c)^{-4}(1 + ‖v‖)^{-4}`,
which absorbs `c = 2π/ℓ > 0` into the constant.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary lattice bookkeeping -/

/-- `Work.BoseB4.vec n = (2π n_i)_i = 2π • latVec n`. -/
private lemma vec_eq_two_pi_smul_latVec (n : Fin 3 → ℤ) :
    Work.BoseB4.vec n = (2 * Real.pi) • latVec n := by
  rw [Work.BoseB4.vec, latVec, ← WithLp.toLp_smul]
  rfl

/-- The sampling lattice is `kmomInt ℓ n = (2π/ℓ) • latVec n`. -/
private lemma kmomInt_eq_smul_latVec (ℓ : ℝ) (n : Fin 3 → ℤ) :
    kmomInt ℓ n = (2 * Real.pi / ℓ) • latVec n := by
  rw [kmomInt, vec_eq_two_pi_smul_latVec, smul_smul]
  congr 1
  ring

/-! ## The scalar rescaling of the `(1 + ‖·‖)^{-N}` majorant -/

/-- `(1 + c‖v‖)^{-N} ≤ (min 1 c)^{-N}·(1 + ‖v‖)^{-N}` for `c > 0`. -/
private lemma inv_one_add_mul_pow_le {c : ℝ} (hc : 0 < c) (N : ℕ) (v : E3) :
    ((1 + c * ‖v‖) ^ N)⁻¹ ≤ ((min 1 c) ^ N)⁻¹ * ((1 + ‖v‖) ^ N)⁻¹ := by
  have hminpos : 0 < min 1 c := lt_min one_pos hc
  have hle : min 1 c * (1 + ‖v‖) ≤ 1 + c * ‖v‖ := by
    rcases le_total 1 c with h | h
    · rw [min_eq_left h, one_mul]; nlinarith [norm_nonneg v]
    · rw [min_eq_right h]; nlinarith [norm_nonneg v]
  have h1 : (1 + c * ‖v‖)⁻¹ ≤ (min 1 c * (1 + ‖v‖))⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr hle
  rw [mul_inv] at h1
  calc ((1 + c * ‖v‖) ^ N)⁻¹ = ((1 + c * ‖v‖)⁻¹) ^ N := by rw [inv_pow]
    _ ≤ ((min 1 c)⁻¹ * (1 + ‖v‖)⁻¹) ^ N := pow_le_pow_left₀ (by positivity) h1 N
    _ = ((min 1 c) ^ N)⁻¹ * ((1 + ‖v‖) ^ N)⁻¹ := by rw [mul_pow, inv_pow, inv_pow]

/-- The phase `e^{i x}` of a real `x` has modulus `1`. -/
private lemma norm_exp_I_mul_ofReal (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm Complex.I (x : ℂ), Complex.norm_exp_ofReal_mul_I]

/-! ## The target -/

theorem summable_kinFT_lattice_phase {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hWs : HasCompactSupport W)
    (z : EuclideanSpace ℝ (Fin 3)) :
    Summable (fun n : Fin 3 → ℤ =>
      Submission.BoseGases.kinFT W (Work.BoseBoxFock.kmomInt ℓ n)
        * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) z : ℂ))) := by
  -- polynomial decay of the Fourier transform of `W`
  obtain ⟨C, hC0, hC⟩ := Work.OneBodyKin.kinFT_decay_le 4 hW hWs
  have hC' : ∀ p : E3, ‖Submission.BoseGases.kinFT W p‖ ≤ C * ((1 + ‖p‖) ^ 4)⁻¹ := by
    intro p
    have := hC p
    rwa [div_eq_mul_inv] at this
  have hcpos : 0 < 2 * Real.pi / ℓ := by positivity
  -- the `(1 + ‖latVec ·‖)^{-4}` lattice series is summable
  have hbase : Summable (fun n : Fin 3 → ℤ => ((1 + ‖latVec n‖) ^ 4)⁻¹) :=
    summable_one_add_norm_latVec_pow_inv (N := 4) le_rfl
  refine Summable.of_norm_bounded
    (g := fun n : Fin 3 → ℤ =>
      C * ((min 1 (2 * Real.pi / ℓ)) ^ 4)⁻¹ * ((1 + ‖latVec n‖) ^ 4)⁻¹) ?_ ?_
  · exact (hbase.mul_left (C * ((min 1 (2 * Real.pi / ℓ)) ^ 4)⁻¹)).congr (fun n => by ring)
  · intro n
    have hnorm : ‖Submission.BoseGases.kinFT W (kmomInt ℓ n)
          * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) z : ℂ))‖
        = ‖Submission.BoseGases.kinFT W (kmomInt ℓ n)‖ := by
      rw [norm_mul, norm_exp_I_mul_ofReal (inner ℝ (kmomInt ℓ n) z), mul_one]
    have hkm : ‖kmomInt ℓ n‖ = (2 * Real.pi / ℓ) * ‖latVec n‖ := by
      rw [kmomInt_eq_smul_latVec ℓ n, norm_smul, Real.norm_of_nonneg hcpos.le]
    rw [hnorm]
    calc ‖Submission.BoseGases.kinFT W (kmomInt ℓ n)‖
        ≤ C * ((1 + ‖kmomInt ℓ n‖) ^ 4)⁻¹ := hC' _
      _ = C * ((1 + (2 * Real.pi / ℓ) * ‖latVec n‖) ^ 4)⁻¹ := by rw [hkm]
      _ ≤ C * (((min 1 (2 * Real.pi / ℓ)) ^ 4)⁻¹ * ((1 + ‖latVec n‖) ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left (inv_one_add_mul_pow_le hcpos 4 (latVec n)) hC0
      _ = C * ((min 1 (2 * Real.pi / ℓ)) ^ 4)⁻¹ * ((1 + ‖latVec n‖) ^ 4)⁻¹ := by ring

end Work.BoseBoxFock
