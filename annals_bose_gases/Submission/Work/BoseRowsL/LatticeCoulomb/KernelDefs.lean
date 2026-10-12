import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsL.LatticeCoulomb.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.KernelDefs`

The normalised kernel `kcal` of the lattice Coulomb comparison and the elementary helpers of the
reduction.  Kept in a *separate, cycle-free* module (importing only `Defs`) so that both the
target file `latticeCoulomb_approx` and the reduction cores can import it.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators Topology

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The cosine form of `chat`**: `chat W k = ∫_y W y · cos⟪k,y⟫ dy`. -/
theorem chat_eq_integral_cos {W : E3 → ℝ} (hW : Integrable W) (k : E3) :
    Work.BoseFixR.chat W k = ∫ y, W y * Real.cos (inner ℝ k y) := by
  have hpt : ∀ y : E3, (Complex.exp (-(Complex.I * (inner ℝ k y : ℂ)))
      * ((W y : ℝ) : ℂ)).re = W y * Real.cos (inner ℝ k y) := by
    intro y
    have h1 : Complex.exp (-(Complex.I * (inner ℝ k y : ℂ)))
        = (Real.cos (inner ℝ k y) : ℂ) - (Real.sin (inner ℝ k y) : ℂ) * Complex.I := by
      rw [show (-(Complex.I * (inner ℝ k y : ℂ)))
            = ((-(inner ℝ k y) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    rw [h1, sub_mul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.sub_re, zero_mul, mul_zero, sub_zero]
    ring
  have hInt : Integrable
      (fun y : E3 => Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * ((W y : ℝ) : ℂ)) := by
    refine Integrable.mono' hW.norm ?_ ?_
    · exact ((by fun_prop : Continuous (fun y : E3 =>
          Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))))).aestronglyMeasurable).mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hW.aestronglyMeasurable)
    · filter_upwards with y
      rw [norm_mul, Complex.norm_exp]
      have hz : (-(Complex.I * (inner ℝ k y : ℂ))).re = 0 := by simp
      simp [hz]
  rw [Work.BoseFixR.chat, Submission.BoseGases.kinFT]
  rw [show (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * ((W y : ℝ) : ℂ)).re
        = ∫ y : E3, (Complex.exp (-(Complex.I * (inner ℝ k y : ℂ)))
            * ((W y : ℝ) : ℂ)).re from (integral_re (μ := volume) hInt).symm]
  simp only [hpt]

/-- `‖ℓ⁻¹ • vec n‖ = (2π/ℓ)‖nvec n‖`. -/
theorem norm_inv_smul_vec (ℓ : ℝ) (hℓ : 0 < ℓ) (n : Fin 3 → ℤ) :
    ‖ℓ⁻¹ • Work.BoseB4.vec n‖ = (2 * Real.pi / ℓ) * ‖nvec n‖ := by
  rw [vec_eq_smul_nvec, smul_smul, norm_smul,
    Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ℓ⁻¹ * (2 * Real.pi))]
  ring

/-- The truncation threshold in the normalised variable:
`‖ℓ⁻¹ • vec n‖ ≤ K ↔ ‖nvec n‖ ≤ Kℓ/(2π)`. -/
theorem norm_inv_smul_vec_le_iff {ℓ K : ℝ} (hℓ : 0 < ℓ) (hK : 0 < K) (n : Fin 3 → ℤ) :
    ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ≤ K ↔ ‖nvec n‖ ≤ K * ℓ / (2 * Real.pi) := by
  have hiff : ((2 * Real.pi / ℓ) * ‖nvec n‖ ≤ K)
      ↔ (‖nvec n‖ ≤ K * ℓ / (2 * Real.pi)) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hℓ,
      le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
    constructor <;> intro h <;> linarith
  simpa [norm_inv_smul_vec ℓ hℓ n] using hiff

/-- The `n = 0` summand of the target vanishes (Lean's junk value of `x / 0`). -/
theorem zero_summand (c₁ c₂ : ℝ) : c₁ * c₂ / (2 * ‖(0 : E3)‖ ^ 2) = 0 := by
  simp

/-- `cos a * cos b = (cos (a+b) + cos (a−b)) / 2`. -/
theorem cos_mul_cos (a b : ℝ) :
    Real.cos a * Real.cos b = (Real.cos (a + b) + Real.cos (a - b)) / 2 := by
  rw [Real.cos_add, Real.cos_sub]; ring

/-- The normalised kernel of the target: `kcal w = Σ_{n∈T} cos⟪kₙ,w⟫/(2‖kₙ‖²)
− ℓ³(2π)⁻³∫_{B_K} cos⟪p,w⟫/(2‖p‖²) dp`, `kₙ = ℓ⁻¹ • vec n`. -/
def kcal (T : Finset (Fin 3 → ℤ)) (ℓ K : ℝ) (w : E3) : ℝ :=
  (∑ n ∈ T, Real.cos (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec n) w)
      / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2))
    - ℓ ^ 3 * ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p in Metric.closedBall 0 K, Real.cos (inner ℝ p w) / (2 * ‖p‖ ^ 2)

/-- **The `T`-bookkeeping**: for `S` as in the target, the nonzero part `T := S.filter (· ≠ 0)`
satisfies exactly the hypotheses of the normalised kernel bound
(`Work.BoseRowsL.LatticeCoulomb.latticeKernel_bound`), with `R = Kℓ/(2π)`. -/
theorem kernel_hypotheses {ℓ K : ℝ} (hℓ : 0 < ℓ) (hK : 0 < K) (S : Finset (Fin 3 → ℤ))
    (hS₁ : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ≤ K → n ∈ S)
    (hS₂ : ∀ n ∈ S, ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ≤ K) :
    (∀ n ∈ S.filter (fun n => n ≠ 0), n ≠ 0) ∧
    (∀ n ∈ S.filter (fun n => n ≠ 0), ‖nvec n‖ ≤ K * ℓ / (2 * Real.pi)) ∧
    (∀ n : Fin 3 → ℤ, n ≠ 0 → ‖nvec n‖ ≤ K * ℓ / (2 * Real.pi) →
        n ∈ S.filter (fun n => n ≠ 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    exact (Finset.mem_filter.mp hn).2
  · intro n hn
    exact (norm_inv_smul_vec_le_iff hℓ hK n).mp (hS₂ n (Finset.mem_filter.mp hn).1)
  · intro n hn0 hnR
    exact Finset.mem_filter.mpr ⟨hS₁ n hn0 ((norm_inv_smul_vec_le_iff hℓ hK n).mpr hnR),
      hn0⟩

/-- The sum over `S` of a summand vanishing at `0` is the sum over `T = S.filter (· ≠ 0)`. -/
theorem sum_eq_sum_filter (S : Finset (Fin 3 → ℤ)) (g : (Fin 3 → ℤ) → ℝ) (h0 : g 0 = 0) :
    (∑ n ∈ S, g n) = ∑ n ∈ S.filter (fun n => n ≠ 0), g n := by
  classical
  exact (Finset.sum_subset (Finset.filter_subset (fun n => n ≠ 0) S) (fun x hxS hx => by
    have hx0 : x = 0 := by
      by_contra h
      exact hx (Finset.mem_filter.mpr ⟨hxS, h⟩)
    rw [hx0]; exact h0)).symm



end Work.BoseRowsL.LatticeCoulomb
