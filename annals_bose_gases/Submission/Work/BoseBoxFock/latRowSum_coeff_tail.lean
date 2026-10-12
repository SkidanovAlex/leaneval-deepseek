import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.rowSumDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latRowSum_coeff_tail`

The coefficient `rhoCoef` of the *difference* `rowSum - ballSum` is

    `rhoCoef ℓ fu N W n = (ζ(kmomInt ℓ n) − 1_{n ∈ latBall (N/4)}) · Ŵ(kmomInt ℓ n)`

where `ζ = uvCut fu (uvRad ℓ N)` is the ultraviolet cut-off of the row sum (`= 1` below the
radius `uvRad ℓ N`, `= 0` above `2·uvRad ℓ N`) and `1_{latBall (N/4)}` is the indicator of the
momentum ball cut at the lattice radius `N/4` (the partial sum `ballSum`).

Two elementary facts pin the coefficient:

* on the momentum ball `‖latVec n‖ ≤ N/4` the two selection factors **coincide**
  (`‖kmomInt ℓ n‖ = (2π/ℓ)‖latVec n‖` and `uvRad ℓ N = (2π/ℓ)(N/4)`, so `‖kmomInt ℓ n‖ ≤ uvRad ℓ N`
  and the `LowCut` equals `1` there), hence `rhoCoef` **vanishes**;
* off the ball the indicator is `0`, so `rhoCoef = ζ · Ŵ` is the full Fourier sample multiplied
  by a factor of modulus `≤ 1` (a `LowCut` takes values in `[0,1]`).

Consequently `|rhoCoef|²` is pointwise dominated (for **every** `n`, inside or outside the cube
`cube N`) by the tail summand `1_{‖latVec n‖ > N/4}·|Ŵ(kmomInt ℓ n)|²`, and the finite sum over
`cube N` is bounded by the lattice tail.  This is the first of the two estimates feeding
`Work.BoseBoxFock.latRowSum_tendsto_L2`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open LatFourier

/-- `‖kmomInt ℓ n‖ = (2π/ℓ)·‖latVec n‖` for `ℓ > 0`. -/
private lemma kmomInt_norm_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (n : Fin 3 → ℤ) :
    ‖kmomInt ℓ n‖ = (2 * Real.pi / ℓ) * ‖latVec n‖ := by
  rw [kmomInt_eq_smul_latVec, norm_smul, Real.norm_of_nonneg (by positivity)]

/-- **The pointwise bound on the coefficient of `rowSum − ballSum`.**  For `ℓ > 0` and every
lattice point `n`,

    `‖rhoCoef ℓ fu N W n‖² ≤ 1_{N/4 < ‖latVec n‖} · ‖latFt ℓ W n‖² .`

On the momentum ball `‖latVec n‖ ≤ N/4` both selection factors are `1`, so the coefficient is `0`;
off it only the cut-off survives, and it is bounded by `1` in modulus. -/
private lemma rhoCoef_norm_sq_le {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (W : EuclideanSpace ℝ (Fin 3) → ℝ) (n : Fin 3 → ℤ) :
    ‖rhoCoef ℓ fu N W n‖ ^ 2 ≤
      (if (N : ℝ) / 4 < ‖latVec n‖ then ‖latFt ℓ W n‖ ^ 2 else 0) := by
  have hpi : 0 < 2 * Real.pi / ℓ := by positivity
  rcases le_or_gt ‖latVec n‖ ((N : ℝ) / 4) with hcase | hcase
  · -- on the momentum ball both selection factors are `1`, so the coefficient vanishes
    rw [if_neg (not_lt.mpr hcase)]
    have hle : ‖kmomInt ℓ n‖ ≤ uvRad ℓ N := by
      rw [kmomInt_norm_eq hℓ, uvRad]
      calc (2 * Real.pi / ℓ) * ‖latVec n‖ ≤ (2 * Real.pi / ℓ) * ((N : ℝ) / 4) :=
            mul_le_mul_of_nonneg_left hcase hpi.le
        _ = 2 * Real.pi / ℓ * (N : ℝ) / 4 := by ring
    have hc : uvCut fu (uvRad ℓ N) (kmomInt ℓ n) = 1 := by
      rw [uvCut]
      exact fu.one _ (div_le_one_of_le₀ hle (by rw [uvRad]; positivity))
    have hzero : rhoCoef ℓ fu N W n = 0 := by
      simp only [rhoCoef]
      rw [hc, if_pos (mem_latBall.mpr hcase)]
      simp
    rw [hzero]
    simp
  · -- off the ball only the cut-off survives, and it has modulus `≤ 1`
    rw [if_pos hcase]
    have hb : ¬ (n ∈ latBall ((N : ℝ) / 4)) :=
      fun h => absurd (mem_latBall.mp h) (not_le.mpr hcase)
    have hrw : rhoCoef ℓ fu N W n
        = ((uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ) : ℂ) * latFt ℓ W n := by
      simp only [rhoCoef]
      rw [if_neg hb, sub_zero]
    have hnormc : ‖((uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ) : ℂ)‖ ≤ 1 := by
      have h1 : ‖((uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ) : ℂ)‖
          = |uvCut fu (uvRad ℓ N) (kmomInt ℓ n)| := by simp
      rw [h1, uvCut]
      exact abs_le.mpr ⟨by linarith [fu.nonneg (‖kmomInt ℓ n‖ / uvRad ℓ N)],
        fu.le_one (‖kmomInt ℓ n‖ / uvRad ℓ N)⟩
    rw [hrw, norm_mul]
    have hnn : 0 ≤ ‖((uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ) : ℂ)‖ * ‖latFt ℓ W n‖ := by
      positivity
    have hle2 : ‖((uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ) : ℂ)‖ * ‖latFt ℓ W n‖
        ≤ 1 * ‖latFt ℓ W n‖ :=
      mul_le_mul_of_nonneg_right hnormc (norm_nonneg _)
    simpa using pow_le_pow_left₀ hnn hle2 2

theorem latRowSum_coeff_tail {ℓ : ℝ} (hℓ : 0 < ℓ) {fu : Work.BoseBoxFix.LowCut} {N : ℕ}
    (hN : 1 ≤ N) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hsumm : Summable (fun n : Fin 3 → ℤ => ‖Work.BoseBoxFock.LatFourier.latFt ℓ W n‖ ^ 2)) :
    (∑ n ∈ Work.BoseRowQ2.cube N, ‖Work.BoseBoxFock.rhoCoef ℓ fu N W n‖ ^ 2)
      ≤ ∑' n : Fin 3 → ℤ,
          (if (N : ℝ) / 4 < ‖Work.BoseBoxFock.latVec n‖ then
            ‖Work.BoseBoxFock.LatFourier.latFt ℓ W n‖ ^ 2 else 0) := by
  -- the tail summand is nonnegative and dominated by the summable `‖latFt‖²`
  have hg : Summable (fun n : Fin 3 → ℤ =>
      (if (N : ℝ) / 4 < ‖Work.BoseBoxFock.latVec n‖ then
        ‖Work.BoseBoxFock.LatFourier.latFt ℓ W n‖ ^ 2 else 0)) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by
        split_ifs with h
        · exact le_rfl
        · positivity) hsumm
  calc (∑ n ∈ Work.BoseRowQ2.cube N, ‖Work.BoseBoxFock.rhoCoef ℓ fu N W n‖ ^ 2)
      ≤ ∑ n ∈ Work.BoseRowQ2.cube N,
          (if (N : ℝ) / 4 < ‖Work.BoseBoxFock.latVec n‖ then
            ‖Work.BoseBoxFock.LatFourier.latFt ℓ W n‖ ^ 2 else 0) :=
        Finset.sum_le_sum (fun n _ => rhoCoef_norm_sq_le hℓ fu N W n)
    _ ≤ ∑' n : Fin 3 → ℤ,
          (if (N : ℝ) / 4 < ‖Work.BoseBoxFock.latVec n‖ then
            ‖Work.BoseBoxFock.LatFourier.latFt ℓ W n‖ ^ 2 else 0) :=
        hg.sum_le_tsum _ (fun n _ => by split_ifs <;> positivity)

end Work.BoseBoxFock
