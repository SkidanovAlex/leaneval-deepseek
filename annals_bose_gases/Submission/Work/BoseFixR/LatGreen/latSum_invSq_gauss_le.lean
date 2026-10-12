import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.LatGreen.MadelungBound
import Submission.Work.BoseFixR.LatGreen.latBox_notMem_norm_ge_three
import Submission.Work.BoseFixR.LatGreen.latticeGaussSummable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.latSum_invSq_gauss_le`

The uniform bound for the "`1/‖x‖²` times Gaussian" lattice tail

`T(u) = Σ_{n ∉ latBox} (1/‖u − n‖²) · e^{−‖u − n‖²/4}`,  `u ∈ ℝ³`, `|u i| ≤ 2`,

which occurs in the short-distance analysis of the periodic lattice Coulomb Green's function:
`T` is summable and bounded uniformly on the fundamental region `[-2,2]³`.

The proof is a two-line reduction to the *uniform Gaussian lattice sum* bound:

* for `n ∉ latBox` (recall `latBox = {−4,…,4}³`) the centre hypothesis `|u i| ≤ 2` forces
  `‖u − latVec n‖ ≥ 3` (`latBox_notMem_norm_ge_three`), hence `1/‖u − latVec n‖² ≤ 1`; the
  `n ∈ latBox` terms are killed by the indicator, so pointwise
  `T`-summand `≤ e^{−‖u−latVec n‖²/4}`;
* `Σ_n e^{−‖u − latVec n‖²/4} ≤ (4π)^{3/2} (1 + ρ(1))³` uniformly in `u`, where `ρ = rhoZ` is
  the Fourier tail of the Poisson summation of the heat kernel (`PoissonGauss1D`): this is
  `latticeGaussSum_le` at time `t = 1` with the numerical ledger left symbolic.

No numerical evaluation is needed (the constant `(4π)^{3/2}(1 + ρ(1))³` is a perfectly good
real number), so the whole file rests on the already-proved Poisson/Jacobi summation for the
periodised heat kernel.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseFixR.LatGreen

/-- **The rescaling identity**: the Gaussian `e^{−‖x‖²/4}` is the heat kernel at time `1`
(up to the normalisation `(4π)^{3/2}`). -/
private lemma exp_neg_norm_sq_div_four_eq (x : EuclideanSpace ℝ (Fin 3)) :
    Real.exp (-‖x‖ ^ 2 / 4) = (4 * Real.pi) ^ (3 / 2 : ℝ) * heatK3 1 x := by
  have hpos : (0 : ℝ) < 4 * Real.pi := by positivity
  rw [heatK3]
  norm_num only [mul_one]
  rw [Real.rpow_neg hpos.le, ← mul_assoc,
    mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hpos _)), one_mul]

/-- **Uniform bound on the shifted lattice Gaussian sum at `c = 1/4`**:
`Σ_{n ∈ ℤ³} e^{−‖u − n‖²/4} ≤ (4π)^{3/2} (1 + rhoZ 1)³` for every `u : ℝ³`.

This is `latticeGaussSum_le` (which treats `c = 5/2`) at the time `t = 1` of the heat kernel,
with the numerical ledger left symbolic: Poisson/Jacobi summation (`PoissonGauss1D`) bounds each
one-dimensional factor `Q1 1 (u i)` by `1 + rhoZ 1`. -/
lemma latticeGaussSum_div_four_le (u : EuclideanSpace ℝ (Fin 3)) :
    (∑' n : Fin 3 → ℤ, Real.exp (-‖u - latVec n‖ ^ 2 / 4))
      ≤ (4 * Real.pi) ^ (3 / 2 : ℝ) * (1 + rhoZ 1) ^ 3 := by
  have hS : (∑' n : Fin 3 → ℤ, Real.exp (-‖u - latVec n‖ ^ 2 / 4))
      = (4 * Real.pi) ^ (3 / 2 : ℝ) * heatPeriod 1 u := by
    rw [heatPeriod]
    rw [show (∑' n : Fin 3 → ℤ, Real.exp (-‖u - latVec n‖ ^ 2 / 4))
        = ∑' n : Fin 3 → ℤ,
            (4 * Real.pi) ^ (3 / 2 : ℝ) * heatK3 1 (u - latVec n) from
      tsum_congr (fun n => exp_neg_norm_sq_div_four_eq (u - latVec n))]
    rw [tsum_mul_left]
  rw [hS]
  have ht : (0 : ℝ) < 1 := by norm_num
  have hQ1le : ∀ i : Fin 3, (∑' m : ℤ, heatK1 1 (u i - m)) ≤ 1 + rhoZ 1 := by
    intro i
    have h := (PoissonGauss1D ht (u i)).2
    have h' : |Q1 1 (u i) - 1| ≤ rhoZ 1 := by simpa only [Q1, rhoZ, SZ] using h
    have h2 : Q1 1 (u i) - 1 ≤ rhoZ 1 := le_trans (le_abs_self _) h'
    have h3 : Q1 1 (u i) = ∑' m : ℤ, heatK1 1 (u i - m) := rfl
    linarith [h2, h3]
  have hQ1nn : ∀ i : Fin 3, (0 : ℝ) ≤ ∑' m : ℤ, heatK1 1 (u i - m) :=
    fun i => tsum_nonneg (fun m => heatK1_nonneg ht _)
  have hh : heatPeriod (1 : ℝ) u ≤ (1 + rhoZ 1) ^ 3 := by
    have hprod := md_heatPeriod_eq_prod ht u
    rw [hprod, Fin.prod_univ_three]
    have hρ : (0 : ℝ) ≤ 1 + rhoZ 1 := by linarith [rhoZ_nonneg (1 : ℝ)]
    have h01 : (∑' m : ℤ, heatK1 1 (u 0 - m)) * (∑' m : ℤ, heatK1 1 (u 1 - m))
        ≤ (1 + rhoZ 1) * (1 + rhoZ 1) :=
      mul_le_mul (hQ1le 0) (hQ1le 1) (hQ1nn 1) hρ
    have h2 : (∑' m : ℤ, heatK1 1 (u 0 - m)) * (∑' m : ℤ, heatK1 1 (u 1 - m))
          * (∑' m : ℤ, heatK1 1 (u 2 - m))
        ≤ (1 + rhoZ 1) * (1 + rhoZ 1) * (1 + rhoZ 1) :=
      mul_le_mul h01 (hQ1le 2) (hQ1nn 2) (by positivity)
    calc _ ≤ (1 + rhoZ 1) * (1 + rhoZ 1) * (1 + rhoZ 1) := h2
      _ = (1 + rhoZ 1) ^ 3 := by ring
  exact mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (by positivity) _)

/-- The shifted lattice Gaussian sum at `c = 1/4` is summable (instance of
`latticeGaussSummable` at `c = 1/4`). -/
lemma summable_exp_neg_norm_sq_div_four (u : EuclideanSpace ℝ (Fin 3)) :
    Summable (fun n : Fin 3 → ℤ => Real.exp (-‖u - latVec n‖ ^ 2 / 4)) := by
  have h := latticeGaussSummable u (show (0 : ℝ) < 1 / 4 by norm_num)
  refine h.congr (fun n => ?_)
  rw [show -(1 / 4 : ℝ) * ‖u - latVec n‖ ^ 2 = -‖u - latVec n‖ ^ 2 / 4 by ring]

/-- **Pointwise domination of the `latBox`-complement summand by the Gaussian.**  For
`|u i| ≤ 2` and every `n : ℤ³` the summand of the target sum is at most `e^{−‖u − n‖²/4}`:
on `latBox` the indicator gives `0`, and off `latBox` we have `‖u − n‖ ≥ 3`, so that
`1/‖u − n‖² ≤ 1`. -/
lemma latSum_invSq_gauss_pointwise_le {u : EuclideanSpace ℝ (Fin 3)}
    (hu : ∀ i : Fin 3, |u i| ≤ 2) (n : Fin 3 → ℤ) :
    (if n ∈ latBox then 0 else (1 / ‖u - latVec n‖ ^ 2)
        * Real.exp (-‖u - latVec n‖ ^ 2 / 4))
      ≤ Real.exp (-‖u - latVec n‖ ^ 2 / 4) := by
  by_cases hn : n ∈ latBox
  · rw [if_pos hn]; exact Real.exp_nonneg _
  · rw [if_neg hn]
    have h3 := latBox_notMem_norm_ge_three hu hn
    have hpos : (0 : ℝ) < ‖u - latVec n‖ ^ 2 := by nlinarith [norm_nonneg (u - latVec n)]
    have hle : 1 / ‖u - latVec n‖ ^ 2 ≤ 1 := by
      rw [div_le_iff₀ hpos]; nlinarith
    exact mul_le_of_le_one_left (Real.exp_nonneg _) hle

/-- The summand of the target sum is nonnegative. -/
private lemma latSum_invSq_gauss_nonneg (u : EuclideanSpace ℝ (Fin 3)) (n : Fin 3 → ℤ) :
    0 ≤ (if n ∈ latBox then 0 else (1 / ‖u - latVec n‖ ^ 2)
        * Real.exp (-‖u - latVec n‖ ^ 2 / 4)) := by
  by_cases hn : n ∈ latBox
  · rw [if_pos hn]
  · rw [if_neg hn]; positivity

/-- **The uniform bound on the `latBox`-complement lattice sum**: for `|u i| ≤ 2` the series
`Σ_{n ∉ latBox} (1/‖u − n‖²) e^{−‖u − n‖²/4}` is summable and bounded by
`(4π)^{3/2}(1 + rhoZ 1)³`. -/
theorem latSum_invSq_gauss_le :
    ∃ K : ℝ, ∀ u : EuclideanSpace ℝ (Fin 3), (∀ i : Fin 3, |u i| ≤ 2) →
      Summable (fun n : Fin 3 → ℤ => if n ∈ Work.BoseFixR.LatGreen.latBox then 0 else
          (1 / ‖u - Work.BoseFixR.LatGreen.latVec n‖ ^ 2)
            * Real.exp (-‖u - Work.BoseFixR.LatGreen.latVec n‖ ^ 2 / 4)) ∧
      (∑' n : Fin 3 → ℤ, if n ∈ Work.BoseFixR.LatGreen.latBox then 0 else
          (1 / ‖u - Work.BoseFixR.LatGreen.latVec n‖ ^ 2)
            * Real.exp (-‖u - Work.BoseFixR.LatGreen.latVec n‖ ^ 2 / 4)) ≤ K := by
  refine ⟨(4 * Real.pi) ^ (3 / 2 : ℝ) * (1 + rhoZ 1) ^ 3, fun u hu => ⟨?_, ?_⟩⟩
  · exact Summable.of_nonneg_of_le (fun n => latSum_invSq_gauss_nonneg u n)
      (fun n => latSum_invSq_gauss_pointwise_le hu n)
      (summable_exp_neg_norm_sq_div_four u)
  · calc (∑' n : Fin 3 → ℤ, if n ∈ latBox then 0 else
          (1 / ‖u - latVec n‖ ^ 2) * Real.exp (-‖u - latVec n‖ ^ 2 / 4))
        ≤ ∑' n : Fin 3 → ℤ, Real.exp (-‖u - latVec n‖ ^ 2 / 4) :=
          Summable.tsum_le_tsum (fun n => latSum_invSq_gauss_pointwise_le hu n)
            (Summable.of_nonneg_of_le (fun n => latSum_invSq_gauss_nonneg u n)
              (fun n => latSum_invSq_gauss_pointwise_le hu n)
              (summable_exp_neg_norm_sq_div_four u))
            (summable_exp_neg_norm_sq_div_four u)
      _ ≤ (4 * Real.pi) ^ (3 / 2 : ℝ) * (1 + rhoZ 1) ^ 3 := latticeGaussSum_div_four_le u

end Work.BoseFixR.LatGreen
