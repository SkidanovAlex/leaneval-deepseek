import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.L3Aux.bcoef_gamCoef_le
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L6Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- For `1 ≤ i ≤ 6` the `i`-th `dthU`-iterate of the angular coefficient `Γ(θ)/c(α)` is
dominated by `10⁶·α·Γ(θ)`: the factor `c(α)⁻¹` costs at most `10` (`Spaces.c_bounds`), the
iterate of `Γ` costs `α·10⁵·Γ(θ)` (`Spaces.dthU_iter_Gam_abs_bound` with the uniform bound
`M = 10⁵` for the coefficients `Tfun j`, `j ≤ 5`, supplied by `LocData6.Tfun_abs_le5`). -/
lemma dthU_gamCoefAng_le6 {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) {i : ℕ} (hi1 : 1 ≤ i) (hi6 : i ≤ 6) :
    |Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ|
      ≤ 10 ^ 6 * α * Work.Spaces.Gam α θ := by
  have hdec : (fun t : ℝ => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t)
      = fun t : ℝ => (Work.Spaces.c α)⁻¹ * Work.Spaces.Gam α t := by
    funext t; rw [Work.FTS.StrongPersist.L3Aux.gamCoefAng_eq]; ring
  have hcpos : 0 < Work.Spaces.c α := Work.FTS.StrongPersist.L3Aux.c_pos hα hα1
  have h1 : (Work.Spaces.c α)⁻¹ ≤ 10 := by
    rw [inv_le_iff_one_le_mul₀ hcpos]
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have h2 : |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * 100000 * Work.Spaces.Gam α θ :=
    Work.Spaces.dthU_iter_Gam_abs_bound i hi1 α hα 100000
      (fun t _ => Work.FTS.LocData6.Tfun_abs_le5 (i - 1) (by omega) α hα hα1 t) θ hθ
  rw [hdec, Work.Spaces.dthU_iter_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hcpos)]
  calc (Work.Spaces.c α)⁻¹ * |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ 10 * (α * 100000 * Work.Spaces.Gam α θ) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 10 ^ 6 * α * Work.Spaces.Gam α θ := by ring

/-- Pointwise square bound for the angular jets: for `1 ≤ i ≤ 6` the square of the `i`-th
`dthU`-iterate of `Γ(θ)/c(α)` is at most `10¹²·α²Γ(θ)²`. -/
lemma dthU_gamCoefAng_sq_le6 {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) {i : ℕ} (hi1 : 1 ≤ i) (hi6 : i ≤ 6) :
    (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
      ≤ 10 ^ 12 * α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := by
  have habs := dthU_gamCoefAng_le6 hα hα1 hθ hi1 hi6
  have hnon : 0 ≤ 10 ^ 6 * α * Work.Spaces.Gam α θ := by
    have hG := (Work.Spaces.Gam_bounds α θ hα hθ).1
    positivity
  have h4 : (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
      ≤ (10 ^ 6 * α * Work.Spaces.Gam α θ) ^ 2 :=
    sq_le_sq.mpr (by rw [abs_of_nonneg hnon]; exact habs)
  calc (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
      ≤ (10 ^ 6 * α * Work.Spaces.Gam α θ) ^ 2 := h4
    _ = 10 ^ 12 * α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := by ring

-- The angular block of the order-`6` separation bound: the `θ`-integrand factor of
-- `HkIntegrand α 6` of the separated function `gamCoefAng α θ * bcoefRad z` is dominated by
-- `radAngInt α θ = sin(2θ)^{-η} + α²Γ(θ)²sin(2θ)^{-γ}` with a constant uniform in `α ∈ (0,1]`.
-- Route: `gamCoefAng² ≤ 100` (`L3Aux.gamCoefAng_sq_le`); for `1 ≤ i ≤ 6`,
-- `dthU^[i] (Γ/c) = c⁻¹ · dthU^[i] Γ` (`Spaces.dthU_iter_const_mul`) with
-- `|dthU^[i] Γ| ≤ α·10⁵·Γ` (`Spaces.dthU_iter_Gam_abs_bound` with `M = 10⁵` furnished by
-- `LocData6.Tfun_abs_le5`; keep the factor `α`!), and `c ≥ 1/10` (`Spaces.c_bounds`), so each
-- square is `≤ 10¹²·α²Γ²`; six of them plus the `≤ 100` first term give
-- `K = 10¹³`.  At the endpoints both sides vanish (`Real.zero_rpow`).
theorem gamCoef_angBlk6 : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
    (Work.FTS.StrongPersist.L3Aux.gamCoefAng α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + ∑ i ∈ Finset.range 7,
          (if 1 ≤ i then
            (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
           else 0)
      ≤ K * Work.FTS.StrongPersist.L3Aux.radAngInt α θ := by
  refine ⟨10 ^ 13, by norm_num, ?_⟩
  intro α hα hα1 θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.StrongPersist.L3Aux.sin_two_nonneg_of_mem_Iθ hθ
  have hG : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hR : 0 ≤ Work.FTS.StrongPersist.L3Aux.radAngInt α θ :=
    Work.FTS.StrongPersist.L3Aux.radAngInt_nonneg hs
  have hsE : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs _
  have hsG : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs _
  -- the two `radAngInt`-comparisons
  have hleE : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.FTS.StrongPersist.L3Aux.radAngInt α θ := by
    rw [Work.FTS.StrongPersist.L3Aux.radAngInt_apply]
    have : 0 ≤ α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsG
    linarith
  have hleG : α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ Work.FTS.StrongPersist.L3Aux.radAngInt α θ := by
    rw [Work.FTS.StrongPersist.L3Aux.radAngInt_apply]
    linarith [hsE]
  -- the first summand
  have h1 : (Work.FTS.StrongPersist.L3Aux.gamCoefAng α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ 100 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ := by
    calc _ ≤ 100 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_right
            (Work.FTS.StrongPersist.L3Aux.gamCoefAng_sq_le hα hα1 hθ) hsE
      _ ≤ 100 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ :=
          mul_le_mul_of_nonneg_left hleE (by norm_num)
  -- the angular sum
  have h3 : ∀ i ∈ Finset.range 7,
      (if 1 ≤ i then
        (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
       else 0)
      ≤ 10 ^ 12 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    intro i hi
    by_cases hi1 : 1 ≤ i
    · rw [if_pos hi1]
      have hi6 : i ≤ 6 := by
        have := Finset.mem_range.mp hi
        omega
      have hb := dthU_gamCoefAng_sq_le6 hα hα1 hθ hi1 hi6
      calc (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          ≤ (10 ^ 12 * α ^ 2 * (Work.Spaces.Gam α θ) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            mul_le_mul_of_nonneg_right hb hsG
        _ = 10 ^ 12 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    · rw [if_neg hi1]
      exact mul_nonneg (by norm_num)
        (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsG)
  have h2 : (∑ i ∈ Finset.range 7,
        (if 1 ≤ i then
          (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
         else 0))
      ≤ 7 * 10 ^ 12 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ := by
    calc (∑ i ∈ Finset.range 7, (if 1 ≤ i then
              (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
             else 0))
        ≤ ∑ _i ∈ Finset.range 7, 10 ^ 12 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := Finset.sum_le_sum h3
      _ = 7 * (10 ^ 12 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
            simp [Finset.sum_const, Finset.card_range]
      _ = 7 * 10 ^ 12 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
      _ ≤ 7 * 10 ^ 12 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ :=
            mul_le_mul_of_nonneg_left hleG (by norm_num)
  have hh : (100 : ℝ) + 7 * 10 ^ 12 ≤ 10 ^ 13 := by norm_num
  have hfin := mul_le_mul_of_nonneg_right hh hR
  linarith [h1, h2, hfin]

end Work.FTS.StrongPersist.L6Aux
