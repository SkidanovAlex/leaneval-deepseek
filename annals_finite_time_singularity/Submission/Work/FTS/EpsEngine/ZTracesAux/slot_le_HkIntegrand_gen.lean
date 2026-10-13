import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.FTS.H2.LinfQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A mixed/radial slot with the bare weight `w` is dominated by `HkIntegrand`

The `H^k` weight attached to a mixed derivative `D_z^b D_θ^a` is `Wt = w · sin(2θ)^{-γ/2}`
(for `a ≥ 1`) resp. `w · sin(2θ)^{-η/2}` (for the pure `D_z`-slots).  Both weights are at
least `w` on the open quadrant, because `sin(2θ) ≤ 1` there.  Hence the squared slot with the
*unweighted* factor `w` is still dominated by the corresponding term of `HkIntegrand`, which
is what `slot_le_HkIntegrand_gen` records.
-/

namespace Work.FTS.EpsEngine.ZTracesAux

theorem slot_le_HkIntegrand_gen {α : ℝ} (hα : 0 < α)
    {f : ℝ → ℝ → ℝ} {m : ℕ} (b a : ℕ) (hab : a + b ≤ m) (s : ℝ) {σ : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2 ≤ Work.Spaces.HkIntegrand α m f s σ := by
  have hsin_pos : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
  have hsin_le : Real.sin (2 * σ) ≤ 1 := Real.sin_le_one _
  have hw_nonneg : 0 ≤ Work.Spaces.w s := by
    rw [Work.Spaces.w]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  rcases Nat.eq_zero_or_pos a with ha | ha
  · -- pure `D_z`-slot: compare with the `η/2`-weighted term of `HkIntegrand`
    subst ha
    have hab' : b ≤ m := by omega
    have hmain := Work.Spaces.sq_le_HkIntegrand_z α m f s σ b hab'
    have ht_pos : 0 < (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) :=
      Real.rpow_pos_of_pos hsin_pos _
    have ht_le : (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) ≤ 1 := by
      refine Real.rpow_le_one hsin_pos.le hsin_le ?_
      rw [Work.Spaces.eta]
      norm_num
    have hwle : Work.Spaces.w s
        ≤ Work.Spaces.w s / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) := by
      rw [le_div_iff₀ ht_pos]
      exact mul_le_of_le_one_right hw_nonneg ht_le
    simp only [Work.Spaces.mixed_zero_right]
    calc (Work.Spaces.DzIter b f s σ * Work.Spaces.w s) ^ 2
        = (Work.Spaces.DzIter b f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 := by ring
      _ ≤ (Work.Spaces.DzIter b f s σ) ^ 2
            * (Work.Spaces.w s / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw_nonneg hwle 2) (sq_nonneg _)
      _ = (Work.Spaces.DzIter b f s σ
            * (Work.Spaces.w s / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α m f s σ := hmain
  · -- mixed slot (`a ≥ 1`): compare with the `γ/2`-weighted term of `HkIntegrand`
    have hgam : 0 ≤ Work.Spaces.gam α := by
      rw [Work.Spaces.gam]; linarith
    have hc : -(Work.Spaces.gam α / 2) ≤ 0 := by linarith
    have hwt : 1 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2)) := by
      have h := Real.rpow_le_rpow_of_nonpos hsin_pos hsin_le hc
      simpa using h
    have hwt_sq : 1 ≤ ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hwt 2
      simpa using h
    have hsq_le : (Work.Spaces.w s) ^ 2 ≤ (Work.Spaces.Wt α s σ) ^ 2 := by
      rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
      simpa using mul_le_mul_of_nonneg_left hwt_sq (sq_nonneg (Work.Spaces.w s))
    have hmain := Work.Spaces.sq_le_HkIntegrand_mixed α m f s σ a b ha hab
    calc (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2
        = (Work.Spaces.mixed b a f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 := by ring
      _ ≤ (Work.Spaces.mixed b a f s σ) ^ 2 * (Work.Spaces.Wt α s σ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq_le (sq_nonneg _)
      _ = (Work.Spaces.mixed b a f s σ * Work.Spaces.Wt α s σ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α m f s σ := hmain

end Work.FTS.EpsEngine.ZTracesAux
