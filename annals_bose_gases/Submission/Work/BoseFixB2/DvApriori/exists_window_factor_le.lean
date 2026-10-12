import ChallengeDeps
import Submission.Work.BoseFixB2.DvApriori.BandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.exists_window_factor_le` — the window-factor threshold

At FS's parameter choice (`Work.BoseBox.paramsAt μ (a v) = fsParams (μ (a v)³)`),
`K_B = X^{-6}` and `K_ℓ = X^{-3/2}` with `X = (μa³)^{1/323}`, so the *window
factor* of the `d₁,d₂` a-priori bound,

    K_B^{3/2} · K_ℓ · (μa³)^{1/4}
      = (μa³)^{-9/323} · (μa³)^{-3/646} · (μa³)^{1/4}
      = (μa³)^{281/1292},

has the **positive** exponent `281/1292 > 0` (this is the content of FS
`con:KB`, `con:sdKellKB`), hence tends to `0` as the diluteness `μa³ → 0`.  So
for any constant `C₁ ≥ 0` there is a window `ε > 0` of diluteness on which
`C₁ · K_B^{3/2} K_ℓ (μa³)^{1/4} ≤ 1/2`, i.e. the window factor is a genuine
small perturbation on the window.
-/

namespace Work.BoseFixB2.DvApriori

/-- The exponent identity behind the window factor: at FS's parameters the
product `K_B^{3/2} K_ℓ (μa³)^{1/4}` is exactly `(μa³)^{281/1292}`. -/
lemma window_factor_eq_rpow {t : ℝ} (ht : 0 < t) :
    (Work.BoseBox.fsParams t).KB ^ (3 / 2 : ℝ) * (Work.BoseBox.fsParams t).Kl
      * t ^ (1 / 4 : ℝ) = t ^ (281 / 1292 : ℝ) := by
  simp only [Work.BoseBox.fsParams]
  rw [Work.BoseBox.fsXp_rpow ht.le (-6) (3 / 2)]
  rw [show (-6 : ℝ) * (3 / 2) = -9 by norm_num]
  rw [Work.BoseBox.fsXp_mul ht (-9) (-(3 / 2))]
  rw [show (-9 : ℝ) + -(3 / 2) = -(21 / 2) by norm_num]
  simp only [Work.BoseBox.fsXp]
  rw [show -((21 : ℝ) / 2) / 323 = -(21 / 646) by norm_num]
  rw [← Real.rpow_add ht]
  norm_num

theorem exists_window_factor_le (v : EuclideanSpace ℝ (Fin 3) → ℝ) (hav : 0 < _root_.BoseGases.a v)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε →
      C₁ * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ (3/2 : ℝ)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1/4 : ℝ)) ≤ 1/2 := by
  have hb : 0 < 2 * C₁ + 1 := by linarith
  refine ⟨min 1 ((2 * C₁ + 1) ^ (-(1292 / 281) : ℝ)),
    lt_min one_pos (Real.rpow_pos_of_pos hb _), ?_⟩
  intro μ hμ hle
  have hav3 : 0 < (_root_.BoseGases.a v) ^ 3 := by positivity
  have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ hav3
  have htε : μ * (_root_.BoseGases.a v) ^ 3 ≤ (2 * C₁ + 1) ^ (-(1292 / 281) : ℝ) :=
    le_trans hle (min_le_right _ _)
  have key : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ (3 / 2 : ℝ)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 4 : ℝ)
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ (281 / 1292 : ℝ) := by
    simp only [Work.BoseBox.paramsAt]
    exact window_factor_eq_rpow ht
  rw [key]
  have hpow : (μ * (_root_.BoseGases.a v) ^ 3) ^ (281 / 1292 : ℝ)
      ≤ (2 * C₁ + 1) ^ (-1 : ℝ) := by
    have h := Real.rpow_le_rpow ht.le htε (by norm_num : (0 : ℝ) ≤ 281 / 1292)
    rwa [← Real.rpow_mul hb.le (-(1292 / 281)) (281 / 1292),
      show (-(1292 / 281 : ℝ)) * (281 / 1292) = -1 by norm_num] at h
  have hfinal : C₁ * (2 * C₁ + 1) ^ (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_iff₀ hb]
    linarith
  calc C₁ * (μ * (_root_.BoseGases.a v) ^ 3) ^ (281 / 1292 : ℝ)
      ≤ C₁ * (2 * C₁ + 1) ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left hpow hC₁
    _ ≤ 1 / 2 := hfinal

end Work.BoseFixB2.DvApriori
