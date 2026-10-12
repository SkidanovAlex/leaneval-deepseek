import ChallengeDeps
import Submission.Work.BoseFixR.adm_R_le_ell_chiR0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

theorem adm_100R_le_ell {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ε₀ μ : ℝ}
    (hR : 0 < R) (hav : 0 < BoseGases.a v)
    (hε : ε₀ ≤ (BoseGases.a v / (100 * R)) ^ (323 / 163 : ℝ))
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) :
    100 * R ≤ Work.BoseFixR.ell v μ := by
  have ha : 0 < BoseGases.a v := hav
  have hμpos : 0 < μ := hAdm.1
  have hdille : μ * (BoseGases.a v) ^ 3 ≤ ε₀ := hAdm.2.1
  have hdilpos : 0 < μ * (BoseGases.a v) ^ 3 := mul_pos hμpos (pow_pos ha 3)
  have hε₀pos : 0 < ε₀ := lt_of_lt_of_le hdilpos hdille
  -- the balanced diluteness `t₀ = 100R/(a v)`, at which `ε₀ = t₀^{-323/163}`
  set t₀ : ℝ := 100 * R / (BoseGases.a v) with ht₀
  have ht₀pos : 0 < t₀ := by rw [ht₀]; positivity
  -- (1) the hypothesis `hε` reads `ε₀ ≤ t₀^{−323/163}`
  have hstep : ε₀ ≤ t₀ ^ (-(323 / 163 : ℝ)) := by
    refine le_trans hε ?_
    have h1 : BoseGases.a v / (100 * R) = t₀⁻¹ := by
      rw [ht₀]
      exact (inv_div (100 * R) (BoseGases.a v)).symm
    rw [h1, Real.inv_rpow ht₀pos.le, ← Real.rpow_neg ht₀pos.le]
  -- (2) monotonicity of the negative power in the diluteness `t ≤ ε₀`
  have hkey : t₀ ≤ (μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323 : ℝ)) := by
    have h1 : t₀ ≤ (t₀ ^ (-(323 / 163 : ℝ))) ^ (-(163 / 323 : ℝ)) := le_of_eq (by
      rw [← Real.rpow_mul ht₀pos.le,
        show (-(323 / 163 : ℝ)) * (-(163 / 323 : ℝ)) = 1 by norm_num, Real.rpow_one])
    have h2 : (t₀ ^ (-(323 / 163 : ℝ))) ^ (-(163 / 323 : ℝ))
        ≤ ε₀ ^ (-(163 / 323 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hε₀pos hstep (by norm_num)
    have h3 : ε₀ ^ (-(163 / 323 : ℝ))
        ≤ (μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hdilpos hdille (by norm_num)
    exact le_trans h1 (le_trans h2 h3)
  -- (3) `ℓ(μ) = (a v)·t^{−163/323} ≥ (a v)·t₀ = 100R`
  have hside : 100 * R ≤ Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [Work.BoseBox.sideAt_eq_rpow ha hμpos]
    have h100 : 100 * R = BoseGases.a v * t₀ := by rw [ht₀]; field_simp
    rw [h100]
    exact mul_le_mul_of_nonneg_left hkey ha.le
  rw [show Work.BoseFixR.ell v μ = Work.BoseBox.sideAt μ (BoseGases.a v) from rfl]
  exact hside

end Work.BoseFixR
