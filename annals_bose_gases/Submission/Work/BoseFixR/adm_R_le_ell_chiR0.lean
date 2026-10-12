import ChallengeDeps
import Submission.Work.BoseFixR.Defs
import Submission.Work.BoseFixR.FamForm.sideAt_d_powers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

/-!
# `Work.BoseFixR.adm_R_le_ell_chiR0`

The large-box condition `R ≤ ℓ(μ)·chiR0` of the comparison argument, at an
**explicit** diluteness cut-off.

The box side is (FS `eq:def_ell`, see `Work.BoseBox.sideAt_eq_rpow`)

  `ℓ(μ) = sideAt μ (a v) = (a v) · (μ (a v)³)^{−163/323}`,

so it blows up as `μ → 0⁺`, like a negative power of the diluteness
`t = μ (a v)³`.  Given the hypothesis

  `ε₀ ≤ ((a v)·chiR0 / R)^{323/163}`,

which is *exactly* `ε₀ ≤ t₀^{−323/163}` at the balanced diluteness
`t₀ = R/((a v)·chiR0)`, and the diluteness bound `t ≤ ε₀` carried by
`Work.BoseBoxFix.Adm v ε₀ μ`, monotonicity of the negative power gives

  `t^{−163/323} ≥ (t₀^{−323/163})^{−163/323} = t₀ = R/((a v)·chiR0)`,

whence `ℓ(μ) = (a v)·t^{−163/323} ≥ R/chiR0`, i.e. `R ≤ ℓ(μ)·chiR0`.

No `ParamsOK` input is needed: the only clauses of `Adm` used are `0 < μ` and
the diluteness bound.
-/

theorem adm_R_le_ell_chiR0 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ε₀ μ : ℝ}
    (hR : 0 < R) (hav : 0 < BoseGases.a v)
    (hε : ε₀ ≤ (BoseGases.a v * Submission.BoseGases.chiR0 / R) ^ (323 / 163 : ℝ))
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) :
    R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 := by
  have ha : 0 < BoseGases.a v := hav
  have hχ : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  have hμpos : 0 < μ := hAdm.1
  have hdille : μ * (BoseGases.a v) ^ 3 ≤ ε₀ := hAdm.2.1
  have hdilpos : 0 < μ * (BoseGases.a v) ^ 3 := mul_pos hμpos (pow_pos ha 3)
  have hε₀pos : 0 < ε₀ := lt_of_lt_of_le hdilpos hdille
  have haχ : 0 < BoseGases.a v * Submission.BoseGases.chiR0 := mul_pos ha hχ
  -- the balanced diluteness `t₀ = R / ((a v)·chiR0)`
  set t₀ : ℝ := R / (BoseGases.a v * Submission.BoseGases.chiR0) with ht₀
  have ht₀pos : 0 < t₀ := by rw [ht₀]; exact div_pos hR haχ
  -- (1) the hypothesis `hε` reads `ε₀ ≤ t₀^{−323/163}`
  have hstep : ε₀ ≤ t₀ ^ (-(323 / 163 : ℝ)) := by
    refine le_trans hε ?_
    have h1 : BoseGases.a v * Submission.BoseGases.chiR0 / R = t₀⁻¹ := by
      rw [ht₀]
      exact (inv_div R (BoseGases.a v * Submission.BoseGases.chiR0)).symm
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
  -- (3) `ℓ(μ) = (a v)·t^{−163/323} ≥ (a v)·t₀ = R/chiR0`
  have hside : BoseGases.a v * t₀ ≤ Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [Work.BoseBox.sideAt_eq_rpow ha hμpos]
    exact mul_le_mul_of_nonneg_left hkey ha.le
  have hR_eq : BoseGases.a v * t₀ * Submission.BoseGases.chiR0 = R := by
    rw [ht₀]; field_simp
  rw [show Work.BoseFixR.ell v μ = Work.BoseBox.sideAt μ (BoseGases.a v) from rfl]
  calc R = BoseGases.a v * t₀ * Submission.BoseGases.chiR0 := hR_eq.symm
    _ ≤ Work.BoseBox.sideAt μ (BoseGases.a v) * Submission.BoseGases.chiR0 :=
        mul_le_mul_of_nonneg_right hside hχ.le

end Work.BoseFixR
