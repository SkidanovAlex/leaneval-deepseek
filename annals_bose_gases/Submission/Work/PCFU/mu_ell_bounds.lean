import ChallengeDeps
import Submission.Work.BoseBoxFock.PCFU.ChDKernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PCFU

/-- Monomial normal form of the inverse cube of a positive rpow monomial:
`(c · t^{-e})^{-3} = t^{3e} · c^{-3}`.  Used only to compute `(ℓ)^{-3}` for the box side
`ℓ = a (μa³)^{-163/323}`. -/
private lemma inv_cube_smul_rpow (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    (c * t ^ (-(163 / 323 : ℝ))) ^ (-3 : ℤ)
      = t ^ (489 / 323 : ℝ) * c ^ (-(3 : ℝ)) := by
  rw [zpow_neg, zpow_ofNat]
  have hinv : (c * t ^ (-(163 / 323 : ℝ)))⁻¹ = c⁻¹ * t ^ (163 / 323 : ℝ) := by
    rw [mul_inv, ← Real.rpow_neg ht.le]
    norm_num
  have hc3 : c⁻¹ ^ 3 = c ^ (-(3 : ℝ)) := by
    rw [inv_pow, ← Real.rpow_natCast c 3, ← Real.rpow_neg hc.le]
    rfl
  have ht3 : (t ^ (163 / 323 : ℝ)) ^ 3 = t ^ (489 / 323 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  rw [← inv_pow, hinv, mul_pow, hc3, ht3]
  ring

theorem mu_ell_bounds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hav : 0 < BoseGases.a v) :
    (∀ ⦃μ : ℝ⦄, 0 < μ → Work.BoseBoxFix.Adm v ε₀ μ →
        μ ≤ ε₀ / (BoseGases.a v) ^ 3) ∧
    (∀ ⦃μ : ℝ⦄, 0 < μ → Work.BoseBoxFix.Adm v ε₀ μ →
        μ * (Work.BoseBoxFock.ellH v μ) ^ (-3 : ℤ)
          ≤ (BoseGases.a v) ^ (-6 : ℤ) * ε₀ ^ (812 / 323 : ℝ)) := by
  constructor
  · intro μ hμ hAdm
    obtain ⟨-, hμa3, -⟩ := hAdm
    have h3 : (0 : ℝ) < (BoseGases.a v) ^ 3 := by positivity
    rw [le_div_iff₀ h3]
    exact hμa3
  · intro μ hμ hAdm
    obtain ⟨-, hμa3, -⟩ := hAdm
    have ha : 0 < BoseGases.a v := hav
    have htz : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
    -- the mode box side is the honest box side `ℓ = a (μa³)^{-163/323}`
    have hell : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) :=
      if_pos (Work.BoseBox.sideAt_pos hμ ha)
    have hside : Work.BoseBox.sideAt μ (BoseGases.a v)
        = BoseGases.a v * (μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323 : ℝ)) :=
      Work.BoseBox.sideAt_eq_rpow ha hμ
    -- its inverse cube, in monomial normal form
    have hpow : (Work.BoseBoxFock.ellH v μ) ^ (-3 : ℤ)
        = (μ * (BoseGases.a v) ^ 3) ^ (489 / 323 : ℝ) * (BoseGases.a v) ^ (-(3 : ℝ)) := by
      rw [hell, hside]
      exact inv_cube_smul_rpow (BoseGases.a v) (μ * (BoseGases.a v) ^ 3) ha htz
    -- `μ = (μ a³) · a^{-3}`
    have hμ_eq : μ = (μ * (BoseGases.a v) ^ 3) * (BoseGases.a v) ^ (-(3 : ℝ)) := by
      have hc : (BoseGases.a v) ^ 3 * (BoseGases.a v) ^ (-(3 : ℝ)) = 1 := by
        rw [← Real.rpow_natCast (BoseGases.a v) 3, Real.rpow_neg ha.le 3]
        exact mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos ha 3))
      rw [mul_assoc, hc, mul_one]
    have h1 : (BoseGases.a v) ^ (-(6 : ℝ))
        = (BoseGases.a v) ^ (-(3 : ℝ)) * (BoseGases.a v) ^ (-(3 : ℝ)) := by
      have : (-(6 : ℝ)) = (-(3 : ℝ)) + (-(3 : ℝ)) := by norm_num
      rw [this, Real.rpow_add ha]
    have h812 : (μ * (BoseGases.a v) ^ 3) ^ (812 / 323 : ℝ)
        = (μ * (BoseGases.a v) ^ 3) ^ (489 / 323 : ℝ) * (μ * (BoseGases.a v) ^ 3) := by
      have : (812 / 323 : ℝ) = (489 / 323 : ℝ) + 1 := by norm_num
      rw [this, Real.rpow_add htz, Real.rpow_one]
    have ha6z : (BoseGases.a v) ^ (-(6 : ℝ)) = (BoseGases.a v) ^ (-6 : ℤ) := by
      rw [Real.rpow_neg ha.le 6, zpow_neg, zpow_ofNat, ← Real.rpow_natCast (BoseGases.a v) 6]
      rfl
    have ha6pos : (0 : ℝ) ≤ (BoseGases.a v) ^ (-6 : ℤ) := by
      rw [zpow_neg, zpow_ofNat]
      exact inv_nonneg.mpr (pow_nonneg ha.le 6)
    -- the exact monomial identity
    have hid : μ * (Work.BoseBoxFock.ellH v μ) ^ (-3 : ℤ)
        = (μ * (BoseGases.a v) ^ 3) ^ (812 / 323 : ℝ) * (BoseGases.a v) ^ (-(6 : ℝ)) := by
      rw [hpow, h1, h812]
      nth_rewrite 1 [hμ_eq]
      ring
    calc μ * (Work.BoseBoxFock.ellH v μ) ^ (-3 : ℤ)
        = (μ * (BoseGases.a v) ^ 3) ^ (812 / 323 : ℝ)
            * (BoseGases.a v) ^ (-(6 : ℝ)) := hid
      _ = (μ * (BoseGases.a v) ^ 3) ^ (812 / 323 : ℝ)
            * (BoseGases.a v) ^ (-6 : ℤ) := by rw [ha6z]
      _ ≤ ε₀ ^ (812 / 323 : ℝ) * (BoseGases.a v) ^ (-6 : ℤ) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow htz.le hμa3 (by norm_num)) ha6pos
      _ = (BoseGases.a v) ^ (-6 : ℤ) * ε₀ ^ (812 / 323 : ℝ) := by ring

end Work.PCFU
