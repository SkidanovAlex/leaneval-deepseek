import ChallengeDeps
import Submission.Work.BoseBoxFock.adm_regime_gate
import Submission.Work.BoseBoxFock.frkCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.FRK

theorem adm_kin_regime (v : EuclideanSpace ℝ (Fin 3) → ℝ) (hav : 0 < BoseGases.a v) {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hs₀1 : s₀ ≤ 1) {μ : ℝ}
    (hμ : Work.BoseBoxFix.Adm v (s₀ ^ 323) μ) :
    let P := Work.BoseBox.paramsAt μ (BoseGases.a v)
    let ℓ := Work.BoseBox.sideAt μ (BoseGases.a v)
    0 < ℓ ∧ 0 < P.s ∧ P.s ≤ s₀ ∧ 0 < P.d ∧ P.d ≤ 1 ∧ 0 ≤ P.eT ∧ P.eT ≤ 1 ∧
      P.eT * P.d ^ 4 ≤ P.s ∧ P.b = Work.BoseBox.bValue ∧
      (P.d ^ 2 * ℓ)⁻¹ ≤ Work.BoseBoxFock.FRK.kappaHon v μ := by
  obtain ⟨hμpos, hdil, _hOK⟩ := hμ
  -- the diluteness `t = μ (a v)³`; `Adm` bounds it by `s₀³²³`
  set t : ℝ := μ * (BoseGases.a v) ^ 3 with htdef
  have hav3 : (0 : ℝ) < (BoseGases.a v) ^ 3 := by positivity
  have ht : 0 < t := by rw [htdef]; exact mul_pos hμpos hav3
  have hs1 : s₀ ^ 323 ≤ 1 := pow_le_one₀ hs₀.le hs₀1
  have ht1 : t ≤ 1 := le_trans hdil hs1
  have hts : t ≤ s₀ ^ (323 : ℝ) := by simpa using hdil
  have hP : Work.BoseBox.paramsAt μ (BoseGases.a v) = Work.BoseBox.fsParams t := rfl
  have hL : Work.BoseBox.sideAt μ (BoseGases.a v) =
      Work.BoseBox.boxSide (Work.BoseBox.fsParams t) μ (BoseGases.a v) := rfl
  dsimp only
  simp only [Work.BoseBoxFock.FRK.kappaHon]
  rw [hP, hL]
  simp only [Work.BoseBox.fsParams, Work.BoseBox.boxSide, Work.BoseBox.bValue]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial, ?_⟩
  · exact mul_pos (Work.BoseBox.fsXp_pos ht) (Real.rpow_pos_of_pos (mul_pos hμpos hav) _)
  · exact Work.BoseBox.fsXp_pos ht
  · -- `s = t^{1/323} ≤ (s₀³²³)^{1/323} = s₀`
    have h := Real.rpow_le_rpow (x := t) (y := s₀ ^ (323 : ℝ)) (z := (1 : ℝ) / 323)
      ht.le hts (by norm_num)
    have h2 : (s₀ ^ (323 : ℝ)) ^ ((1 : ℝ) / 323) = s₀ := by
      rw [← Real.rpow_mul hs₀.le, show (323 : ℝ) * (1 / 323) = 1 by norm_num, Real.rpow_one]
    exact le_trans h (le_of_eq h2)
  · exact Work.BoseBox.fsXp_pos ht
  · exact Work.BoseBox.fsXp_le_one ht ht1 (by norm_num)
  · exact (Work.BoseBox.fsXp_pos ht).le
  · exact Work.BoseBox.fsXp_le_one ht ht1 (by norm_num)
  · -- `ε_T d⁴ = t^{119/(4·323)} ≤ t^{1/323} = s`
    have hpow : Work.BoseBox.fsXp t 6 ^ 4 = Work.BoseBox.fsXp t 24 := by
      rw [Work.BoseBox.fsXp_pow ht.le]; norm_num
    rw [hpow, Work.BoseBox.fsXp_mul ht (23 / 4) 24,
      show (23 : ℝ) / 4 + 24 = 119 / 4 by norm_num]
    exact Work.BoseBox.fsXp_le_fsXp ht ht1 (by norm_num)
  · -- `κ = (K_ℓ d²)⁻¹√(μa)` equals `(d²ℓ)⁻¹` since `ℓ = K_ℓ(μa)^{-1/2}`
    have hμa : 0 < μ * BoseGases.a v := mul_pos hμpos hav
    have hroot : ((μ * BoseGases.a v) ^ ((-(1 / 2)) : ℝ))⁻¹ = Real.sqrt (μ * BoseGases.a v) := by
      rw [Real.rpow_neg hμa.le (1 / 2), inv_inv, Real.sqrt_eq_rpow]
    refine le_of_eq ?_
    rw [show Work.BoseBox.fsXp t 6 ^ 2 *
          (Work.BoseBox.fsXp t (-(3 / 2)) * (μ * BoseGases.a v) ^ ((-(1 / 2)) : ℝ))
        = (Work.BoseBox.fsXp t (-(3 / 2)) * Work.BoseBox.fsXp t 6 ^ 2) *
          (μ * BoseGases.a v) ^ ((-(1 / 2)) : ℝ) by ring,
      mul_inv, hroot, Real.rpow_neg_one]

end Work.BoseBoxFock.FRK
