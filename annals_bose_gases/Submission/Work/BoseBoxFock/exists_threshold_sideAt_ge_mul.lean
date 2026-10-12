import ChallengeDeps
import Submission.Work.BoseBox.sideAt_large
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The support-radius threshold.**  For every positive scattering length `a v`,
every radius `R > 0` and every `r > 0` there is a diluteness threshold `ε₀ ∈ (0,1]`
such that for all `μ > 0` with `μ (a v)³ ≤ ε₀` the box side satisfies
`R ≤ sideAt μ (a v) · r`.

Math: `sideAt μ a = a (μa³)^{-163/323}` (`sideAt_eq_rpow`), whose exponent is
negative, so the side diverges as `μ → 0⁺`.  Explicitly take
`ε₀ = min 1 ((a r / R)^{323/163})`; then `μa³ ≤ ε₀` gives
`(μa³)^{163/323} ≤ a r / R`, whence `R ≤ a (μa³)^{-163/323} r`. -/
theorem exists_threshold_sideAt_ge_mul {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hav : 0 < _root_.BoseGases.a v)
    {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * r := by
  set a := _root_.BoseGases.a v with ha
  have hav' : 0 < a := hav
  have har : 0 < a * r / R := by positivity
  refine ⟨min 1 ((a * r / R) ^ ((323 : ℝ) / 163)),
    lt_min one_pos (Real.rpow_pos_of_pos har _), min_le_left _ _, ?_⟩
  intro μ hμ hμle
  have ht : 0 < μ * a ^ 3 := by positivity
  rw [Work.BoseBox.sideAt_eq_rpow hav' hμ]
  set t : ℝ := μ * a ^ 3 with htdef
  have htpos : 0 < t := ht
  -- `(μa³)^{163/323} ≤ a r / R`
  have htr : t ≤ (a * r / R) ^ ((323 : ℝ) / 163) := le_trans hμle (min_le_right _ _)
  have hle := Real.rpow_le_rpow htpos.le htr (by norm_num : (0 : ℝ) ≤ (163 : ℝ) / 323)
  have hmul : ((a * r / R) ^ ((323 : ℝ) / 163)) ^ ((163 : ℝ) / 323)
      = (a * r / R) ^ (((323 : ℝ) / 163) * ((163 : ℝ) / 323)) :=
    (Real.rpow_mul har.le _ _).symm
  rw [hmul] at hle
  have hexp : ((323 : ℝ) / 163) * ((163 : ℝ) / 323) = 1 := by norm_num
  rw [hexp, Real.rpow_one] at hle
  -- `R (μa³)^{163/323} ≤ a r`
  have hkey : R * t ^ ((163 : ℝ) / 323) ≤ a * r := by
    have h1 : R * t ^ ((163 : ℝ) / 323) ≤ R * (a * r / R) :=
      mul_le_mul_of_nonneg_left hle hR.le
    have h2 : R * (a * r / R) = a * r := by field_simp
    linarith [h1, le_of_eq h2]
  have hsum : t ^ ((163 : ℝ) / 323) * t ^ (-(163 / 323 : ℝ)) = 1 := by
    rw [← Real.rpow_add htpos]
    norm_num
  calc R = R * (t ^ ((163 : ℝ) / 323) * t ^ (-(163 / 323 : ℝ))) := by rw [hsum, mul_one]
    _ = R * t ^ ((163 : ℝ) / 323) * t ^ (-(163 / 323 : ℝ)) := by ring
    _ ≤ (a * r) * t ^ (-(163 / 323 : ℝ)) :=
          mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg htpos.le _)
    _ = a * t ^ (-(163 / 323 : ℝ)) * r := by ring

end Work.BoseBoxFock
