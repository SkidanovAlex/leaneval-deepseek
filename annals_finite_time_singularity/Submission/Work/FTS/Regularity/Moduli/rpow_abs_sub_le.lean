import Mathlib.Analysis.MeanInequalitiesPow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity.Moduli

/-- For `0 < p ≤ 1` the map `x ↦ x ^ p` is subadditive on `ℝ≥0`, hence `p`-Hölder
as a self-map of `ℝ≥0`. -/
lemma rpow_abs_sub_le {p s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hp0 : 0 < p) (hp1 : p ≤ 1) : |s ^ p - t ^ p| ≤ |s - t| ^ p := by
  rcases le_total t s with hts | hst
  · rw [abs_of_nonneg (sub_nonneg.2 hts),
      abs_of_nonneg (sub_nonneg.2 (Real.rpow_le_rpow ht hts hp0.le))]
    have h := Real.rpow_add_le_add_rpow ht (sub_nonneg.2 hts) hp0.le hp1
    rw [show t + (s - t) = s by ring] at h
    linarith
  · have h1 : s ^ p ≤ t ^ p := Real.rpow_le_rpow hs hst hp0.le
    have h := Real.rpow_add_le_add_rpow hs (sub_nonneg.2 hst) hp0.le hp1
    rw [show s + (t - s) = t by ring] at h
    rw [abs_of_nonpos (sub_nonpos.2 h1), abs_of_nonpos (sub_nonpos.2 hst)]
    simp only [neg_sub]
    linarith

end Work.FTS.Regularity.Moduli
