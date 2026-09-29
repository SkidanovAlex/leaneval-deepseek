import Mathlib
import Submission.Work.Cert.WL.Defs
import Submission.Work.Cert.LeafAux

namespace Work.Cert.WL

namespace Work.Cert.WL
open Complex
theorem ratio_le (Aq Bq aa bb : ℂ) (eA eB aU bU bL Blo : ℤ)
    (hA : ‖Aq - aa‖ ≤ ((eA : ℤ) : ℝ) / (S : ℝ)) (hB : ‖Bq - bb‖ ≤ ((eB : ℤ) : ℝ) / (S : ℝ))
    (haa : ‖aa‖ ≤ ((aU : ℤ) : ℝ) / (S : ℝ)) (hbu : ‖bb‖ ≤ ((bU : ℤ) : ℝ) / (S : ℝ))
    (hbl : ((bL : ℤ) : ℝ) / (S : ℝ) ≤ ‖bb‖) (hBq : ((Blo : ℤ) : ℝ) / (S : ℝ) ≤ ‖Bq‖)
    (heA : 0 ≤ eA) (heB : 0 ≤ eB) (haU : 0 ≤ aU) (hbU : 0 ≤ bU) (hbL : 0 < bL) (hBlo : 0 < Blo) :
    ‖Aq / Bq - aa / bb‖ ≤ (((eA : ℤ) : ℝ) * ((bU : ℤ) : ℝ) + ((aU : ℤ) : ℝ) * ((eB : ℤ) : ℝ)) /
      (((Blo : ℤ) : ℝ) * ((bL : ℤ) : ℝ)) := by
  have hS : (0 : ℝ) < (S : ℝ) := Work.Cert.S_posR
  have hSne : ((S : ℝ)) ≠ 0 := ne_of_gt hS
  have heAr : (0 : ℝ) ≤ ((eA : ℤ) : ℝ) := by exact_mod_cast heA
  have heBr : (0 : ℝ) ≤ ((eB : ℤ) : ℝ) := by exact_mod_cast heB
  have haUr : (0 : ℝ) ≤ ((aU : ℤ) : ℝ) := by exact_mod_cast haU
  have hbUr : (0 : ℝ) ≤ ((bU : ℤ) : ℝ) := by exact_mod_cast hbU
  have hbLr : (0 : ℝ) < ((bL : ℤ) : ℝ) := by exact_mod_cast hbL
  have hBlr : (0 : ℝ) < ((Blo : ℤ) : ℝ) := by exact_mod_cast hBlo
  have hBqp : 0 < ((Blo : ℤ) : ℝ) / (S : ℝ) := div_pos hBlr hS
  have hbbp : 0 < ((bL : ℤ) : ℝ) / (S : ℝ) := div_pos hbLr hS
  -- both denominators are nonzero, so the difference can be put over a common denominator
  have hBq0 : Bq ≠ 0 := by
    intro h
    rw [h, norm_zero] at hBq
    linarith
  have hbb0 : bb ≠ 0 := by
    intro h
    rw [h, norm_zero] at hbl
    linarith
  -- numerator: `Aq * bb - Bq * aa = (Aq - aa) * bb + aa * (bb - Bq)`
  have hnum : ‖Aq * bb - Bq * aa‖ ≤
      (((eA : ℤ) : ℝ) * ((bU : ℤ) : ℝ) + ((aU : ℤ) : ℝ) * ((eB : ℤ) : ℝ)) / (S : ℝ) ^ 2 := by
    have h1 : ‖(Aq - aa) * bb‖ ≤ (((eA : ℤ) : ℝ) / (S : ℝ)) * (((bU : ℤ) : ℝ) / (S : ℝ)) := by
      rw [norm_mul]
      exact mul_le_mul hA hbu (norm_nonneg _) (div_nonneg heAr hS.le)
    have h2 : ‖aa * (bb - Bq)‖ ≤ (((aU : ℤ) : ℝ) / (S : ℝ)) * (((eB : ℤ) : ℝ) / (S : ℝ)) := by
      rw [norm_mul, norm_sub_rev]
      exact mul_le_mul haa hB (norm_nonneg _) (div_nonneg haUr hS.le)
    have hsplit : Aq * bb - Bq * aa = (Aq - aa) * bb + aa * (bb - Bq) := by ring
    calc ‖Aq * bb - Bq * aa‖ = ‖(Aq - aa) * bb + aa * (bb - Bq)‖ := by rw [hsplit]
      _ ≤ ‖(Aq - aa) * bb‖ + ‖aa * (bb - Bq)‖ := norm_add_le _ _
      _ ≤ (((eA : ℤ) : ℝ) / (S : ℝ)) * (((bU : ℤ) : ℝ) / (S : ℝ)) +
            (((aU : ℤ) : ℝ) / (S : ℝ)) * (((eB : ℤ) : ℝ) / (S : ℝ)) := add_le_add h1 h2
      _ = (((eA : ℤ) : ℝ) * ((bU : ℤ) : ℝ) + ((aU : ℤ) : ℝ) * ((eB : ℤ) : ℝ)) / (S : ℝ) ^ 2 := by
            field_simp
  have hNnn : 0 ≤ (((eA : ℤ) : ℝ) * ((bU : ℤ) : ℝ) + ((aU : ℤ) : ℝ) * ((eB : ℤ) : ℝ)) /
      (S : ℝ) ^ 2 := by
    apply div_nonneg _ (le_of_lt (pow_pos hS 2))
    nlinarith [heAr, heBr, haUr, hbUr]
  have hDpos : 0 < (((Blo : ℤ) : ℝ) * ((bL : ℤ) : ℝ)) / (S : ℝ) ^ 2 :=
    div_pos (mul_pos hBlr hbLr) (pow_pos hS 2)
  -- denominator: `|Bq * bb| ≥ (Blo / S) * (bL / S)`
  have hden : (((Blo : ℤ) : ℝ) * ((bL : ℤ) : ℝ)) / (S : ℝ) ^ 2 ≤ ‖Bq‖ * ‖bb‖ := by
    calc (((Blo : ℤ) : ℝ) * ((bL : ℤ) : ℝ)) / (S : ℝ) ^ 2
        = (((Blo : ℤ) : ℝ) / (S : ℝ)) * (((bL : ℤ) : ℝ) / (S : ℝ)) := by field_simp
      _ ≤ ‖Bq‖ * ‖bb‖ := mul_le_mul hBq hbl (le_of_lt hbbp) (norm_nonneg _)
  calc ‖Aq / Bq - aa / bb‖
      = ‖Aq * bb - Bq * aa‖ / ‖Bq * bb‖ := by
          rw [div_sub_div Aq aa hBq0 hbb0, norm_div]
      _ = ‖Aq * bb - Bq * aa‖ / (‖Bq‖ * ‖bb‖) := by rw [norm_mul]
      _ ≤ ((((eA : ℤ) : ℝ) * ((bU : ℤ) : ℝ) + ((aU : ℤ) : ℝ) * ((eB : ℤ) : ℝ)) / (S : ℝ) ^ 2) /
            ((((Blo : ℤ) : ℝ) * ((bL : ℤ) : ℝ)) / (S : ℝ) ^ 2) :=
          div_le_div₀ hNnn hnum hDpos hden
      _ = (((eA : ℤ) : ℝ) * ((bU : ℤ) : ℝ) + ((aU : ℤ) : ℝ) * ((eB : ℤ) : ℝ)) /
            (((Blo : ℤ) : ℝ) * ((bL : ℤ) : ℝ)) := by
          rw [div_div_div_cancel_right₀ (pow_ne_zero 2 hSne)]
end Work.Cert.WL

end Work.Cert.WL

namespace Work.Cert.WL

/-- The requested statement, restated under the module's own namespace so that it is available
as `Work.Cert.WL.ratio_le` (the declaration above sits in the doubly-nested namespace that the
request template produced). -/
theorem ratio_le (Aq Bq aa bb : ℂ) (eA eB aU bU bL Blo : ℤ)
    (hA : ‖Aq - aa‖ ≤ ((eA : ℤ) : ℝ) / (S : ℝ)) (hB : ‖Bq - bb‖ ≤ ((eB : ℤ) : ℝ) / (S : ℝ))
    (haa : ‖aa‖ ≤ ((aU : ℤ) : ℝ) / (S : ℝ)) (hbu : ‖bb‖ ≤ ((bU : ℤ) : ℝ) / (S : ℝ))
    (hbl : ((bL : ℤ) : ℝ) / (S : ℝ) ≤ ‖bb‖) (hBq : ((Blo : ℤ) : ℝ) / (S : ℝ) ≤ ‖Bq‖)
    (heA : 0 ≤ eA) (heB : 0 ≤ eB) (haU : 0 ≤ aU) (hbU : 0 ≤ bU) (hbL : 0 < bL) (hBlo : 0 < Blo) :
    ‖Aq / Bq - aa / bb‖ ≤ (((eA : ℤ) : ℝ) * ((bU : ℤ) : ℝ) + ((aU : ℤ) : ℝ) * ((eB : ℤ) : ℝ)) /
      (((Blo : ℤ) : ℝ) * ((bL : ℤ) : ℝ)) :=
  Work.Cert.WL.Work.Cert.WL.ratio_le Aq Bq aa bb eA eB aU bU bL Blo
    hA hB haa hbu hbl hBq heA heB haU hbU hbL hBlo

end Work.Cert.WL
