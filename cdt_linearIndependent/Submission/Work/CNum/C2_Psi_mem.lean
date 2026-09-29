import Mathlib
import Submission.Work.CNum.C2_setup

namespace Work.CNum

theorem C2_Psi_mem {t : ℝ} (ht : t ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) :
    C2Psi t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hαpos : 0 < alpR := alpR_pos
  have hαlt : alpR < Real.pi := alpR_lt_pi
  have hC : 0 < C2C := C2C_pos
  set β : ℝ := Real.pi / 2 - alpR / 2 with hβdef
  have hβpos : 0 < β := by rw [hβdef]; linarith
  have hβlt : β < Real.pi / 2 := by rw [hβdef]; linarith
  have hβltpi : β < Real.pi := by linarith
  have hsinβ : Real.sin β = C2C := by
    rw [hβdef, Real.sin_pi_div_two_sub, cos_half_alpR]
  set θ : ℝ := Real.pi / 2 - t with hθdef
  have hθ1 : -β < θ := by rw [hθdef, hβdef]; linarith [ht.2]
  have hθ2 : θ < β := by rw [hθdef, hβdef]; linarith [ht.1]
  have hθabs : |θ| < β := abs_lt.mpr ⟨hθ1, hθ2⟩
  have hsinθ_lt : |Real.sin θ| < C2C := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith), ← hsinβ]
    refine Real.strictMonoOn_sin ?_ ?_ hθabs
    · exact ⟨by linarith [abs_nonneg θ], by linarith⟩
    · exact ⟨by linarith, le_of_lt hβlt⟩
  have harg_lt : |Real.sin θ / C2C| < 1 := by
    rw [abs_div, abs_of_pos hC, div_lt_iff₀ hC, one_mul]
    exact hsinθ_lt
  have harg : Real.sin θ / C2C ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp harg_lt
  set g : ℝ := Real.arcsin (Real.sin θ / C2C) with hgdef
  have hgmem : g ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨Real.neg_pi_div_two_lt_arcsin.mpr harg.1, Real.arcsin_lt_pi_div_two.mpr harg.2⟩
  have hPsi : C2Psi t = g - θ := by
    have ht_eq : t - Real.pi / 2 = -θ := by rw [hθdef]; ring
    have hcos : Real.cos t = Real.sin θ := by
      have : t = Real.pi / 2 - θ := by rw [hθdef]; ring
      rw [this, Real.cos_pi_div_two_sub]
    rw [C2Psi, hgdef, hcos, ht_eq]
    ring
  rw [hPsi]
  refine ⟨?_, ?_⟩
  · by_cases h : θ ≤ 0
    · linarith [hgmem.1, h]
    · have hθpos : 0 < θ := not_le.mp h
      have hsinpos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith)
      have hgpos : 0 < g := by
        rw [hgdef, Real.arcsin_pos]
        exact div_pos hsinpos hC
      linarith [hθ1, hgpos, hβlt]
  · by_cases h : θ ≤ 0
    · have hgle : g ≤ 0 := by
        rw [hgdef, Real.arcsin_nonpos]
        have hsin : Real.sin θ ≤ 0 :=
          Real.sin_nonpos_of_nonpos_of_neg_pi_le h (by linarith [hθ1, hβlt, hpi])
        exact div_nonpos_of_nonpos_of_nonneg hsin hC.le
      linarith [hgle, hθ1, hβlt]
    · have hθpos : 0 < θ := not_le.mp h
      linarith [hgmem.2, hθpos]

end Work.CNum

