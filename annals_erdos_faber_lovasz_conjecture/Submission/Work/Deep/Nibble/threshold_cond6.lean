import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.threshold_tools

namespace Work.Deep.Nibble

/-- Auxiliary form of `threshold_cond6` with the threshold instantiated: for `0 < κ < 1`,
`n ≥ ((1+κ)^{21/20}/(1-κ))^{10000}` and `D ≥ n^{1/100}` we have
`(1-κ) D^{21/20} ≥ ((1+κ)D)^{26/25}`.

The proof reduces, via `26/25 = 21/20 - 1/100`, `Real.rpow_sub` and `Real.mul_rpow`,
to `(1+κ)^{21/20} ≤ (1-κ) ((1+κ)D)^{1/100}`, and this follows from
`D^{1/100} ≥ (n^{1/100})^{1/100} = n^{1/10000} ≥ (1+κ)^{21/20}/(1-κ)`. -/
private theorem threshold_cond6_aux {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (n : ℕ) (D : ℝ)
    (hn : ((1 + κ) ^ ((21 : ℝ) / 20) / (1 - κ)) ^ ((10000 : ℝ)) ≤ (n : ℝ))
    (hD : (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D) :
    (1 - κ) * D ^ ((21 : ℝ) / 20) ≥ ((1 + κ) * D) ^ ((26 : ℝ) / 25) := by
  have h1κ : 0 < 1 + κ := by linarith
  have h1mκ : 0 < 1 - κ := by linarith
  have hA : 0 < (1 + κ) ^ ((21 : ℝ) / 20) := Real.rpow_pos_of_pos h1κ ((21 : ℝ) / 20)
  have hc0 : 0 < (1 + κ) ^ ((21 : ℝ) / 20) / (1 - κ) := div_pos hA h1mκ
  have hN0 : 0 < ((1 + κ) ^ ((21 : ℝ) / 20) / (1 - κ)) ^ ((10000 : ℝ)) :=
    Real.rpow_pos_of_pos hc0 ((10000 : ℝ))
  have hnr : 0 < (n : ℝ) := hN0.trans_le hn
  have hnD0 : 0 < (n : ℝ) ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hnr ((1 : ℝ) / 100)
  have hD0 : 0 < D := hnD0.trans_le hD
  have hx0 : 0 < (1 + κ) * D := mul_pos h1κ hD0
  have hD21 : 0 < D ^ ((21 : ℝ) / 20) := Real.rpow_pos_of_pos hD0 ((21 : ℝ) / 20)
  have hX0 : 0 < ((1 + κ) * D) ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hx0 ((1 : ℝ) / 100)
  have hxD : D ≤ (1 + κ) * D := by
    have h2 : D + κ * D = (1 + κ) * D := by ring
    have h1 : D ≤ D + κ * D := le_add_of_nonneg_right (mul_nonneg hκ0.le hD0.le)
    linarith
  -- `(1+κ)^{21/20}/(1-κ) ≤ n^{1/10000}`
  have hroot : (1 + κ) ^ ((21 : ℝ) / 20) / (1 - κ) ≤ (n : ℝ) ^ ((1 : ℝ) / 10000) := by
    have h1 : (((1 + κ) ^ ((21 : ℝ) / 20) / (1 - κ)) ^ ((10000 : ℝ))) ^ ((1 : ℝ) / 10000)
        ≤ (n : ℝ) ^ ((1 : ℝ) / 10000) :=
      Real.rpow_le_rpow hN0.le hn (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 10000)
    have h2 : (((1 + κ) ^ ((21 : ℝ) / 20) / (1 - κ)) ^ ((10000 : ℝ))) ^ ((1 : ℝ) / 10000)
        = (1 + κ) ^ ((21 : ℝ) / 20) / (1 - κ) := by
      rw [← Real.rpow_mul hc0.le,
        show (10000 : ℝ) * ((1 : ℝ) / 10000) = 1 from by norm_num, Real.rpow_one]
    rwa [h2] at h1
  -- `n^{1/10000} ≤ D^{1/100} ≤ ((1+κ)D)^{1/100}`
  have hmid : (n : ℝ) ^ ((1 : ℝ) / 10000) ≤ ((1 + κ) * D) ^ ((1 : ℝ) / 100) := by
    calc (n : ℝ) ^ ((1 : ℝ) / 10000)
        = ((n : ℝ) ^ ((1 : ℝ) / 100)) ^ ((1 : ℝ) / 100) := by
          rw [← Real.rpow_mul hnr.le,
            show ((1 : ℝ) / 100) * ((1 : ℝ) / 100) = (1 : ℝ) / 10000 from by norm_num]
      _ ≤ D ^ ((1 : ℝ) / 100) :=
          Real.rpow_le_rpow hnD0.le hD (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 100)
      _ ≤ ((1 + κ) * D) ^ ((1 : ℝ) / 100) :=
          Real.rpow_le_rpow hD0.le hxD (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 100)
  -- the reduced inequality
  have hkey : (1 + κ) ^ ((21 : ℝ) / 20) ≤ ((1 + κ) * D) ^ ((1 : ℝ) / 100) * (1 - κ) :=
    (div_le_iff₀ h1mκ).mp (hroot.trans hmid)
  have hfin : (1 + κ) ^ ((21 : ℝ) / 20) * D ^ ((21 : ℝ) / 20)
      ≤ (1 - κ) * D ^ ((21 : ℝ) / 20) * ((1 + κ) * D) ^ ((1 : ℝ) / 100) := by
    calc (1 + κ) ^ ((21 : ℝ) / 20) * D ^ ((21 : ℝ) / 20)
        ≤ (((1 + κ) * D) ^ ((1 : ℝ) / 100) * (1 - κ)) * D ^ ((21 : ℝ) / 20) :=
          mul_le_mul_of_nonneg_right hkey hD21.le
      _ = (1 - κ) * D ^ ((21 : ℝ) / 20) * ((1 + κ) * D) ^ ((1 : ℝ) / 100) := by ring
  -- split the exponent `26/25 = 21/20 - 1/100`
  have hsplit : ((1 + κ) * D) ^ ((26 : ℝ) / 25)
      = (1 + κ) ^ ((21 : ℝ) / 20) * D ^ ((21 : ℝ) / 20)
        / (((1 + κ) * D) ^ ((1 : ℝ) / 100)) := by
    have e : ((26 : ℝ) / 25) = ((21 : ℝ) / 20) - ((1 : ℝ) / 100) := by norm_num
    rw [e, Real.rpow_sub hx0, Real.mul_rpow h1κ.le hD0.le]
  rw [hsplit]
  exact (div_le_iff₀ hX0).mpr hfin

/-- **Clause 6 of the asymptotic side conditions of `cor:sparse_egj`** (threshold form).
For every `0 < κ < 1` there is `N > 0` such that for all `n ≥ N` and all
`D ≥ n^{1/100}` one has `(1-κ) * D^(21/20) ≥ ((1+κ)D)^(26/25)`.

Route: `26/25 = 21/20 - 1/100`, so `((1+κ)D)^(26/25)
= ((1+κ)D)^(21/20) / ((1+κ)D)^(1/100) = (1+κ)^(21/20) D^(21/20) / ((1+κ)D)^(1/100)`
(`Real.rpow_sub`, `Real.mul_rpow`); cancelling the common positive factor `D^(21/20)` this is
equivalent to `(1+κ)^(21/20) ≤ (1-κ) ((1+κ)D)^(1/100)`.  Since
`((1+κ)D)^(1/100) ≥ D^(1/100) ≥ (n^{1/100})^(1/100) = n^(1/10000)`, it suffices to take
`N := ((1+κ)^(21/20)/(1-κ)) ^ (10000)`. -/
theorem threshold_cond6 {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∃ N : ℝ, 0 < N ∧ ∀ n : ℕ, N ≤ (n : ℝ) → ∀ D : ℝ, (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
      (1 - κ) * D ^ ((21 : ℝ) / 20) ≥ ((1 + κ) * D) ^ ((26 : ℝ) / 25) := by
  have h1κ : 0 < 1 + κ := by linarith
  have hA : 0 < (1 + κ) ^ ((21 : ℝ) / 20) := Real.rpow_pos_of_pos h1κ _
  have hc0 : 0 < (1 + κ) ^ ((21 : ℝ) / 20) / (1 - κ) := div_pos hA (by linarith)
  refine ⟨((1 + κ) ^ ((21 : ℝ) / 20) / (1 - κ)) ^ ((10000 : ℝ)), ?_, ?_⟩
  · exact Real.rpow_pos_of_pos hc0 _
  · intro n hn D hD
    exact threshold_cond6_aux hκ0 hκ1 n D hn hD

end Work.Deep.Nibble
