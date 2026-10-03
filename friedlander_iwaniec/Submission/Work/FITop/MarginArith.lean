import Mathlib
import Submission.Work.FITop.Defs

open Filter Asymptotics

namespace Work.FITop

/-- The arithmetic margin of the Friedlander–Iwaniec argument.

With `t = N^{3/4}` and `s = √N`, the quantity
`(4/π)(4κt - C₂s) - C(4κt + C₂s)(log log N / log N) - 4/π`
equals, up to the factor `1/4` in front,
`(4κ/π)t - (C₂/π)s - Cκt·L - C(C₂/4)s·L - 1/π` where `L = log log N / log N`.
Since `L → 0` and `s/t = N^{-1/4} → 0`, the lower-order terms are `o(t)`, while
`4κ/π > 1.11` leaves a positive linear remainder; hence for all large `N` the whole
expression dominates `1.11·N^{3/4}`. -/
theorem MarginArith (κ C C₂ : ℝ) (hκ : 0 < κ) (hmarg : (1.11 : ℝ) < 4 * κ / Real.pi)
    (hC : 0 < C) (hC2 : 0 < C₂) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (1.11 : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4)
        ≤ (1 / 4) * ((4 / Real.pi) * (4 * κ * (N : ℝ) ^ ((3 : ℝ) / 4)
              - C₂ * Real.sqrt (N : ℝ))
            - C * (4 * κ * (N : ℝ) ^ ((3 : ℝ) / 4) + C₂ * Real.sqrt (N : ℝ))
                * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
            - 4 / Real.pi) := by
  set ε : ℝ := 4 * κ / Real.pi - 1.11 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith [hmarg]
  have hε4 : 0 < ε / 4 := by positivity
  -- limit: `log log N / log N → 0`
  have hL : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      atTop (nhds 0) := by
    have hf : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hlog : (fun N : ℕ => Real.log (Real.log (N : ℝ)))
        =o[atTop] (fun N : ℕ => Real.log (N : ℝ)) :=
      Real.isLittleO_log_id_atTop.comp_tendsto hf
    exact hlog.tendsto_div_nhds_zero
  -- limit: `N^{-1/4} → 0`
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 4) : ℝ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  -- limit: `N^{3/4} → ∞`
  have htend : Tendsto (fun N : ℕ => (N : ℝ) ^ ((3 : ℝ) / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp tendsto_natCast_atTop_atTop
  -- the four eventual estimates, each term of the error bounded by `(ε/4)·t`
  have hb1 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) / Real.pi ≤ (ε / 4) * (N : ℝ) ^ ((3 : ℝ) / 4) :=
    (htend.const_mul_atTop hε4).eventually_ge_atTop (1 / Real.pi)
  have hb2 : ∀ᶠ N : ℕ in atTop,
      (C₂ / Real.pi) * (N : ℝ) ^ (-(1 / 4) : ℝ) ≤ ε / 4 := by
    have h := hpow.const_mul (C₂ / Real.pi)
    exact h.eventually_le_const (by rw [mul_zero]; exact hε4)
  have hb3 : ∀ᶠ N : ℕ in atTop,
      (C * κ) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) ≤ ε / 4 := by
    have h := hL.const_mul (C * κ)
    exact h.eventually_le_const (by rw [mul_zero]; exact hε4)
  have hb4 : ∀ᶠ N : ℕ in atTop,
      (C * (C₂ / 4)) * ((N : ℝ) ^ (-(1 / 4) : ℝ)
        * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))) ≤ ε / 4 := by
    have h := (hpow.mul hL).const_mul (C * (C₂ / 4))
    exact h.eventually_le_const
      (by rw [show (C * (C₂ / 4)) * ((0 : ℝ) * 0) = 0 by ring]; exact hε4)
  filter_upwards [hb1, hb2, hb3, hb4, eventually_ge_atTop (1 : ℕ)]
    with N hb1N hb2N hb3N hb4N hN1
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  have htpos : 0 < (N : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hNR _
  have hs : Real.sqrt (N : ℝ) = (N : ℝ) ^ (-(1 / 4) : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, show (1 : ℝ) / 2 = -(1 / 4) + 3 / 4 by norm_num, Real.rpow_add hNR]
  have hab1 : (C₂ / Real.pi) * Real.sqrt (N : ℝ) ≤ (ε / 4) * (N : ℝ) ^ ((3 : ℝ) / 4) :=
    calc (C₂ / Real.pi) * Real.sqrt (N : ℝ)
        = ((C₂ / Real.pi) * (N : ℝ) ^ (-(1 / 4) : ℝ)) * (N : ℝ) ^ ((3 : ℝ) / 4) := by
          rw [hs]; ring
      _ ≤ (ε / 4) * (N : ℝ) ^ ((3 : ℝ) / 4) := mul_le_mul_of_nonneg_right hb2N htpos.le
  have hab2 : C * κ * (N : ℝ) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      ≤ (ε / 4) * (N : ℝ) ^ ((3 : ℝ) / 4) :=
    calc C * κ * (N : ℝ) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
        = ((C * κ) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)))
            * (N : ℝ) ^ ((3 : ℝ) / 4) := by ring
      _ ≤ (ε / 4) * (N : ℝ) ^ ((3 : ℝ) / 4) := mul_le_mul_of_nonneg_right hb3N htpos.le
  have hab3 : C * (C₂ / 4) * Real.sqrt (N : ℝ)
        * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      ≤ (ε / 4) * (N : ℝ) ^ ((3 : ℝ) / 4) :=
    calc C * (C₂ / 4) * Real.sqrt (N : ℝ)
          * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
        = ((C * (C₂ / 4)) * ((N : ℝ) ^ (-(1 / 4) : ℝ)
              * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))))
            * (N : ℝ) ^ ((3 : ℝ) / 4) := by rw [hs]; ring
      _ ≤ (ε / 4) * (N : ℝ) ^ ((3 : ℝ) / 4) := mul_le_mul_of_nonneg_right hb4N htpos.le
  have hab4 : (1 : ℝ) / Real.pi ≤ (ε / 4) * (N : ℝ) ^ ((3 : ℝ) / 4) := hb1N
  -- expansion of the right-hand side into a linear combination of the four terms
  have hexp : (1 / 4) * ((4 / Real.pi) * (4 * κ * (N : ℝ) ^ ((3 : ℝ) / 4)
              - C₂ * Real.sqrt (N : ℝ))
            - C * (4 * κ * (N : ℝ) ^ ((3 : ℝ) / 4) + C₂ * Real.sqrt (N : ℝ))
                * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
            - 4 / Real.pi)
      = (4 * κ / Real.pi) * (N : ℝ) ^ ((3 : ℝ) / 4) - (C₂ / Real.pi) * Real.sqrt (N : ℝ)
          - C * κ * (N : ℝ) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
          - C * (C₂ / 4) * Real.sqrt (N : ℝ)
              * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
          - 1 / Real.pi := by
    field_simp
    ring
  have h4kp : 4 * κ / Real.pi = ε + 1.11 := by rw [hεdef]; ring
  rw [hexp, h4kp]
  linarith [hab1, hab2, hab3, hab4]

end Work.FITop
