import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.num_13
import Submission.Work.BW.num_T
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.acH_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

set_option maxHeartbeats 4000000

/-- Pure real arithmetic: the exponent budget `0.1hT + (log 1.7)T + Θe` of the rational-factor
bound (with `Θe = ((log(57rd)+3/(57rd))h + z/(57rd))(D₀+1)`, `z ≥ 0`) fits into
`0.203·S·D/d + 0.007·z·D/d`, where `S = pS r d h = 16rdh`, `D = pD r d σ`,
`T = pT r d σ = ⌊11.75 rD⌋ ≤ 11.75 rD`, `D₀ = pD0 r d σ = ⌊rD/(2log(2rd))⌋`.
The slack is `0.095·S·D/d - 1.175 r h D ≥ 0.345 r h D` against `(log 1.7)T ≤ 0.532·11.75 rD`
(needs `h ≥ 19`) and `D₀ + 1 ≤ 0.399 rD`; `num_13`'s third component with `x = z` supplies
`((log(57rd)+2/(57rd))h + z/(57rd))(D₀+1) ≤ (0.108·S + 0.007z)D/d`, and the extra
`h(D₀+1)/(57rd) ≤ 0.007hD/d` (from `D₀+1 ≤ 0.399 rD`) is covered by the slack. -/
theorem est17_arch_num {r : ℕ} (hr : 2 ≤ r) (d h : ℕ) (hd : 1 ≤ d) (hh : 19 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (z : ℝ) (hz : 0 ≤ z) :
    0.1 * (h : ℝ) * (pT r d σ : ℝ) + Real.log 1.7 * (pT r d σ : ℝ)
      + ((Real.log (57 * (r : ℝ) * (d : ℝ)) + 3 / (57 * (r : ℝ) * (d : ℝ))) * (h : ℝ)
          + z / (57 * (r : ℝ) * (d : ℝ))) * ((pD0 r d σ : ℝ) + 1)
    ≤ 0.203 * (pS r d h : ℝ) * pD r d σ / (d : ℝ) + 0.007 * z * pD r d σ / (d : ℝ) := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hh19 : (19:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hd0 : (0:ℝ) < (d:ℝ) := by linarith
  have hDpos : 0 < pD r d σ := pD_pos hr hd σ hσ
  have hTle : (pT r d σ : ℝ) ≤ 11.75 * (r:ℝ) * pD r d σ := by
    have h0 : (0:ℝ) ≤ (11.75:ℝ) * (r:ℝ) * pD r d σ := by positivity
    simpa only [pT] using Nat.floor_le h0
  have hT0 : (0:ℝ) ≤ (pT r d σ : ℝ) := Nat.cast_nonneg _
  have hS : (pS r d h : ℝ) = 16 * (r:ℝ) * (d:ℝ) * (h:ℝ) := by
    simp only [pS]; push_cast; ring
  have hxpart : (pD0 r d σ : ℝ) + 1 ≤ 0.399 * ((r:ℝ) * pD r d σ) := num13_xpart hr hd σ hσ
  have h13 : ((Real.log (57 * (r:ℝ) * (d:ℝ)) + 2 / (57 * (r:ℝ) * (d:ℝ))) * (h:ℝ)
      + z / (57 * (r:ℝ) * (d:ℝ))) * ((pD0 r d σ : ℝ) + 1)
      ≤ (0.108 * (pS r d h : ℝ) + 0.007 * z) * pD r d σ / (d:ℝ) := by
    have hpart := num13_hpart hr hd σ hσ
    have xpart := num13_xpart hr hd σ hσ
    have hh0 : (0:ℝ) ≤ (h:ℝ) := by positivity
    have h1 : (Real.log (57 * (r:ℝ) * (d:ℝ)) + 2 / (57 * (r:ℝ) * (d:ℝ))) * (h:ℝ)
          * ((pD0 r d σ : ℝ) + 1)
        ≤ 1.728 * (r:ℝ) * pD r d σ * (h:ℝ) := by
      have h := mul_le_mul_of_nonneg_right hpart hh0
      linarith [h]
    have h2 : z / (57 * (r:ℝ) * (d:ℝ)) * ((pD0 r d σ : ℝ) + 1)
        ≤ 0.007 * z * pD r d σ / (d:ℝ) := by
      have hstep : z / (57 * (r:ℝ) * (d:ℝ)) * ((pD0 r d σ : ℝ) + 1)
          ≤ z / (57 * (r:ℝ) * (d:ℝ)) * (0.399 * ((r:ℝ) * pD r d σ)) :=
        mul_le_mul_of_nonneg_left xpart (by positivity)
      have hxe : z / (57 * (r:ℝ) * (d:ℝ)) * (0.399 * ((r:ℝ) * pD r d σ))
          = 0.007 * z * pD r d σ / (d:ℝ) := by
        field_simp
        ring
      rw [hxe] at hstep
      exact hstep
    rw [add_mul]
    have hS3 : (0.108:ℝ) * (pS r d h : ℝ) * pD r d σ / (d:ℝ)
        = 1.728 * (r:ℝ) * pD r d σ * (h:ℝ) := by
      rw [hS]; field_simp; ring
    have hRHS : (0.108 * (pS r d h : ℝ) + 0.007 * z) * pD r d σ / (d:ℝ)
        = 0.108 * (pS r d h : ℝ) * pD r d σ / (d:ℝ) + 0.007 * z * pD r d σ / (d:ℝ) := by
      ring
    rw [hRHS, hS3]
    linarith [h1, h2]
  have hTheta : ((Real.log (57 * (r:ℝ) * (d:ℝ)) + 3 / (57 * (r:ℝ) * (d:ℝ))) * (h:ℝ)
      + z / (57 * (r:ℝ) * (d:ℝ))) * ((pD0 r d σ : ℝ) + 1)
      ≤ (0.108 * (pS r d h : ℝ) + 0.007 * z) * pD r d σ / (d:ℝ)
          + 0.007 * (h:ℝ) * pD r d σ / (d:ℝ) := by
    have hsplit : ((Real.log (57 * (r:ℝ) * (d:ℝ)) + 3 / (57 * (r:ℝ) * (d:ℝ))) * (h:ℝ)
        + z / (57 * (r:ℝ) * (d:ℝ)))
        = ((Real.log (57 * (r:ℝ) * (d:ℝ)) + 2 / (57 * (r:ℝ) * (d:ℝ))) * (h:ℝ)
            + z / (57 * (r:ℝ) * (d:ℝ))) + (h:ℝ) / (57 * (r:ℝ) * (d:ℝ)) := by
      field_simp
      ring
    rw [hsplit, add_mul]
    have hextra : (h:ℝ) / (57 * (r:ℝ) * (d:ℝ)) * ((pD0 r d σ : ℝ) + 1)
        ≤ 0.007 * (h:ℝ) * pD r d σ / (d:ℝ) := by
      have hnn : (0:ℝ) ≤ (h:ℝ) / (57 * (r:ℝ) * (d:ℝ)) := by positivity
      have hstep := mul_le_mul_of_nonneg_left hxpart hnn
      have heq : (h:ℝ) / (57 * (r:ℝ) * (d:ℝ)) * (0.399 * ((r:ℝ) * pD r d σ))
          = 0.007 * (h:ℝ) * pD r d σ / (d:ℝ) := by
        field_simp
        ring
      linarith [hstep, heq]
    linarith [h13, hextra]
  have hA : 0.1 * (h:ℝ) * (pT r d σ : ℝ) ≤ 1.175 * ((r:ℝ) * (h:ℝ) * pD r d σ) := by
    nlinarith [mul_le_mul_of_nonneg_left hTle (show (0:ℝ) ≤ 0.1 * (h:ℝ) by positivity)]
  have hB : Real.log 1.7 * (pT r d σ : ℝ) ≤ 6.251 * ((r:ℝ) * pD r d σ) := by
    have h1 : Real.log 1.7 * (pT r d σ : ℝ) ≤ 0.532 * (11.75 * (r:ℝ) * pD r d σ) :=
      mul_le_mul (le_of_lt num13_log_17_lt) hTle hT0 (by norm_num)
    nlinarith [h1]
  have hC : 1.175 * ((r:ℝ) * (h:ℝ) * pD r d σ) + 6.251 * ((r:ℝ) * pD r d σ)
        + 0.007 * (h:ℝ) * pD r d σ / (d:ℝ) ≤ 0.095 * (pS r d h : ℝ) * pD r d σ / (d:ℝ) := by
    rw [hS]
    have hkey : 6.251 * (r:ℝ) * (d:ℝ) + 0.007 * (h:ℝ) ≤ 0.345 * (r:ℝ) * (h:ℝ) * (d:ℝ) := by
      have hrd : (2:ℝ) ≤ (r:ℝ) * (d:ℝ) := by nlinarith [hr2, hd1]
      have hlin : (0:ℝ) ≤ 0.345 * (h:ℝ) - 6.251 := by nlinarith [hh19]
      have hstep : 0.007 * (h:ℝ) ≤ 2 * (0.345 * (h:ℝ) - 6.251) := by nlinarith [hh19]
      nlinarith [hrd, hlin, hstep]
    have heq : (0.095:ℝ) * (16 * (r:ℝ) * (d:ℝ) * (h:ℝ)) * pD r d σ / (d:ℝ)
        = 1.52 * ((r:ℝ) * (h:ℝ) * pD r d σ) := by
      field_simp
      ring
    rw [heq]
    have hstep : 6.251 * ((r:ℝ) * pD r d σ) + 0.007 * (h:ℝ) * pD r d σ / (d:ℝ)
        ≤ 0.345 * ((r:ℝ) * (h:ℝ) * pD r d σ) := by
      apply le_of_mul_le_mul_right _ hd0
      rw [show (6.251 * ((r:ℝ) * pD r d σ) + 0.007 * (h:ℝ) * pD r d σ / (d:ℝ)) * (d:ℝ)
            = 6.251 * ((r:ℝ) * pD r d σ) * (d:ℝ) + 0.007 * (h:ℝ) * pD r d σ by
        field_simp]
      nlinarith [hkey, hDpos]
    linarith [hstep]
  have hA' : 0.1 * (h:ℝ) * (pT r d σ : ℝ) + Real.log 1.7 * (pT r d σ : ℝ)
      + ((Real.log (57 * (r:ℝ) * (d:ℝ)) + 3 / (57 * (r:ℝ) * (d:ℝ))) * (h:ℝ)
          + z / (57 * (r:ℝ) * (d:ℝ))) * ((pD0 r d σ : ℝ) + 1)
      ≤ 1.175 * ((r:ℝ) * (h:ℝ) * pD r d σ) + 6.251 * ((r:ℝ) * pD r d σ)
        + ((0.108 * (pS r d h : ℝ) + 0.007 * z) * pD r d σ / (d:ℝ)
            + 0.007 * (h:ℝ) * pD r d σ / (d:ℝ)) := by
    linarith [hA, hB, hTheta]
  have hcomb : 1.175 * ((r:ℝ) * (h:ℝ) * pD r d σ) + 6.251 * ((r:ℝ) * pD r d σ)
        + ((0.108 * (pS r d h : ℝ) + 0.007 * z) * pD r d σ / (d:ℝ)
            + 0.007 * (h:ℝ) * pD r d σ / (d:ℝ))
      = (1.175 * ((r:ℝ) * (h:ℝ) * pD r d σ) + 6.251 * ((r:ℝ) * pD r d σ)
            + 0.007 * (h:ℝ) * pD r d σ / (d:ℝ))
        + (0.108 * (pS r d h : ℝ) * pD r d σ / (d:ℝ) + 0.007 * z * pD r d σ / (d:ℝ)) := by
    ring
  have hR : 0.203 * (pS r d h : ℝ) * pD r d σ / (d:ℝ) + 0.007 * z * pD r d σ / (d:ℝ)
      = 0.095 * (pS r d h : ℝ) * pD r d σ / (d:ℝ)
        + (0.108 * (pS r d h : ℝ) * pD r d σ / (d:ℝ) + 0.007 * z * pD r d σ / (d:ℝ)) := by
    ring
  linarith [hA', hcomb, hC, hR]

end Work.BW

