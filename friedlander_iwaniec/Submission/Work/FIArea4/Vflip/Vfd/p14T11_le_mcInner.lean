import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.McDefs
import Submission.Work.FIArea4.A4varbounds

namespace Work.FIArea4.Vflip.Vfd

/-- If `0 < m`, `0 ≤ q ≤ 1` and `0 ≤ X`, and `q = 0` forces `X = 0`, then multiplying by the
larger factor `(m q)^{-1/2} ≥ m^{-1/2}` does not decrease `X`.  (The hypothesis `q = 0 → X = 0`
is what makes the degenerate case `q = 0` harmless, where `(m·0)^{-1/2} = 0`.) -/
lemma rpow_neg_half_mul_le {m q X : ℝ} (hm : 0 < m) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hX : 0 ≤ X) (hX0 : q = 0 → X = 0) :
    m^(-(1:ℝ)/2) * X ≤ (m*q)^(-(1:ℝ)/2) * X := by
  rcases eq_or_lt_of_le hX with h | h
  · rw [← h, mul_zero, mul_zero]
  · have hqpos : 0 < q := by
      rcases eq_or_lt_of_le hq0 with hq | hq
      · subst hq; rw [hX0 rfl] at h; exact absurd h (lt_irrefl 0)
      · exact hq
    have hmq_pos : 0 < m*q := mul_pos hm hqpos
    have hmq_le : m*q ≤ m := mul_le_of_le_one_right (le_of_lt hm) hq1
    have hstep : m^(-(1:ℝ)/2) ≤ (m*q)^(-(1:ℝ)/2) :=
      Real.rpow_le_rpow_of_nonpos hmq_pos hmq_le (by norm_num)
    exact mul_le_mul_of_nonneg_right hstep (le_of_lt h)

/-- `p14T11 m (⌈R/c⌉) S (ε/4)` is dominated by the inner bracket `mcInner` of the far-part
estimate: the flipped-modulus bracket of Proposition 11.1 at the reduced box parameter
`R' = ⌈R/c⌉`, the modulus `D = m`, and the exponent `ε/4`, is at most the per-`(m,c)` bracket
`mcInner D R S m c H ε`, under the standing hypotheses
`SR/(5HcD) < 1/2` (i.e. `Qmin < 1/2`), `cD ≤ 8RS`, and `R' ≤ R`. -/
theorem p14T11_le_mcInner {D R S m c : ℕ} {H ε : ℝ}
    (hD : 1 ≤ D) (hc : 1 ≤ c) (hH : 1 ≤ H) (hε : 0 < ε)
    (hQmin : (S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ)) < 1/2)
    (hcD : (c:ℝ)*(D:ℝ) ≤ 8*(R:ℝ)*(S:ℝ))
    (hRle : (cR c R : ℝ) ≤ (R:ℝ))
    (hm : 1 ≤ m) :
    Work.FIArea4.p14T11 m (cR c R) S (ε/4) ≤ mcInner D R S m c H ε := by
  have hc1 : (1:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  have hmnn : (0:ℝ) ≤ (m:ℝ) := le_of_lt hmpos
  have hH0 : (0:ℝ) < H := by linarith
  have hc0 : (0:ℝ) < (c:ℝ) := by linarith
  have hD0 : (0:ℝ) < (D:ℝ) := by linarith
  have hden : 0 < 5*H*(c:ℝ)*(D:ℝ) := by positivity
  have hSnn : (0:ℝ) ≤ (S:ℝ) := Nat.cast_nonneg S
  have hRnn : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg R
  have hR'nn : (0:ℝ) ≤ (cR c R : ℝ) := Nat.cast_nonneg _
  have hε4 : 0 ≤ ε/4 := by linarith
  have hRSle : (cR c R:ℝ)*(S:ℝ) ≤ (R:ℝ)*(S:ℝ) :=
    mul_le_mul_of_nonneg_right hRle hSnn
  have hXnn : 0 ≤ (cR c R:ℝ)*(S:ℝ) := mul_nonneg hR'nn hSnn
  have hqnn : 0 ≤ (S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ)) :=
    div_nonneg (mul_nonneg hSnn hRnn) (le_of_lt hden)
  have hqle : (S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ)) ≤ 1 := by
    have := hQmin; linarith
  have hX0 : (S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ)) = 0 → (cR c R:ℝ)*(S:ℝ) = 0 := by
    intro hq0
    have hSR : (S:ℝ)*(R:ℝ) = 0 := by
      rcases (div_eq_zero_iff.mp hq0) with h | h
      · exact h
      · exact absurd h (ne_of_gt hden)
    have hRS0 : (R:ℝ)*(S:ℝ) = 0 := by rw [mul_comm]; exact hSR
    rw [hRS0] at hRSle
    exact le_antisymm hRSle hXnn
  have h1 : pT1 m (cR c R) S
      ≤ (m * ((S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))))^(-(1:ℝ)/2) * ((cR c R:ℝ)*(S:ℝ)) := by
    unfold pT1
    have key := rpow_neg_half_mul_le hmpos hqnn hqle hXnn hX0
    rw [show (m:ℝ)^(-(1:ℝ)/2) * (cR c R:ℝ) * (S:ℝ)
        = (m:ℝ)^(-(1:ℝ)/2) * ((cR c R:ℝ)*(S:ℝ)) by ring]
    exact key
  have h16 : (1:ℝ) ≤ 16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)) := by
    rw [le_div_iff₀ (mul_pos hc0 hD0)]
    nlinarith [hcD, hRnn, hSnn]
  have hlog0 : (0:ℝ) ≤ Real.log (160*H) := by
    have h160 : (1:ℝ) ≤ 160*H := by nlinarith [hH]
    exact Real.log_nonneg h160
  have hlog1nn : (0:ℝ) ≤ Real.log (160*H) + 1 := by linarith
  have hlog1ge : (1:ℝ) ≤ Real.log (160*H) + 1 := by linarith
  have hsnn : 0 ≤ Real.sqrt ((cR c R:ℝ)*(S:ℝ)) := Real.sqrt_nonneg _
  have hZnn : 0 ≤ (cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)) := by positivity
  have hknn : 0 ≤ 16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ)) := by positivity
  have hA1 : (m:ℝ) * Real.sqrt ((cR c R:ℝ)*(S:ℝ))
      ≤ (m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ))) * Real.sqrt ((cR c R:ℝ)*(S:ℝ)) := by
    nlinarith [hmnn, hsnn, h16, mul_nonneg hmnn hsnn,
      mul_nonneg (mul_nonneg hmnn hsnn) (sub_nonneg.mpr h16)]
  have hA2 : (cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4))
      ≤ (Real.log (160*H)+1) * ((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4))) := by
    nlinarith [hZnn, hlog1ge]
  have hAleB : (m:ℝ) * Real.sqrt ((cR c R:ℝ)*(S:ℝ)) + (cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4))
      ≤ (m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ))) * Real.sqrt ((cR c R:ℝ)*(S:ℝ))
        + (Real.log (160*H)+1) * ((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4))) := by
    linarith [hA1, hA2]
  have hxle : ((cR c R:ℝ)*(S:ℝ))^(ε/4) ≤ ((R:ℝ)*(S:ℝ))^(ε/4) :=
    Real.rpow_le_rpow hXnn hRSle hε4
  have hxnn : 0 ≤ ((cR c R:ℝ)*(S:ℝ))^(ε/4) := Real.rpow_nonneg hXnn _
  have hBnn : 0 ≤ (m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ))) * Real.sqrt ((cR c R:ℝ)*(S:ℝ))
        + (Real.log (160*H)+1) * ((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4))) := by
    apply add_nonneg
    · apply mul_nonneg
      · apply mul_nonneg hmnn
        exact div_nonneg (by positivity) (by positivity)
      · exact hsnn
    · exact mul_nonneg hlog1nn hZnn
  have h2 : pT2 m (cR c R) S (ε/4) + pT3 m (cR c R) S (ε/4) + pT4 m (cR c R) S (ε/4)
      ≤ ((R:ℝ)*(S:ℝ))^(ε/4) * ((m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ))) * Real.sqrt ((cR c R:ℝ)*(S:ℝ))
        + (Real.log (160*H)+1) * ((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)))) := by
    have hfac : pT2 m (cR c R) S (ε/4) + pT3 m (cR c R) S (ε/4) + pT4 m (cR c R) S (ε/4)
        = ((m:ℝ) * Real.sqrt ((cR c R:ℝ)*(S:ℝ)) + (cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)))
          * ((cR c R:ℝ)*(S:ℝ))^(ε/4) := by
      unfold pT2 pT3 pT4; ring
    rw [hfac]
    calc ((m:ℝ) * Real.sqrt ((cR c R:ℝ)*(S:ℝ)) + (cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4))) * ((cR c R:ℝ)*(S:ℝ))^(ε/4)
        ≤ ((m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ))) * Real.sqrt ((cR c R:ℝ)*(S:ℝ))
              + (Real.log (160*H)+1) * ((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)))) * ((cR c R:ℝ)*(S:ℝ))^(ε/4) :=
          mul_le_mul_of_nonneg_right hAleB hxnn
      _ ≤ ((m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ))) * Real.sqrt ((cR c R:ℝ)*(S:ℝ))
              + (Real.log (160*H)+1) * ((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)))) * ((R:ℝ)*(S:ℝ))^(ε/4) :=
          mul_le_mul_of_nonneg_left hxle hBnn
      _ = ((R:ℝ)*(S:ℝ))^(ε/4) * ((m:ℝ) * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ))) * Real.sqrt ((cR c R:ℝ)*(S:ℝ))
              + (Real.log (160*H)+1) * ((cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)))) := by ring
  rw [Work.FIArea4.Vflip.Vfd.p14T11_eq_sum]
  unfold mcInner
  linarith [h1, h2]

end Work.FIArea4.Vflip.Vfd
