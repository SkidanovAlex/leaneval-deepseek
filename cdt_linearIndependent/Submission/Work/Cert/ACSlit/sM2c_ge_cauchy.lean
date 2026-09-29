import Mathlib
import Submission.Work.Cert.ACSlit.Shadow

namespace Work.Cert.ACSlit

/-- The integer-rounding core of `slitStage_M2c_sound`: with `sd > 0` and `sdsq = ⌊sd²/S⌋ > 0`,
the Cauchy quotient `2S²/sd²` is dominated by `sM2c/S = ⌈2S²/sdsq⌉/S`.
Route: `ACBall.md_le` gives `sdsq·S ≤ sd²`; `ACBall.dvu_ge` gives `2S²/sdsq ≤ sM2c`; and
`sM2c = dvu (2*S) sdsq` because both `decide` guards of its `if` are true. -/
theorem sM2c_ge_cauchy (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW)
    (hd : 0 < Work.Cert.ACSlit.sd A B2 E C1 G8 A2 ror roi st w)
    (hdsq : 0 < Work.Cert.ACSlit.sdsq A B2 E C1 G8 A2 ror roi st w) :
    2 * (Work.Cert.S : ℝ) ^ 2 / ((Work.Cert.ACSlit.sd A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) ^ 2
      ≤ ((Work.Cert.ACSlit.sM2c A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (Work.Cert.S : ℝ) := by
  -- both `decide` guards of the `if` defining `sM2c` hold
  have hM : sM2c A B2 E C1 G8 A2 ror roi st w
      = dvu (2 * S) (sdsq A B2 E C1 G8 A2 ror roi st w) := by
    unfold sM2c
    rw [if_pos]
    simp [hd, hdsq]
  rw [hM]
  have hs : (0 : ℝ) < (S : ℝ) := Work.Cert.ACBall.S_posR
  have hq : (0 : ℝ) < ((sdsq A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) := by
    exact_mod_cast hdsq
  have hdR : (0 : ℝ) < ((sd A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) := by
    exact_mod_cast hd
  -- `dvu_ge`: `2S·S/sdsq ≤ dvu (2S) sdsq`
  have hD : 2 * (S : ℝ) * (S : ℝ) / ((sdsq A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ)
      ≤ ((dvu (2 * S) (sdsq A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ) := by
    have h := Work.Cert.ACBall.dvu_ge (a := 2 * S) (b := sdsq A B2 E C1 G8 A2 ror roi st w) hdsq
    push_cast at h
    exact h
  -- `md_le`: `sdsq ≤ sd·sd/S`
  have hQle : ((sdsq A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ)
      ≤ ((sd A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ)
        * ((sd A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (S : ℝ) := by
    have h := Work.Cert.ACBall.md_le (sd A B2 E C1 G8 A2 ror roi st w)
      (sd A B2 E C1 G8 A2 ror roi st w)
    simpa [sdsq] using h
  have hDsnn : 0 ≤ ((dvu (2 * S) (sdsq A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ) :=
    le_trans (div_nonneg (by positivity) hq.le) hD
  have hD' : 2 * (S : ℝ) * (S : ℝ)
      ≤ ((dvu (2 * S) (sdsq A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ)
        * ((sdsq A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) :=
    (div_le_iff₀ hq).mp hD
  have hQle' : ((sdsq A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) * (S : ℝ)
      ≤ ((sd A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ)
        * ((sd A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) :=
    (le_div_iff₀ hs).mp hQle
  have hsd2 : (0 : ℝ) < ((sd A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) ^ 2 := by positivity
  rw [div_le_div_iff₀ hsd2 hs]
  nlinarith [mul_le_mul_of_nonneg_right hD' hs.le, mul_le_mul_of_nonneg_left hQle' hDsnn, hs, hq, hdR]

end Work.Cert.ACSlit
