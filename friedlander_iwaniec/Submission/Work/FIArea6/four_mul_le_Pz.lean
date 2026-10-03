import Mathlib
import Submission.Work.FIArea6.S16UDefs

namespace Work.FIArea6

noncomputable section

/-- The fixed exponent `ν = nuU = 3·sigmaChoice Asave + 4` of §16 is positive. -/
lemma nuU_pos : (0 : ℝ) < Work.FITop4.nuU := by
  unfold Work.FITop4.nuU Work.FITop4.sigmaChoice Work.FITop4.Aprime Work.FITop4.Asave
  norm_num

/-- The numerical core of the `Pz`-threshold: if `t ≥ nuU + 2 + log 4` then
`log 4 + nuU·t ≤ t²` (with `nuU ≥ 0`). -/
lemma log4_add_nuU_mul_le_sq (t : ℝ) (ht : Work.FITop4.nuU + 2 + Real.log 4 ≤ t) :
    Real.log 4 + Work.FITop4.nuU * t ≤ t ^ 2 := by
  have hnu : (0 : ℝ) ≤ Work.FITop4.nuU := le_of_lt nuU_pos
  have hL0 : (0 : ℝ) ≤ Real.log 4 := (Real.log_pos (by norm_num)).le
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have h1 : Real.log 4 ≤ t := by linarith
  have h2 : 1 + Work.FITop4.nuU ≤ t := by linarith
  calc Real.log 4 + Work.FITop4.nuU * t ≤ t + Work.FITop4.nuU * t := by linarith
    _ = t * (1 + Work.FITop4.nuU) := by ring
    _ ≤ t * t := mul_le_mul_of_nonneg_left h2 ht0
    _ = t ^ 2 := by ring

/-- The `Pz`-threshold of the §16 display: for `x ≥ exp(4·exp(nuU+2))` and `X ≤ (log N)^{nuU}` one has `4X ≤ Pz`, because `loglog N ≥ nuU + 2` and (4.4) `log Pz ≥ (loglog x)²` give `log(4X) ≤ log 4 + nuU·loglog N ≤ (loglog x)² ≤ log Pz`. -/
theorem four_mul_le_Pz (Pa : Work.FITop.Params) (X : ℕ)
    (hx : Real.exp (4 * Real.exp (Work.FITop4.nuU + 2)) ≤ (Pa.x : ℝ))
    (hX : (X : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU) :
    4 * X ≤ Pa.Pz := by
  rcases Nat.eq_zero_or_pos X with hX0 | hXpos
  · subst hX0; exact Nat.zero_le _
  suffices hmain : 4 * (X : ℝ) ≤ (Pa.Pz : ℝ) by exact_mod_cast hmain
  have hnu : (0 : ℝ) < Work.FITop4.nuU := nuU_pos
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hx1 : (1 : ℝ) < (Pa.x : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  -- step 1: `log x ≥ 4·exp(nuU+2) ≥ 4 ≥ 1`
  have hexp1 : (1 : ℝ) ≤ Real.exp (Work.FITop4.nuU + 2) := Real.one_le_exp (by linarith)
  have hlogx : 4 * Real.exp (Work.FITop4.nuU + 2) ≤ Real.log (Pa.x : ℝ) := by
    rw [← Real.log_exp (4 * Real.exp (Work.FITop4.nuU + 2))]
    exact Real.log_le_log (Real.exp_pos _) hx
  have hlogx4 : (4 : ℝ) ≤ Real.log (Pa.x : ℝ) := by nlinarith
  have hlogx1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by linarith
  -- step 2: `t = loglog x ≥ nuU + 2 + log 4`
  have ht : Work.FITop4.nuU + 2 + Real.log 4 ≤ Real.log (Real.log (Pa.x : ℝ)) := by
    have hpos : (0 : ℝ) < 4 * Real.exp (Work.FITop4.nuU + 2) := by positivity
    have h := Real.log_le_log hpos hlogx
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at h
    linarith
  -- step 3: `1 < N` and `log N ≤ log x`
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := Pa.hN1
  have hNpos : (0 : ℝ) < (Pa.N : ℝ) := by linarith
  have hNgt1 : (1 : ℝ) < (Pa.N : ℝ) := by
    have hη : (0 : ℝ) < (1 : ℝ) / 4 + Pa.η := by linarith [Pa.hη]
    have hlt : (1 : ℝ) < (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) := Real.one_lt_rpow hx1 hη
    linarith [Pa.hNlo]
  have hlogNpos : (0 : ℝ) < Real.log (Pa.N : ℝ) := Real.log_pos hNgt1
  have hNltx : (Pa.N : ℝ) < (Pa.x : ℝ) := by
    have hrpow : (Real.log (Pa.x : ℝ)) ^ (-Pa.B) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hlogx1 (by linarith [Pa.hB])
    have hstep : (Pa.x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (Pa.x : ℝ)) ^ (-Pa.B)
        ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 2) * 1 :=
      mul_le_mul_of_nonneg_left hrpow (Real.rpow_nonneg (le_of_lt hxpos) _)
    have hxhalf : (Pa.x : ℝ) ^ ((1 : ℝ) / 2) ≤ (Pa.x : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) (by norm_num : (1 : ℝ) / 2 ≤ 1)
      rwa [Real.rpow_one] at h
    linarith [Pa.hNhi, hstep, hxhalf]
  have hlogNle : Real.log (Pa.N : ℝ) ≤ Real.log (Pa.x : ℝ) :=
    Real.log_le_log hNpos (le_of_lt hNltx)
  -- step 4: `log X ≤ nuU·loglog x`
  have hXposR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXpos
  have hXle : Real.log (X : ℝ) ≤ Work.FITop4.nuU * Real.log (Real.log (Pa.x : ℝ)) := by
    calc Real.log (X : ℝ) ≤ Real.log ((Real.log (Pa.N : ℝ)) ^ Work.FITop4.nuU) :=
          Real.log_le_log hXposR hX
      _ = Work.FITop4.nuU * Real.log (Real.log (Pa.N : ℝ)) := Real.log_rpow hlogNpos _
      _ ≤ Work.FITop4.nuU * Real.log (Real.log (Pa.x : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.log_le_log hlogNpos hlogNle) (le_of_lt hnu)
  -- step 5: take logarithms
  have hlog4X : Real.log (4 * (X : ℝ)) ≤ Real.log (Pa.Pz : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hXposR)]
    calc Real.log 4 + Real.log (X : ℝ)
        ≤ Real.log 4 + Work.FITop4.nuU * Real.log (Real.log (Pa.x : ℝ)) := by linarith
      _ ≤ (Real.log (Real.log (Pa.x : ℝ))) ^ 2 := log4_add_nuU_mul_le_sq _ ht
      _ ≤ Real.log (Pa.Pz : ℝ) := Pa.hPlo
  have hPzpos : (0 : ℝ) < (Pa.Pz : ℝ) := by
    have h : (0 : ℕ) < Pa.Pz := lt_of_lt_of_le (by norm_num) Pa.hP2
    exact_mod_cast h
  exact (Real.log_le_log_iff (by linarith : (0 : ℝ) < 4 * (X : ℝ)) hPzpos).mp hlog4X

end

end Work.FIArea6
