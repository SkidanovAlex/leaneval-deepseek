import Mathlib
import Submission.Work.Cert.WLDefs

namespace Work.ANum3.Z2

open Complex

/-- Real part of `cx cr ci * z` in terms of the mantissas: `cx cr ci = (cr + ci·I)/S`. -/
lemma halfplane_cx_mul_re (cr ci : ℤ) (z : ℂ) :
    (Work.Cert.cx cr ci * z).re = ((cr : ℝ) / (Work.Cert.S : ℝ)) * z.re
      - ((ci : ℝ) / (Work.Cert.S : ℝ)) * z.im := by
  rw [Complex.mul_re]
  simp [Work.Cert.cx]

/-- A point `w` within distance `ρ/S` of the centre `cx cr ci` (mantissas, scale `S`) has positive
`Re (w · conj (I^lab))`, provided the centre's own value exceeds `ρ/S` (i.e. `ρ < labRe lab cr ci`)
and `lab < 4`.  This is the geometric step turning the integer half-plane test `windLeafOK` into a
statement about the complex plane. -/
theorem halfplane {w : ℂ} {lab : ℕ} {cr ci ρ : ℤ} (hlab : lab < 4)
    (hρ : ρ < Work.Cert.labRe lab cr ci)
    (hw : ‖w - Work.Cert.cx cr ci‖ ≤ (ρ : ℝ) / (Work.Cert.S : ℝ)) :
    0 < (w * star ((Complex.I : ℂ) ^ lab)).re := by
  have hS : (0 : ℝ) < (Work.Cert.S : ℝ) := by norm_num [Work.Cert.S]
  set u : ℂ := star ((Complex.I : ℂ) ^ lab) with hu
  have hnu : ‖u‖ = 1 := by
    rw [hu, norm_star, norm_pow, Complex.norm_I, one_pow]
  -- the centre's own value: `Re (cx cr ci · ū) = labRe lab cr ci / S`
  have hrec : (Work.Cert.cx cr ci * u).re
      = ((Work.Cert.labRe lab cr ci : ℤ) : ℝ) / (Work.Cert.S : ℝ) := by
    rw [hu, halfplane_cx_mul_re]
    interval_cases lab
    · simp [Work.Cert.labRe]
    · simp [Work.Cert.labRe, Complex.conj_I]
    · simp [Work.Cert.labRe, pow_succ, Complex.I_mul_I]
      ring
    · simp [Work.Cert.labRe, Complex.conj_I, pow_succ, Complex.I_mul_I]
      ring
  -- the deviation is controlled by the disc radius
  have hb : |(w * u).re - (Work.Cert.cx cr ci * u).re| ≤ (ρ : ℝ) / (Work.Cert.S : ℝ) := by
    have heq : (w * u).re - (Work.Cert.cx cr ci * u).re = ((w - Work.Cert.cx cr ci) * u).re := by
      rw [sub_mul, Complex.sub_re]
    rw [heq]
    calc |((w - Work.Cert.cx cr ci) * u).re| ≤ ‖(w - Work.Cert.cx cr ci) * u‖ :=
          Complex.abs_re_le_norm _
      _ = ‖w - Work.Cert.cx cr ci‖ * ‖u‖ := norm_mul _ _
      _ = ‖w - Work.Cert.cx cr ci‖ := by rw [hnu, mul_one]
      _ ≤ (ρ : ℝ) / (Work.Cert.S : ℝ) := hw
  have hge : (w * u).re ≥ ((Work.Cert.labRe lab cr ci : ℤ) : ℝ) / (Work.Cert.S : ℝ)
      - (ρ : ℝ) / (Work.Cert.S : ℝ) := by
    have h1 := (abs_le.mp hb).1
    linarith
  have hpos : (0 : ℝ)
      < (((Work.Cert.labRe lab cr ci : ℤ) : ℝ) - (ρ : ℝ)) / (Work.Cert.S : ℝ) := by
    have hlt : (ρ : ℝ) < ((Work.Cert.labRe lab cr ci : ℤ) : ℝ) := by exact_mod_cast hρ
    exact div_pos (by linarith) hS
  have heq2 : (((Work.Cert.labRe lab cr ci : ℤ) : ℝ) - (ρ : ℝ)) / (Work.Cert.S : ℝ)
      = ((Work.Cert.labRe lab cr ci : ℤ) : ℝ) / (Work.Cert.S : ℝ)
        - (ρ : ℝ) / (Work.Cert.S : ℝ) := by
    ring
  linarith

end Work.ANum3.Z2
