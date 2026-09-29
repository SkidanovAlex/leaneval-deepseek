import Mathlib
import Submission.Work.Fx.ExpDefs

/-!
# One-stage fixed-point error for the complex exponential recurrence

`Work.Fx.expStepErr` bounds the error of one fixed-point Horner stage
`Q ← 1 + (z/dd)·Q` of the complex exponential: the two truncated divisions
(`Int.tdiv`) in `stepQre`/`stepQim` each introduce an error of modulus at most
`1`, so the total error is at most `2` in each of the real and imaginary parts,
hence `≤ 4/2^P` in the complex norm.

Real-valued ingredient: `Int.tdiv` truncation error.  For `0 < b`,

  `|((a.tdiv b : ℤ) : ℝ) - a/b| ≤ 1`,

iterated twice for the composite `tdiv (tdiv a p) d` with `0 < p`, `0 < d`.
-/

namespace Work.Fx

/-- Truncated-division error: `|a.tdiv b - a/b| ≤ 1` for `0 < b`. -/
lemma tdiv_abs_le_one (a b : ℤ) (hb : 0 < b) :
    |((a.tdiv b : ℤ) : ℝ) - (a : ℝ) / (b : ℝ)| ≤ 1 := by
  have hbR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hb0 : (b:ℝ) ≠ 0 := ne_of_gt hbR
  have hcast : ((a.tmod b : ℤ) : ℝ) + (b:ℝ) * ((a.tdiv b : ℤ):ℝ) = (a:ℝ) := by
    rw [← Int.cast_mul, ← Int.cast_add, Int.tmod_add_mul_tdiv]
  have hkey : ((a.tdiv b : ℤ) : ℝ) - (a:ℝ)/(b:ℝ) = -(((a.tmod b : ℤ):ℝ))/(b:ℝ) := by
    field_simp
    linarith
  have hbnd : |((a.tmod b : ℤ) : ℝ)| ≤ (b:ℝ) := by
    rw [abs_le]
    constructor
    · exact_mod_cast le_of_lt (Int.lt_tmod_of_pos a hb)
    · exact_mod_cast le_of_lt (Int.tmod_lt_of_pos a hb)
  rw [hkey]
  rw [abs_div, abs_neg, abs_of_pos hbR]
  rw [div_le_one hbR]
  exact hbnd

/-- Two-stage truncated-division error: `|tdiv (tdiv a p) d - a/(p·d)| ≤ 2`
for `0 < p`, `0 < d`. -/
lemma tdiv_tdiv_abs_le_two (a p d : ℤ) (hp : 0 < p) (hd : 0 < d) :
    |((Int.tdiv (Int.tdiv a p) d : ℤ) : ℝ) - (a:ℝ)/((p:ℝ)*(d:ℝ))| ≤ 2 := by
  have h1 : |(((a.tdiv p).tdiv d : ℤ):ℝ) - ((a.tdiv p : ℤ):ℝ)/(d:ℝ)| ≤ 1 :=
    tdiv_abs_le_one (a.tdiv p) d hd
  have h2 : |((a.tdiv p : ℤ):ℝ) - (a:ℝ)/(p:ℝ)| ≤ 1 := tdiv_abs_le_one a p hp
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hbnd : |(((a.tdiv p : ℤ):ℝ) - (a:ℝ)/(p:ℝ))/(d:ℝ)| ≤ 1 := by
    rw [abs_div, abs_of_pos hdR]
    rw [div_le_one hdR]
    have : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ d by omega)
    linarith
  have hkey : ((Int.tdiv (Int.tdiv a p) d : ℤ):ℝ) - (a:ℝ)/((p:ℝ)*(d:ℝ))
      = ((((a.tdiv p).tdiv d : ℤ):ℝ) - ((a.tdiv p : ℤ):ℝ)/(d:ℝ))
        + ((((a.tdiv p : ℤ):ℝ) - (a:ℝ)/(p:ℝ))/(d:ℝ)) := by
    field_simp
    ring
  calc |((Int.tdiv (Int.tdiv a p) d : ℤ):ℝ) - (a:ℝ)/((p:ℝ)*(d:ℝ))|
      = |(((a.tdiv p).tdiv d : ℤ):ℝ) - ((a.tdiv p : ℤ):ℝ)/(d:ℝ)
          + (((a.tdiv p : ℤ):ℝ) - (a:ℝ)/(p:ℝ))/(d:ℝ)| := by rw [hkey]
    _ ≤ |(((a.tdiv p).tdiv d : ℤ):ℝ) - ((a.tdiv p : ℤ):ℝ)/(d:ℝ)|
          + |(((a.tdiv p : ℤ):ℝ) - (a:ℝ)/(p:ℝ))/(d:ℝ)| := abs_add_le _ _
    _ ≤ 1 + 1 := add_le_add h1 hbnd
    _ = 2 := by norm_num

theorem expStepErr (P : ℕ) (Zs Zt Pow Qre Qim dd : ℤ) (hPow : Pow = (2 : ℤ) ^ P) (hdd : 1 ≤ dd) :
    ‖(((stepQre Zs Zt Pow Qre Qim dd : ℤ) : ℂ) +
        ((stepQim Zs Zt Pow Qre Qim dd : ℤ) : ℂ) * Complex.I) / 2 ^ P
      - (1 + (((Zs : ℂ) + (Zt : ℂ) * Complex.I) / 2 ^ P) / (dd : ℂ)
          * (((Qre : ℂ) + (Qim : ℂ) * Complex.I) / 2 ^ P))‖ ≤ 4 / (2 : ℝ) ^ P := by
  have hPowC : ((Pow : ℤ) : ℂ) = (2 : ℂ) ^ P := by rw [hPow]; push_cast; ring
  rw [← hPowC]
  have hPC : ((Pow:ℤ):ℂ) ≠ 0 := by rw [hPowC]; exact pow_ne_zero _ (by norm_num)
  have hddC : ((dd:ℤ):ℂ) ≠ 0 := by
    have h : (dd:ℤ) ≠ 0 := by omega
    exact_mod_cast h
  have hPowpos : (0:ℤ) < Pow := by rw [hPow]; positivity
  have hddpos : (0:ℤ) < dd := by omega
  have hPWnorm : ‖((Pow:ℤ):ℂ)‖ = (2:ℝ)^P := by
    rw [Complex.norm_intCast, hPow]
    push_cast
    rw [abs_of_nonneg (by positivity)]
  -- the stage error as a complex number with explicit real/imaginary parts
  let ere : ℝ := (((Int.tdiv (Int.tdiv (Zs*Qre - Zt*Qim) Pow) dd : ℤ)) : ℝ)
      - ((Zs*Qre - Zt*Qim : ℤ) : ℝ)/((Pow:ℝ)*(dd:ℝ))
  let eim : ℝ := (((Int.tdiv (Int.tdiv (Zs*Qim + Zt*Qre) Pow) dd : ℤ)) : ℝ)
      - ((Zs*Qim + Zt*Qre : ℤ) : ℝ)/((Pow:ℝ)*(dd:ℝ))
  let E : ℂ := (ere:ℂ) + (eim:ℂ) * Complex.I
  have hEre : E.re = ere := by simp [E]
  have hEim : E.im = eim := by simp [E]
  have hEeq : E = (((Int.tdiv (Int.tdiv (Zs*Qre - Zt*Qim) Pow) dd : ℤ) : ℂ)
        - (((Zs*Qre - Zt*Qim : ℤ):ℂ))/(((Pow:ℤ):ℂ)*((dd:ℤ):ℂ))
      + ((((Int.tdiv (Int.tdiv (Zs*Qim + Zt*Qre) Pow) dd : ℤ) : ℂ)
        - (((Zs*Qim + Zt*Qre : ℤ):ℂ))/(((Pow:ℤ):ℂ)*((dd:ℤ):ℂ)))*Complex.I)) := by
    simp only [E, ere, eim]
    push_cast
    ring
  -- algebraic identity: the difference of fixed-point stage and exact stage is `E/2^P`
  have hIdent : (((stepQre Zs Zt Pow Qre Qim dd : ℤ) : ℂ) +
        ((stepQim Zs Zt Pow Qre Qim dd : ℤ) : ℂ) * Complex.I)/((Pow:ℤ):ℂ)
      - (1 + ((((Zs:ℂ)+(Zt:ℂ)*Complex.I)/((Pow:ℤ):ℂ))/(dd:ℂ))
          * (((Qre:ℂ)+(Qim:ℂ)*Complex.I)/((Pow:ℤ):ℂ)))
      = E / ((Pow:ℤ):ℂ) := by
    rw [hEeq]
    have huv0 : (((Zs:ℂ)+(Zt:ℂ)*Complex.I) * ((Qre:ℂ)+(Qim:ℂ)*Complex.I))
        = (((Zs*Qre - Zt*Qim:ℤ):ℂ) + ((Zs*Qim + Zt*Qre:ℤ):ℂ)*Complex.I) := by
      apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.I_re, Complex.I_im, Int.cast_sub, Int.cast_add, Int.cast_mul]
    set u : ℂ := (Zs:ℂ) + (Zt:ℂ)*Complex.I with hu
    set v : ℂ := (Qre:ℂ) + (Qim:ℂ)*Complex.I with hv
    have huv : u * v = (((Zs*Qre - Zt*Qim:ℤ):ℂ) + ((Zs*Qim + Zt*Qre:ℤ):ℂ)*Complex.I) := by
      rw [hu, hv]; exact huv0
    simp only [stepQre, stepQim, Int.cast_add]
    rw [show (u/((Pow:ℤ):ℂ))/(dd:ℂ)*(v/((Pow:ℤ):ℂ))
            = u*v/(((Pow:ℤ):ℂ)*((dd:ℤ):ℂ)*((Pow:ℤ):ℂ)) by field_simp]
    rw [huv]
    field_simp
    simp only [Int.cast_add, Int.cast_mul]
    ring
  rw [hIdent]
  rw [Complex.norm_div, hPWnorm]
  have hEbound : ‖E‖ ≤ 4 := by
    have e1 : |E.re| ≤ 2 := by
      rw [hEre]
      simp only [ere]
      exact tdiv_tdiv_abs_le_two (Zs*Qre - Zt*Qim) Pow dd hPowpos hddpos
    have e2 : |E.im| ≤ 2 := by
      rw [hEim]
      simp only [eim]
      exact tdiv_tdiv_abs_le_two (Zs*Qim + Zt*Qre) Pow dd hPowpos hddpos
    calc ‖E‖ ≤ |E.re| + |E.im| := Complex.norm_le_abs_re_add_abs_im E
      _ ≤ 2 + 2 := add_le_add e1 e2
      _ = 4 := by norm_num
  exact div_le_div_of_nonneg_right hEbound (by positivity)

end Work.Fx
