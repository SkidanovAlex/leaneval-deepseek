/-
# OffAxis/Tf72One/Core

Infrastructure for the numerical verification of Heath-Brown (10.8)/(10.9) at `λ = 1`.

The Lemma 7.2 Laplace transform at `λ = 1` is `G72` (`tf72Fc_one_eq_G72`), and the quantity of
interest for (10.8) is `Isub s σ = Re G72(-s+iσ) - 2 Re G72(iσ)`.

`cornerB` is the certified upper bound for `Isub s σ` obtained from the closed form
`Isub_eq_closed` together with rational enclosures of `cos (2σ)`, `sin (2σ)` and `exp (2s)`;
`Isub_le_box` glues four corner bounds into a bound valid on a whole box, using the two
interpolation lemmas `Isub_le_interp_s`, `Isub_le_interp_t`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.OffAxis.G72Base

noncomputable section
namespace Work.OffAxis.Tf72One

open MeasureTheory intervalIntegral
open Work.ZeroFreeTables
open Work.ZeroFreeTables.OffAxis
open scoped BigOperators

/-! ## The bridge `tf72Fc 1 = G72` -/

/-- At `λ = 1` the Lemma 7.2 Laplace transform `tf72Fc` of `testFn72_defs` coincides with the
scale-free transform `G72`. -/
theorem tf72Fc_one_eq_G72 (z : ℂ) : tf72Fc 1 z = G72 z := by
  have h2 : (2:ℝ)/1 = 2 := by norm_num
  rw [tf72Fc, G72, h2]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht2 : t ∈ Set.Icc (0:ℝ) 2 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] at ht
    exact ht
  show Complex.exp (-(z * (t:ℂ))) * ((tf72f 1 t : ℝ):ℂ)
      = Complex.exp (-(z * (t:ℂ))) * ((g72 t : ℝ):ℂ)
  rw [tf72f_eq_poly 1 (by norm_num) t (by simpa using ht2)]
  simp only [g72]
  push_cast
  ring

/-- `Isub` is even in `σ` (`Isub s σ = Isub s |σ|`). -/
theorem Isub_abs (s σ : ℝ) : Isub s σ = Isub s |σ| := by
  rw [Isub_eq_integral, Isub_eq_integral]
  apply intervalIntegral.integral_congr
  intro y hy
  have hy0 : 0 ≤ y := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] at hy
    exact hy.1
  show (Real.exp (s * y) - 2) * Real.cos (σ * y) * g72 y
      = (Real.exp (s * y) - 2) * Real.cos (|σ| * y) * g72 y
  have h1 : |σ| * y = |σ * y| := by rw [abs_mul, abs_of_nonneg hy0]
  rw [h1, Real.cos_abs]

/-! ## Certified corner bounds -/

/-- Upper end of the range of the `cos (2σ)`-coefficient in `Isub_eq_closed`, given
`Elo ≤ exp (2s) ≤ Ehi`. -/
def RcHi (s σ Elo Ehi : ℝ) : ℝ :=
  max (Elo * RB72 s σ) (Ehi * RB72 s σ) - 8 * (σ ^ 2 - 1) / σ ^ 6

/-- Lower end of the range of the `cos (2σ)`-coefficient in `Isub_eq_closed`. -/
def RcLo (s σ Elo Ehi : ℝ) : ℝ :=
  min (Elo * RB72 s σ) (Ehi * RB72 s σ) - 8 * (σ ^ 2 - 1) / σ ^ 6

/-- Upper end of the range of the `sin (2σ)`-coefficient in `Isub_eq_closed`. -/
def RsHi (s σ Elo Ehi : ℝ) : ℝ :=
  max (Elo * RI72 s σ) (Ehi * RI72 s σ) + 16 / σ ^ 5

/-- Lower end of the range of the `sin (2σ)`-coefficient in `Isub_eq_closed`. -/
def RsLo (s σ Elo Ehi : ℝ) : ℝ :=
  min (Elo * RI72 s σ) (Ehi * RI72 s σ) + 16 / σ ^ 5

/-- Certified upper bound for `Isub s σ` from rational enclosures `[c0,c1]` of `cos (2σ)`,
`[t0,t1]` of `sin (2σ)` and `[Elo,Ehi]` of `exp (2s)`. -/
def cornerB (s σ Elo Ehi c0 c1 t0 t1 : ℝ) : ℝ :=
  RA72 s σ - 8 / σ ^ 4 - 8 / σ ^ 6
    + max (max (c0 * RcLo s σ Elo Ehi) (c0 * RcHi s σ Elo Ehi))
          (max (c1 * RcLo s σ Elo Ehi) (c1 * RcHi s σ Elo Ehi))
    + max (max (t0 * RsLo s σ Elo Ehi) (t0 * RsHi s σ Elo Ehi))
          (max (t1 * RsLo s σ Elo Ehi) (t1 * RsHi s σ Elo Ehi))

/-- **Certified corner bound.**  With `Elo ≤ exp (2s) ≤ Ehi`, `c0 ≤ cos (2σ) ≤ c1` and
`t0 ≤ sin (2σ) ≤ t1`, the closed form of `Isub` gives `Isub s σ ≤ cornerB s σ Elo Ehi c0 c1 t0 t1`. -/
theorem Isub_le_cornerB (s σ Elo Ehi c0 c1 t0 t1 : ℝ) (hs : 0 ≤ s) (hσ : σ ≠ 0)
    (hElo : Elo ≤ Real.exp (2 * s)) (hEhi : Real.exp (2 * s) ≤ Ehi)
    (hc0 : c0 ≤ Real.cos (2 * σ)) (hc1 : Real.cos (2 * σ) ≤ c1)
    (ht0 : t0 ≤ Real.sin (2 * σ)) (ht1 : Real.sin (2 * σ) ≤ t1) :
    Isub s σ ≤ cornerB s σ Elo Ehi c0 c1 t0 t1 := by
  have hσ2 : s ^ 2 + σ ^ 2 ≠ 0 := by
    have h1 : (0:ℝ) < σ ^ 2 := lt_of_le_of_ne (sq_nonneg σ) (Ne.symm (pow_ne_zero 2 hσ))
    positivity
  have hRcHi : Real.exp (2 * s) * RB72 s σ - 8 * (σ ^ 2 - 1) / σ ^ 6 ≤ RcHi s σ Elo Ehi := by
    have h : Real.exp (2 * s) * RB72 s σ ≤ max (Elo * RB72 s σ) (Ehi * RB72 s σ) := by
      rcases le_total 0 (RB72 s σ) with hR | hR
      · exact le_trans (mul_le_mul_of_nonneg_right hEhi hR) (le_max_right _ _)
      · exact le_trans (mul_le_mul_of_nonpos_right hElo hR) (le_max_left _ _)
    simp only [RcHi]
    linarith
  have hRcLo : RcLo s σ Elo Ehi ≤ Real.exp (2 * s) * RB72 s σ - 8 * (σ ^ 2 - 1) / σ ^ 6 := by
    have h : min (Elo * RB72 s σ) (Ehi * RB72 s σ) ≤ Real.exp (2 * s) * RB72 s σ := by
      rcases le_total 0 (RB72 s σ) with hR | hR
      · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right hElo hR)
      · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right hEhi hR)
    simp only [RcLo]
    linarith
  have hRsHi : Real.exp (2 * s) * RI72 s σ + 16 / σ ^ 5 ≤ RsHi s σ Elo Ehi := by
    have h : Real.exp (2 * s) * RI72 s σ ≤ max (Elo * RI72 s σ) (Ehi * RI72 s σ) := by
      rcases le_total 0 (RI72 s σ) with hR | hR
      · exact le_trans (mul_le_mul_of_nonneg_right hEhi hR) (le_max_right _ _)
      · exact le_trans (mul_le_mul_of_nonpos_right hElo hR) (le_max_left _ _)
    simp only [RsHi]
    linarith
  have hRsLo : RsLo s σ Elo Ehi ≤ Real.exp (2 * s) * RI72 s σ + 16 / σ ^ 5 := by
    have h : min (Elo * RI72 s σ) (Ehi * RI72 s σ) ≤ Real.exp (2 * s) * RI72 s σ := by
      rcases le_total 0 (RI72 s σ) with hR | hR
      · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right hElo hR)
      · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right hEhi hR)
    simp only [RsLo]
    linarith
  have hkey : ∀ (c r lo hi u0 u1 : ℝ), u0 ≤ c → c ≤ u1 → lo ≤ r → r ≤ hi →
      c * r ≤ max (max (u0 * lo) (u0 * hi)) (max (u1 * lo) (u1 * hi)) := by
    intro c r lo hi u0 u1 hcu0 hcu1 hlo hhi
    have step1 : c * r ≤ max (u0 * r) (u1 * r) := by
      rcases le_total r 0 with hr | hr
      · exact le_trans (mul_le_mul_of_nonpos_right hcu0 hr) (le_max_left _ _)
      · exact le_trans (mul_le_mul_of_nonneg_right hcu1 hr) (le_max_right _ _)
    have step2' : ∀ c' : ℝ, c' * r ≤ max (c' * lo) (c' * hi) := by
      intro c'
      rcases le_total 0 c' with hc | hc
      · exact le_trans (mul_le_mul_of_nonneg_left hhi hc) (le_max_right _ _)
      · exact le_trans (mul_le_mul_of_nonpos_left hlo hc) (le_max_left _ _)
    have step2 : max (u0 * r) (u1 * r)
        ≤ max (max (u0 * lo) (u0 * hi)) (max (u1 * lo) (u1 * hi)) := by
      apply max_le
      · exact le_trans (step2' u0) (le_max_left _ _)
      · exact le_trans (step2' u1) (le_max_right _ _)
    exact le_trans step1 step2
  have hcos := hkey (Real.cos (2 * σ))
    (Real.exp (2 * s) * RB72 s σ - 8 * (σ ^ 2 - 1) / σ ^ 6)
    (RcLo s σ Elo Ehi) (RcHi s σ Elo Ehi) c0 c1 hc0 hc1 hRcLo hRcHi
  have hsin := hkey (Real.sin (2 * σ))
    (Real.exp (2 * s) * RI72 s σ + 16 / σ ^ 5)
    (RsLo s σ Elo Ehi) (RsHi s σ Elo Ehi) t0 t1 ht0 ht1 hRsLo hRsHi
  have key : RA72 s σ - 2 * (4 / σ ^ 4 + 4 / σ ^ 6) = RA72 s σ - 8 / σ ^ 4 - 8 / σ ^ 6 := by ring
  rw [Isub_eq_closed hσ hσ2, key]
  have h1 : RA72 s σ - 8 / σ ^ 4 - 8 / σ ^ 6
      + Real.cos (2 * σ) * (Real.exp (2 * s) * RB72 s σ - 8 * (σ ^ 2 - 1) / σ ^ 6)
      ≤ RA72 s σ - 8 / σ ^ 4 - 8 / σ ^ 6
        + max (max (c0 * RcLo s σ Elo Ehi) (c0 * RcHi s σ Elo Ehi))
              (max (c1 * RcLo s σ Elo Ehi) (c1 * RcHi s σ Elo Ehi)) := by
    linarith [hcos]
  have h2 : RA72 s σ - 8 / σ ^ 4 - 8 / σ ^ 6
        + max (max (c0 * RcLo s σ Elo Ehi) (c0 * RcHi s σ Elo Ehi))
              (max (c1 * RcLo s σ Elo Ehi) (c1 * RcHi s σ Elo Ehi))
        + Real.sin (2 * σ) * (Real.exp (2 * s) * RI72 s σ + 16 / σ ^ 5)
      ≤ cornerB s σ Elo Ehi c0 c1 t0 t1 := by
    rw [cornerB]
    linarith [hsin]
  linarith [h1, h2]

end Work.OffAxis.Tf72One
