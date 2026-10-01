/-
# ZeroFreeTables/HB95h3/Tstep — the `T`-bracket of the `P₃` method for `h = 3`

The `h = 3` analogue of the "argument leading to Lemma 8.3" of Heath-Brown's paper: with
`a = 26/10`, `α = a + λ₁`, `λ₁ ≤ 348/1000`, the positive pole contributions to the
`T₃`-bracket (denominator `a`) are dominated by the negative near-zero contributions
(denominator `α`).  The numeric content is the side condition (9.17) in the form
`6000·(α/a)³ ≤ 16150`.

These lemmas were proved in `Submission/Work/ZeroFreeTables/HBTheorem1_complex_h3.lean`
(`Work.ZeroFreeTables.ratio_cube`, `Work.ZeroFreeTables.h3_side`,
`Work.ZeroFreeTables.h3_Tstep`); they are reproduced here, in the `HB95h3` namespace, on the
import surface of the `h = 3` engine, which cannot import the consumer file.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Table4.HB83

open Complex

namespace Work.ZeroFreeTables.HB95h3

/-- Elementary comparison of the two `P₃` arguments: for `0 < a ≤ α`,
`(αa/(a²+t²))³ ≤ (α/a)³·(α²/(α²+t²))³`. -/
theorem ratio_cube {a α t : ℝ} (ha : 0 < a) (hα : 0 < α) (hale : a ≤ α) :
    (α * a / (a^2 + t^2))^3 ≤ (α/a)^3 * (α^2/(α^2 + t^2))^3 := by
  have hkey : ((α/a) * (α^2/(α^2 + t^2))) - (α * a / (a^2 + t^2))
      = (α*(α^2 - a^2)*t^2)/(a*(a^2+t^2)*(α^2+t^2)) := by
    field_simp
    ring
  have hnum : 0 ≤ α*(α^2 - a^2)*t^2 := by
    have h1 : 0 ≤ α^2 - a^2 := by nlinarith [hale, ha.le, hα.le]
    positivity
  have hden : 0 < a*(a^2+t^2)*(α^2+t^2) := by
    have h1 : 0 < a^2 + t^2 := by nlinarith [sq_nonneg t, sq_pos_of_pos ha]
    have h2 : 0 < α^2 + t^2 := by nlinarith [sq_nonneg t, sq_pos_of_pos hα]
    positivity
  have hAB : α * a / (a^2 + t^2) ≤ (α/a) * (α^2/(α^2 + t^2)) := by
    have h3 : 0 ≤ ((α/a) * (α^2/(α^2 + t^2))) - (α * a / (a^2 + t^2)) := by
      rw [hkey]; exact div_nonneg hnum hden.le
    linarith [h3]
  have hnn : 0 ≤ α * a / (a^2 + t^2) := by
    have h1 : 0 < a^2 + t^2 := by nlinarith [sq_nonneg t, sq_pos_of_pos ha]
    exact div_nonneg (mul_nonneg hα.le ha.le) h1.le
  calc (α * a / (a^2 + t^2))^3 ≤ ((α/a) * (α^2/(α^2 + t^2)))^3 :=
        pow_le_pow_left₀ hnn hAB 3
    _ = (α/a)^3 * (α^2/(α^2 + t^2))^3 := by ring

/-- The numeric side condition (9.17) at `a = 2.6`, `λ₁ ≤ 348/1000`: `6000·(α/a)³ ≤ 16150`. -/
theorem h3_side {lam : ℝ} (h0 : 0 ≤ lam) (hle : lam ≤ 348 / 1000) :
    6000 * (((26:ℝ)/10 + lam) / ((26:ℝ)/10))^3 ≤ 16150 := by
  have hle' : (26:ℝ)/10 + lam ≤ (2948:ℝ)/1000 := by linarith
  have hpos' : 0 < (26:ℝ)/10 + lam := by linarith
  have hcube : ((26:ℝ)/10 + lam)^3 ≤ ((2948:ℝ)/1000)^3 := pow_le_pow_left₀ hpos'.le hle' 3
  rw [div_pow,
    show 6000 * (((26:ℝ)/10 + lam)^3 / ((26:ℝ)/10)^3)
        = (6000 * ((26:ℝ)/10 + lam)^3) / ((26:ℝ)/10)^3 by ring,
    div_le_iff₀ (by norm_num : (0:ℝ) < ((26:ℝ)/10)^3)]
  have h1 : 6000 * ((26:ℝ)/10 + lam)^3 ≤ 6000 * ((2948:ℝ)/1000)^3 :=
    mul_le_mul_of_nonneg_left hcube (by norm_num)
  have h2 : 6000 * ((2948:ℝ)/1000)^3 ≤ 16150 * ((26:ℝ)/10)^3 := by norm_num
  linarith [h1, h2]

/-- **The `T₃`-step.**  For `0 ≤ λ₁ ≤ 348/1000` and every `T`,
`6000·Re P₃(α/(a+iT)) ≤ 14900·Re P₃(α/(α+iT)) + 1250·Re P₃(α/(α+iT))`. -/
theorem h3_Tstep {lam T : ℝ} (h0 : 0 ≤ lam) (hle : lam ≤ 348 / 1000) :
    6000 * Table4.P3AB ((26:ℝ)/10 + lam) ((26:ℝ)/10) T
      ≤ 14900 * Table4.P3AB ((26:ℝ)/10 + lam) ((26:ℝ)/10 + lam) T
        + 1250 * Table4.P3AB ((26:ℝ)/10 + lam) ((26:ℝ)/10 + lam) T := by
  have hs := h3_side h0 hle
  have ha : 0 < ((26:ℝ)/10) := by norm_num
  have hα : 0 < ((26:ℝ)/10) + lam := by linarith
  have hale : ((26:ℝ)/10) ≤ ((26:ℝ)/10) + lam := by linarith
  have hfac : (((26:ℝ)/10 + lam) * ((26:ℝ)/10) / (((26:ℝ)/10)^2 + T^2))^3
      ≤ (((26:ℝ)/10 + lam) / ((26:ℝ)/10))^3
        * ((((26:ℝ)/10 + lam)^2) / ((((26:ℝ)/10 + lam)^2) + T^2))^3 :=
    ratio_cube ha hα hale
  have hle1 := Table4.P3AB_le (((26:ℝ)/10 + lam)) ((26:ℝ)/10) T hα ha hale
  have hge1 := Table4.P3AB_ge (((26:ℝ)/10 + lam)) (((26:ℝ)/10 + lam)) T hα hα le_rfl
  have hbb : 0 ≤ ((((26:ℝ)/10 + lam)^2) / ((((26:ℝ)/10 + lam)^2) + T^2))^3 := by positivity
  have key : 6000 * ((8/3) * (((26:ℝ)/10 + lam) * ((26:ℝ)/10) / (((26:ℝ)/10)^2 + T^2))^3)
      ≤ 16150 * ((8/3) * (((26:ℝ)/10 + lam)^2 / (((26:ℝ)/10 + lam)^2 + T^2))^3) := by
    have h1 : 6000 * ((((26:ℝ)/10 + lam) * ((26:ℝ)/10) / (((26:ℝ)/10)^2 + T^2))^3)
        ≤ 6000 * ((((26:ℝ)/10 + lam) / ((26:ℝ)/10))^3
            * ((((26:ℝ)/10 + lam)^2) / ((((26:ℝ)/10 + lam)^2) + T^2))^3) :=
      mul_le_mul_of_nonneg_left hfac (by norm_num)
    have h2 : 6000 * ((((26:ℝ)/10 + lam) / ((26:ℝ)/10))^3
          * ((((26:ℝ)/10 + lam)^2) / ((((26:ℝ)/10 + lam)^2) + T^2))^3)
        ≤ 16150 * ((((26:ℝ)/10 + lam)^2 / ((((26:ℝ)/10 + lam)^2) + T^2))^3) := by
      have h3 : 6000 * ((((26:ℝ)/10 + lam) / ((26:ℝ)/10))^3) ≤ 16150 := hs
      nlinarith [h3, hbb]
    have h5 : 0 ≤ (8/3 : ℝ) := by norm_num
    nlinarith [h1, h2, h5]
  have hk : 6000 * Table4.P3AB ((26:ℝ)/10 + lam) ((26:ℝ)/10) T
      ≤ 16150 * ((8/3) * (((26:ℝ)/10 + lam)^2 / (((26:ℝ)/10 + lam)^2 + T^2))^3) :=
    le_trans (mul_le_mul_of_nonneg_left hle1 (by norm_num)) key
  have hge1' : (8/3) * ((((26:ℝ)/10 + lam)^2) / (((26:ℝ)/10 + lam)^2 + T^2))^3
      ≤ Table4.P3AB ((26:ℝ)/10 + lam) ((26:ℝ)/10 + lam) T := by
    simpa [pow_two] using hge1
  have hfin : 16150 * ((8/3) * (((26:ℝ)/10 + lam)^2 / (((26:ℝ)/10 + lam)^2 + T^2))^3)
      ≤ 16150 * Table4.P3AB ((26:ℝ)/10 + lam) ((26:ℝ)/10 + lam) T :=
    mul_le_mul_of_nonneg_left hge1' (by norm_num)
  nlinarith [hk, hfin]

end Work.ZeroFreeTables.HB95h3
