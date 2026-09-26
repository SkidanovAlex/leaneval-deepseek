/-
# Geometry of the first pole on the *closed* tangency region

`tangPoleGeom` (tangPoleGeom.lean) proves that for `τ` in the open tangency region `ctanRegion`
the pole `z₁ = poleOne τ` lies strictly inside the rectangle `(0,1/4) × (1/2,3/2)`, in
particular with `0 < Re z₁`.  The boundary version needed by the contour shift uses the *closed*
region `ctanCl`, where `Re z₁ = 0` is attained at the two tangency points
`τ = ±1/2 + i/2` (there `z₁ = i`), so the positivity of `Re z₁` genuinely fails; but the three
*non-contour* edges of the rectangle are still missed, because the other three inequalities
`Re z₁ < 1/4`, `1/2 < Im z₁ < 3/2` survive with margin.

The proof is the closed version of the one in `tangPoleGeom`: writing `τ = ±1/2 + a + i(1/2+b)`,
the region gives `|a| ≤ 1/8`, `0 ≤ b ≤ 1/8`, `a² + b² ≤ 1/64`, and
`z₁ = ((a²+b+b²) + i(1/2+b)) / ((1/2+a)² + (1/2+b)²)`; the three inequalities are then the
elementary estimates of `pole_coords_aux_cl` below (the last one uses
`3b - a ≤ |3b - a| ≤ √10·√(a²+b²) ≤ √10/8 < 29/64`).
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangPoleGeom
import Submission.Work.Asymptotics.HalfFunnel.tangOrbitRectCl

open UpperHalfPlane ModularGroup

set_option linter.unusedSimpArgs false

namespace Work.Asymptotics.HalfFunnel

noncomputable section

/-- **The three pole inequalities in the closed region.**  For `|a| ≤ 1/8`, `0 ≤ b ≤ 1/8` and
`a² + b² ≤ 1/64` one has (`D := (1/2+a)² + (1/2+b)²`)
`(a²+b+b²)/D < 1/4`, `1/2 < (1/2+b)/D` and `(1/2+b)/D < 3/2`; these are the coordinates of the
first pole `z₁ = poleOne τ` in the normalised coordinates `τ = ±1/2 + a + i(1/2+b)`. -/
lemma pole_coords_aux_cl {a b : ℝ} (ha : |a| ≤ 1 / 8) (hb1 : 0 ≤ b) (_hb2 : b ≤ 1 / 8)
    (hab : a ^ 2 + b ^ 2 ≤ 1 / 64) :
    (a ^ 2 + b + b ^ 2) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) < 1 / 4 ∧
      (1 : ℝ) / 2 < (1 / 2 + b) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) ∧
      (1 / 2 + b) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) < 3 / 2 := by
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  set D : ℝ := (1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; nlinarith
  have hden : D = 1 / 2 + a + b + a ^ 2 + b ^ 2 := by rw [hDdef]; ring
  have hsq : (3 * b - a) ^ 2 ≤ 10 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (3 * a + b)]
  have hsqrt : Real.sqrt (a ^ 2 + b ^ 2) ≤ 1 / 8 := by
    have h : Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt (1 / 64) := Real.sqrt_le_sqrt hab
    rwa [show Real.sqrt (1 / 64) = 1 / 8 by
      rw [show (1 / 64 : ℝ) = (1 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hs10 : Real.sqrt 10 < 29 / 8 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h3ba : 3 * b - a < 29 / 64 := by
    have h1 : |3 * b - a| ≤ Real.sqrt 10 / 8 := by
      have h2 : Real.sqrt ((3 * b - a) ^ 2) ≤ Real.sqrt (10 * (a ^ 2 + b ^ 2)) :=
        Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10)] at h2
      calc |3 * b - a| ≤ Real.sqrt 10 * Real.sqrt (a ^ 2 + b ^ 2) := h2
        _ ≤ Real.sqrt 10 * (1 / 8) :=
            mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg 10)
        _ = Real.sqrt 10 / 8 := by ring
    have h3 := le_abs_self (3 * b - a)
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [div_lt_iff₀ hDpos, hden]
    nlinarith [h3ba, hab]
  · rw [lt_div_iff₀ hDpos, hden]
    nlinarith [ha1, hab, hb1]
  · rw [div_lt_iff₀ hDpos, hden]
    nlinarith [ha1, hab, hb1]

/-- **Geometry of the first pole `z₁τ = poleOne τ` on the closed tangency region.**

For `τ ∈ ctanCl` the pole `z₁ = poleOne τ` misses the three non-contour edges of the rectangle
`[0,1/4] × [1/2,3/2]`: `Re z₁ < 1/4` and `1/2 < Im z₁ < 3/2`.  (The fourth edge, the contour
`Re z = 0`, *is* met, at the two tangency points `τ = ±1/2 + i/2`, where `z₁ = i`; that is why
this closed version cannot also assert `0 < Re z₁`, which is true only on the open region.) -/
theorem tangPoleGeomCl (τ : ℍ) (hτ : τ ∈ ctanCl) :
    (poleOne τ).re < 1 / 4 ∧ (1 : ℝ) / 2 < (poleOne τ).im ∧ (poleOne τ).im < 3 / 2 := by
  obtain ⟨hy1, hy2, _h3, _h4, hb⟩ := hτ
  have hb1 : 0 ≤ τ.im - 1 / 2 := by linarith
  have hb2 : τ.im - 1 / 2 ≤ 1 / 8 := by linarith
  rcases hb with hball | hball
  · -- the right tangency point: `τ = 1/2 + a + i(1/2+b)`, `z₁ = 1 - 1/τ`
    have habs : |τ.re - 1 / 2| ≤ 1 / 8 := by
      have h := Complex.abs_re_le_norm ((τ : ℂ) - ctanP)
      rw [show ((τ : ℂ) - ctanP).re = τ.re - 1 / 2 by simp [ctanP, Complex.sub_re]] at h
      linarith
    have ha2 : (τ.re - 1 / 2) ^ 2 + (τ.im - 1 / 2) ^ 2 ≤ 1 / 64 := by
      have hns : Complex.normSq ((τ : ℂ) - ctanP) ≤ 1 / 64 := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [hball, norm_nonneg ((τ : ℂ) - ctanP)]
      rw [Complex.normSq_apply] at hns
      have hre : ((τ : ℂ) - ctanP).re = τ.re - 1 / 2 := by simp [ctanP, Complex.sub_re]
      have him : ((τ : ℂ) - ctanP).im = τ.im - 1 / 2 := by simp [ctanP, Complex.sub_im]
      rw [hre, him] at hns
      simpa [pow_two] using hns
    have hpos : 0 ≤ τ.re := by linarith [(abs_le.mp habs).1]
    have hDpos : 0 < (1 / 2 + (τ.re - 1 / 2)) ^ 2 + (1 / 2 + (τ.im - 1 / 2)) ^ 2 := by
      nlinarith [ha2, sq_nonneg (1 / 2 + (τ.re - 1 / 2))]
    obtain ⟨hre_eq, him_eq⟩ :=
      poleOne_coords_pos τ (a := τ.re - 1 / 2) (b := τ.im - 1 / 2) (by ring) (by ring) hpos hDpos
    obtain ⟨h1, h2, h3⟩ := pole_coords_aux_cl habs hb1 hb2 ha2
    exact ⟨by rw [hre_eq]; exact h1, by rw [him_eq]; exact h2, by rw [him_eq]; exact h3⟩
  · -- the left tangency point: `τ = -1/2 + a + i(1/2+b)`, `z₁ = τ/(1+τ)`
    have habs : |τ.re + 1 / 2| ≤ 1 / 8 := by
      have h := Complex.abs_re_le_norm ((τ : ℂ) - ctanM)
      rw [show ((τ : ℂ) - ctanM).re = τ.re + 1 / 2 by simp [ctanM, Complex.sub_re]] at h
      linarith
    have ha2 : (τ.re + 1 / 2) ^ 2 + (τ.im - 1 / 2) ^ 2 ≤ 1 / 64 := by
      have hns : Complex.normSq ((τ : ℂ) - ctanM) ≤ 1 / 64 := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [hball, norm_nonneg ((τ : ℂ) - ctanM)]
      rw [Complex.normSq_apply] at hns
      have hre : ((τ : ℂ) - ctanM).re = τ.re + 1 / 2 := by simp [ctanM, Complex.sub_re]
      have him : ((τ : ℂ) - ctanM).im = τ.im - 1 / 2 := by simp [ctanM, Complex.sub_im]
      rw [hre, him] at hns
      simpa [pow_two] using hns
    have hneg : τ.re < 0 := by linarith [(abs_le.mp habs).2]
    have hDpos : 0 < (1 / 2 + (τ.re + 1 / 2)) ^ 2 + (1 / 2 + (τ.im - 1 / 2)) ^ 2 := by
      nlinarith [ha2, sq_nonneg (1 / 2 + (τ.im - 1 / 2))]
    obtain ⟨hre_eq, him_eq⟩ :=
      poleOne_coords_neg τ (a := τ.re + 1 / 2) (b := τ.im - 1 / 2) (by ring) (by ring) hneg hDpos
    obtain ⟨h1, h2, h3⟩ := pole_coords_aux_cl habs hb1 hb2 ha2
    exact ⟨by rw [hre_eq]; exact h1, by rw [him_eq]; exact h2, by rw [him_eq]; exact h3⟩

end

end Work.Asymptotics.HalfFunnel
