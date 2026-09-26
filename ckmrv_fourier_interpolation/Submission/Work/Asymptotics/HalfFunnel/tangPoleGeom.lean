/-
# Geometry of the first pole on the tangency region

For `τ ∈ ctanRegion` the pole `z₁ = poleOne τ` of `z ↦ K(τ,z)` lies strictly inside the
rectangle `(0,1/4) × (1/2,3/2)`.

Writing `τ = ±1/2 + a + i(1/2+b)` (the sign being that of `Re τ`, so that `a` is the offset
from the nearer tangency point and `b = Im τ - 1/2`), one has in both cases the same formula

`z₁ = ((a² + b + b²) + i(1/2 + b)) / ((1/2 + a)² + (1/2 + b)²)`,

with `a² + b² < 1/64`, `b ≥ 0`, and `a² + b + b² > 0` (which is exactly the fundamental-domain
condition `|τ ∓ 1/2| > 1/2`). The four inequalities are then linear arithmetic, using
`Work.Asymptotics.HalfFunnel.pole_helper` and `pole_helper2` of `tangPoleGeomAux.lean`.
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangDefs
import Submission.Work.Asymptotics.HalfFunnel.tangPoleGeomAux
import Submission.Work.Asymptotics.HalfFunnel.tangOrbitRect

open UpperHalfPlane ModularGroup

set_option linter.unusedSimpArgs false

namespace Work.Asymptotics.HalfFunnel

noncomputable section

/-- The denominator `(1/2+a)² + (1/2+b)²` is non-zero as a complex number whenever it is
positive as a real number. -/
lemma dne_aux {a b : ℝ} (hDpos : 0 < (1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) :
    ((1 / 2 : ℂ) + ↑a) ^ 2 + ((1 / 2 : ℂ) + ↑b) ^ 2 ≠ 0 := by
  have h1 : (((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hDpos)
  have hEq : (((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2 : ℝ) : ℂ)
      = ((1 / 2 : ℂ) + ↑a) ^ 2 + ((1 / 2 : ℂ) + ↑b) ^ 2 := by push_cast; ring
  rwa [hEq] at h1

/-- The four pole inequalities, in the normalised coordinates `a`, `b` of the region. -/
lemma pole_coords_aux {a b : ℝ} (hab : a ^ 2 + b ^ 2 < 1 / 64) (hb : 0 ≤ b)
    (hD : 0 < a ^ 2 + b + b ^ 2) :
    0 < (a ^ 2 + b + b ^ 2) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) ∧
      (a ^ 2 + b + b ^ 2) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) < 1 / 4 ∧
      (1 : ℝ) / 2 < (1 / 2 + b) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) ∧
      (1 / 2 + b) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) < 3 / 2 := by
  set D : ℝ := (1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2 with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    nlinarith [sq_nonneg (1 / 2 + a), sq_nonneg (1 / 2 + b), hab]
  have hnum : 0 < a ^ 2 + b + b ^ 2 := hD
  have h1 : 0 < (a ^ 2 + b + b ^ 2) / D := div_pos hnum hDpos
  have hden : D = 1 / 2 + a + b + a ^ 2 + b ^ 2 := by rw [hDdef]; ring
  have habs : a ^ 2 + b ^ 2 < 1 / 64 := hab
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ hDpos, hden]
    have h := pole_helper hab
    nlinarith [h]
  · rw [lt_div_iff₀ hDpos, hden]
    have h := pole_helper2 hab
    nlinarith [h]
  · rw [div_lt_iff₀ hDpos, hden]
    nlinarith [habs, hb]

/-- The real coordinate identity behind the first branch, `re` part. -/
lemma pole_re_aux {a b : ℝ} (h : (1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2 ≠ 0) :
    1 - (1 / 2 + a) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2)
      = (a ^ 2 + b + b ^ 2) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) := by
  rw [eq_div_iff h, sub_mul, div_mul_cancel₀ _ h, one_mul]
  ring

/-- The real coordinate identity behind the first branch, `im` part. -/
lemma pole_im_aux {a b : ℝ} :
    (0 : ℝ) - (-(1 / 2 + b)) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2)
      = (1 / 2 + b) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) := by
  rw [zero_sub, neg_div, neg_neg]

/-- The real coordinate identity behind the second branch, `re` part. -/
lemma polequot_re_aux {a b : ℝ} (h : (1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2 ≠ 0) :
    (-(1 / 2) + a) * (1 / 2 + a) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2)
        + (1 / 2 + b) * (1 / 2 + b) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2)
      = (a ^ 2 + b + b ^ 2) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) := by
  rw [← add_div]
  congr 1
  ring

/-- The real coordinate identity behind the second branch, `im` part. -/
lemma polequot_im_aux {a b : ℝ} (h : (1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2 ≠ 0) :
    (1 / 2 + b) * (1 / 2 + a) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2)
        - (-(1 / 2) + a) * (1 / 2 + b) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2)
      = (1 / 2 + b) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) := by
  rw [← sub_div]
  congr 1
  ring

/-- The coordinates of `z₁ = poleOne τ` in the first (right) branch: `z₁ = 1 - 1/τ`,
with `τ = 1/2 + a + i(1/2+b)`. -/
lemma poleOne_coords_pos (τ : ℍ) {a b : ℝ} (hre : τ.re = 1 / 2 + a) (him : τ.im = 1 / 2 + b)
    (hpos : 0 ≤ τ.re) (hDpos : 0 < (1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) :
    (poleOne τ).re = (a ^ 2 + b + b ^ 2) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) ∧
      (poleOne τ).im = (1 / 2 + b) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) := by
  have hDne : (1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2 ≠ 0 := ne_of_gt hDpos
  have hcoe : ((poleOne τ : ℍ) : ℂ) = 1 - 1 / (τ : ℂ) := by
    rw [poleOne_coe, if_neg (not_lt.mpr hpos)]
  have hnsq : Complex.normSq (τ : ℂ) = (1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2 := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hre, him]
    ring
  constructor
  · rw [← UpperHalfPlane.coe_re, hcoe, Complex.sub_re, Complex.one_re, one_div, Complex.inv_re]
    rw [UpperHalfPlane.coe_re, hre, hnsq]
    exact pole_re_aux hDne
  · rw [← UpperHalfPlane.coe_im, hcoe, Complex.sub_im, Complex.one_im, one_div, Complex.inv_im]
    rw [UpperHalfPlane.coe_im, him, hnsq]
    exact pole_im_aux

/-- The coordinates of `z₁ = poleOne τ` in the second (left) branch: `z₁ = τ/(1+τ)`,
with `τ = -1/2 + a + i(1/2+b)`. -/
lemma poleOne_coords_neg (τ : ℍ) {a b : ℝ} (hre : τ.re = -(1 / 2) + a) (him : τ.im = 1 / 2 + b)
    (hneg : τ.re < 0) (hDpos : 0 < (1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) :
    (poleOne τ).re = (a ^ 2 + b + b ^ 2) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) ∧
      (poleOne τ).im = (1 / 2 + b) / ((1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2) := by
  have hDne : (1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2 ≠ 0 := ne_of_gt hDpos
  have hcoe : ((poleOne τ : ℍ) : ℂ) = (τ : ℂ) / (1 + (τ : ℂ)) := by
    rw [poleOne_coe, if_pos hneg]
  have hre1 : (1 + (τ : ℂ)).re = 1 / 2 + a := by
    rw [Complex.add_re, Complex.one_re, UpperHalfPlane.coe_re, hre]; ring
  have him1 : (1 + (τ : ℂ)).im = 1 / 2 + b := by
    rw [Complex.add_im, Complex.one_im, UpperHalfPlane.coe_im, him]; ring
  have hnsq : Complex.normSq (1 + (τ : ℂ)) = (1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2 := by
    rw [Complex.normSq_apply, hre1, him1]; ring
  constructor
  · rw [← UpperHalfPlane.coe_re, hcoe, Complex.div_re]
    rw [UpperHalfPlane.coe_re, hre, UpperHalfPlane.coe_im, him, hre1, him1, hnsq]
    exact polequot_re_aux hDne
  · rw [← UpperHalfPlane.coe_im, hcoe, Complex.div_im]
    rw [UpperHalfPlane.coe_re, hre, UpperHalfPlane.coe_im, him, hre1, him1, hnsq]
    exact polequot_im_aux hDne

/-- **Geometry of the first pole `z₁τ = poleOne τ` on the tangency region.**

For `τ ∈ ctanRegion` the pole `z₁ = poleOne τ` of `z ↦ K(τ,z)` lies strictly inside the
rectangle `(0,1/4) × (1/2,3/2)`: `0 < Re z₁ < 1/4` and `1/2 < Im z₁ < 3/2`. -/
theorem tangPoleGeom (τ : ℍ) (hτ : τ ∈ ctanRegion) :
    0 < (poleOne τ).re ∧ (poleOne τ).re < 1 / 4 ∧ (1 : ℝ) / 2 < (poleOne τ).im ∧
      (poleOne τ).im < 3 / 2 := by
  obtain ⟨⟨hy1, _hy2⟩, _hxcase⟩ := ctanRegion_bounds τ hτ
  obtain ⟨hdomLo, _hdomHi, hdom1, hdom2⟩ := hτ.1
  set b : ℝ := τ.im - 1 / 2 with hbdef
  have hb0 : 0 ≤ b := by rw [hbdef]; linarith
  rcases hτ.2.2.2 with hball | hball
  · -- ## the case of the right tangency point: `z₁ = 1 - 1/τ`
    have hre_bd : |τ.re - 1 / 2| ≤ ‖(τ : ℂ) - ctanP‖ := by
      have h := Complex.abs_re_le_norm ((τ : ℂ) - ctanP)
      rwa [show ((τ : ℂ) - ctanP).re = τ.re - 1 / 2 by simp [ctanP, Complex.sub_re]] at h
    have hre_pos : 0 < τ.re := by
      have := (abs_lt.mp (lt_of_le_of_lt hre_bd hball)).1
      linarith
    set a : ℝ := τ.re - 1 / 2 with hadef
    have ha2 : a ^ 2 + b ^ 2 < 1 / 64 := by
      have hns : Complex.normSq ((τ : ℂ) - ctanP) < 1 / 64 := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [hball, norm_nonneg ((τ : ℂ) - ctanP)]
      rw [Complex.normSq_apply] at hns
      have hre : ((τ : ℂ) - ctanP).re = τ.re - 1 / 2 := by simp [ctanP, Complex.sub_re]
      have him : ((τ : ℂ) - ctanP).im = τ.im - 1 / 2 := by simp [ctanP, Complex.sub_im]
      rw [hre, him] at hns
      rw [hadef, hbdef]; nlinarith [hns]
    have hDcond : 0 < a ^ 2 + b + b ^ 2 := by
      have hns : 1 / 4 < Complex.normSq ((τ : ℂ) - (1 / 2 : ℂ)) := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [hdom1, norm_nonneg ((τ : ℂ) - (1 / 2 : ℂ))]
      rw [Complex.normSq_apply] at hns
      have hre : ((τ : ℂ) - (1 / 2 : ℂ)).re = τ.re - 1 / 2 := by simp
      have him : ((τ : ℂ) - (1 / 2 : ℂ)).im = τ.im := by simp
      rw [hre, him] at hns
      rw [hadef, hbdef]; nlinarith [hns]
    obtain ⟨h1, h2, h3, h4⟩ := pole_coords_aux ha2 hb0 hDcond
    have hreτ : τ.re = 1 / 2 + a := by rw [hadef]; ring
    have himτ : τ.im = 1 / 2 + b := by rw [hbdef]; ring
    have hDpos : 0 < (1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2 := by
      nlinarith [ha2, sq_nonneg (1 / 2 + a), sq_nonneg (1 / 2 + b)]
    obtain ⟨hre_eq, him_eq⟩ := poleOne_coords_pos τ hreτ himτ hre_pos.le hDpos
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hre_eq]; exact h1
    · rw [hre_eq]; exact h2
    · rw [him_eq]; exact h3
    · rw [him_eq]; exact h4
  · -- ## the case of the left tangency point: `z₁ = τ/(1+τ)`
    have hre_bd : |τ.re + 1 / 2| ≤ ‖(τ : ℂ) - ctanM‖ := by
      have h := Complex.abs_re_le_norm ((τ : ℂ) - ctanM)
      rwa [show ((τ : ℂ) - ctanM).re = τ.re + 1 / 2 by simp [ctanM, Complex.sub_re]] at h
    have hre_neg : τ.re < 0 := by
      have := (abs_lt.mp (lt_of_le_of_lt hre_bd hball)).2
      linarith
    set a : ℝ := τ.re + 1 / 2 with hadef
    have ha2 : a ^ 2 + b ^ 2 < 1 / 64 := by
      have hns : Complex.normSq ((τ : ℂ) - ctanM) < 1 / 64 := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [hball, norm_nonneg ((τ : ℂ) - ctanM)]
      rw [Complex.normSq_apply] at hns
      have hre : ((τ : ℂ) - ctanM).re = τ.re + 1 / 2 := by simp [ctanM, Complex.sub_re]
      have him : ((τ : ℂ) - ctanM).im = τ.im - 1 / 2 := by simp [ctanM, Complex.sub_im]
      rw [hre, him] at hns
      rw [hadef, hbdef]; nlinarith [hns]
    have hDcond : 0 < a ^ 2 + b + b ^ 2 := by
      have hns : 1 / 4 < Complex.normSq ((τ : ℂ) + (1 / 2 : ℂ)) := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [hdom2, norm_nonneg ((τ : ℂ) + (1 / 2 : ℂ))]
      rw [Complex.normSq_apply] at hns
      have hre : ((τ : ℂ) + (1 / 2 : ℂ)).re = τ.re + 1 / 2 := by simp
      have him : ((τ : ℂ) + (1 / 2 : ℂ)).im = τ.im := by simp
      rw [hre, him] at hns
      rw [hadef, hbdef]; nlinarith [hns]
    obtain ⟨h1, h2, h3, h4⟩ := pole_coords_aux ha2 hb0 hDcond
    have hreτ : τ.re = -(1 / 2) + a := by rw [hadef]; ring
    have himτ : τ.im = 1 / 2 + b := by rw [hbdef]; ring
    have hDpos : 0 < (1 / 2 + a) ^ 2 + (1 / 2 + b) ^ 2 := by
      nlinarith [ha2, sq_nonneg (1 / 2 + a), sq_nonneg (1 / 2 + b)]
    obtain ⟨hre_eq, him_eq⟩ := poleOne_coords_neg τ hreτ himτ hre_neg hDpos
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hre_eq]; exact h1
    · rw [hre_eq]; exact h2
    · rw [him_eq]; exact h3
    · rw [him_eq]; exact h4

end

end Work.Asymptotics.HalfFunnel
