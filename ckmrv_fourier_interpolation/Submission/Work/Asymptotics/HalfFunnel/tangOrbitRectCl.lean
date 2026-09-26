import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangDefs
import Submission.Work.Asymptotics.HalfFunnel.tangPoleGeomAux
import Submission.Work.Asymptotics.HalfFunnel.tangOrbitRect
import Submission.Work.Asymptotics.HalfFunnel.tangLayerDefs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace Work.Asymptotics.HalfFunnel

open UpperHalfPlane ModularGroup

noncomputable section

/-! ## Closed bounds on `ctanCl`

The only inputs of the orbit analysis that `ctanCl` provides are the non-strict versions of
the bounds of `ctanRegion`. -/

lemma ctanCl_bounds (τ : ℍ) (hτ : τ ∈ ctanCl) :
    (1 / 2 ≤ τ.im ∧ τ.im ≤ 5 / 8) ∧
      ((3 / 8 ≤ τ.re ∧ τ.re ≤ 5 / 8) ∨ (-(5 / 8) ≤ τ.re ∧ τ.re ≤ -(3 / 8))) := by
  obtain ⟨hy1, hy2, _h3, _h4, hb⟩ := hτ
  refine ⟨⟨hy1, hy2⟩, ?_⟩
  rcases hb with hb | hb
  · left
    have hre := Complex.abs_re_le_norm ((τ : ℂ) - ctanP)
    have hcoe : ((τ : ℂ) - ctanP).re = τ.re - 1 / 2 := by simp [ctanP, Complex.sub_re]
    rw [hcoe] at hre
    have := abs_le.mp (le_trans hre hb)
    constructor <;> linarith
  · right
    have hre := Complex.abs_re_le_norm ((τ : ℂ) - ctanM)
    have hcoe : ((τ : ℂ) - ctanM).re = τ.re + 1 / 2 := by simp [ctanM, Complex.sub_re]
    rw [hcoe] at hre
    have := abs_le.mp (le_trans hre hb)
    constructor <;> linarith

/-! ## Closed ratio bounds -/

/-- For `u ∈ [3/8,5/8]` and `Y ∈ [1/2,5/8]`, `u/(u²+Y²) ∈ (1/4,1]`. -/
lemma ratio_pos_cl {u Y : ℝ} (hu1 : 3 / 8 ≤ u) (hu2 : u ≤ 5 / 8) (hY1 : 1 / 2 ≤ Y)
    (hY2 : Y ≤ 5 / 8) : 1 / 4 < u / (u ^ 2 + Y ^ 2) ∧ u / (u ^ 2 + Y ^ 2) ≤ 1 := by
  have hpos : 0 < u ^ 2 + Y ^ 2 := by nlinarith [sq_nonneg u, hY1]
  constructor
  · rw [lt_div_iff₀ hpos]
    have h1 : (u - 2) ^ 2 ≤ (13 / 8 : ℝ) ^ 2 := by
      rw [sq_le_sq, abs_of_nonpos (by linarith : u - 2 ≤ 0),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 13 / 8)]
      linarith
    have h2 : Y ^ 2 ≤ (5 / 8 : ℝ) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Y),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 8)]
      exact hY2
    nlinarith [h1, h2]
  · rw [div_le_one hpos]
    nlinarith [sq_nonneg (u - 1 / 2), sq_nonneg Y, hY1]

/-- For `u ∈ [-5/8,-3/8]` and `Y ∈ [1/2,5/8]`, `u/(u²+Y²) ∈ [-1,-1/4)`. -/
lemma ratio_neg_cl {u Y : ℝ} (hu1 : -(5 / 8) ≤ u) (hu2 : u ≤ -(3 / 8)) (hY1 : 1 / 2 ≤ Y)
    (hY2 : Y ≤ 5 / 8) : -1 ≤ u / (u ^ 2 + Y ^ 2) ∧ u / (u ^ 2 + Y ^ 2) < -(1 / 4) := by
  have hpos : 0 < u ^ 2 + Y ^ 2 := by nlinarith [sq_nonneg u, hY1]
  constructor
  · rw [le_div_iff₀ hpos]
    nlinarith [sq_nonneg (u + 1 / 2), sq_nonneg Y, hY1]
  · rw [div_lt_iff₀ hpos]
    have h1 : (u + 2) ^ 2 ≤ (13 / 8 : ℝ) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u + 2),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 13 / 8)]
      linarith
    have h2 : Y ^ 2 ≤ (5 / 8 : ℝ) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Y),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 8)]
      exact hY2
    nlinarith [h1, h2]

/-- Equality `u/(u²+Y²) = -1` forces `u = -1/2`, `Y = 1/2`. -/
lemma ratio_eq_neg_one {u Y : ℝ} (hY1 : 1 / 2 ≤ Y) (h : u / (u ^ 2 + Y ^ 2) = -1) :
    u = -1 / 2 ∧ Y = 1 / 2 := by
  have hpos : 0 < u ^ 2 + Y ^ 2 := by nlinarith [sq_nonneg u, hY1]
  rw [div_eq_iff (ne_of_gt hpos)] at h
  have h2 : (u + 1 / 2) ^ 2 + (Y ^ 2 - 1 / 4) = 0 := by nlinarith [h]
  have h4 : 0 ≤ Y ^ 2 - 1 / 4 := by nlinarith [hY1]
  have h5 : (u + 1 / 2) ^ 2 = 0 := by nlinarith [sq_nonneg (u + 1 / 2), h2, h4]
  have h6 : Y ^ 2 - 1 / 4 = 0 := by nlinarith [sq_nonneg (u + 1 / 2), h2, h4]
  constructor
  · nlinarith [h5]
  · nlinarith [h6, hY1]

/-! ## The integer offset -/

/-- Closed version of `u_mem_of`. -/
lemma u_mem_of_cl {X u : ℝ} {m : ℤ}
    (hX : (3 / 8 ≤ X ∧ X ≤ 5 / 8) ∨ (-(5 / 8) ≤ X ∧ X ≤ -(3 / 8))) (hm : |u| < 1)
    (hrel : u = X + (m : ℝ)) :
    (3 / 8 ≤ u ∧ u ≤ 5 / 8) ∨ (-(5 / 8) ≤ u ∧ u ≤ -(3 / 8)) := by
  have hulo : -1 < u := (abs_lt.mp hm).1
  have huhi : u < 1 := (abs_lt.mp hm).2
  have hmv : (m : ℝ) = u - X := by linarith [hrel]
  rcases hX with hA | hB
  · have hm2a : (-2 : ℤ) < m := by
      have : (-2 : ℝ) < (m : ℝ) := by rw [hmv]; linarith [hulo, hA.2]
      exact_mod_cast this
    have hm2b : m < 1 := by
      have : (m : ℝ) < 1 := by rw [hmv]; linarith [huhi, hA.1]
      exact_mod_cast this
    interval_cases m
    · right; rw [hrel]; push_cast; constructor <;> linarith [hA.1, hA.2]
    · left; rw [hrel]; push_cast; simpa using hA
  · have hm2a : (-1 : ℤ) < m := by
      have : (-1 : ℝ) < (m : ℝ) := by rw [hmv]; linarith [hulo, hB.1]
      exact_mod_cast this
    have hm2b : m < 2 := by
      have : (m : ℝ) < 2 := by rw [hmv]; linarith [huhi, hB.2]
      exact_mod_cast this
    interval_cases m
    · right; rw [hrel]; push_cast; simpa using hB
    · left; rw [hrel]; push_cast; constructor <;> linarith [hB.1, hB.2]

/-- Positive sign of the offset: `u ∈ [3/8,5/8]` and `u = X + m` force `m = 0` (right
half-axis) or `m = 1` (left half-axis). -/
lemma cd_cases_cl_pos {X u : ℝ} {m : ℤ}
    (hX : (3 / 8 ≤ X ∧ X ≤ 5 / 8) ∨ (-(5 / 8) ≤ X ∧ X ≤ -(3 / 8)))
    (hu : 3 / 8 ≤ u ∧ u ≤ 5 / 8) (hrel : u = X + (m : ℝ)) :
    ((3 / 8 ≤ X ∧ X ≤ 5 / 8) ∧ m = 0) ∨ ((-(5 / 8) ≤ X ∧ X ≤ -(3 / 8)) ∧ m = 1) := by
  have hmv : (m : ℝ) = u - X := by linarith [hrel]
  rcases hX with hA | hB
  · left
    refine ⟨hA, ?_⟩
    have h1 : (-(1 : ℝ)) < (m : ℝ) := by rw [hmv]; linarith [hu.1, hA.2]
    have h2 : (m : ℝ) < 1 := by rw [hmv]; linarith [hu.2, hA.1]
    have hz1 : (-1 : ℤ) < m := by exact_mod_cast h1
    have hz2 : m < 1 := by exact_mod_cast h2
    omega
  · right
    refine ⟨hB, ?_⟩
    have h1 : (0 : ℝ) < (m : ℝ) := by rw [hmv]; linarith [hu.1, hB.2]
    have h2 : (m : ℝ) < 2 := by rw [hmv]; linarith [hu.2, hB.1]
    have hz1 : (0 : ℤ) < m := by exact_mod_cast h1
    have hz2 : m < 2 := by exact_mod_cast h2
    omega

/-- A real number of the form `-1/2 + k` (`k ∈ ℤ`) lying in `[3/8,5/8] ∪ [-5/8,-3/8]` is
`±1/2`. -/
lemma re_half_of_int {X : ℝ} {k : ℤ} (hX : X = -1 / 2 + (k : ℝ))
    (hXc : (3 / 8 ≤ X ∧ X ≤ 5 / 8) ∨ (-(5 / 8) ≤ X ∧ X ≤ -(3 / 8))) :
    X = 1 / 2 ∨ X = -1 / 2 := by
  have hk : (k : ℝ) = X + 1 / 2 := by linarith
  rcases hXc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have hk1 : (0 : ℤ) < k := by
      have : (0 : ℝ) < (k : ℝ) := by rw [hk]; linarith
      exact_mod_cast this
    have hk2 : k < 2 := by
      have : (k : ℝ) < 2 := by rw [hk]; linarith
      exact_mod_cast this
    have : k = 1 := by omega
    rw [hX, this]; norm_num
  · right
    have hk1 : (-1 : ℤ) < k := by
      have : (-1 : ℝ) < (k : ℝ) := by rw [hk]; linarith
      exact_mod_cast this
    have hk2 : k < 1 := by
      have : (k : ℝ) < 1 := by rw [hk]; linarith
      exact_mod_cast this
    have : k = 0 := by omega
    rw [hX, this]; norm_num

/-- At the two tangency points the first pole is `i`. -/
lemma poleOne_eq_I_of {τ : ℍ} (him : τ.im = 1 / 2) (hre : τ.re = 1 / 2 ∨ τ.re = -1 / 2) :
    (poleOne τ : ℂ) = Complex.I := by
  have hcoe : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [poleOne_coe]
  rcases hre with h | h
  · rw [if_neg (by rw [h]; norm_num), hcoe, h, him]
    rw [show ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I = (1 + Complex.I) / 2 by
      push_cast; ring]
    rw [one_div,
      show ((1 + Complex.I) / 2 : ℂ)⁻¹ = 1 - Complex.I by
        rw [inv_eq_of_mul_eq_one_right (a := ((1 + Complex.I) / 2 : ℂ))]
        ring_nf; rw [pow_two, Complex.I_mul_I]; norm_num]
    ring
  · rw [if_pos (by rw [h]; norm_num), hcoe, h, him]
    rw [show (((-1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I) = (Complex.I - 1) / 2 by
      push_cast; ring]
    rw [show (1 + (Complex.I - 1) / 2 : ℂ) = (Complex.I + 1) / 2 by ring]
    rw [show ((Complex.I - 1) / 2 : ℂ) / ((Complex.I + 1) / 2) =
      (Complex.I - 1) / (Complex.I + 1) by field_simp]
    rw [show (Complex.I - 1) / (Complex.I + 1) = Complex.I by
      have hne : (Complex.I + 1 : ℂ) ≠ 0 := by
        intro hh; have := congrArg Complex.re hh; simp at this
      rw [div_eq_iff hne]; ring_nf; rw [pow_two, Complex.I_mul_I]; ring]

/-! ## Copies of the private helpers of `tangOrbitRect` -/

/-- If `c² = 1` and `ad - bc = 1` then `(aτ+b)/(cτ+d) = ca - 1/(τ+cd)`. -/
private lemma moebius_sub_inv (τ c d a b : ℂ) (hc : c ^ 2 = 1) (hdet : a * d - b * c = 1)
    (hden : c * τ + d ≠ 0) (hden2 : τ + c * d ≠ 0) :
    (a * τ + b) / (c * τ + d) = c * a - 1 / (τ + c * d) := by
  rw [div_eq_iff hden]
  have key : c * (τ + c * d) = c * τ + d := by
    rw [mul_add, ← mul_assoc, ← pow_two, hc, one_mul]
  have hratio : (1 / (τ + c * d)) * (c * τ + d) = c := by
    rw [one_div, ← key, mul_comm c (τ + c * d), ← mul_assoc, inv_mul_cancel₀ hden2, one_mul]
  rw [sub_mul, hratio]
  have hgoal : c * a * (c * τ + d) - c - (a * τ + b) = 0 := by
    linear_combination (τ * a + b) * hc + c * hdet
  linear_combination -hgoal

/-- The integer squares not exceeding `4`. -/
private lemma int_cases_of_sq_le_four (c : ℤ) (h : (c : ℝ) ^ 2 ≤ 4) :
    c = -2 ∨ c = -1 ∨ c = 0 ∨ c = 1 ∨ c = 2 := by
  have habs : (-2 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ 2 := by
    have h' : (c : ℝ) ^ 2 ≤ (2 : ℝ) ^ 2 := by norm_num at h ⊢; exact h
    have h2 := abs_le.mp (sq_le_sq.mp h')
    rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h2
  have hz1 : (-2 : ℤ) ≤ c := by exact_mod_cast habs.1
  have hz2 : c ≤ 2 := by exact_mod_cast habs.2
  omega

/-! ## The main theorem -/

/-- **The orbit classification in the rectangle, on the closed tangency region.** -/
theorem tangOrbitRectCl (τ ζ : UpperHalfPlane) (hτ : τ ∈ Work.Asymptotics.HalfFunnel.ctanCl)
    (hre : 0 ≤ ζ.re) (hre' : ζ.re ≤ 1 / 4) (him : (1 : ℝ) / 2 ≤ ζ.im) (him' : ζ.im ≤ 3 / 2)
    (hj : Work.Kernels.jInvariantFun ζ = Work.Kernels.jInvariantFun τ) :
    ζ = Work.Asymptotics.HalfFunnel.poleOne τ := by
  obtain ⟨g, hg⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hj
  obtain ⟨⟨hy1, hy2⟩, hxcase⟩ := ctanCl_bounds τ hτ
  set c : ℤ := g 1 0 with hc
  set d : ℤ := g 1 1 with hd
  set a : ℤ := g 0 0 with ha
  set b : ℤ := g 0 1 with hb
  have hdet : a * d - b * c = 1 := by
    have hh := g.2
    rw [Matrix.det_fin_two] at hh
    rw [← hc, ← hd, ← ha, ← hb] at hh
    exact_mod_cast hh
  have hcoe : (ζ : ℂ) = ((a:ℂ)*(τ:ℂ)+(b:ℂ))/((c:ℂ)*(τ:ℂ)+(d:ℂ)) := by
    have h0 : (ζ:ℂ) = (((g 0 0 : ℤ):ℂ)*(τ:ℂ)+((g 0 1 : ℤ):ℂ))
        /(((g 1 0 : ℤ):ℂ)*(τ:ℂ)+((g 1 1 : ℤ):ℂ)) := by
      rw [← hg, UpperHalfPlane.coe_specialLinearGroup_apply]
      simp only [algebraMap_int_eq]
      simp
    rw [h0, ← ha, ← hb, ← hc, ← hd]
  have him_eq : ζ.im = τ.im / ‖((c:ℝ):ℂ)*(τ:ℂ)+((d:ℝ):ℂ)‖^2 := by
    have hD : ((g 1 0 : ℤ):ℂ)*(τ:ℂ)+((g 1 1 : ℤ):ℂ) = ((c:ℝ):ℂ)*(τ:ℂ)+((d:ℝ):ℂ) := by
      rw [hc, hd]; push_cast <;> ring
    rw [← hg, ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply,
      Complex.normSq_eq_norm_sq, hD]
  have hNcoords : ‖((c:ℝ):ℂ)*(τ:ℂ)+((d:ℝ):ℂ)‖^2
      = ((c:ℝ)*τ.re+(d:ℝ))^2+((c:ℝ)*τ.im)^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hNne : ‖((c:ℝ):ℂ)*(τ:ℂ)+((d:ℝ):ℂ)‖^2 ≠ 0 := by
    intro h0
    rw [him_eq, h0, div_zero] at him
    linarith [him]
  have hNpos : 0 < ‖((c:ℝ):ℂ)*(τ:ℂ)+((d:ℝ):ℂ)‖^2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm hNne)
  rw [him_eq] at him
  have hF1 : ((c:ℝ)*τ.re+(d:ℝ))^2+((c:ℝ)*τ.im)^2 ≤ 2*τ.im := by
    rw [← hNcoords]
    have hmul := mul_le_mul_of_nonneg_right him (le_of_lt hNpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hNpos)] at hmul
    linarith
  have hcsq_le : (c:ℝ)^2 * τ.im ≤ 2 := by
    have h1 : ((c:ℝ)*τ.im)^2 ≤ 2*τ.im := by
      nlinarith [hF1, sq_nonneg ((c:ℝ)*τ.re+(d:ℝ))]
    nlinarith [h1, τ.im_pos]
  have hc_sq_le4 : (c:ℝ)^2 ≤ 4 := by nlinarith [hcsq_le, hy1]
  have hc_le2 := int_cases_of_sq_le_four c hc_sq_le4
  by_cases hcsq4 : (c:ℝ)^2 = 4
  · -- the exceptional case `c² = 4` forces `τ` to be a tangency point and then `ζ.re`
    -- is a half-integer in `[0,1/4]`, contradicting `ad - bc = 1`.
    exfalso
    have hc2 : c = 2 ∨ c = -2 := by
      rcases hc_le2 with h | h | h | h | h
      · exact Or.inr h
      · exact absurd hcsq4 (by rw [h]; norm_num)
      · exact absurd hcsq4 (by rw [h]; norm_num)
      · exact absurd hcsq4 (by rw [h]; norm_num)
      · exact Or.inl h
    have hτim : τ.im = 1 / 2 := by
      have h := hcsq_le
      rw [hcsq4] at h
      linarith [h, hy1]
    have hcτd : (c:ℝ)*τ.re + (d:ℝ) = 0 := by
      have h1 := hF1
      rw [hτim] at h1
      have h3 : ((c:ℝ)*(1/2))^2 = 1 := by rw [mul_pow, hcsq4]; norm_num
      have h4 : ((c:ℝ)*τ.re+(d:ℝ))^2 ≤ 0 := by linarith [h1, h3]
      nlinarith [sq_nonneg ((c:ℝ)*τ.re+(d:ℝ)), h4]
    have hcne : (c:ℝ) ≠ 0 := by rcases hc2 with h | h <;> rw [h] <;> norm_num
    have hB : (c:ℂ)*(τ:ℂ)+(d:ℂ) = (((c:ℝ)/2 : ℝ):ℂ) * Complex.I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
          UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        push_cast
        linarith [hcτd]
      · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
          UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        push_cast
        rw [hτim]; ring
    have hζre_eq : ζ.re = (a:ℝ)/(c:ℝ) := by
      rw [← UpperHalfPlane.coe_re]
      rw [hcoe, hB, Complex.div_re]
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im, Complex.add_re,
        Complex.add_im, Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal, mul_zero,
        mul_one, add_zero]
      rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hτim]
      field_simp
      ring
    have ha0 : a = 0 := by
      rcases hc2 with h | h
      · have hc' : ζ.re = (a:ℝ)/2 := by rw [hζre_eq, h]; norm_num
        have h1 : (0:ℝ) ≤ (a:ℝ) := by have := hre; rw [hc'] at this; linarith
        have h2 : (a:ℝ) < 1 := by have := hre'; rw [hc'] at this; linarith
        have hz1 : (0:ℤ) ≤ a := by exact_mod_cast h1
        have hz2 : a < 1 := by exact_mod_cast h2
        omega
      · have hc' : ζ.re = (a:ℝ)/(-2) := by rw [hζre_eq, h]; norm_num
        have h1 : (a:ℝ) ≤ 0 := by have := hre; rw [hc'] at this; linarith
        have h2 : (-1:ℝ) < (a:ℝ) := by have := hre'; rw [hc'] at this; linarith
        have hz1 : a ≤ 0 := by exact_mod_cast h1
        have hz2 : (-1:ℤ) < a := by exact_mod_cast h2
        omega
    rw [ha0] at hdet
    rcases hc2 with h | h <;> rw [h] at hdet <;> omega
  · -- `c² ≠ 4`: exclude `c = 0` and conclude `c = ±1`.
    have hc_ne0 : c ≠ 0 := by
      intro hc0
      have had : a * d = 1 := by rw [hc0] at hdet; linarith
      have had1 : (a = 1 ∧ d = 1) ∨ (a = -1 ∧ d = -1) := by
        rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
      have hζm : (ζ:ℂ) = (τ:ℂ) + ((d*b:ℤ):ℂ) := by
        rw [hcoe, hc0]
        simp only [Int.cast_zero, zero_mul, zero_add]
        rcases had1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; push_cast; ring
        · rw [h1, h2]; push_cast; ring
      have hre_eq : ζ.re = τ.re + ((d*b:ℤ):ℝ) := by
        have h := congrArg Complex.re hζm
        rw [Complex.add_re, UpperHalfPlane.coe_re] at h
        have hc' : ((d*b:ℤ):ℂ).re = ((d*b:ℤ):ℝ) := by push_cast; simp
        rw [hc'] at h
        exact h
      rcases hxcase with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
      · have h1 : (-(5:ℝ)/8) ≤ ((d*b:ℤ):ℝ) := by linarith [hre_eq, hre, hx2]
        have h2 : ((d*b:ℤ):ℝ) ≤ (-(1:ℝ)/8) := by linarith [hre_eq, hre', hx1]
        have hz1 : (-1:ℤ) < d*b := by
          have : (-1:ℝ) < ((d*b:ℤ):ℝ) := by linarith
          exact_mod_cast this
        have hz2 : d*b < 0 := by
          have : ((d*b:ℤ):ℝ) < 0 := by linarith
          exact_mod_cast this
        omega
      · have h1 : (3:ℝ)/8 ≤ ((d*b:ℤ):ℝ) := by linarith [hre_eq, hre, hx1]
        have h2 : ((d*b:ℤ):ℝ) ≤ (7:ℝ)/8 := by linarith [hre_eq, hre', hx2]
        have hz1 : (0:ℤ) < d*b := by
          have : (0:ℝ) < ((d*b:ℤ):ℝ) := by linarith
          exact_mod_cast this
        have hz2 : d*b < 1 := by
          have : ((d*b:ℤ):ℝ) < 1 := by linarith
          exact_mod_cast this
        omega
    have hc_pm1 : c = 1 ∨ c = -1 := by
      rcases hc_le2 with h | h | h | h | h
      · exact absurd hcsq4 (by rw [h]; norm_num)
      · exact Or.inr h
      · exact absurd h hc_ne0
      · exact Or.inl h
      · exact absurd hcsq4 (by rw [h]; norm_num)
    have hcsq1 : (c:ℝ)^2 = 1 := by rcases hc_pm1 with h | h <;> rw [h] <;> norm_num
    have hcsqC : (c:ℂ)^2 = 1 := by rcases hc_pm1 with h | h <;> rw [h] <;> norm_num
    have hcabs : |(c:ℝ)| = 1 := by rcases hc_pm1 with h | h <;> rw [h] <;> norm_num
    have hden : (c:ℂ)*(τ:ℂ)+(d:ℂ) ≠ 0 := by
      intro h0
      apply hNne
      have : ((c:ℝ):ℂ)*(τ:ℂ)+((d:ℝ):ℂ) = 0 := by rw [← h0]; push_cast; ring
      rw [this]; simp
    have hζ : (ζ:ℂ) = (c:ℂ)*(a:ℂ) - 1/((τ:ℂ)+(c:ℂ)*(d:ℂ)) := by
      have hdetC : (a:ℂ)*(d:ℂ)-(b:ℂ)*(c:ℂ) = 1 := by exact_mod_cast hdet
      have hden2 : (τ:ℂ) + (c:ℂ)*(d:ℂ) ≠ 0 := by
        intro h0
        apply hden
        have key : (c:ℂ)*((τ:ℂ)+(c:ℂ)*(d:ℂ)) = (c:ℂ)*(τ:ℂ)+(d:ℂ) := by
          rw [mul_add, ← mul_assoc, ← pow_two, hcsqC, one_mul]
        rw [h0, mul_zero] at key
        exact key.symm
      have h := moebius_sub_inv (τ:ℂ) (c:ℂ) (d:ℂ) (a:ℂ) (b:ℂ) hcsqC hdetC hden hden2
      rw [hcoe, h]
    have hζre0 : ζ.re = (c:ℝ)*(a:ℝ)
        - (τ.re + (c:ℝ)*(d:ℝ))/((τ.re+(c:ℝ)*(d:ℝ))^2 + τ.im^2) := by
      have hw : ((τ:ℂ)+(c:ℂ)*(d:ℂ)).re = τ.re + (c:ℝ)*(d:ℝ) := by
        simp [Complex.add_re, Complex.mul_re, UpperHalfPlane.coe_re]
      have hwn : Complex.normSq ((τ:ℂ)+(c:ℂ)*(d:ℂ))
          = (τ.re+(c:ℝ)*(d:ℝ))^2 + τ.im^2 := by
        rw [Complex.normSq_apply, hw]
        have him2 : ((τ:ℂ)+(c:ℂ)*(d:ℂ)).im = τ.im := by
          simp [Complex.add_im, Complex.mul_im, UpperHalfPlane.coe_im]
        rw [him2]; ring
      have h1 : ((c:ℂ)*(a:ℂ)).re = (c:ℝ)*(a:ℝ) := by simp [Complex.mul_re]
      have hr := congrArg Complex.re hζ
      rw [Complex.sub_re, h1, one_div, Complex.inv_re, hw, hwn] at hr
      simpa using hr
    set u : ℝ := τ.re + (c:ℝ)*(d:ℝ) with hu
    have hrel : u = τ.re + ((c*d:ℤ):ℝ) := by rw [hu]; push_cast; ring
    have hsq_lt : ((c:ℝ)*τ.re+(d:ℝ))^2 < 1 := by
      have h1 : ((c:ℝ)*τ.re+(d:ℝ))^2 + τ.im^2 ≤ 2*τ.im := by
        have h2 : ((c:ℝ)*τ.im)^2 = τ.im^2 := by rw [mul_pow, hcsq1, one_mul]
        linarith [hF1, h2]
      nlinarith [h1, hy1, hy2]
    have hlt1 : |(c:ℝ)*τ.re+(d:ℝ)| < 1 := (sq_lt_one_iff_abs_lt_one _).mp hsq_lt
    have hcu : (c:ℝ) * u = (c:ℝ)*τ.re+(d:ℝ) := by
      rw [hu, mul_add, ← mul_assoc, ← pow_two, hcsq1, one_mul]
    have hu_abs : |u| < 1 := by
      have h2 : |(c:ℝ)*u| < 1 := by rw [hcu]; exact hlt1
      rwa [abs_mul, hcabs, one_mul] at h2
    have hmem : (3/8 ≤ u ∧ u ≤ 5/8) ∨ (-(5/8) ≤ u ∧ u ≤ -(3/8)) :=
      u_mem_of_cl hxcase hu_abs hrel
    have hu_lo : -(5/8 : ℝ) ≤ u := by rcases hmem with h | h <;> linarith [h.1]
    have hu_hi : u ≤ 5/8 := by rcases hmem with h | h <;> linarith [h.2]
    have hζre : ζ.re = ((c*a:ℤ):ℝ) - u/(u^2+τ.im^2) := by
      rw [hu, hζre0]
      push_cast
      ring
    rcases lt_trichotomy u 0 with hun | huz | hup
    · -- `u < 0`
      have hu_nhi : u ≤ -(3/8 : ℝ) := by rcases hmem with h | h <;> linarith [h.1, h.2, hun]
      have hneg := ratio_neg_cl hu_lo hu_nhi hy1 hy2
      have hca : c*a = -1 := by
        have e : ((c*a:ℤ):ℝ) = ζ.re + u/(u^2+τ.im^2) := by linarith [hζre]
        have h1 : ((c*a:ℤ):ℝ) < 0 := by linarith [e, hre', hneg.2]
        have h2 : (-1:ℝ) ≤ ((c*a:ℤ):ℝ) := by linarith [e, hre, hneg.1]
        have hz1 : c*a < 0 := by exact_mod_cast h1
        have hz2 : (-1:ℤ) ≤ c*a := by exact_mod_cast h2
        omega
      have hζre' : ζ.re = -1 - u/(u^2+τ.im^2) := by rw [hζre, hca]; push_cast; ring
      have hr_le : u/(u^2+τ.im^2) ≤ -1 := by linarith [hre, hζre']
      have hr_eq : u/(u^2+τ.im^2) = -1 := le_antisymm hr_le hneg.1
      obtain ⟨hu_eq, hY_eq⟩ := ratio_eq_neg_one hy1 hr_eq
      have hXrel : τ.re = -1/2 + ((-(c*d):ℤ):ℝ) := by
        have hh := hrel
        rw [hu_eq] at hh
        push_cast
        linarith [hh]
      have hτre : τ.re = 1/2 ∨ τ.re = -1/2 := re_half_of_int hXrel hxcase
      have hpI : (poleOne τ : ℂ) = Complex.I := poleOne_eq_I_of hY_eq hτre
      have hζI : (ζ:ℂ) = Complex.I := by
        have hcaC : (c:ℂ)*(a:ℂ) = -1 := by rw [← Int.cast_mul, hca]; norm_num
        have hrel' : u = τ.re + (c:ℝ) * (d:ℝ) := by rw [hrel]; push_cast; ring
        have htau_cd : (τ:ℂ) + (c:ℂ)*(d:ℂ) = ((-1/2:ℝ):ℂ) + ((1/2:ℝ):ℂ) * Complex.I := by
          apply Complex.ext
          · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
              Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
              UpperHalfPlane.coe_re, mul_zero, sub_zero]
            linarith [hrel', hu_eq]
          · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
              UpperHalfPlane.coe_im, mul_zero, zero_mul, add_zero]
            push_cast
            linarith [hY_eq]
        rw [hζ, hcaC, htau_cd]
        rw [show (((-1/2:ℝ):ℂ) + ((1/2:ℝ):ℂ) * Complex.I) = (Complex.I - 1)/2 by
          push_cast; ring]
        rw [one_div,
          show ((Complex.I - 1)/2 : ℂ)⁻¹ = -1 - Complex.I by
            rw [inv_eq_of_mul_eq_one_right (a := (Complex.I - 1)/2)]
            ring_nf; rw [pow_two, Complex.I_mul_I]; norm_num]
        ring
      exact UpperHalfPlane.ext (by rw [hζI, hpI])
    · -- `u = 0` is excluded because `0 ∉ [3/8,5/8] ∪ [-5/8,-3/8]`.
      rcases hmem with h | h <;> linarith [h.1, h.2, huz]
    · -- `u > 0`: the offset is `0` or `1` and the pole is `1 - 1/(τ+cd)`
      have hu_pos : 3/8 ≤ u ∧ u ≤ 5/8 := by
        rcases hmem with h | h
        · exact h
        · linarith [h.1, h.2, hup]
      have hratio := ratio_pos_cl hu_pos.1 hu_pos.2 hy1 hy2
      have hca : c*a = 1 := by
        have e : ((c*a:ℤ):ℝ) = ζ.re + u/(u^2+τ.im^2) := by linarith [hζre]
        have h1 : (1:ℝ)/4 < ((c*a:ℤ):ℝ) := by linarith [e, hre, hratio.1]
        have h2 : ((c*a:ℤ):ℝ) ≤ 5/4 := by linarith [e, hre', hratio.2]
        have hz1 : (0:ℤ) < c*a := by
          have : (0:ℝ) < ((c*a:ℤ):ℝ) := by linarith
          exact_mod_cast this
        have hz2 : c*a < 2 := by
          have : ((c*a:ℤ):ℝ) < 2 := by linarith
          exact_mod_cast this
        omega
      have hcc := cd_cases_cl_pos hxcase hu_pos hrel
      rcases hcc with ⟨hA, hm⟩ | ⟨hB, hm⟩
      · apply UpperHalfPlane.ext
        have hcaC : (c:ℂ)*(a:ℂ) = 1 := by rw [← Int.cast_mul, hca]; norm_num
        have hcdC : (c:ℂ)*(d:ℂ) = 0 := by rw [← Int.cast_mul, hm]; norm_num
        have hζv : (ζ:ℂ) = 1 - 1/(τ:ℂ) := by rw [hζ, hcaC, hcdC, add_zero]
        have hpole : (poleOne τ : ℂ) = 1 - 1/(τ:ℂ) := by
          rw [poleOne_coe, if_neg (by linarith [hA.1] : ¬ τ.re < 0)]
        rw [hζv, hpole]
      · apply UpperHalfPlane.ext
        have hcaC : (c:ℂ)*(a:ℂ) = 1 := by rw [← Int.cast_mul, hca]; norm_num
        have hcdC : (c:ℂ)*(d:ℂ) = 1 := by rw [← Int.cast_mul, hm]; norm_num
        have hne : (τ:ℂ) + 1 ≠ 0 := by
          intro h
          have h1 : (τ:ℂ) = -1 := by linear_combination h
          have h2 : (τ:ℂ).im = 0 := by rw [h1]; simp
          rw [UpperHalfPlane.coe_im] at h2
          linarith [τ.im_pos]
        have hζv : (ζ:ℂ) = (τ:ℂ)/(1+(τ:ℂ)) := by
          rw [hζ, hcaC, hcdC, add_comm (1:ℂ) (τ:ℂ)]
          field_simp
          ring
        have hpole : (poleOne τ : ℂ) = (τ:ℂ)/(1+(τ:ℂ)) := by
          rw [poleOne_coe, if_pos (by linarith [hB.2] : τ.re < 0)]
        rw [hζv, hpole]

end

end Work.Asymptotics.HalfFunnel
