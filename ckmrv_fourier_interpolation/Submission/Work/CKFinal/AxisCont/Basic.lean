/-
# Geometry of the imaginary axis for the continuity of the CKMRV layer

Shared, elementary inputs for the continuity of the CKMRV layer `paperLayer` across the
imaginary axis.

* `Work.CKFinal.imagAxis_*` and `Work.CKFinal.eq_imagAxis_of_re_eq_zero` — the point `i y` of
  `ℍ` described by its real and imaginary parts;
* `Work.CKFinal.ball_imagAxis_subset_DomainD` — a small hyperbolic ball around an axis point
  `i y` lies in the CKMRV fundamental domain `𝒟`; the three quantitative hypotheses `h₁ h₂ h₃`
  on `δ = y (e^ρ - 1)` are easily met, e.g. by `ρ ≤ min (y/8) (Real.log (1 + 1/y) / 2)`;
* `Work.CKFinal.eq_or_inv_of_jInvariantFun_eq_imagAxis` — **the classification of the
  coincidences of the contour with the orbit of a point of `𝒟`**: if `τ ∈ 𝒟` and the contour
  point `i t` has the same `j`-invariant as `τ`, then `τ` is on the axis and `t = Im τ` or
  `t · Im τ = 1` (the two orbit points `i y` and `S • (i y) = i/y` of an axis point);
* `Work.CKFinal.jInvariantFun_ne_imagAxis_of_re_ne_zero` — points of `𝒟` off the axis are
  *clean*: their orbit misses the contour;
* `Work.CKFinal.finite_coincidenceSet_imagAxis` — the coincidence set of a point of `𝒟` with the
  contour has at most two elements.  The last two are the inputs of the a.e.-continuity of the
  contour integrand in `τ`.
-/
import Mathlib
import Submission.Work.CKFinal.U0Defs
import Submission.Work.Asymptotics.Kaxis_tile_aux
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis

noncomputable section

namespace Work.CKFinal

open UpperHalfPlane Work.Kernels

/-! ## The point `i y` of the imaginary axis -/

lemma imagAxis_coe_eq (y : ℝ) (hy : 0 < y) :
    ((Work.Kernels.imagAxis y hy : ℍ) : ℂ) = (y : ℂ) * Complex.I := rfl

@[simp] lemma imagAxis_im_eq (y : ℝ) (hy : 0 < y) : (Work.Kernels.imagAxis y hy).im = y := by
  rw [← UpperHalfPlane.coe_im, imagAxis_coe_eq]
  simp

@[simp] lemma imagAxis_re_eq (y : ℝ) (hy : 0 < y) : (Work.Kernels.imagAxis y hy).re = 0 := by
  rw [← UpperHalfPlane.coe_re, imagAxis_coe_eq]
  simp

lemma imagAxis_re_coe (y : ℝ) (hy : 0 < y) :
    ((Work.Kernels.imagAxis y hy : ℍ) : ℂ).re = 0 := by
  rw [UpperHalfPlane.coe_re, imagAxis_re_eq]

lemma eq_imagAxis_of_re_eq_zero {z : ℍ} (hz : (z : ℂ).re = 0) :
    z = Work.Kernels.imagAxis z.im z.im_pos := by
  apply UpperHalfPlane.ext
  show (z : ℂ) = (z.im : ℂ) * Complex.I
  have h := Complex.re_add_im (z : ℂ)
  rw [hz, UpperHalfPlane.coe_im] at h
  rw [← h]
  simp

lemma norm_imagAxis_sub_imagAxis (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - ((Work.Kernels.imagAxis s hs : ℍ) : ℂ)‖
      = |t - s| := by
  rw [imagAxis_coe_eq, imagAxis_coe_eq]
  have h : (t : ℂ) * Complex.I - (s : ℂ) * Complex.I = ((t - s : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- `S • (i y) = i / y`: the second orbit point of `i y` on the imaginary axis. -/
lemma S_smul_imagAxis_ac (y : ℝ) (hy : 0 < y) :
    ModularGroup.S • Work.Kernels.imagAxis y hy
      = Work.Kernels.imagAxis y⁻¹ (inv_pos.mpr hy) := by
  rw [UpperHalfPlane.modular_S_smul]
  apply UpperHalfPlane.ext
  show (-((Work.Kernels.imagAxis y hy : ℍ) : ℂ))⁻¹
    = ((Work.Kernels.imagAxis y⁻¹ (inv_pos.mpr hy) : ℍ) : ℂ)
  rw [imagAxis_coe_eq, imagAxis_coe_eq, Complex.ofReal_inv, inv_neg, mul_inv, Complex.inv_I]
  ring

/-- `j (i / y) = j (i y)`. -/
lemma jInvariantFun_imagAxis_inv (y : ℝ) (hy : 0 < y) :
    Work.Kernels.jInvariantFun (Work.Kernels.imagAxis y⁻¹ (inv_pos.mpr hy))
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis y hy) := by
  rw [← S_smul_imagAxis_ac y hy, Work.Kernels.KernelFacts.jInvariantFun_S_smul]

/-! ## A small hyperbolic ball around `i y` lies in `𝒟` -/

/-- If a point of `ℍ` lies in one of the two discs `|z ∓ 1/2| ≤ 1/2`, then
`(Im z)² ≤ |Re z|`. -/
private lemma im_sq_le_abs_re_of_mem_disc {τ : ℍ}
    (h : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ≤ 1 / 2 ∨ ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ≤ 1 / 2) :
    τ.im ^ 2 ≤ |τ.re| := by
  have key : τ.re ^ 2 + τ.im ^ 2 ≤ |τ.re| := by
    rcases h with h | h
    · have hns : (τ.re - 1 / 2) ^ 2 + τ.im ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        have h2 : Complex.normSq ((τ : ℂ) - (1 / 2 : ℂ)) ≤ (1 / 2 : ℝ) ^ 2 := by
          rw [Complex.normSq_eq_norm_sq]
          nlinarith [h, norm_nonneg ((τ : ℂ) - (1 / 2 : ℂ))]
        rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re,
          UpperHalfPlane.coe_im] at h2
        norm_num at h2 ⊢
        simpa only [sq] using h2
      nlinarith [hns, le_abs_self τ.re]
    · have hns : (τ.re + 1 / 2) ^ 2 + τ.im ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        have h2 : Complex.normSq ((τ : ℂ) + (1 / 2 : ℂ)) ≤ (1 / 2 : ℝ) ^ 2 := by
          rw [Complex.normSq_eq_norm_sq]
          nlinarith [h, norm_nonneg ((τ : ℂ) + (1 / 2 : ℂ))]
        rw [Complex.normSq_apply, Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re,
          UpperHalfPlane.coe_im] at h2
        norm_num at h2 ⊢
        simpa only [sq] using h2
      nlinarith [hns, neg_le_abs τ.re]
  nlinarith [key, sq_nonneg τ.re]

/-- **A hyperbolic ball around an axis point, inside `𝒟`.**  On `Metric.ball (i y) ρ` one has
`‖τ - i y‖ ≤ y (e^ρ - 1)` (`UpperHalfPlane.dist_coe_le`); writing `δ = y (e^ρ - 1)`, the
hypotheses say `δ ≤ y/4`, `δ < 1` and `δ ≤ y²/4`.  A point `τ` of the ball outside `𝒟` either has
`|Re τ| ≥ 1` (impossible since `|Re τ| ≤ δ < 1`), or lies in one of the two discs
`|τ ∓ 1/2| ≤ 1/2`, whence `Im²τ ≤ |Re τ| ≤ δ`; but `Re τ` is within `δ` of `0` and `Im τ` is
within `δ` of `y`, so `Im τ ≥ y - δ ≥ 3y/4` and `9y²/16 ≤ Im²τ ≤ δ ≤ y²/4`, a contradiction. -/
theorem ball_imagAxis_subset_DomainD {y ρ : ℝ} (hy : 0 < y)
    (h₁ : y * (Real.exp ρ - 1) ≤ y / 4) (h₂ : y * (Real.exp ρ - 1) < 1)
    (h₃ : y * (Real.exp ρ - 1) ≤ y ^ 2 / 4) :
    Metric.ball (Work.Kernels.imagAxis y hy) ρ ⊆ Work.Asymptotics.DomainD := by
  intro τ hτ
  rw [Metric.mem_ball] at hτ
  set δ : ℝ := y * (Real.exp ρ - 1) with hδdef
  have hΔ : ‖(τ : ℂ) - ((Work.Kernels.imagAxis y hy : ℍ) : ℂ)‖ ≤ δ := by
    have h := UpperHalfPlane.dist_coe_le τ (Work.Kernels.imagAxis y hy)
    rw [imagAxis_im_eq y hy] at h
    have hexp : Real.exp (dist τ (Work.Kernels.imagAxis y hy)) ≤ Real.exp ρ :=
      Real.exp_le_exp.mpr hτ.le
    have h2 : y * (Real.exp (dist τ (Work.Kernels.imagAxis y hy)) - 1) ≤ δ := by
      rw [hδdef]
      exact mul_le_mul_of_nonneg_left (by linarith) hy.le
    calc ‖(τ : ℂ) - ((Work.Kernels.imagAxis y hy : ℍ) : ℂ)‖
        = dist (τ : ℂ) ((Work.Kernels.imagAxis y hy : ℍ) : ℂ) := by rw [dist_eq_norm]
      _ ≤ y * (Real.exp (dist τ (Work.Kernels.imagAxis y hy)) - 1) := h
      _ ≤ δ := h2
  have hx : |τ.re| ≤ δ := by
    have h1 := Complex.abs_re_le_norm ((τ : ℂ) - ((Work.Kernels.imagAxis y hy : ℍ) : ℂ))
    simp only [Complex.sub_re, UpperHalfPlane.coe_re] at h1
    rw [imagAxis_re_eq y hy, sub_zero] at h1
    exact le_trans h1 hΔ
  have hyim : y - δ ≤ τ.im := by
    have h1 := Complex.abs_im_le_norm ((τ : ℂ) - ((Work.Kernels.imagAxis y hy : ℍ) : ℂ))
    simp only [Complex.sub_im, UpperHalfPlane.coe_im] at h1
    rw [imagAxis_im_eq y hy] at h1
    have h2 : |τ.im - y| ≤ δ := le_trans h1 hΔ
    rw [abs_le] at h2
    linarith [h2.1]
  have hstr : -1 < τ.re ∧ τ.re < 1 := by
    have h := abs_le.mp hx
    exact ⟨by linarith [h.1, h₂], by linarith [h.2, h₂]⟩
  rw [Work.Asymptotics.mem_DomainD]
  refine ⟨hstr.1, hstr.2, ?_, ?_⟩
  · by_contra hcon
    have hy2 : τ.im ^ 2 ≤ δ :=
      le_trans (im_sq_le_abs_re_of_mem_disc (Or.inl (not_lt.mp hcon))) hx
    have h34 : 3 * y / 4 ≤ τ.im := by linarith
    have hsq : (3 * y / 4) ^ 2 ≤ τ.im ^ 2 := pow_le_pow_left₀ (by linarith) h34 2
    nlinarith [hsq, hy2, h₃, hy]
  · by_contra hcon
    have hy2 : τ.im ^ 2 ≤ δ :=
      le_trans (im_sq_le_abs_re_of_mem_disc (Or.inr (not_lt.mp hcon))) hx
    have h34 : 3 * y / 4 ≤ τ.im := by linarith
    have hsq : (3 * y / 4) ^ 2 ≤ τ.im ^ 2 := pow_le_pow_left₀ (by linarith) h34 2
    nlinarith [hsq, hy2, h₃, hy]

/-- A convenient explicit radius for `Work.CKFinal.ball_imagAxis_subset_DomainD`: with
`ρ ≤ axisRadius y` (and `y > 0`) the ball `Metric.ball (i y) ρ` lies in `𝒟`. -/
def axisRadius (y : ℝ) : ℝ :=
  min (1 / 8) (min (y / 8) (min (Real.log (5 / 4)) (Real.log (1 + 1 / y) / 2)))

lemma axisRadius_pos {y : ℝ} (hy : 0 < y) : 0 < axisRadius y := by
  have h1 : (0 : ℝ) < 1 / 8 := by norm_num
  have h2 : (0 : ℝ) < y / 8 := by linarith
  have h3 : (0 : ℝ) < Real.log (5 / 4) := Real.log_pos (by norm_num)
  have h4 : (0 : ℝ) < Real.log (1 + 1 / y) / 2 := by
    refine div_pos ?_ (by norm_num)
    exact Real.log_pos (by rw [lt_add_iff_pos_right]; exact div_pos one_pos hy)
  unfold axisRadius
  exact lt_min h1 (lt_min h2 (lt_min h3 h4))

lemma exp_sub_one_le_two_mul {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ 1) :
    Real.exp ρ - 1 ≤ 2 * ρ := by
  have h : |Real.exp ρ - 1| ≤ 2 * ρ := by
    have h0 := Real.abs_exp_sub_one_le (x := ρ) (by rw [abs_of_pos hρ0]; linarith)
    rwa [abs_of_pos hρ0] at h0
  rwa [abs_of_nonneg (by linarith [Real.one_le_exp hρ0.le])] at h

theorem ball_imagAxis_subset_DomainD_radius {y ρ : ℝ} (hy : 0 < y) (hρ0 : 0 < ρ)
    (hρ : ρ ≤ axisRadius y) :
    Metric.ball (Work.Kernels.imagAxis y hy) ρ ⊆ Work.Asymptotics.DomainD := by
  have hρ1 : ρ ≤ 1 / 8 := le_trans hρ (min_le_left _ _)
  have hρ2 : ρ ≤ y / 8 := le_trans hρ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ3 : ρ ≤ Real.log (5 / 4) :=
    le_trans hρ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hρ4 : ρ ≤ Real.log (1 + 1 / y) / 2 :=
    le_trans hρ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hlogpos : 0 < Real.log (1 + 1 / y) :=
    Real.log_pos (by rw [lt_add_iff_pos_right]; exact div_pos one_pos hy)
  have h₁ : y * (Real.exp ρ - 1) ≤ y / 4 := by
    have h1 : Real.exp ρ - 1 ≤ 1 / 4 := by
      have h2 : Real.exp ρ ≤ Real.exp (Real.log (5 / 4)) := Real.exp_le_exp.mpr hρ3
      rw [Real.exp_log (by norm_num)] at h2
      linarith
    nlinarith [hy, h1]
  have h₂ : y * (Real.exp ρ - 1) < 1 := by
    have hlt : ρ < Real.log (1 + 1 / y) := by linarith
    have h1 : Real.exp ρ - 1 < 1 / y := by
      have h2 : Real.exp ρ < Real.exp (Real.log (1 + 1 / y)) := Real.exp_lt_exp.mpr hlt
      rw [Real.exp_log (by positivity)] at h2
      linarith
    have h3 : y * (Real.exp ρ - 1) < y * (1 / y) := mul_lt_mul_of_pos_left h1 hy
    rwa [mul_one_div, div_self (ne_of_gt hy)] at h3
  have h₃ : y * (Real.exp ρ - 1) ≤ y ^ 2 / 4 := by
    have h1 : Real.exp ρ - 1 ≤ y / 4 := by
      have h2 := exp_sub_one_le_two_mul hρ0 (by linarith [hρ1])
      linarith [hρ2]
    nlinarith [hy, h1]
  exact ball_imagAxis_subset_DomainD hy h₁ h₂ h₃

/-! ## The classification of the coincidences with the contour -/

/-- **The coincidences of the contour with the orbit of a point of `𝒟`.**  If `τ ∈ 𝒟` and
`j τ = j (i t)` for some `t > 0`, then `τ` lies on the imaginary axis and `t` is one of its two
orbit points `Im τ` and `1 / Im τ`: the classification `eq_or_eq_S_of_re_eq_zero'` gives
`i t = τ` or `i t = S • τ`, and `S • τ = i / Im τ` for `τ = i Im τ`. -/
theorem eq_or_inv_of_jInvariantFun_eq_imagAxis {τ : ℍ} (hτ : τ ∈ Work.Asymptotics.DomainD)
    {t : ℝ} (ht : 0 < t)
    (h : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    τ.re = 0 ∧ (t = τ.im ∨ t * τ.im = 1) := by
  rcases Work.Asymptotics.eq_or_eq_S_of_re_eq_zero' hτ (imagAxis_re_coe t ht) h with h' | h'
  · have hre : τ.re = 0 := by
      rw [← h', ← UpperHalfPlane.coe_re]
      exact imagAxis_re_coe t ht
    refine ⟨hre, Or.inl ?_⟩
    have him : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ).im = t := by
      rw [imagAxis_coe_eq]
      simp
    rw [h'] at him
    rw [UpperHalfPlane.coe_im] at him
    exact him.symm
  · have hre : τ.re = 0 := by
      refine Work.Asymptotics.orbit_imagAxis_of_mem_DomainD τ hτ ModularGroup.S ?_
      rw [← h']
      exact imagAxis_re_coe t ht
    refine ⟨hre, Or.inr ?_⟩
    have hτc : (τ : ℂ) = (τ.im : ℂ) * Complex.I := by
      have h1 : (τ : ℂ).re = 0 := by rw [UpperHalfPlane.coe_re]; exact hre
      have h2 := Complex.re_add_im (τ : ℂ)
      have h3 : (((τ : ℂ).re : ℝ) : ℂ) = 0 := by rw [h1]; simp
      rw [h3, zero_add] at h2
      rw [UpperHalfPlane.coe_im] at h2
      exact h2.symm
    have hSc : ((ModularGroup.S • τ : ℍ) : ℂ) = ((τ.im : ℂ))⁻¹ * Complex.I := by
      rw [UpperHalfPlane.modular_S_smul]
      show (-(((τ : ℍ) : ℂ)))⁻¹ = ((τ.im : ℂ))⁻¹ * Complex.I
      rw [hτc, inv_neg, mul_inv, Complex.inv_I]
      ring
    have hcoe : (t : ℂ) * Complex.I = ((τ.im : ℂ))⁻¹ * Complex.I := by
      rw [← imagAxis_coe_eq t ht, h', hSc]
    have ht' : (t : ℂ) = ((τ.im : ℂ))⁻¹ := mul_right_cancel₀ Complex.I_ne_zero hcoe
    have ht'' : t = (τ.im)⁻¹ := Complex.ofReal_inj.mp (by simpa using ht')
    rw [ht'', inv_mul_cancel₀ (ne_of_gt τ.im_pos)]

/-! ## Cleanliness off the axis and finiteness of the coincidence set -/

/-- **Points of `𝒟` off the axis are clean**: the orbit of such a point misses the contour. -/
theorem jInvariantFun_ne_imagAxis_of_re_ne_zero {τ : ℍ} (hτ : τ ∈ Work.Asymptotics.DomainD)
    (hre : τ.re ≠ 0) (t : ℝ) (ht : 0 < t) :
    Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro h
  exact hre (eq_or_inv_of_jInvariantFun_eq_imagAxis hτ ht h).1

/-- **The coincidence set of a point of `𝒟` with the contour is finite** (at most the two orbit
points `i Im τ` and `i / Im τ`). -/
theorem finite_coincidenceSet_imagAxis {τ : ℍ} (hτ : τ ∈ Work.Asymptotics.DomainD) :
    ∃ S : Set ℝ, S.Finite ∧ ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        t ∈ S := by
  by_cases hre : τ.re = 0
  · refine ⟨{(τ.im)⁻¹, τ.im}, (Set.finite_singleton _).insert _, ?_⟩
    intro t ht h
    obtain ⟨-, h'⟩ := eq_or_inv_of_jInvariantFun_eq_imagAxis hτ ht h
    rcases h' with h' | h'
    · exact Set.mem_insert_iff.mpr (Or.inr h')
    · refine Set.mem_insert_iff.mpr (Or.inl ?_)
      have hcomm : τ.im * t = 1 := by rw [mul_comm]; exact h'
      exact eq_inv_of_mul_eq_one_right hcomm
  · exact ⟨∅, Set.finite_empty, fun t ht h =>
      absurd (eq_or_inv_of_jInvariantFun_eq_imagAxis hτ ht h).1 hre⟩

end Work.CKFinal
