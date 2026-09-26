/-
# The `Im ≥ 1/2` cover of the `Γ(2)`-fundamental domain `𝒟`

CKMRV (proof of Prop. 3.2, and the reduction of the contour integral (5.2) to the cusp
neighbourhoods) repeatedly need to move an arbitrary point `w ∈ 𝒟` into the part of `𝒟` living
above the line `Im z = 1/2`, using only the Möbius map `S : z ↦ -1/z` and the integer
translations `z ↦ z ± 1`.  This file proves the corresponding covering statement:

for every `w ∈ 𝒟` at least one of

* `w` itself,
* `S • w`,
* `S • ((-1) +ᵥ w) = S • (w - 1)`,
* `S • ((1) +ᵥ w)  = S • (w + 1)`

belongs to `𝒟` and has imaginary part `≥ 1/2`.

The proof is elementary plane geometry.  Write `z = x + iy = (w : ℂ)`.  The two arc conditions
of `𝒟` are the quadratic inequalities

  `x² - x + y² > 0`   (from `|z - 1/2| > 1/2`),    `x² + x + y² > 0`   (from `|z + 1/2| > 1/2`).

If `y ≥ 1/2` we are done.  Otherwise the cross-section `𝒟 ∩ {Im = y}` is the union of the three
intervals `(-1, -1/2 - r) ∪ (-1/2 + r, 1/2 - r) ∪ (1/2 + r, 1)` with `r = sqrt(1/4 - y²)`, so
`x` sits in one of the three intervals.  In the three cases `w`, `w - 1`, `w + 1` are the shifts
that lie again in `𝒟` (the middle one trivially, the outer two because `T^{∓1}` preserves `𝒟`
on the strips `±Re > 0`), and the quadratic inequalities above give, by `nlinarith`, the single
estimate

  `‖(shift)‖² ≤ 2 y`  (respectively `‖w - 1‖² ≤ 2y`, `‖w + 1‖² ≤ 2y`),

which is exactly `Im (S • shift) ≥ 1/2` because `Im (S • u) = u.im / ‖u‖²`.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.KEpsilon

set_option linter.unusedSimpArgs false

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-! ### Elementary norm estimates -/

/-- If `Re w > 1/2` then `‖w‖ > 1/2`. -/
private lemma half_lt_norm_of_re {w : ℂ} (h : (1 : ℝ) / 2 < w.re) : (1 : ℝ) / 2 < ‖w‖ := by
  have := Complex.abs_re_le_norm w
  rw [abs_of_pos (by linarith)] at this
  linarith

/-- If `Re w < -1/2` then `‖w‖ > 1/2`. -/
private lemma half_lt_norm_of_neg_re {w : ℂ} (h : w.re < -(1 : ℝ) / 2) : (1 : ℝ) / 2 < ‖w‖ := by
  have := Complex.abs_re_le_norm w
  rw [abs_of_neg (by linarith)] at this
  linarith

/-! ### The imaginary part of `S • u = -1/u` -/

/-- `S : u ↦ -1/u` has `Im (S • u) = u.im / ‖u‖²`. -/
private lemma im_S_smul (u : ℍ) :
    (ModularGroup.S • u).im = u.im / Complex.normSq (u : ℂ) := by
  rw [← UpperHalfPlane.coe_im, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
    Complex.inv_im, Complex.neg_im, Complex.normSq_neg, UpperHalfPlane.coe_im]
  ring

/-- `Im (S • u) ≥ 1/2` is equivalent to `‖u‖² ≤ 2 Im u`. -/
private lemma half_le_im_S_smul_iff (u : ℍ) :
    (1 : ℝ) / 2 ≤ (ModularGroup.S • u).im ↔ Complex.normSq (u : ℂ) ≤ 2 * u.im := by
  rw [im_S_smul]
  have hpos : (0 : ℝ) < Complex.normSq (u : ℂ) := Complex.normSq_pos.mpr u.ne_zero
  rw [le_div_iff₀ hpos]
  constructor <;> intro h <;> linarith

/-- `‖x +ᵥ u‖² = (x + Re u)² + (Im u)²` for the translation by `x : ℝ`. -/
private lemma normSq_coe_vadd (x : ℝ) (u : ℍ) :
    Complex.normSq (((x : ℝ) +ᵥ u : ℍ) : ℂ) = (x + u.re) ^ 2 + u.im ^ 2 := by
  rw [UpperHalfPlane.coe_vadd, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-! ### The two translations preserve `𝒟` on the relevant strips -/

/-- `z ↦ z - 1` maps `𝒟 ∩ {0 < Re z < 1}` into `𝒟`. -/
private lemma vadd_neg_one_mem_DomainD {w : ℍ} (hw : w ∈ DomainD) (h0 : 0 < w.re)
    (h1 : w.re < 1) : ((-1 : ℝ) +ᵥ w) ∈ DomainD := by
  rw [mem_DomainD] at hw ⊢
  obtain ⟨-, -, h3, h4⟩ := hw
  refine ⟨by rw [UpperHalfPlane.vadd_re]; linarith, by rw [UpperHalfPlane.vadd_re]; linarith,
    ?_, ?_⟩
  · have hcoe : ((((-1 : ℝ) +ᵥ w : ℍ)) : ℂ) - (1 / 2 : ℂ) = (w : ℂ) - (3 / 2 : ℂ) := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    rw [hcoe]
    apply half_lt_norm_of_neg_re
    have h32 : ((3 / 2 : ℂ)).re = (3 / 2 : ℝ) := by norm_num
    rw [Complex.sub_re, h32, UpperHalfPlane.coe_re]
    linarith
  · have hcoe : ((((-1 : ℝ) +ᵥ w : ℍ)) : ℂ) + (1 / 2 : ℂ) = (w : ℂ) - (1 / 2 : ℂ) := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    rw [hcoe]; exact h3

/-- `z ↦ z + 1` maps `𝒟 ∩ {-1 < Re z < 0}` into `𝒟`. -/
private lemma vadd_one_mem_DomainD {w : ℍ} (hw : w ∈ DomainD) (h0 : -1 < w.re)
    (h1 : w.re < 0) : ((1 : ℝ) +ᵥ w) ∈ DomainD := by
  rw [mem_DomainD] at hw ⊢
  obtain ⟨-, -, h3, h4⟩ := hw
  refine ⟨by rw [UpperHalfPlane.vadd_re]; linarith, by rw [UpperHalfPlane.vadd_re]; linarith,
    ?_, ?_⟩
  · have hcoe : ((((1 : ℝ) +ᵥ w : ℍ)) : ℂ) - (1 / 2 : ℂ) = (w : ℂ) + (1 / 2 : ℂ) := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    rw [hcoe]; exact h4
  · have hcoe : ((((1 : ℝ) +ᵥ w : ℍ)) : ℂ) + (1 / 2 : ℂ) = (w : ℂ) + (3 / 2 : ℂ) := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    rw [hcoe]
    apply half_lt_norm_of_re
    have h32 : ((3 / 2 : ℂ)).re = (3 / 2 : ℝ) := by norm_num
    rw [Complex.add_re, h32, UpperHalfPlane.coe_re]
    linarith

/-! ### The cover -/

/-- **The `Im ≥ 1/2` cover of `𝒟`.**  Every `w ∈ 𝒟` has one of `w`, `S • w`,
`S • (w - 1)`, `S • (w + 1)` lying again in `𝒟` with imaginary part `≥ 1/2`. -/
theorem DomainD_cover_half (w : UpperHalfPlane) (hw : w ∈ Work.Asymptotics.DomainD) :
    ((1 : ℝ) / 2 ≤ w.im) ∨
    (ModularGroup.S • w ∈ Work.Asymptotics.DomainD ∧ (1 : ℝ) / 2 ≤ (ModularGroup.S • w).im) ∨
    (ModularGroup.S • ((-1 : ℝ) +ᵥ w) ∈ Work.Asymptotics.DomainD ∧
      (1 : ℝ) / 2 ≤ (ModularGroup.S • ((-1 : ℝ) +ᵥ w)).im) ∨
    (ModularGroup.S • ((1 : ℝ) +ᵥ w) ∈ Work.Asymptotics.DomainD ∧
      (1 : ℝ) / 2 ≤ (ModularGroup.S • ((1 : ℝ) +ᵥ w)).im) := by
  obtain ⟨hx1, hx2, h3, h4⟩ := mem_DomainD.mp hw
  have hy0 : 0 < w.im := w.im_pos
  rcases le_or_gt ((1 : ℝ) / 2) w.im with hylarge | hysmall
  · exact Or.inl hylarge
  · -- `Im w < 1/2`: the two arc conditions as quadratic inequalities in `(Re w, Im w)`
    have h1 : w.re ^ 2 - w.re + w.im ^ 2 > 0 := by
      have h : (1 / 4 : ℝ) < Complex.normSq ((w : ℂ) - (1 / 2 : ℂ)) := by
        rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ((w : ℂ) - (1 / 2 : ℂ))]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im] at h
      norm_num at h
      nlinarith
    have h2 : w.re ^ 2 + w.re + w.im ^ 2 > 0 := by
      have h : (1 / 4 : ℝ) < Complex.normSq ((w : ℂ) + (1 / 2 : ℂ)) := by
        rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ((w : ℂ) + (1 / 2 : ℂ))]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im] at h
      norm_num at h
      nlinarith
    rcases le_or_gt w.re (1 / 2) with hxle | hxgt
    · rcases le_or_gt (-1 / 2) w.re with hxge | hxlt
      · -- middle interval: `S • w` itself
        refine Or.inr (Or.inl ⟨S_smul_mem_DomainD hw, ?_⟩)
        rw [half_le_im_S_smul_iff]
        rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        nlinarith [sq_nonneg (w.re - 1 / 2), sq_nonneg (w.re + 1 / 2)]
      · -- left interval: `S • (w + 1)`
        refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
        · exact S_smul_mem_DomainD (vadd_one_mem_DomainD hw hx1 (by linarith))
        · rw [half_le_im_S_smul_iff, normSq_coe_vadd, UpperHalfPlane.vadd_im]
          nlinarith [sq_nonneg (w.re + 1 / 2), sq_nonneg w.re]
    · -- right interval: `S • (w - 1)`
      refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
      · exact S_smul_mem_DomainD (vadd_neg_one_mem_DomainD hw (by linarith) hx2)
      · rw [half_le_im_S_smul_iff, normSq_coe_vadd, UpperHalfPlane.vadd_im]
        nlinarith [sq_nonneg (w.re - 1 / 2), sq_nonneg w.re]

end Work.Asymptotics
