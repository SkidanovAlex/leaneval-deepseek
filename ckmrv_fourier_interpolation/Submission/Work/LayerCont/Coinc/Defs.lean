/-
# The removable coincidence `ST⁻¹τ` as a point of `ℂ`

CKMRV §5.3 compares the kernel `K(τ,·)` across the line `Re τ = 1`.  The obstruction to the naive
contour shift is the moving pole `z = τ - 1`, but the rectangle swept by the *left* detour at
height `t₀⁻¹ = 1/τ.im` also contains the second `SL(2,ℤ)`-translate of `τ` of that height, the
**removable coincidence**

  `ST⁻¹ τ = -1/(τ-1)`,

whose residue vanishes because `φ(TS) = 0` (`Work.LayerCont.hasResidue_Kfun_coinc`).

For `Re τ < 1` this point has *positive* real part (`Work.Asymptotics.tauCoinc_re_pos`), so it lies
strictly to the right of the axis and the left detour misses it; for `Re τ > 1` it lies strictly to
the left of the axis, inside the swept rectangle, and the left detour may be pushed through it
residue-free.  This file fixes the elementary geometry of that point:

* `coincℂ τ` is the complex number `((S • (-1 +ᵥ τ) : ℍ) : ℂ)`;
* `coincℂ_im_pos`, `ofComplex_coincℂ`;
* `coincℂ_eq : coincℂ τ = -1/((τ:ℂ) - 1)`, `coincℂ_re_eq`;
* `one_lt_re_of_coincℂ_re_neg` : a coincidence of negative real part forces `1 < τ.re` (the "far
  side" of the line);
* `ofComplex_eq_coinc_iff`, `imagAxis_ne_coinc`, `imagAxis_ne_smul_neg_one_vadd` : the invariance of
  the coincidence, in the two forms in which the far-side cleanliness arguments need it.
-/
import Mathlib
import Submission.Work.LayerCont.CoincResidue
import Submission.Work.Asymptotics.kerFormAux

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle
open Filter
open scoped Topology

namespace Work.LayerCont.Coinc

open Work.Kernels Work.Asymptotics

/-- **The removable coincidence `ST⁻¹ τ = -1/(τ-1)` as a point of `ℂ`.**

This is the point `ModularGroup.S • ((-1 : ℝ) +ᵥ τ) = (S T⁻¹) • τ` of `ℍ`, read in `ℂ`; the
kernel `z ↦ K^{(d)}(τ,z)` has a *removable* singularity there (`φ(TS) = 0`, see
`Work.LayerCont.hasResidue_Kfun_coinc`). -/
def coincℂ (τ : UpperHalfPlane) : ℂ :=
  ((ModularGroup.S • ((-1 : ℝ) +ᵥ τ) : UpperHalfPlane) : ℂ)

lemma coincℂ_re (τ : UpperHalfPlane) :
    (coincℂ τ).re = (ModularGroup.S • ((-1 : ℝ) +ᵥ τ) : UpperHalfPlane).re := rfl

lemma coincℂ_im (τ : UpperHalfPlane) :
    (coincℂ τ).im = (ModularGroup.S • ((-1 : ℝ) +ᵥ τ) : UpperHalfPlane).im := rfl

/-- The coincidence lies in the upper half plane. -/
lemma coincℂ_im_pos (τ : UpperHalfPlane) : 0 < (coincℂ τ).im := by
  rw [coincℂ_im]
  exact (ModularGroup.S • ((-1 : ℝ) +ᵥ τ) : UpperHalfPlane).im_pos

/-- `ofComplex` of `coincℂ τ` is the coincidence point of `ℍ`. -/
lemma ofComplex_coincℂ (τ : UpperHalfPlane) :
    UpperHalfPlane.ofComplex (coincℂ τ) = ModularGroup.S • ((-1 : ℝ) +ᵥ τ) := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (coincℂ_im_pos τ)]
  rfl

@[simp] lemma ofComplex_coincℂ' (τ : UpperHalfPlane) :
    UpperHalfPlane.ofComplex (coincℂ τ) = ModularGroup.S • ((-1 : ℝ) +ᵥ τ) :=
  ofComplex_coincℂ τ

/-- The coincidence is the `(S T⁻¹)`-translate of `τ`. -/
lemma coincℂ_eq_smul (τ : UpperHalfPlane) :
    coincℂ τ = (((ModularGroup.S * ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ :
      UpperHalfPlane) : ℂ) := by
  show ((ModularGroup.S • ((-1 : ℝ) +ᵥ τ) : UpperHalfPlane) : ℂ) = _
  rw [Work.LayerCont.coinc_eq]

/-- The explicit value `coincℂ τ = -1/(τ - 1)`. -/
lemma coincℂ_eq (τ : UpperHalfPlane) : coincℂ τ = -1 / ((τ : ℂ) - 1) := by
  rw [coincℂ_eq_smul]
  exact Work.Asymptotics.tauCoinc_coe τ

/-- The point `τ - 1` is never `0`, so the denominator of `coincℂ` is invertible. -/
lemma tau_sub_one_ne_zero (τ : UpperHalfPlane) : (τ : ℂ) - 1 ≠ 0 := by
  intro h0
  have h1 : (τ : ℂ) = 1 := sub_eq_zero.mp h0
  have h2 : τ.im = 0 := by rw [← UpperHalfPlane.coe_im, h1]; simp
  exact absurd h2 (ne_of_gt τ.im_pos)

lemma norm_tau_sub_one_pos (τ : UpperHalfPlane) : 0 < ‖(τ : ℂ) - 1‖ ^ 2 :=
  pow_pos (norm_pos_iff.mpr (tau_sub_one_ne_zero τ)) 2

/-- The real part of the coincidence, explicitly.  In particular the coincidence lies off the
imaginary axis exactly when `τ.re ≠ 1`, and to its left exactly when `1 < τ.re`. -/
lemma coincℂ_re_eq (τ : UpperHalfPlane) :
    (coincℂ τ).re = (1 - τ.re) / ‖(τ : ℂ) - 1‖ ^ 2 := by
  have hne : (τ : ℂ) - 1 ≠ 0 := tau_sub_one_ne_zero τ
  rw [coincℂ_eq,
    show (-1 : ℂ) / ((τ : ℂ) - 1) = -(((τ : ℂ) - 1)⁻¹) by rw [inv_eq_one_div, neg_div],
    Complex.neg_re, Complex.inv_re, show ((τ : ℂ) - 1).re = τ.re - 1 by simp,
    ← Complex.sq_norm,
    show -((τ.re - 1) / ‖(τ : ℂ) - 1‖ ^ 2) = (1 - τ.re) / ‖(τ : ℂ) - 1‖ ^ 2 by ring]

/-- **A coincidence of strictly negative real part forces `1 < τ.re`.**  This is the "far side"
of the line `Re τ = 1`: there the swept left rectangle at height `t₀⁻¹` genuinely meets the
removable coincidence. -/
lemma one_lt_re_of_coincℂ_re_neg (τ : UpperHalfPlane) (h : (coincℂ τ).re < 0) : 1 < τ.re := by
  rw [coincℂ_re_eq] at h
  have hpos := norm_tau_sub_one_pos τ
  rw [div_neg_iff] at h
  rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact absurd h2 (not_lt.mpr (le_of_lt hpos))
  · linarith

lemma coincℂ_re_ne_zero_of_ne_one (τ : UpperHalfPlane) (h : τ.re ≠ 1) :
    (coincℂ τ).re ≠ 0 := by
  rw [coincℂ_re_eq]
  have hpos := norm_tau_sub_one_pos τ
  exact div_ne_zero (sub_ne_zero.mpr (Ne.symm h)) (ne_of_gt hpos)

/-- The imaginary part of the coincidence, explicitly: `(coincℂ τ).im = τ.im / ‖τ-1‖²`.  Together
with `coincℂ_re_eq` this is what a caller needs in order to *discharge* the hypothesis `hcoinc`
(that the coincidence lies in the open left rectangle at height `t₀⁻¹`). -/
lemma coincℂ_im_eq (τ : UpperHalfPlane) :
    (coincℂ τ).im = τ.im / ‖(τ : ℂ) - 1‖ ^ 2 := by
  have hne : (τ : ℂ) - 1 ≠ 0 := tau_sub_one_ne_zero τ
  rw [coincℂ_eq,
    show (-1 : ℂ) / ((τ : ℂ) - 1) = -(((τ : ℂ) - 1)⁻¹) by rw [inv_eq_one_div, neg_div],
    Complex.neg_im, Complex.inv_im, show ((τ : ℂ) - 1).im = τ.im by simp, ← Complex.sq_norm,
    show -(-τ.im / ‖(τ : ℂ) - 1‖ ^ 2) = τ.im / ‖(τ : ℂ) - 1‖ ^ 2 by ring]

/-- The coincidence is `((S T⁻¹) • τ : ℍ)` read in `ℂ`, in the `tauCoinc` spelling of
`Submission/Work/Asymptotics/contourLeftDefs.lean`. -/
lemma coincℂ_eq_tauCoinc_coe (τ : UpperHalfPlane) :
    coincℂ τ = ((Work.Asymptotics.tauCoinc τ : UpperHalfPlane) : ℂ) := by
  rw [Work.Asymptotics.tauCoinc]
  exact coincℂ_eq_smul τ

/-- **Membership of the coincidence in the open left rectangle**, in terms of the explicit real and
imaginary parts.  This is the shape in which a caller discharges the hypothesis `hcoinc` of the
far-side detour/layer lemmas. -/
lemma coincℂ_mem_openLeftRectℂ_iff (τ : UpperHalfPlane) (c A ξ : ℝ) :
    coincℂ τ ∈ Work.Asymptotics.openLeftRectℂ c A ξ ↔
      -ξ < (1 - τ.re) / ‖(τ : ℂ) - 1‖ ^ 2 ∧
      (1 - τ.re) / ‖(τ : ℂ) - 1‖ ^ 2 < 0 ∧
      c - A < τ.im / ‖(τ : ℂ) - 1‖ ^ 2 ∧
      τ.im / ‖(τ : ℂ) - 1‖ ^ 2 < c + A := by
  simp only [Work.Asymptotics.openLeftRectℂ, Set.mem_ofPred_eq, coincℂ_re_eq, coincℂ_im_eq]

/-- **Membership of the coincidence in the open left rectangle, cleared of denominators.**  The
denominator `‖τ-1‖²` is positive (`Work.LayerCont.Coinc.norm_tau_sub_one_pos`), so each of the four
inequalities can be multiplied out — the form used together with estimates on `‖τ-1‖²`. -/
lemma coincℂ_mem_openLeftRectℂ_iff_mul (τ : UpperHalfPlane) (c A ξ : ℝ) :
    coincℂ τ ∈ Work.Asymptotics.openLeftRectℂ c A ξ ↔
      -ξ * ‖(τ : ℂ) - 1‖ ^ 2 < 1 - τ.re ∧
      1 - τ.re < 0 ∧
      (c - A) * ‖(τ : ℂ) - 1‖ ^ 2 < τ.im ∧
      τ.im < (c + A) * ‖(τ : ℂ) - 1‖ ^ 2 := by
  rw [coincℂ_mem_openLeftRectℂ_iff]
  have hpos := norm_tau_sub_one_pos τ
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rw [lt_div_iff₀ hpos] at h1
    rw [lt_div_iff₀ hpos] at h3
    rw [div_lt_iff₀ hpos] at h4
    have h2' : 1 - τ.re < 0 := by
      rw [div_neg_iff] at h2
      rcases h2 with ⟨_, h⟩ | ⟨h, _⟩
      · exact absurd h (not_lt.mpr (le_of_lt hpos))
      · exact h
    exact ⟨h1, h2', h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [lt_div_iff₀ hpos]; exact h1
    · rw [div_neg_iff]; exact Or.inr ⟨h2, hpos⟩
    · rw [lt_div_iff₀ hpos]; exact h3
    · rw [div_lt_iff₀ hpos]; exact h4

/-- A point of `ℍ` of the shape `S • (-1 +ᵥ τ)` is a coincidence: the translation of
`ofComplex_coincℂ` into an `iff` on `ℂ`. -/
lemma ofComplex_eq_coinc_iff {τ : UpperHalfPlane} {z : ℂ} (hz : 0 < z.im) :
    UpperHalfPlane.ofComplex z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ) ↔ z = coincℂ τ := by
  constructor
  · intro h
    have hcoe : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz, UpperHalfPlane.coe_mk]
    rw [← hcoe, h]
    rfl
  · intro h
    rw [h, ofComplex_coincℂ]

lemma imagAxis_re (t : ℝ) (ht : 0 < t) : (Work.Kernels.imagAxis t ht).re = 0 := by
  simp [Work.Kernels.imagAxis]

lemma imagAxis_im (t : ℝ) (ht : 0 < t) : (Work.Kernels.imagAxis t ht).im = t := by
  simp [Work.Kernels.imagAxis]

lemma imagAxis_coe (t : ℝ) (ht : 0 < t) :
    ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := rfl

/-- The imaginary-axis point `i t` is never the coincidence when the coincidence is off the
imaginary axis. -/
lemma imagAxis_ne_coinc {τ : UpperHalfPlane} (h : (coincℂ τ).re < 0)
    (t : ℝ) (ht : 0 < t) :
    ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) ≠ coincℂ τ := by
  intro heq
  have h0 : (coincℂ τ).re = 0 := by
    rw [← heq, imagAxis_coe]
    simp
  linarith

/-- The corresponding statement for the `ℍ`-valued coincidence: `i t ≠ S • (-1 +ᵥ τ)`.  This is
the form in which the far-side cleanliness of the coincidence interval `I₂` is derived from the
orbit-exclusion hypothesis. -/
lemma imagAxis_ne_smul_neg_one_vadd {τ : UpperHalfPlane} (h : (coincℂ τ).re < 0)
    (t : ℝ) (ht : 0 < t) :
    Work.Kernels.imagAxis t ht ≠ ModularGroup.S • ((-1 : ℝ) +ᵥ τ) := by
  intro heq
  have h0 : (coincℂ τ).re = 0 := by
    have hre : (Work.Kernels.imagAxis t ht).re
        = (ModularGroup.S • ((-1 : ℝ) +ᵥ τ) : UpperHalfPlane).re := by rw [heq]
    rw [imagAxis_re t ht] at hre
    rw [coincℂ_re]
    exact hre.symm
  linarith

/-- The whole line `Re z = 0` misses the coincidence when the coincidence is off the imaginary
axis: the `re`-form used to place the coincidence in the open left rectangle. -/
lemma coincℂ_re_neg_iff (τ : UpperHalfPlane) : (coincℂ τ).re < 0 ↔ 1 < τ.re := by
  rw [coincℂ_re_eq]
  have hpos := norm_tau_sub_one_pos τ
  rw [div_neg_iff]
  constructor
  · rintro (⟨_, h2⟩ | ⟨h1, _⟩)
    · exact absurd h2 (not_lt.mpr (le_of_lt hpos))
    · linarith
  · intro h
    exact Or.inr ⟨by linarith, hpos⟩

end Work.LayerCont.Coinc
