import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.AsmDefs
import Submission.Work.Interfaces.Fatou

/-!
# PERT · `Work.Pert.Gates`

The elementary geometry of the two §4.2 gates, factored out of `Work.Pert.crux_compact`
so that lemmas about them can be stated and proved *without* importing `crux_compact`
(which would create a build cycle: `Work.Pert.exists_shift_waist_image` already imports
`crux_compact`).

Contents: the coordinate descriptions of the two gates, the fact that the deck translation
`Tt α = w ↦ w - 1/α` maps the upper gate *onto* the lower one (so `Qp = Qm + 1/α`), the
**waist** `Qm ξ α ∩ Qp ξ α = {z | |Re z| < |Im z| - ξ}` (nonempty only at heights `|Im z| > ξ`),
and the observation that with the (A.4.2) relation `Φm ∘ Tt α = Φp + d₁` the residual of
`crux_compact` equals `Φm (ζ - 1/α) + 1/α` at the chosen preimage `ζ ∈ Qm ∩ Qp`.
-/

namespace Work.Pert

open MandelDim Complex Set Metric

noncomputable section

/-! ## The two gates: `Tt` and the waist -/

/-- The two `Qreg`-conditions of the *upper* gate `Qp ξ α`, in coordinates. -/
theorem Qp_mem_iff {ξ : ℝ} {α z : ℂ} :
    z ∈ Qp ξ α ↔ (ξ - |z.im| < z.re ∧ z.re < (1/α).re - ξ + |z.im - (1/α).im|) := by
  unfold Qp MandelDim.Qreg
  constructor
  · rintro ⟨hA, hB⟩
    have hA2 : -|z.im| < z.re - ξ := by
      have h := hA (ξ : ℂ) (by simp)
      simpa [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im] using h
    have hB2 : z.re + ξ - (1/α).re < |z.im - (1/α).im| := by
      have h := hB (-(ξ : ℂ) + 1/α) (by simp)
      have hr : (z - (-(ξ : ℂ) + 1/α)).re = z.re + ξ - (1/α).re := by
        simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re]; ring
      have hi : (z - (-(ξ : ℂ) + 1/α)).im = z.im - (1/α).im := by
        simp only [Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.ofReal_im]; ring
      rw [hr, hi] at h; linarith
    constructor <;> linarith
  · rintro ⟨hA, hB⟩
    refine ⟨?_, ?_⟩
    · intro b hb
      rw [Option.mem_def, Option.some.injEq] at hb; subst hb
      have h : -|z.im| < z.re - ξ := by linarith
      simpa [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im] using h
    · intro b hb
      rw [Option.mem_def, Option.some.injEq] at hb; subst hb
      have h : z.re + ξ - (1/α).re < |z.im - (1/α).im| := by linarith
      have hr : (z - (-(ξ : ℂ) + 1/α)).re = z.re + ξ - (1/α).re := by
        simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re]; ring
      have hi : (z - (-(ξ : ℂ) + 1/α)).im = z.im - (1/α).im := by
        simp only [Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.ofReal_im]; ring
      rw [hr, hi]; exact h

/-- The deck translation `Tt α` maps the upper gate into the lower gate. -/
theorem Tt_mem_Qm_iff {ξ : ℝ} {α z : ℂ} : Tt α z ∈ Qm ξ α ↔ z ∈ Qp ξ α := by
  rw [Qm_mem_iff, Qp_mem_iff]
  have hr : (Tt α z).re = z.re - (1/α).re := by simp [Tt, Complex.sub_re]
  have hi : (Tt α z).im = z.im - (1/α).im := by simp [Tt, Complex.sub_im]
  rw [hr, hi, show z.im - (1/α).im + (1/α).im = z.im from sub_add_cancel _ _]
  constructor
  · intro ⟨h1, h2⟩; constructor <;> linarith
  · intro ⟨h1, h2⟩; constructor <;> linarith

/-- `Tt α '' Qp ξ α = Qm ξ α`. -/
theorem Tt_image_Qp {ξ : ℝ} {α : ℂ} : Tt α '' Qp ξ α = Qm ξ α := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩; exact Tt_mem_Qm_iff.mpr hw
  · intro hz
    refine ⟨z + 1/α, ?_, ?_⟩
    · rw [← Tt_mem_Qm_iff, show Tt α (z + 1/α) = z from by simp [Tt]]
      exact hz
    · simp [Tt]

/-- **The waist.**  In the admissible range (`InF1 α`), the two gates intersect exactly in the
symmetric horizontal window `{z | |Re z| < |Im z| - ξ}`: the intersection is nonempty only at
heights `|Im z| > ξ`. -/
theorem Qm_inter_Qp {ξ : ℝ} {α : ℂ} (hF1 : |(1/α).im| < (1/α).re) :
    Qm ξ α ∩ Qp ξ α = {z : ℂ | |z.re| < |z.im| - ξ} := by
  have hA : ∀ z : ℂ, |z.im| ≤ |z.im + (1/α).im| + (1/α).re := by
    intro z
    have h := abs_add_le (z.im + (1/α).im) (-(1/α).im)
    have h2 : z.im + (1/α).im + -(1/α).im = z.im := by ring
    rw [h2, abs_neg] at h; linarith
  have hB : ∀ z : ℂ, |z.im| ≤ (1/α).re + |z.im - (1/α).im| := by
    intro z
    have h := abs_add_le (z.im - (1/α).im) ((1/α).im)
    have h2 : z.im - (1/α).im + (1/α).im = z.im := by ring
    rw [h2] at h; linarith
  ext z
  rw [Set.mem_inter_iff, Qm_mem_iff, Qp_mem_iff, Set.mem_setOf_eq, abs_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨by linarith, h2⟩
  · rintro ⟨hm, hp⟩
    have h3 : ξ - |z.im| < z.re := by linarith
    have h4 : z.re < (1/α).re - ξ + |z.im - (1/α).im| := by
      have := hB z; linarith
    exact ⟨⟨by have := hA z; linarith, hp⟩, ⟨h3, h4⟩⟩

/-! ## The residual only sees `Φm` and the preimage -/

/-- With the (A.4.2) relation, the residual of the statement is `Φm (ζ - 1/α) + 1/α - d.E w` at
the chosen preimage `ζ ∈ Qp`. -/
theorem residual_eq {Φm Φp : ℂ → ℂ} {Q : Set ℂ} {d₁ α : ℂ}
    (hrel : ∀ w ∈ Q, Φm (Tt α w) = Φp w + d₁)
    {w : ℂ} (hw : invOn Φm Q w ∈ Q) :
    Φp (invOn Φm Q w) + d₁ + 1 / α = Φm (invOn Φm Q w - 1 / α) + 1 / α := by
  have h := hrel (invOn Φm Q w) hw
  simp only [Tt] at h
  rw [h]


/-! ## Elementary closure properties of `IsFatouCoordOn` -/

/-- Adding a constant to a Fatou coordinate preserves the property (the three clauses are
invariant: differentiability, injectivity, and the Abel equation). -/
theorem MandelDim.IsFatouCoordOn.add_const {F Φ : ℂ → ℂ} {Q : Set ℂ}
    (h : MandelDim.IsFatouCoordOn F Φ Q) (c : ℂ) :
    MandelDim.IsFatouCoordOn F (fun z => Φ z + c) Q := by
  refine ⟨?_, ?_, ?_⟩
  · exact h.1.add_const c
  · intro x hx y hy hxy
    simp only at hxy
    exact h.2.1 hx hy (add_right_cancel hxy)
  · intro z hz hFz
    change Φ (F z) + c = Φ z + c + 1
    rw [h.2.2 z hz hFz]; ring

end

end Work.Pert
