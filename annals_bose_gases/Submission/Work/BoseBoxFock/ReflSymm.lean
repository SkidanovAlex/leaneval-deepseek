import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.ReflSymm` — reflection symmetry of the corpus modes

Two facts used by `Work.BoseBoxFock.gramFamV` (the complex Gram matrix of the
physical mode family `Work.BoseBoxFock.FamV`):

* `reflsymm_modes` — the corpus modes `qVec ℓ k`, `thetaExp ℓ s` and `thetaFun ℓ`
  are **real up to the reflection** `x ↦ -x`: `conj (f (-x)) = f x`.  This is the
  parity of `χ` (`BoxData.chi_even`), the reality of `χ̂` and the symmetry of the
  box `Λ(ℓ) = ℓ • unitCell`.
* `integral_conj_reflsymm` — for two such functions, the complex pairing
  `∫ x, conj (f x) · g x` equals the complexification of its real part
  `realIP f g = ∫ x, Re (conj (f x) · g x)`: the substitution `x ↦ -x`
  (`MeasureTheory.integral_neg_eq_self`, the Lebesgue measure is negation
  invariant) shows that the integrand's imaginary part is odd, hence that the
  integral is fixed by complex conjugation.
-/

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Work.BoseBoxFock

set_option autoImplicit false

/-! ## The symmetry of the box and of the modes -/

/-- The unit cell is stable under `x ↦ -x`. -/
lemma neg_mem_unitCell {x : EuclideanSpace ℝ (Fin 3)} :
    -x ∈ Work.BoseB4.unitCell ↔ x ∈ Work.BoseB4.unitCell := by
  simp only [Work.BoseB4.unitCell, Set.mem_ofPred_eq, WithLp.ofLp_neg, Pi.neg_apply, abs_neg]

/-- The box `Λ(ℓ) = ℓ • unitCell` is stable under `x ↦ -x` (for every real `ℓ`). -/
lemma neg_mem_boxL (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    -x ∈ Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ ↔
      x ∈ Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ := by
  have hb : Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ
      = ℓ • Work.BoseB4.unitCell := rfl
  rw [hb, Set.mem_smul_set, Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨-y, neg_mem_unitCell.mpr hy, by rw [smul_neg, hyx, neg_neg]⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨-y, neg_mem_unitCell.mpr hy, by rw [smul_neg, hyx]⟩

/-- `θ_Λ` is real: `conj (θ_Λ (-x)) = θ_Λ x`. -/
lemma conj_thetaFun (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ (-x)) =
      Work.BoseK15.corpusBox.thetaFun ℓ x := by
  rw [Work.BoseB4.BoxData.thetaFun_apply, Work.BoseB4.BoxData.thetaFun_apply]
  by_cases h : x ∈ Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ
  · rw [if_pos ((neg_mem_boxL ℓ x).mpr h), if_pos h, map_one]
  · rw [if_neg (fun h' => h ((neg_mem_boxL ℓ x).mp h')), if_neg h, map_zero]

/-- `e^{ikx}χ_Λ` is real up to the reflection. -/
lemma conj_modeVec (ℓ : ℝ) (k x : EuclideanSpace ℝ (Fin 3)) :
    (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k (-x)) =
      Work.BoseK15.corpusBox.modeVec ℓ k x := by
  rw [Work.BoseB4.BoxData.modeVec_apply, Work.BoseB4.BoxData.modeVec_apply, map_mul,
    Complex.conj_ofReal, Work.BoseB4.BoxData.chiLam_even, ← Complex.exp_conj, map_mul,
    Complex.conj_I, Complex.conj_ofReal, inner_neg_right, Complex.ofReal_neg]
  congr 1
  ring_nf

/-- `Q(e^{ikx}χ_Λ) = qVec ℓ k` is real up to the reflection. -/
lemma conj_qVec (ℓ : ℝ) (k x : EuclideanSpace ℝ (Fin 3)) :
    (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k (-x)) =
      Work.BoseK15.corpusBox.qVec ℓ k x := by
  rw [Work.BoseB4.BoxData.qVec_apply, Work.BoseB4.BoxData.qVec_apply, map_sub, map_mul,
    Complex.conj_ofReal, conj_modeVec, conj_thetaFun]

/-- The θ-mode `e^{isx}θ_Λ` is real up to the reflection. -/
lemma conj_thetaExp (ℓ : ℝ) (s x : EuclideanSpace ℝ (Fin 3)) :
    (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaExp ℓ s (-x)) =
      Work.BoseK15.corpusBox.thetaExp ℓ s x := by
  rw [Work.BoseB4.BoxData.thetaExp_apply, Work.BoseB4.BoxData.thetaExp_apply, map_mul,
    ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, inner_neg_right,
    Complex.ofReal_neg, conj_thetaFun]
  congr 1
  ring_nf

/-- **The three corpus modes are real up to the reflection** `x ↦ -x`. -/
theorem reflsymm_modes (ℓ : ℝ) :
    (∀ (k x : EuclideanSpace ℝ (Fin 3)),
      (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k (-x))
        = Work.BoseK15.corpusBox.qVec ℓ k x) ∧
    (∀ (s x : EuclideanSpace ℝ (Fin 3)),
      (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaExp ℓ s (-x))
        = Work.BoseK15.corpusBox.thetaExp ℓ s x) ∧
    (∀ x : EuclideanSpace ℝ (Fin 3),
      (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ (-x))
        = Work.BoseK15.corpusBox.thetaFun ℓ x) :=
  ⟨conj_qVec ℓ, conj_thetaExp ℓ, conj_thetaFun ℓ⟩

/-! ## The complex pairing of two reflection-symmetric functions is real -/

/-- **The complex pairing of two reflection-symmetric functions is real.**  If
`conj (f (-x)) = f x` and `conj (g (-x)) = g x`, then the pairing
`∫ x, conj (f x) · g x` is the complexification of `realIP f g = ∫ x, Re (conj (f x) · g x)`. -/
theorem integral_conj_reflsymm (f g : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hf : ∀ x, (starRingEnd ℂ) (f (-x)) = f x)
    (hg : ∀ x, (starRingEnd ℂ) (g (-x)) = g x)
    (hint : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (f x) * g x)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :
    (∫ x, (starRingEnd ℂ) (f x) * g x)
      = (((∫ x, ((starRingEnd ℂ) (f x) * g x).re) : ℝ) : ℂ) := by
  have hg' : ∀ x, (starRingEnd ℂ) (g x) = g (-x) := by
    intro x
    have h := congrArg (starRingEnd ℂ) (hg x)
    simpa using h.symm
  have hpt : ∀ x, (starRingEnd ℂ) ((starRingEnd ℂ) (f x) * g x)
      = (starRingEnd ℂ) (f (-x)) * g (-x) := by
    intro x
    rw [map_mul, Complex.conj_conj, hg' x, ← hf x]
  have h1 : (starRingEnd ℂ) (∫ x, (starRingEnd ℂ) (f x) * g x)
      = ∫ x, (starRingEnd ℂ) (f x) * g x := by
    rw [← integral_conj (f := fun x => (starRingEnd ℂ) (f x) * g x)]
    rw [show (fun x => (starRingEnd ℂ) ((starRingEnd ℂ) (f x) * g x))
        = fun x => (starRingEnd ℂ) (f (-x)) * g (-x) from funext hpt]
    rw [MeasureTheory.integral_neg_eq_self (fun y => (starRingEnd ℂ) (f y) * g y)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))]
  have h2 : (∫ x, (starRingEnd ℂ) (f x) * g x).im = 0 := by
    have h := congrArg Complex.im h1
    simp only [Complex.conj_im] at h
    linarith
  have h3 : (∫ x, (starRingEnd ℂ) (f x) * g x).re
      = ∫ x, ((starRingEnd ℂ) (f x) * g x).re := by
    simpa using (integral_re hint).symm
  rw [show (∫ x, (starRingEnd ℂ) (f x) * g x)
      = (((∫ x, (starRingEnd ℂ) (f x) * g x).re : ℝ) : ℂ) from by
    apply Complex.ext
    · simp
    · simpa using h2]
  rw [h3]

end Work.BoseBoxFock
