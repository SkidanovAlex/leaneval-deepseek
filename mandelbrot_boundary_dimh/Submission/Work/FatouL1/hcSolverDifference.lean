import Mathlib
import Submission.Work.FatouL1.solverKernel
import Submission.Work.FatouL1.hcCotFacts
import Submission.Work.FatouL1.hcBoundaryDecay
import Submission.Work.FatouL1.hcRectCot
import Submission.Work.FatouL1.hcHorizontalPlus
import Submission.Work.FatouL1.hcHorizontalMinus
import Submission.Work.FatouL1.hcVerticalPlus
import Submission.Work.FatouL1.hcVerticalMinus

open MeasureTheory Filter
open scoped Topology Interval ENNReal

namespace Work.FatouL1

noncomputable section

/-! ### helper lemmas -/

lemma hcContinuousOnLine {a b : ℝ} {h : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b}) {c d Y : ℝ}
    (hc : a < c) (hd : d < b) (hcd : c ≤ d) :
    ContinuousOn (fun x : ℝ => h ((x : ℂ) + Y * Complex.I)) (Set.uIcc c d) := by
  refine hhol.continuousOn.comp ((Complex.continuous_ofReal.add continuous_const).continuousOn) ?_
  intro x hx
  have hx' : x ∈ Set.Icc c d := by rw [Set.uIcc_of_le hcd] at hx; exact hx
  constructor
  · show a < ((x : ℂ) + Y * Complex.I).re
    rw [show ((x : ℂ) + Y * Complex.I).re = x by simp]
    linarith [hx'.1]
  · show ((x : ℂ) + Y * Complex.I).re < b
    rw [show ((x : ℂ) + Y * Complex.I).re = x by simp]
    linarith [hx'.2]

lemma hcSinNeZero {z : ℂ} {Y : ℝ} (hY : 1 / 2 ≤ |Y - z.im|) (x : ℝ) :
    Complex.sin (Real.pi * (((x : ℂ) + Y * Complex.I) - z)) ≠ 0 := by
  intro hzero
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hzero
  have him : (Real.pi * (((x : ℂ) + Y * Complex.I) - z)).im = 0 := by
    rw [hk]; simp
  have h2 : (((x : ℂ) + Y * Complex.I) - z).im = Y - z.im := by
    simp [Complex.sub_im, Complex.add_im]
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, h2] at him
  have hzero' : Y - z.im = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact absurd h Real.pi_ne_zero
    · exact h
  rw [hzero', abs_zero] at hY
  linarith

lemma hcContinuousOnCotLine {z : ℂ} {Y : ℝ} (hY : 1 / 2 ≤ |Y - z.im|) {c d : ℝ} :
    ContinuousOn (fun x : ℝ => Complex.cot (Real.pi * (((x : ℂ) + Y * Complex.I) - z)))
      (Set.uIcc c d) := by
  have hcont : Continuous (fun x : ℝ => Real.pi * (((x : ℂ) + Y * Complex.I) - z)) := by
    fun_prop
  have hc : ContinuousOn (fun x : ℝ => Complex.cos (Real.pi * (((x : ℂ) + Y * Complex.I) - z)))
      (Set.uIcc c d) := (Complex.continuous_cos.comp hcont).continuousOn
  have hs : ContinuousOn (fun x : ℝ => Complex.sin (Real.pi * (((x : ℂ) + Y * Complex.I) - z)))
      (Set.uIcc c d) := (Complex.continuous_sin.comp hcont).continuousOn
  have hdiv := hc.div hs (fun x _ => hcSinNeZero hY x)
  refine hdiv.congr ?_
  intro x _
  simp only [Pi.div_apply, Complex.cot_eq_cos_div_sin]

lemma hcContinuousOnCotUp {z : ℂ} {Y : ℝ} (hY : z.im + 1 / 2 ≤ Y) {A B : ℝ} :
    ContinuousOn (fun x : ℝ =>
      Complex.I / 2 * Complex.cot (Real.pi * (((x : ℂ) + Y * Complex.I) - z))) (Set.uIcc A B) := by
  refine ((hcContinuousOnCotLine (z := z) (Y := Y) ?_).const_mul (Complex.I / 2))
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Y - z.im)]
  linarith

lemma hcContinuousOnCotDown {z : ℂ} {Y : ℝ} (hY : 1 / 2 - z.im ≤ Y) {A B : ℝ} :
    ContinuousOn (fun x : ℝ =>
      Complex.I / 2 * Complex.cot (Real.pi * (((x : ℂ) + (-Y) * Complex.I) - z))) (Set.uIcc A B) := by
  have hY' : 1 / 2 ≤ |(-Y) - z.im| := by
    rw [show (-Y) - z.im = -(Y + z.im) by ring, abs_neg,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ Y + z.im)]
    linarith
  have h := (hcContinuousOnCotLine (z := z) (Y := -Y) (c := A) (d := B) hY').const_mul (Complex.I / 2)
  simpa only [Complex.ofReal_neg, neg_mul] using h

set_option maxHeartbeats 4000000 in
/-- **The Cauchy–Heine difference identity.** -/
theorem hcSolverDifference {a b m : ℝ} (hab : a < b) {h : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b})
    (hint : ∀ x ∈ Set.Ioo a b, MeasureTheory.Integrable (fun y : ℝ => h ((x : ℂ) + y * Complex.I)))
    (hmass : ∀ x ∈ Set.Ioo a b, ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m) :
    ∀ z : ℂ, a + 1 / 2 < z.re → z.re < b - 1 / 2 →
      Work.FatouL1.hcSolver h (z + 1) - Work.FatouL1.hcSolver h z = -h z := by
  intro z hz1 hz2
  obtain ⟨hcotp, hcotm, hdecp, hdecm, hcotid, hdsl, hcotdiff⟩ := hcCotFacts
  have ha' : a < z.re - 1 / 2 := by linarith
  have hb' : z.re + 1 / 2 < b := by linarith
  have hle : z.re - 1 / 2 ≤ z.re + 1 / 2 := by linarith
  have hstripOpen : IsOpen {w : ℂ | a < w.re ∧ w.re < b} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  obtain ⟨hbnd, hlimp, hlimm⟩ := hcBoundaryDecay hab hhol hint hmass ha' hle hb'
  obtain ⟨C, hC0, hCpt⟩ := hbnd
  -- the removable-singularity hypothesis of the contour identity
  have hdiff : ∀ Y : ℝ, z.im < Y → DifferentiableOn ℂ
      (fun ζ => h ζ * (Complex.I / 2 * Complex.cot (Real.pi * (ζ - z))
        - Complex.I / (2 * Real.pi * (ζ - z))))
      (Set.uIcc (z.re - 1 / 2) (z.re + 1 / 2) ×ℂ Set.uIcc (-Y) Y) := by
    intro Y hY ζ hζ
    rw [Complex.mem_reProdIm] at hζ
    have hζre : ζ.re ∈ Set.Icc (z.re - 1 / 2) (z.re + 1 / 2) := by
      rw [Set.uIcc_of_le hle] at hζ
      exact hζ.1
    have hτ : |(ζ - z).re| < 1 := by
      rw [Complex.sub_re, abs_lt]
      constructor <;> linarith [hζre.1, hζre.2]
    have hstrip : ζ ∈ {w : ℂ | a < w.re ∧ w.re < b} :=
      ⟨by linarith [hζre.1], by linarith [hζre.2]⟩
    have hfun : (fun ζ : ℂ => h ζ * (Complex.I / 2 * Complex.cot (Real.pi * (ζ - z))
          - Complex.I / (2 * Real.pi * (ζ - z))))
        = fun ζ : ℂ => h ζ * (Complex.I / 2 * (Complex.cot (Real.pi * (ζ - z))
          - 1 / (Real.pi * (ζ - z)))) := by
      funext w
      congr 1
      field_simp
    rw [hfun]
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.mul (hhol.differentiableAt ?_) ?_)
    · exact hstripOpen.mem_nhds hstrip
    · have hg : DifferentiableAt ℂ
          (fun w : ℂ => Complex.I / 2 * (Complex.cot (Real.pi * w) - 1 / (Real.pi * w))) (ζ - z) :=
        (hcotdiff (ζ - z) hτ).const_mul (Complex.I / 2)
      have hf : DifferentiableAt ℂ (fun w : ℂ => w - z) ζ := by fun_prop
      exact DifferentiableAt.comp (f := fun w : ℂ => w - z)
        (g := fun w : ℂ => Complex.I / 2 * (Complex.cot (Real.pi * w) - 1 / (Real.pi * w))) ζ hg hf
  -- the contour identity, valid for all Y > |Im z|
  have hval : ∀ Y : ℝ, |z.im| < Y → rectB (z.re - 1 / 2) (z.re + 1 / 2) Y
      (fun ζ => h ζ * (Complex.I / 2 * Complex.cot (Real.pi * (ζ - z)))) = -h z := by
    intro Y hY
    have h1 : -Y < z.im := by have := neg_abs_le z.im; linarith
    have h2 : z.im < Y := lt_of_le_of_lt (le_abs_self z.im) hY
    exact hcRectCot hhol ha' hb' (by linarith) (by linarith) h1 h2 (hdiff Y h2)
  -- the four boundary limits
  have hT2 : Tendsto (fun Y : ℝ => ∫ x in (z.re - 1 / 2)..(z.re + 1 / 2),
      h ((x : ℂ) + Y * Complex.I) * (Complex.I / 2 * Complex.cot (Real.pi * (((x : ℂ) + Y * Complex.I) - z))))
      atTop (nhds 0) :=
    hcHorizontalPlus (z := z) (A := z.re - 1 / 2) (B := z.re + 1 / 2) (C := C) hle hC0 hCpt hdecp
      (fun Y => hcContinuousOnLine hhol ha' hb' hle)
      (fun Y hY => hcContinuousOnCotUp hY) hlimp
  have hT1 : Tendsto (fun Y : ℝ => ∫ x in (z.re - 1 / 2)..(z.re + 1 / 2),
      h ((x : ℂ) + (-Y) * Complex.I) * (Complex.I / 2 * Complex.cot (Real.pi * (((x : ℂ) + (-Y) * Complex.I) - z))))
      atTop (nhds 0) :=
    hcHorizontalMinus (z := z) (A := z.re - 1 / 2) (B := z.re + 1 / 2) (C := C) hle hC0 hCpt hdecm
      (fun Y => by simpa only [Complex.ofReal_neg, neg_mul] using hcContinuousOnLine (Y := -Y) hhol ha' hb' hle)
      (fun Y hY => hcContinuousOnCotDown hY) hlimm
  have hT3 : Tendsto (fun Y : ℝ => Complex.I * ∫ y in (-Y)..Y,
      h (((z.re + 1 / 2 : ℝ) : ℂ) + y * Complex.I)
        * (Complex.I / 2 * Complex.cot (Real.pi * ((((z.re + 1 / 2 : ℝ) : ℂ) + y * Complex.I) - z))))
      atTop (nhds (hcSolver h (z + 1))) :=
    hcVerticalPlus (z := z) (hint (z.re + 1 / 2) ⟨by linarith, by linarith⟩) hcotp
  have hT4 : Tendsto (fun Y : ℝ => Complex.I * ∫ y in (-Y)..Y,
      h (((z.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I)
        * (Complex.I / 2 * Complex.cot (Real.pi * ((((z.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I) - z))))
      atTop (nhds (hcSolver h z)) :=
    hcVerticalMinus (z := z) (hint (z.re - 1 / 2) ⟨by linarith, by linarith⟩) hcotm
  -- combine
  have hlim : Tendsto (fun Y : ℝ => rectB (z.re - 1 / 2) (z.re + 1 / 2) Y
      (fun ζ => h ζ * (Complex.I / 2 * Complex.cot (Real.pi * (ζ - z)))))
      atTop (nhds (hcSolver h (z + 1) - hcSolver h z)) := by
    have hcomb : Tendsto (fun Y : ℝ =>
        ((∫ x in (z.re - 1 / 2)..(z.re + 1 / 2),
            h ((x : ℂ) + (-Y) * Complex.I) * (Complex.I / 2 * Complex.cot (Real.pi * (((x : ℂ) + (-Y) * Complex.I) - z))))
          - (∫ x in (z.re - 1 / 2)..(z.re + 1 / 2),
            h ((x : ℂ) + Y * Complex.I) * (Complex.I / 2 * Complex.cot (Real.pi * (((x : ℂ) + Y * Complex.I) - z)))))
        + ((Complex.I * ∫ y in (-Y)..Y,
            h (((z.re + 1 / 2 : ℝ) : ℂ) + y * Complex.I)
              * (Complex.I / 2 * Complex.cot (Real.pi * ((((z.re + 1 / 2 : ℝ) : ℂ) + y * Complex.I) - z))))
          - (Complex.I * ∫ y in (-Y)..Y,
            h (((z.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I)
              * (Complex.I / 2 * Complex.cot (Real.pi * ((((z.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I) - z))))))
        atTop (nhds (hcSolver h (z + 1) - hcSolver h z)) := by
      have h := (hT1.sub hT2).add (hT3.sub hT4)
      simpa using h
    refine hcomb.congr' (Eventually.of_forall (fun Y => ?_))
    simp only [rectB]
    ring
  -- the constant value
  have hconst : Tendsto (fun Y : ℝ => rectB (z.re - 1 / 2) (z.re + 1 / 2) Y
      (fun ζ => h ζ * (Complex.I / 2 * Complex.cot (Real.pi * (ζ - z))))) atTop (nhds (-h z)) :=
    tendsto_const_nhds.congr'
      ((eventually_gt_atTop |z.im|).mono (fun Y hY => (hval Y hY).symm))
  exact (tendsto_nhds_unique hconst hlim).symm

end

end Work.FatouL1
