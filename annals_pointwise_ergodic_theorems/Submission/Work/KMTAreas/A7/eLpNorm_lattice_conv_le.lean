import Mathlib
import Submission.Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm
import Submission.Port.Aesm

/-!
# Young's inequality for lattice convolutions on `ℤ`

For `1 ≤ p` and any `q : ℕ`, the lattice convolution
`n ↦ ∑' k, c k * g (n - k * q)` of a complex sequence `c` with a complex sequence `g`
satisfies the `ℓᵖ`-Young inequality

`‖n ↦ ∑' k, c k * g (n - k * q)‖_{ℓᵖ} ≤ (∑' k, ‖c k‖) * ‖g‖_{ℓᵖ}`.

The proof is the classical one: the pointwise triangle inequality for the (possibly
non-summable) series, Minkowski's inequality for countable sums of `ℝ≥0∞`-valued functions
(`Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm`), and the invariance of the `ℓᵖ`-norm
under translations (the counting measure on `ℤ` is translation invariant).
-/

namespace Work.KMTAreas.A7

open MeasureTheory ENNReal

/-- Pointwise `enorm` triangle inequality for a lattice convolution:
the `enorm` of the series is at most the series of the `enorm`s of its terms. -/
private lemma enorm_tsum_lattice_le (q : ℕ) (c g : ℤ → ℂ) (n : ℤ) :
    ‖∑' k : ℤ, c k * g (n - (k : ℤ) * (q : ℤ))‖ₑ
      ≤ ∑' k : ℤ, ‖c k‖ₑ * ‖g (n - (k : ℤ) * (q : ℤ))‖ₑ := by
  refine (enorm_tsum_le_tsum_enorm (f := fun k : ℤ =>
    c k * g (n - (k : ℤ) * (q : ℤ)))).trans ?_
  exact ENNReal.tsum_le_tsum (fun k => by rw [enorm_mul])

/-- Invariance of the `ℒᵖ(ℤ)`-norm (counting measure) under translation of the argument. -/
private lemma eLpNorm_comp_sub_count (p : ℝ) (t : ℤ) (g : ℤ → ℂ) :
    eLpNorm (fun n : ℤ => g (n - t)) (ENNReal.ofReal p) (Measure.count : Measure ℤ)
      = eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
  have hf : MeasurePreserving (fun n : ℤ => n - t) (Measure.count : Measure ℤ)
      (Measure.count : Measure ℤ) := by
    have h := measurePreserving_add_right (Measure.count : Measure ℤ) (-t)
    simpa [sub_eq_add_neg] using h
  have h2 := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal p)
    (μ := (Measure.count : Measure ℤ)) (f := fun n : ℤ => n - t) (g := g)
    ((measurable_of_countable g).aestronglyMeasurable) hf
  simpa [Function.comp_def] using h2

/-- Homogeneity of the `ℒᵖ(ℤ)`-norm (counting measure) under multiplication by a constant. -/
private lemma eLpNorm_const_mul_count (p : ℝ) (a : ℂ) (f : ℤ → ℂ) :
    eLpNorm (fun n : ℤ => a * f n) (ENNReal.ofReal p) (Measure.count : Measure ℤ)
      = ‖a‖ₑ * eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
  have h := eLpNorm_const_smul a f (ENNReal.ofReal p) (Measure.count : Measure ℤ)
  have hsmul : (a • f) = fun n : ℤ => a * f n := by funext n; simp
  rw [hsmul] at h
  exact h

theorem eLpNorm_lattice_conv_le {p : ℝ} (hp : 1 ≤ p) (q : ℕ) (hq : 1 ≤ q) (c g : ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun n : ℤ => ∑' k : ℤ, c k * g (n - (k : ℤ) * (q : ℤ)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ (∑' k : ℤ, ENNReal.ofReal ‖c k‖) *
        MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  set μ : Measure ℤ := Measure.count with hμ
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hP1 : 1 ≤ P := by
    rw [hP]
    simpa using (ENNReal.ofReal_le_ofReal hp : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  -- the `k`-th summand of the majorant, i.e. the term where the norm is taken inside
  have hterm : ∀ k : ℤ,
      eLpNorm (fun n : ℤ => ‖c k‖ₑ * ‖g (n - (k : ℤ) * (q : ℤ))‖ₑ) P μ
        = ‖c k‖ₑ * eLpNorm g P μ := by
    intro k
    have hshift : eLpNorm (fun n : ℤ => g (n - (k : ℤ) * (q : ℤ))) P μ = eLpNorm g P μ := by
      simpa only [hP, hμ] using eLpNorm_comp_sub_count p (k * (q : ℤ)) g
    have hscale : eLpNorm (fun n : ℤ => c k * g (n - (k : ℤ) * (q : ℤ))) P μ
        = ‖c k‖ₑ * eLpNorm (fun n : ℤ => g (n - (k : ℤ) * (q : ℤ))) P μ := by
      simpa only [hP, hμ] using
        eLpNorm_const_mul_count p (c k) (fun n : ℤ => g (n - (k : ℤ) * (q : ℤ)))
    have h1 : eLpNorm (fun n : ℤ => ‖c k * g (n - (k : ℤ) * (q : ℤ))‖ₑ) P μ
        = eLpNorm (fun n : ℤ => c k * g (n - (k : ℤ) * (q : ℤ))) P μ :=
      eLpNorm_enorm (hf := by pw_aesm) (p := P) (μ := μ) _
    have h2 : (fun n : ℤ => ‖c k‖ₑ * ‖g (n - (k : ℤ) * (q : ℤ))‖ₑ)
        = (fun n : ℤ => ‖c k * g (n - (k : ℤ) * (q : ℤ))‖ₑ) := by
      funext n
      exact (enorm_mul (c k) (g (n - (k : ℤ) * (q : ℤ)))).symm
    rw [h2, h1, hscale, hshift]
  have hpoint : ∀ n : ℤ, ‖∑' k : ℤ, c k * g (n - (k : ℤ) * (q : ℤ))‖ₑ
      ≤ ∑' k : ℤ, ‖c k‖ₑ * ‖g (n - (k : ℤ) * (q : ℤ))‖ₑ := enorm_tsum_lattice_le q c g
  have hstep1 : eLpNorm (fun n : ℤ => ∑' k : ℤ, c k * g (n - (k : ℤ) * (q : ℤ))) P μ
      ≤ eLpNorm (fun n : ℤ => ∑' k : ℤ, ‖c k‖ₑ * ‖g (n - (k : ℤ) * (q : ℤ))‖ₑ) P μ :=
    eLpNorm_mono_enorm (hf := by pw_aesm) hpoint
  have hstep2 : eLpNorm (fun n : ℤ => ∑' k : ℤ, ‖c k‖ₑ * ‖g (n - (k : ℤ) * (q : ℤ))‖ₑ) P μ
      ≤ ∑' k : ℤ, ‖c k‖ₑ * eLpNorm g P μ := by
    refine (Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm (p := P) hP1
      (f := fun k : ℤ => fun n : ℤ => ‖c k‖ₑ * ‖g (n - (k : ℤ) * (q : ℤ))‖ₑ)
      (fun k => (measurable_of_countable _).aemeasurable)).trans ?_
    exact ENNReal.tsum_le_tsum (fun k => le_of_eq (hterm k))
  calc eLpNorm (fun n : ℤ => ∑' k : ℤ, c k * g (n - (k : ℤ) * (q : ℤ))) P μ
      ≤ eLpNorm (fun n : ℤ => ∑' k : ℤ, ‖c k‖ₑ * ‖g (n - (k : ℤ) * (q : ℤ))‖ₑ) P μ :=
        hstep1
    _ ≤ ∑' k : ℤ, ‖c k‖ₑ * eLpNorm g P μ := hstep2
    _ = (∑' k : ℤ, ‖c k‖ₑ) * eLpNorm g P μ := ENNReal.tsum_mul_right
    _ = (∑' k : ℤ, ENNReal.ofReal ‖c k‖) * eLpNorm g P μ := by
        have h : (∑' k : ℤ, ‖c k‖ₑ) = (∑' k : ℤ, ENNReal.ofReal ‖c k‖) :=
          tsum_congr (fun k => by simp)
        rw [h]

end Work.KMTAreas.A7
