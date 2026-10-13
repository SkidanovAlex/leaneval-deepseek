import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# `TT.interpGamma_slots`

The two *slot* comparisons consumed by the assembly `TT.interpGamma_of_core`:

* `TTint α G ≤ HkSq α 0 (pthIter 2 G)`,
* `DDint α G ≤ 2 HkSq α 0 (DzIter 2 G) + 18 HkSq α 0 (DzIter 1 G)`,

where `TTint = ∫∫(∂_θ²G)²w²σ_a`, `DDint = ∫∫(D_z²G + b D_zG)²w²σ_a` with
`σ_a = sin(2θ)^{2-γ(α)}`, `b z = (z-3)/(1+z)`, and the right-hand sides are the *heavy*
`ℋ⁰`-slots against `σ_η = sin(2θ)^{-η}`.

Both follow from the single weight comparison `σ_a ≤ σ_η` on `Iθ` (valid because
`α ≤ 1` gives `2 - γ ≥ 1 - 1/10 > -η`) and the estimate `|b z| ≤ 3`; the `HkMem`
hypotheses make the heavy slots honest, so that the elementary monotonicity lemma for
integrals of nonnegative functions can be applied.
-/

/-! ## The heavy `ℋ⁰`-slot is honest -/

/-- The `σ_η`-weighted `θ`-slice of `f²` is integrable for every `z ∈ Iz` as soon as
`f ∈ ℋ⁰`: it is the `k = 0` `HkIntegrand` of `f` in the sense of `hkIntegrand_zero_eq'`. -/
theorem integrableOn_slice_sEta_slots {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ => (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
  IntegrableOn.congr_fun (hf.1 z hz)
    (fun θ hθ => hkIntegrand_zero_eq' α f hθ) measurableSet_Icc

/-- The `z`-function of the `σ_η`-weighted `θ`-slice integrals of `f²` is integrable as
soon as `f ∈ ℋ⁰`. -/
theorem integrableOn_zfun_sEta_slots {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz :=
  IntegrableOn.congr_fun hf.2
    (fun z _ => setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => hkIntegrand_zero_eq' α f hθ)) measurableSet_Ici

/-! ## The light slot is dominated by the heavy one -/

/-- **The `ℋ⁰`-slot of `f` dominates its `σ_a`-weighted slot** (for `α ≤ 1`):
`∫∫ f² w² σ_a ≤ HkSq α 0 f`. -/
theorem integral_sigA_le_HkSq_slots {α : ℝ} (hα : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ) ≤ Work.Spaces.HkSq α 0 f := by
  rw [HkSq_zero_eq_integral α f]
  refine integral_mono_of_nonneg ?_ (integrableOn_zfun_sEta_slots hf) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with z _
    exact setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sigA_nonneg α θ hθ)
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    refine integral_mono_of_nonneg ?_ (integrableOn_slice_sEta_slots hf hz) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sigA_nonneg α θ hθ)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_le_mul_of_nonneg_left (sigA_le_sEta hα hθ)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- **`TTint` is dominated by the honest `ℋ⁰`-slot of `∂_θ²G`.** -/
theorem TTint_le_HkSq_slots {α : ℝ} (hα : α ≤ 1) {G : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 G)) :
    TTint α G ≤ Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G) :=
  integral_sigA_le_HkSq_slots hα h

/-! ## The radial slot `DDint` -/

/-- The coefficient `b z = (z-3)/(1+z)` of `DDint` has square `≤ 9` on `z ≥ 0`. -/
theorem bcoef_sq_le_nine_slots {z : ℝ} (hz : 0 ≤ z) : (bcoef z) ^ 2 ≤ 9 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : |bcoef z| ≤ 3 := by
    rw [bcoef, abs_div, abs_of_pos h1, div_le_iff₀ h1, abs_le]
    constructor <;> linarith
  have h3 : (bcoef z) ^ 2 ≤ (3 : ℝ) ^ 2 := (sq_le_sq).mpr (by simpa using h2)
  nlinarith [h3]

/-- **The radial slot `DDint` is dominated by the two honest `ℋ⁰`-slots.**  Pointwise in `z`
the square `(D_z²G + b D_zG)²` is at most `2 (D_z²G)² + 18 (D_zG)²` (because `b² ≤ 9`), and
the light weight `σ_a` is dominated by the heavy one `σ_η`. -/
theorem DDint_le_slots {α : ℝ} (hα : α ≤ 1) {G : ℝ → ℝ → ℝ}
    (h2 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 G))
    (h1 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 G)) :
    DDint α G ≤ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
      + 18 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G) := by
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter 2 G z θ + bcoef z * Work.Spaces.DzIter 1 G z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * sigA α θ)
        ≤ 2 * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter 2 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + 18 * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter 1 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    intro z hz
    have hP : MeasureTheory.Integrable (fun θ => (Work.Spaces.DzIter 2 G z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (volume.restrict Work.Spaces.Iθ) := integrableOn_slice_sEta_slots h2 hz
    have hQ : MeasureTheory.Integrable (fun θ => (Work.Spaces.DzIter 1 G z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (volume.restrict Work.Spaces.Iθ) := integrableOn_slice_sEta_slots h1 hz
    have hInt2 : MeasureTheory.Integrable
        (fun θ => (2 * (Work.Spaces.DzIter 2 G z θ) ^ 2
            + 18 * (Work.Spaces.DzIter 1 G z θ) ^ 2) * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (volume.restrict Work.Spaces.Iθ) := by
      have h := (hP.const_mul 2).add (hQ.const_mul 18)
      refine h.congr (Filter.Eventually.of_forall fun θ => ?_)
      simp only [Pi.add_apply]
      ring
    have hpt : ∀ θ ∈ Work.Spaces.Iθ,
        (Work.Spaces.DzIter 2 G z θ + bcoef z * Work.Spaces.DzIter 1 G z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * sigA α θ
          ≤ (2 * (Work.Spaces.DzIter 2 G z θ) ^ 2
              + 18 * (Work.Spaces.DzIter 1 G z θ) ^ 2)
            * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      intro θ hθ
      have hc2 : (bcoef z) ^ 2 ≤ 9 := bcoef_sq_le_nine_slots hz
      have hquad : (Work.Spaces.DzIter 2 G z θ + bcoef z * Work.Spaces.DzIter 1 G z θ) ^ 2
          ≤ 2 * (Work.Spaces.DzIter 2 G z θ) ^ 2
            + 18 * (Work.Spaces.DzIter 1 G z θ) ^ 2 := by
        have hcQ : (bcoef z * Work.Spaces.DzIter 1 G z θ) ^ 2
            ≤ 9 * (Work.Spaces.DzIter 1 G z θ) ^ 2 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right hc2 (sq_nonneg _)
        nlinarith [sq_nonneg (Work.Spaces.DzIter 2 G z θ
            - bcoef z * Work.Spaces.DzIter 1 G z θ)]
      have hW2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hsa : sigA α θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := sigA_le_sEta hα hθ
      have hsa0 : 0 ≤ sigA α θ := sigA_nonneg α θ hθ
      calc (Work.Spaces.DzIter 2 G z θ + bcoef z * Work.Spaces.DzIter 1 G z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * sigA α θ
          ≤ (2 * (Work.Spaces.DzIter 2 G z θ) ^ 2
              + 18 * (Work.Spaces.DzIter 1 G z θ) ^ 2)
            * (Work.Spaces.w z) ^ 2 * sigA α θ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hquad hW2) hsa0
        _ ≤ (2 * (Work.Spaces.DzIter 2 G z θ) ^ 2
              + 18 * (Work.Spaces.DzIter 1 G z θ) ^ 2)
            * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_left hsa (mul_nonneg (by positivity) hW2)
    have hmono := integral_mono_of_nonneg
      (f := fun θ => (Work.Spaces.DzIter 2 G z θ + bcoef z * Work.Spaces.DzIter 1 G z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * sigA α θ)
      (g := fun θ => (2 * (Work.Spaces.DzIter 2 G z θ) ^ 2
          + 18 * (Work.Spaces.DzIter 1 G z θ) ^ 2) * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sigA_nonneg α θ hθ))
      hInt2 (ae_restrict_of_forall_mem measurableSet_Icc hpt)
    have hsplit : (∫ θ in Work.Spaces.Iθ, (2 * (Work.Spaces.DzIter 2 G z θ) ^ 2
          + 18 * (Work.Spaces.DzIter 1 G z θ) ^ 2) * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 2 G z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + 18 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 1 G z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      rw [show (fun θ => (2 * (Work.Spaces.DzIter 2 G z θ) ^ 2
              + 18 * (Work.Spaces.DzIter 1 G z θ) ^ 2) * (Work.Spaces.w z) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            = (fun θ => 2 * ((Work.Spaces.DzIter 2 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
                + 18 * ((Work.Spaces.DzIter 1 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) from by funext θ; ring]
      rw [MeasureTheory.integral_add (hP.const_mul 2) (hQ.const_mul 18)]
      simp only [MeasureTheory.integral_const_mul]
    exact le_trans hmono (le_of_eq hsplit)
  have hPz : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter 2 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (volume.restrict Work.Spaces.Iz) :=
    integrableOn_zfun_sEta_slots h2
  have hQz : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter 1 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (volume.restrict Work.Spaces.Iz) :=
    integrableOn_zfun_sEta_slots h1
  have hH : MeasureTheory.Integrable (fun z => 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter 2 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      + 18 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 1 G z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
      (volume.restrict Work.Spaces.Iz) :=
    (hPz.const_mul 2).add (hQz.const_mul 18)
  have houter := integral_mono_of_nonneg
    (f := fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter 2 G z θ + bcoef z * Work.Spaces.DzIter 1 G z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * sigA α θ)
    (g := fun z => 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter 2 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      + 18 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 1 G z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
    (ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
      setIntegral_nonneg measurableSet_Icc fun θ hθ =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sigA_nonneg α θ hθ))
    hH (ae_restrict_of_forall_mem measurableSet_Ici hslice)
  have hfinal : (∫ z in Work.Spaces.Iz, 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter 2 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      + 18 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 1 G z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
      = 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
        + 18 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G) := by
    rw [MeasureTheory.integral_add (hPz.const_mul 2) (hQz.const_mul 18)]
    simp only [MeasureTheory.integral_const_mul]
    rw [← HkSq_zero_eq_integral α (Work.Spaces.DzIter 2 G),
      ← HkSq_zero_eq_integral α (Work.Spaces.DzIter 1 G)]
  rw [DDint]
  exact le_trans houter (le_of_eq hfinal)

theorem interpGamma_slots :
    ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen G →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 G) →
      Work.FTS.EllipticEst.TT.TTint α G ≤ Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G)
        ∧ Work.FTS.EllipticEst.TT.DDint α G
            ≤ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
              + 18 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G) := by
  intro α G hα hα1 _ hDz2 hpth2 hDz1
  exact ⟨TTint_le_HkSq_slots hα1 hpth2, DDint_le_slots hα1 hDz2 hDz1⟩

end Work.FTS.EllipticEst.TT
