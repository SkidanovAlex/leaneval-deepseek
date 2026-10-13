import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Honest.HonSliceFinite
import Submission.Work.FTS.EllipticEst.Honest.honestBarLim
import Submission.Work.FTS.EllipticEst.Honest.sliceBarSq2
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The two angular weights `Work.FTS.EllipticEst.sEta` (`StraightDefs`) and
`Work.FTS.EllipticEst.AngSecond.sig` are the same function; recorded as a lemma so that
consumers can `rw` instead of relying on definitional unfolding. -/
theorem sEta_eq_sig : Work.FTS.EllipticEst.sEta = Work.FTS.EllipticEst.AngSecond.sig := rfl

/-- `AngSecond.sig` is a.e. strongly measurable on `Iθ`. -/
theorem aesm_sig' :
    AEStronglyMeasurable (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ)
      (volume.restrict Work.Spaces.Iθ) :=
  aesm_sEta'

/-- `AngSecond.sig` is integrable on `Iθ`. -/
theorem sig_integrableOn' :
    IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
  sEta_integrableOn

/-- **Domination criterion for the `σ`-weighted square.**  If `u` is a.e. strongly measurable on
`Iθ` and bounded by `B ≥ 0`, then `u²σ` is integrable on `Iθ`, because `σ` itself is. -/
theorem integrableOn_sq_mul_sig_of_abs_le {u : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (haesm : AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ))
    (hbdd : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), |u θ| ≤ B) :
    IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ := by
  have hInt : IntegrableOn (fun θ => B ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ := sig_integrableOn'.const_mul (B ^ 2)
  refine hInt.mono' ((haesm.pow 2).mul aesm_sig') ?_
  filter_upwards [hbdd, ae_mem_Ioo_Iθ'] with θ h1 h2
  have hsig : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
    Work.FTS.EllipticEst.AngSecond.sig_nonneg ⟨le_of_lt h2.1, le_of_lt h2.2⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hsig)]
  have hsq : (u θ) ^ 2 ≤ B ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hB]
    exact h1
  exact mul_le_mul_of_nonneg_right hsq hsig

/-- The `θ`-slice of `Ψ` is `C²` on `(0, π/2)`. -/
theorem contDiffOn_two_psi_slice {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ}
    (hz : 0 < z) :
    ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have h2 := h.sm 2
  have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
  exact h2.comp (by fun_prop) hmap

/-- **Slicewise `σ`-weighted square-integrability of the level-`0` profiles.**

For `Hon α F Ψ` and every `z > 0`, the slices of `Ψ`, `∂_θΨ`, `z ∂_zΨ` and `Ψ/cos θ` are
square-integrable against `σ θ = sin(2θ)^{-η}` on `Iθ`:

`∫_θ Ψ²σ < ∞`, `∫_θ (∂_θΨ)²σ < ∞`, `∫_θ (z ∂_zΨ)²σ < ∞`, `∫_θ (Ψ/cos θ)²σ < ∞`.

Route (all inputs clash-free, from the listed imports):
* `Honest/HonSliceFinite.lean` gives `integrableOn_sq_sEta_psi` (`∫_θ Ψ²σ < ∞`),
  `integrableOn_zpz_sigma'` (`∫_θ (∂_zΨ)²σ < ∞`, and the extra factor `z²` is a constant on the
  slice), and `slice_pth_bdd` (a *uniform* bound `|∂_θΨ| ≤ B` on the slice), which together
  with the integrability of `σ` (`HonEnergyAux.sEta_integrableOn`) gives
  `∫_θ (∂_θΨ)²σ ≤ B² ∫_θ σ < ∞` (dominate by `B²σ`);
* `∫_θ (Ψ/cos θ)²σ < ∞` follows from `sliceBarSq2`
  (`∫_θ (u/cos)²σ ≤ 100(∫_θ u²σ + ∫_θ (u')²σ)`, whose bar-limit hypothesis is
  `Honest/honestBarLim.lean`) applied to `u = Ψ(z,·)` with `deriv (Ψ z ·) = pth Ψ z ·` and
  `AngSecond.sig = sEta` (`rfl`), using the two integrabilities just proved. -/
theorem honSliceIntFacts (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.Honest.Hon α F Ψ) :
    ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn
          (fun θ => (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.pth Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn
          (fun θ => (z * Work.Spaces.pz Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn
          (fun θ => (Ψ z θ / Real.cos θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
  intro z hz
  -- (1) `Ψ²σ`
  have h₁ : IntegrableOn
      (fun θ => (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
    integrableOn_sq_sEta_psi h hz
  -- (2) `(∂_θΨ)²σ`, dominated by `B²σ` with `B` the uniform slice bound of `slice_pth_bdd`
  have h₂ : IntegrableOn
      (fun θ => (Work.Spaces.pth Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ := by
    set B : ℝ := |Work.Spaces.pth Ψ z (Real.pi / 4)|
      + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| with hBdef
    have hB0 : 0 ≤ B := by
      rw [hBdef]
      have h1 := integral_nonneg (μ := volume.restrict Work.Spaces.Iθ)
        (f := fun t => |Work.Spaces.pthIter 2 Ψ z t|) (fun t => abs_nonneg _)
      linarith [abs_nonneg (Work.Spaces.pth Ψ z (Real.pi / 4))]
    exact integrableOn_sq_mul_sig_of_abs_le hB0 (aesm_pth_slice h hz)
      ((ae_mem_Ioo_Iθ').mono fun θ hθ => by
        simpa only [hBdef] using slice_pth_bdd h hz θ hθ)
  -- (3) `(z ∂_zΨ)²σ`, from `(∂_zΨ)²σ` and the constant factor `z²`
  have h₃ : IntegrableOn
      (fun θ => (z * Work.Spaces.pz Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
    have hG : IntegrableOn
        (fun θ => (Work.Spaces.pz Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
      integrableOn_zpz_sigma' h hz
    have h2 : IntegrableOn
        (fun θ => z ^ 2 * ((Work.Spaces.pz Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ)) Work.Spaces.Iθ := hG.const_mul (z ^ 2)
    refine h2.congr (Eventually.of_forall fun θ => ?_)
    ring
  -- (4) `(Ψ/cos θ)²σ`, from the slicewise bar estimate `sliceBarSq2`
  have h₄ : IntegrableOn
      (fun θ => (Ψ z θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
    (sliceBarSq2 (fun θ => Ψ z θ) (contDiffOn_two_psi_slice h hz)
      (honestBarLim α F Ψ h z hz) h₁ h₂).1
  exact ⟨h₁, h₂, h₃, h₄⟩

end Work.FTS.EllipticEst.Honest
