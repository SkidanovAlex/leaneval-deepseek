/-
# `Work.FTS.EllSol.EllPkgAux.MollDom.window_E_le_F`

**The windowed angular Poincaré comparison for a trace-class datum.**

For a datum `G` in the trace class (`TraceClass G`) satisfying the four outer integrability
hypotheses (`FourInts G`) and a window half-width `δ > 0`, there is a constant `C > 0` such
that for every radius `z > 0` the function of the logarithmic variable
`t ↦ 1_{|log z - t| ≤ δ} · ∫_{Iθ} thEta θ · (∂_θG(exp t, θ))²` is integrable and

  `∫_t 1_{|log z - t| ≤ δ} ∫_{Iθ} thEta θ (∂_θG(exp t, θ))²
     ≤ C ∫_t 1_{|log z - t| ≤ δ} ∫_{Iθ} (∂_θ²G(exp t, θ))²`.

This is the *windowed, slicewise* form of the angular Poincaré estimate: the singular weight
`thEta θ = sin(2θ)^{-η}` (`η = 99/100`) on the *first* angular derivative is controlled by the
*unweighted* `L²`-norm of the *second* angular derivative, and the logarithmic window
`|log z - t| ≤ δ` is simply carried through both sides.

## Proof

1. **Slicewise Poincaré.** `slice_pth_poincare_unif` supplies a single constant `C₀ > 0` with
   `∫_{Iθ} thEta θ (∂_θG(w,θ))² ≤ C₀ ∫_{Iθ} (∂_θ²G(w,θ))²` for *every* radius `w > 0`
   (uniform version, via `thetaPoincare_unif`).  Applying it at `w = exp t > 0` gives the
   pointwise-in-`t` inequality.
2. **Integrability of the right-hand side.** `window_ttIntS_plain_integrable` gives that the
   windowed *unweighted* angular second derivative is integrable in `t`.
3. **A.e. strong measurability of the left-hand side.** `thSlice_window_aesm_pth` gives the
   a.e. strong measurability of the *joint* windowed function
   `p ↦ thEta p.2 · (∂_θG(exp p.1, p.2))²` on the product space, and
   `AEStronglyMeasurable.integral_prod_right'` turns it into the a.e. strong measurability of
   the parameter integral (the constant `if` is pulled out of the `θ`-integral, which is
   `integral_ite_const`).
4. **Conclusion.** `Integrable.mono'` gives the integrability of the left-hand side from the
   pointwise bound, and `integral_mono_ae` plus `integral_const_mul` the integral inequality.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_pth_poincare_unif
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.window_ttIntS_plain_integrable
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.thSlice_window_aesm_pth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

/-- A constant `if` may be pulled out of a set integral. -/
private lemma integral_ite_const {c : Prop} [Decidable c] (u : ℝ → ℝ) :
    (∫ s in Work.Spaces.Iθ, (if c then u s else 0))
      = (if c then ∫ s in Work.Spaces.Iθ, u s else 0) := by
  by_cases h : c
  · rw [ite_eq_left h]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun s => ite_eq_left h))
  · rw [ite_eq_right h]
    have heq : (fun s : ℝ => (if c then u s else 0))
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] (fun _ => (0 : ℝ)) :=
      Filter.Eventually.of_forall (fun s => ite_eq_right h)
    rw [MeasureTheory.integral_congr_ae heq, MeasureTheory.integral_zero]

/-- The windowed weighted angular first derivative of `G` in the logarithmic variable. -/
private def Efun (G : ℝ → ℝ → ℝ) (δ z : ℝ) : ℝ → ℝ :=
  fun t => if |Real.log z - t| ≤ δ then
    (∫ s in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0

/-- The windowed (unweighted) angular second derivative of `G` in the logarithmic variable. -/
private def Rfun (G : ℝ → ℝ → ℝ) (δ z : ℝ) : ℝ → ℝ :=
  fun t => if |Real.log z - t| ≤ δ then
    (∫ s in Work.Spaces.Iθ,
      (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0

theorem window_E_le_F (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z →
      MeasureTheory.Integrable (fun t : ℝ => if |Real.log z - t| ≤ δ then
          (∫ s in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0) ∧
      (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0))
        ≤ C * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0)) := by
  -- the uniform slicewise Poincaré constant
  obtain ⟨C₀, hC₀pos, hC₀⟩ := slice_pth_poincare_unif G hT
  refine ⟨C₀, hC₀pos, fun z hz => ?_⟩
  -- the right-hand side is integrable in `t`
  have hRint : MeasureTheory.Integrable (Rfun G δ z) :=
    window_ttIntS_plain_integrable G hT hF δ z hδ hz
  -- the left-hand side is a.e. strongly measurable in `t`
  have hLaesm : MeasureTheory.AEStronglyMeasurable (Efun G δ z) MeasureTheory.volume := by
    have hprod := thSlice_window_aesm_pth G hT δ z
    have hE : MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => ∫ s in Work.Spaces.Iθ,
          (if |Real.log z - t| ≤ δ then
            Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2
            else 0)) MeasureTheory.volume := hprod.integral_prod_right'
    have hEq : (fun t : ℝ => ∫ s in Work.Spaces.Iθ,
          (if |Real.log z - t| ≤ δ then
            Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2
            else 0)) = Efun G δ z := by
      funext t
      exact integral_ite_const
        (u := fun s : ℝ => Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2)
    rwa [hEq] at hE
  -- the two pointwise unfoldings of the window
  have hEw : ∀ t : ℝ, |Real.log z - t| ≤ δ → Efun G δ z t = ∫ s in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2 := by
    intro t h; simp only [Efun]; exact ite_eq_left h
  have hRw : ∀ t : ℝ, |Real.log z - t| ≤ δ → Rfun G δ z t = ∫ s in Work.Spaces.Iθ,
      (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 := by
    intro t h; simp only [Rfun]; exact ite_eq_left h
  have hEo : ∀ t : ℝ, ¬ (|Real.log z - t| ≤ δ) → Efun G δ z t = 0 := by
    intro t h; simp only [Efun]; exact ite_eq_right h
  have hRo : ∀ t : ℝ, ¬ (|Real.log z - t| ≤ δ) → Rfun G δ z t = 0 := by
    intro t h; simp only [Rfun]; exact ite_eq_right h
  -- nonnegativity of the left-hand side
  have hEnn : ∀ t : ℝ, 0 ≤ Efun G δ z t := by
    intro t
    by_cases h : |Real.log z - t| ≤ δ
    · rw [hEw t h]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun s hs => mul_nonneg (Work.FTS.EllipticEst.thEta_nonneg hs) (sq_nonneg _))
    · simp only [hEo t h, le_refl]
  -- the pointwise (slicewise) Poincaré inequality
  have hle : ∀ t : ℝ, Efun G δ z t ≤ C₀ * Rfun G δ z t := by
    intro t
    by_cases h : |Real.log z - t| ≤ δ
    · rw [hEw t h, hRw t h]
      exact hC₀ (Real.exp t) (Real.exp_pos t)
    · simp only [hEo t h, hRo t h, mul_zero, le_refl]
  have hpt : ∀ t : ℝ, ‖Efun G δ z t‖ ≤ C₀ * Rfun G δ z t := by
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (hEnn t)]
    exact hle t
  -- integrability of the left-hand side
  have hLint : MeasureTheory.Integrable (Efun G δ z) :=
    MeasureTheory.Integrable.mono' (hRint.const_mul C₀) hLaesm
      (Filter.Eventually.of_forall hpt)
  refine ⟨hLint, ?_⟩
  have hmono : (∫ t, Efun G δ z t) ≤ ∫ t, C₀ * Rfun G δ z t :=
    MeasureTheory.integral_mono_ae hLint (hRint.const_mul C₀)
      (Filter.Eventually.of_forall hle)
  rw [MeasureTheory.integral_const_mul] at hmono
  exact hmono

end Work.FTS.EllSol.EllPkgAux.MollDom
