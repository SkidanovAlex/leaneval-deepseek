import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.H2W.ShiftC.integrableOn_sinCos2_pzIter2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.Zpz.Aux

set_option autoImplicit false

/-!
# `integrable_and_swap_abs_pzIter2`

Box integrability and Fubini for the radial second derivative `∂_z²F` of a source which is
`C^∞` on the open quadrant and honest in `ℋ²`, at the level of the *weighted* `θ`-slices.

The pointwise input is the second-order slice bound

  `|∂_z²F(τ,θ)| ≤ (2/τ²)·√(HkIntegrand α 2 F τ θ)`   (`hpt`),

valid for `τ > 0` and `θ ∈ (0,π/2)`; the two integrability hypotheses `hsl`, `hout` say that
the right-hand side is an honest object: every `θ`-slice `√(HkIntegrand α 2 F τ ·)` is
integrable on `Iθ` for `τ ≥ 0`, and its `θ`-integral is integrable in `τ` on every `[a,b]`
with `a > 0`.

On the box `(z₀, x]` (with `z₀, x > 0`, so `τ ≥ min z₀ x > 0`) the bound `2/τ² ≤ 2/a²`,
`a := min z₀ x`, therefore turns the target into a constant multiple of `√(HkIntegrand)`,
which is integrable on the product box: this is Tonelli for a nonnegative integrand
(`Work.Spaces.integrable_prod_of_iterated`), the a.e. strong measurability coming from the
`C^∞`-smoothness of `F` on the open quadrant (`SmoothOpen`).  Fubini's theorem for interval
integrals (`MeasureTheory.intervalIntegral_integral_swap`) then gives the swap.

Every declaration in this file is fully proved and rests only on the axioms
`[propext, Classical.choice, Quot.sound]`.
-/

/-- A.e. strong measurability on the box `(a,b] × Iθ`, `0 < a`, of a function which is
continuous on the open quadrant.  The product measure on the box differs from the restriction
of the planar Lebesgue measure to the open rectangle `(a,b) × (0,π/2)` only by null sets. -/
theorem aesm_uncurry_prod_Ioc_Iθ_pzIter2 {g : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hz : (Set.Ioc a b : Set ℝ) =ᵐ[volume] Set.Ioo a b :=
    (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  have hprod : (Set.Ioc a b ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) =ᵐ[volume.prod volume]
      (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
  refine (hg.mono ?_).aestronglyMeasurable
    (isOpen_Ioo.prod isOpen_Ioo).measurableSet (μ := volume.prod volume)
  intro p hp
  exact ⟨lt_trans ha hp.1.1, hp.2⟩

theorem integrable_and_swap_abs_pzIter2 {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hpt : ∀ τ θ : ℝ, 0 < τ → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |Work.Spaces.pzIter 2 F τ θ|
        ≤ (2 / τ ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ))
    (hsl : ∀ τ : ℝ, 0 ≤ τ → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ)) Work.Spaces.Iθ)
    (hout : ∀ a b : ℝ, 0 < a → MeasureTheory.IntegrableOn
      (fun τ : ℝ => ∫ θ in Work.Spaces.Iθ,
        Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ)) (Set.Icc a b))
    {z₀ x : ℝ} (hz₀ : 0 < z₀) (hx : 0 < x) :
    MeasureTheory.Integrable (Function.uncurry (fun τ θ : ℝ => |Work.Spaces.pzIter 2 F τ θ|))
        ((MeasureTheory.volume.restrict (Set.uIoc z₀ x)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∫ θ in Work.Spaces.Iθ, (∫ τ in Set.uIoc z₀ x, |Work.Spaces.pzIter 2 F τ θ|))
        = ∫ τ in Set.uIoc z₀ x,
            (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 F τ θ|) := by
  set a : ℝ := min z₀ x with ha_def
  set b : ℝ := max z₀ x with hb_def
  have ha : 0 < a := by rw [ha_def]; exact lt_min hz₀ hx
  have hab : a ≤ b := by rw [ha_def, hb_def]; exact min_le_max
  have huIoc : Set.uIoc z₀ x = Set.Ioc a b := by
    rw [Set.uIoc, ha_def, hb_def]
  -- ## A.e. strong measurability of the two integrands on the box
  have hGmeas : AEStronglyMeasurable
      (Function.uncurry fun τ θ : ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ))
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    aesm_uncurry_prod_Ioc_Iθ_pzIter2
      (g := fun τ θ : ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ)) ha
      ((hsm.continuousOn_HkIntegrand α 2).sqrt)
  have hFmeas : AEStronglyMeasurable
      (Function.uncurry fun τ θ : ℝ => |Work.Spaces.pzIter 2 F τ θ|)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    aesm_uncurry_prod_Ioc_Iθ_pzIter2
      (g := fun τ θ : ℝ => |Work.Spaces.pzIter 2 F τ θ|) ha
      ((hsm.pzIter 2).continuousOn.abs)
  -- ## The `τ`-slices of `√(HkIntegrand)` are integrable, and so is their `θ`-integral
  have hslice : ∀ᵐ τ ∂(volume.restrict (Set.Ioc a b)),
      Integrable (fun θ : ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ))
        (volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      (fun τ hτ => hsl τ (le_of_lt (lt_trans ha hτ.1)))
  have houter : Integrable
      (fun τ : ℝ => ∫ θ, Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ)
        ∂(volume.restrict Work.Spaces.Iθ))
      (volume.restrict (Set.Ioc a b)) :=
    (hout a b ha).mono_set (fun τ hτ => ⟨le_of_lt hτ.1, hτ.2⟩)
  -- ## Tonelli for the nonnegative majorant `√(HkIntegrand)`
  have hGint : Integrable
      (Function.uncurry fun τ θ : ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ))
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.integrable_prod_of_iterated
      (μ := volume.restrict (Set.Ioc a b)) (ν := volume.restrict Work.Spaces.Iθ)
      (G := fun τ θ : ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ))
      (fun _ _ => Real.sqrt_nonneg _) hGmeas hslice houter).1
  have hmaj : Integrable
      (fun p : ℝ × ℝ => (2 / a ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 2 F p.1 p.2))
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    hGint.const_mul (2 / a ^ 2)
  -- ## Domination of `|∂_z²F|` by the majorant, a.e. on the box
  have hIntF : Integrable (Function.uncurry fun τ θ : ℝ => |Work.Spaces.pzIter 2 F τ θ|)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine Integrable.mono' hmaj hFmeas ?_
    rw [MeasureTheory.Measure.prod_restrict]
    have hθae : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
    have hboxae : (Set.Ioc a b ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) =ᵐ[volume.prod volume]
        (Set.Ioc a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      MeasureTheory.Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _) hθae
    rw [MeasureTheory.Measure.restrict_congr_set hboxae]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ioc.prod isOpen_Ioo.measurableSet) ?_
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hp1pos : 0 < p.1 := lt_trans ha hp1.1
    have hgoal : ‖Function.uncurry (fun τ θ : ℝ => |Work.Spaces.pzIter 2 F τ θ|) p‖
        = |Work.Spaces.pzIter 2 F p.1 p.2| := by
      rw [Real.norm_eq_abs, Function.uncurry_apply_pair, abs_abs]
    rw [hgoal]
    refine le_trans (hpt p.1 p.2 hp1pos hp2) ?_
    have hsq : a ^ 2 ≤ p.1 ^ 2 := pow_le_pow_left₀ (le_of_lt ha) (le_of_lt hp1.1) 2
    have hdiv : 2 / p.1 ^ 2 ≤ 2 / a ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos ha 2) hsq
    exact mul_le_mul_of_nonneg_right hdiv (Real.sqrt_nonneg _)
  -- ## The conclusion
  rw [huIoc]
  refine ⟨hIntF, ?_⟩
  have hIntF' : Integrable (Function.uncurry fun τ θ : ℝ => |Work.Spaces.pzIter 2 F τ θ|)
      ((volume.restrict (Set.uIoc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rwa [Set.uIoc_of_le hab]
  have hswap := MeasureTheory.intervalIntegral_integral_swap
    (μ := volume.restrict Work.Spaces.Iθ)
    (f := fun τ θ : ℝ => |Work.Spaces.pzIter 2 F τ θ|) hIntF'
  simp only [intervalIntegral.integral_of_le hab] at hswap
  exact hswap.symm

end Work.FTS.ClassCHon.Zpz.Aux
