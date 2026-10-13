/-
Copyright: work module for the Elgindi finite-time singularity project.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.integrable_prod_of_iterated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!

# Integrability on a box from integrability of the slices

Fubini–Tonelli bookkeeping used by the elliptic estimates of §'Elliptic Regularity
Estimates'.  For a source `g` which is

* continuous on the open quadrant `Q0 = (0,∞) × (0,π/2)`;
* nonnegative;
* slicewise integrable in `θ` on `Iθ = [0,π/2]` for every `s ∈ [a,b]` (`a > 0`);
* such that the *iterated* integral `s ↦ ∫_{Iθ} g s θ dθ` is integrable on `[a,b]`,

the uncurried `g` is integrable on the box `[a,b] × Iθ`.

The point of the lemma is that no *joint* measurability hypothesis is assumed: it is
deduced from continuity on the open quadrant, which differs from the box only by the two
null lines `θ = 0`, `θ = π/2` (note `a > 0`, so the radial boundary `z = 0` is not in the
box at all).  This is exactly the situation of the `z`-estimates, where the source is
`C^∞` only on the open quadrant.

PROOF.  `Measure.prod_restrict` turns the restricted planar Lebesgue measure on the box
into the product `(volume|{a ≤ · ≤ b}).prod (volume|Iθ)`, and
`Work.Spaces.aesm_of_continuousOn_Qd` (continuity on the open quadrant ⇒ a.e. strong
measurability for `(volume|Iz).prod (volume|Iθ)`) descends to the box by monotonicity of
the restricted measures (the box is contained in `Iz ×ˢ Iθ`, using `a > 0`).  The two
remaining hypotheses are precisely the slice and iterated-integral inputs of
`Work.Spaces.integrable_prod_of_iterated`, Tonelli for a nonnegative function.
-/

namespace Work.FTS.EllipticEst

set_option linter.unusedVariables false

theorem integrableOn_box_of_slice {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hnn : ∀ z θ : ℝ, 0 ≤ g z θ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hsl : ∀ s ∈ Set.Icc a b, MeasureTheory.IntegrableOn (fun θ : ℝ => g s θ) Work.Spaces.Iθ)
    (hint : MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, g s θ) (Set.Icc a b)) :
    MeasureTheory.IntegrableOn (Function.uncurry g) (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  -- The box sits inside `Iz ×ˢ Iθ` because `a > 0`.
  have hbox : Set.Icc a b ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ :=
    Set.prod_mono (fun x hx => le_trans (le_of_lt ha) hx.1) subset_rfl
  -- Restricting the product measure is monotone in the set.
  have hmono : (MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono hbox le_rfl
  -- Continuity on the open quadrant gives a.e. strong measurability on the box.
  have hAE : MeasureTheory.AEStronglyMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => g p.1 p.2) hg).mono_measure hmono
  -- The two Fubini inputs, read off from the hypotheses.
  have hslice : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
      MeasureTheory.Integrable (fun θ : ℝ => g s θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
    simpa only [MeasureTheory.IntegrableOn] using hsl s hs
  have houter : MeasureTheory.Integrable
      (fun s : ℝ => ∫ θ, g s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict (Set.Icc a b)) := by
    simpa only [MeasureTheory.IntegrableOn] using hint
  have hfin := (Work.Spaces.integrable_prod_of_iterated (G := g) hnn hAE hslice houter).1
  -- Identify the product measure with the restriction of the planar Lebesgue measure.
  have hEq : ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict]
    rfl
  rw [hEq] at hfin
  exact hfin

end Work.FTS.EllipticEst
