import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.BoseBox.CNodeDefs
import Submission.Work.BoseBox.fsT_fibre_aemeasurable
import Submission.Work.BoseBox.slotForm_eq_zero_of_nonpos
import Submission.Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.tKinAmbAEMeasurable`

**The ambient localised kinetic word `u ↦ tKinAmb N L ℓ d s ε_T b u Ψ` is a.e. strongly
measurable in the translation parameter `u` of the sliding box** (for a smooth state `Ψ`
supported in the corner box `([0,L]³)ᴺ`).

This is the (measurability) side condition of the `C` node `CKinAmb`, whose integrability
variant is `Work.BoseBox.CWordIntegrable` (`Submission/Work/BoseBox/tKinAmbIntegrable.lean`).
It is what lets the corpus write `∫_u tKinAmb … u Ψ du` at all.

## What the word is

`tKinAmb N L ℓ d s ε_T b u Ψ = tKinWord N ℓ d s ε_T b u Ψ = kinForm N ℓ d s ε_T b u Ψ`
(`CNodeDefs.lean`), i.e. FS `eq:Def_HB`'s kinetic part `Σ_i (𝒯_u)^{(i)}` as a quadratic form
on the `N`-body state:

    `kinForm N ℓ d s ε_T b u Ψ = Σ_i ℓ⁻³ ∫_x 1_{Λ(u)}(x_i)·fsT ℓ d s ε_T b u (fibre_i Ψ x)`,

with `Λ(u) = ℓu + [−ℓ/2,ℓ/2]³` the sliding box and `fsT = neuWord + gapWord + momWord + mainWord`
FS `eq:DefT`'s four kinetic pieces.

## Proof

The only delicate piece of `fsT` is `neuWord`, whose first factor `neuFrac` is an `sInf` over
variational trials rather than an integral; the measurability of all four pieces along the
slot-`i` fibre is the delegated node `Work.BoseBox.fsT_fibre_aemeasurable`.

Two degeneracies must be handled separately, since both make the *peeling* identity
`Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral` (which needs `0 < ℓ`, through the volume
`∫ indU = ℓ³`) unavailable:

* `ℓ ≤ 0`: the moving box is empty (`ℓ < 0`) or the prefactor `ℓ⁻³ = 0` vanishes (`ℓ = 0`), so
  every slot form is `0` (`Work.BoseBox.slotForm_eq_zero_of_nonpos`) and so is the word;
* the particle number `N = 0`: the word is an empty sum.

In the remaining case `0 < ℓ`, `N = n + 1`, the corner-box hypothesis on `Ψ` only enters to
produce `HasCompactSupport Ψ` (the corner box is a product of compact intervals for **every**
`L`), after which each slot form is peeled into the integral over the remaining configuration
of the fibre `z ↦ Ψ (kcInsN n i (z, r))`, and the product-measure Fubini measurability lemma
`AEStronglyMeasurable.integral_prod_right'` together with the joint measurability of the fibre
word gives the result; finite sums of a.e. strongly measurable functions are a.e. strongly
measurable.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real

namespace Work.BoseBox

/-- A state whose topological support lies in the corner box `([0,L]³)ᴺ` is compactly
supported — **for every** `L ∈ ℝ`, including the degenerate `L ≤ 0`: the corner box is a
product of compact intervals (`Icc 0 L` is compact whether or not it is empty), and for `L < 0`
it is empty while for `0 ≤ L` the box lies in the ball of radius `√3·L`. -/
lemma hasCompactSupport_of_tsupport_subset_box {N : ℕ} {L : ℝ}
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hsupp : tsupport Ψ ⊆ _root_.BoseGases.box N L) : HasCompactSupport Ψ := by
  rcases lt_or_ge L 0 with hL | hL
  · rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      exact HasCompactSupport.of_support_subset_isCompact Set.finite_univ.isCompact
        (fun x _ => Set.mem_univ x)
    · have hempty : _root_.BoseGases.box N L = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        have h1 : (x ⟨0, hN⟩ 0) ∈ Set.Icc (0 : ℝ) L := hx ⟨0, hN⟩ 0
        linarith [h1.1, h1.2]
      refine HasCompactSupport.of_support_subset_isCompact
        (K := (∅ : Set (Submission.BoseGases.X N))) isCompact_empty ?_
      intro x hx
      rw [hempty] at hsupp
      exact absurd (hsupp (subset_tsupport Ψ hx)) (Set.notMem_empty x)
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : Submission.BoseGases.X N) (Real.sqrt 3 * L)) ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact Submission.BoseGases.norm_le_of_mem_box hL (hsupp (subset_tsupport Ψ hx))

/-- **The kinetic word is a.e. strongly measurable in the box position, for `ℓ > 0`.**

Peeling the slot integral (`Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral`, valid because
`ℓ > 0`) turns the `i`-th summand of `kinForm (n+1)` into the integral over the remaining
configuration of the fibre word `fsT ℓ d s ε_T b u (z ↦ Ψ (kcInsN n i (z, r)))`; the joint
measurability of the latter in `(u, r)` is `Work.BoseBox.fsT_fibre_aemeasurable`, and
`AEStronglyMeasurable.integral_prod_right'` integrates it out.  For `N = 0` the word is an
empty sum, hence `0`. -/
theorem kinForm_aemeasurable_of_pos {N : ℕ} {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hcs : HasCompactSupport Ψ) :
    MeasureTheory.AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.kinForm N ℓ d s eT b u Ψ)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  cases N with
  | zero =>
    have h : (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.kinForm 0 ℓ d s eT b u Ψ)
        = fun _ => (0 : ℝ) := by
      funext u
      simp [Work.BoseKinLoc.kinForm]
    rw [h]
    exact aestronglyMeasurable_const
  | succ n =>
    have hpeel : (fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.BoseKinLoc.kinForm (n + 1) ℓ d s eT b u Ψ)
        = ∑ i : Fin (n + 1), fun u : EuclideanSpace ℝ (Fin 3) =>
            ∫ r : Submission.BoseGases.X n,
              Work.BoseKinLoc.fsT ℓ d s eT b u
                (fun z : EuclideanSpace ℝ (Fin 3) =>
                  Ψ (Submission.BoseGases.kcInsN n i (z, r))) := by
      funext u
      simp only [Work.BoseKinLoc.kinForm, Finset.sum_apply]
      exact Finset.sum_congr rfl (fun i _ =>
        Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral hℓ
          (Work.BoseKinLoc.fsT ℓ d s eT b u) u i Ψ)
    rw [hpeel]
    exact Finset.aestronglyMeasurable_sum _ (fun i _ =>
      MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (fsT_fibre_aemeasurable (ℓ := ℓ) (d := d) (s := s) (eT := eT) (b := b)
          hℓ hΨ hcs i))

/-- **The ambient localised kinetic word is a.e. strongly measurable in the translation
parameter.** -/
theorem tKinAmbAEMeasurable {N : ℕ} {L ℓ d s eT b : ℝ}
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hsupp : tsupport Ψ ⊆ _root_.BoseGases.box N L) :
    MeasureTheory.AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseBox.tKinAmb N L ℓ d s eT b u Ψ)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  by_cases hℓ : 0 < ℓ
  · have h := kinForm_aemeasurable_of_pos (N := N) (ℓ := ℓ) (d := d) (s := s) (eT := eT)
      (b := b) hℓ hΨ (hasCompactSupport_of_tsupport_subset_box hsupp)
    simpa only [Work.BoseBox.tKinAmb, Work.BoseBox.tKinWord] using h
  · have hℓ' : ℓ ≤ 0 := le_of_not_gt hℓ
    have hzero : (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.kinForm N ℓ d s eT b u Ψ)
        = fun _ => (0 : ℝ) := by
      funext u
      simp only [Work.BoseKinLoc.kinForm]
      exact Finset.sum_eq_zero fun i _ => slotForm_eq_zero_of_nonpos hℓ' _ u i Ψ
    rw [show (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseBox.tKinAmb N L ℓ d s eT b u Ψ)
        = (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.kinForm N ℓ d s eT b u Ψ)
        from rfl, hzero]
    exact aestronglyMeasurable_const

end Work.BoseBox
