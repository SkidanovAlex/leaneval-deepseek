/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Mine.TopSlotTwo`: the two top angular slots of the level-`2` elliptic estimate

Target (fixed statement, unchanged):

```
theorem TopSlotTwo : (∃ C, 0 < C ∧ TT.EllWeak0 C) →
    ∃ C, 0 < C ∧ ∀ α F Ψ, 0 < α → α ≤ 1/4 → TT.EllWeakPos α 2 F Ψ →
      α² √(Tk α 2 (z²∂_z²Ψ)) + √(Tk α 2 (∂_θ²Ψ)) ≤ C · HkNorm α 2 F
```

## The route (why the statement is true, and what it needs)

Write `A = z²∂_z²Ψ` and `B = ∂_θ²Ψ`.  With `D_θ²f = sin²(2θ)∂_θ²f + 2 sin(2θ)cos(2θ)∂_θf` and
`(v·Wt α z θ)² = w(z)²·v²·sGam α θ` (`mix_term_eq`), the two `Tk`-slots are controlled by the
bare angular derivatives with the weights `σ₄ = sin(2θ)^{4-γ}` and `σ₂ = sin(2θ)^{2-γ}`
(`γ = gam α`):

* `Tk α 2 f ≤ 2∫∫(∂_θ²f)²σ₄w² + 8∫∫(∂_θf)²σ₂w²`;

so it suffices to bound, for `f = A` and `f = B`, those two `z`-integrals.  For `f = B` this is
the paper's Steps 4 and 5 (`SliceStep4TwoD`, `SliceStep5TwoD`, the 1-D versions of which are
`remov/slice_step4`, `remov/slice_step5`); for `f = A` it follows from the identity
`z²∂_z²Ψ = D_z²Ψ - D_zΨ` and the level-`0` estimates for the radially shifted data
(`ShiftLevelOne`, `ShiftedTwoLtwo` via the hypothesis `EllWeak0`), together with the weighted
Agmon inequality on `A`.  The source `Gsrc α F Ψ` of the `θ`-equation is bounded with the
`F`-slots (`FSlotsTwoD`), the shifted `η`-estimates and `AngularBoundsTwoD`.
## Where the proof comes from (the two routes to this statement)

The *exploratory* route through the `Mine.*` pieces of this directory (`Mine.TkRedTwoD`,
`Mine.AngularBoundsTwoD`, `Mine.SourceBoundsTwoD`, `Mine.Step4TwoDGam`, `Mine.Step5TwoDGam`,
`Mine.FSlotsTwoD`, `Mine.ShiftZeroSlots2`, …) is mathematically the paper's Steps 1--5 and all
of those pieces are proved in the workspace, but it does **not** compose formally into this
statement: every one of them carries a *free* exponent `γ ∈ [1, 3/2]` with the hypothesis
`γ ≤ gam α` and an `∃ C` *inside* the `∀ γ` (`Mine/AngularBoundsTwoD.lean`,
`Mine/SourceBoundsTwoD.lean`, `Mine/FSlotsTwoD.lean`), while the target demands a single
constant uniform in `α`, i.e. it needs the slots at the `α`-dependent exponent
`γ = gam α = 1 + α/10`.  Extracting `C(gam α)` from `∃ C` under a `∀ γ` is not formally
possible without re-proving those leaves with an explicit (`γ`-independent) constant.
(The leaf analysis is the "`γ`-uniformity caveat" of
`Submission/Work/FTS/EllipticEst/TopSlotTwoFts/NOTES_TopSlotTwo.md`.)

The *canonical* route of the project avoids the free `γ` altogether: it works throughout with
the `α`-dependent weights of `HkIntegrand` and is therefore uniformly stated in `α`.  That route
is complete and verified in this workspace:

* `Final.Rep.TopSlotTwoFts.AHalfFinal` -- `Work.FTS.EllipticEst.TopSlotTwoFts.Tk_A_le`
  (`Tk α 2 (z²∂_z²Ψ) ≤ C·HkSq α 2 F`),
* `Final.Rep.TopSlotTwoFts.BHalf` -- `Work.FTS.EllipticEst.TopSlotTwoFts.Tk_B_le`
  (`Tk α 2 (∂_θ²Ψ) ≤ C·HkSq α 2 F`),

both axioms-clean (`[propext, Classical.choice, Quot.sound]`).  The proof below is the assembly
of those two halves into the requested statement: the `α²`-weighted square root of the first,
the square root of the second, `√(c·HkSq) = √c·HkNorm`, `α² ≤ 1` and `HkNorm ≥ 0`.

The seven pointwise helpers (`DthIter_two_eq` … `Tk_pointwise_le_closed`) that used to sit in
this file have moved to `Final/Rep/Mine/TopSlotTwo.lean`, which is byte-identical and is the
copy that the `Final/Rep` cone imports; keeping a second copy here would be a duplicate
declaration in any module that imports both (e.g. `Final/Rep/H2W/slot20_bound`).  The names
`Work.FTS.EllipticEst.Mine.DthIter_two_eq` etc. remain available to every consumer of this file,
transitively through the import below.
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.Final.Rep.TopSlotTwoFts.AHalfFinal
import Submission.Work.FTS.EllipticEst.Final.Rep.TopSlotTwoFts.BHalf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The integral form of `Tk_pointwise_le_closed`.**  If the pointwise bound holds on the
closed quadrant and the dominating function is `θ`-integrable for every `z ∈ Iz` and
`z`-integrable over `Iz` (after `θ`-integration), then `Tk α 2 f` is bounded by the iterated
integral of the dominating function. -/
theorem Tk_le_two_terms (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ)
    (hpt : ∀ z θ : ℝ, z ∈ Work.Spaces.Iz → θ ∈ Work.Spaces.Iθ →
      (Work.Spaces.DthIter 2 f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ 2 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
          + 8 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ))
    (hR : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
        2 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
          + 8 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ)) Work.Spaces.Iθ)
    (hRz : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
        2 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
          + 8 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    Work.FTS.EllipticEst.remov.Step.Tk α 2 f
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (2 * (Work.Spaces.w z) ^ 2 *
              ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2
                * sig4 (Work.Spaces.gam α) θ)
            + 8 * (Work.Spaces.w z) ^ 2 *
              ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ)) := by
  rw [Work.FTS.EllipticEst.remov.Step.Tk]
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ,
            (2 * (Work.Spaces.w z) ^ 2 *
                ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2
                  * sig4 (Work.Spaces.gam α) θ)
              + 8 * (Work.Spaces.w z) ^ 2 *
                ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ)) := by
    intro z hz
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hR z hz) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    rw [Work.Spaces.mixed_zero_left]
    exact hpt z θ hz hθ
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hRz ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz

/-- **The split form of the `Tk`-reduction**: under the outer-integrability side conditions,
`Tk α 2 f ≤ 2·∫∫(∂_θ²f)²σ₄w² + 8·∫∫(∂_θf)²σ₂w²`. -/
theorem Tk_le_two_split (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (f : ℝ → ℝ → ℝ)
    (hpt : ∀ z θ : ℝ, z ∈ Work.Spaces.Iz → θ ∈ Work.Spaces.Iθ →
      (Work.Spaces.DthIter 2 f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ 2 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
          + 8 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ))
    (hR : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
        2 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
          + 8 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ)) Work.Spaces.Iθ)
    (hRz : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
        2 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
          + 8 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hpθ : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
        2 * (Work.Spaces.w z) ^ 2 *
          ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ))
      Work.Spaces.Iθ)
    (hqθ : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
        8 * (Work.Spaces.w z) ^ 2 *
          ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ)) Work.Spaces.Iθ)
    (hpz : MeasureTheory.Integrable (fun z => 2 * (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hqz : MeasureTheory.Integrable (fun z => 8 * (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    Work.FTS.EllipticEst.remov.Step.Tk α 2 f
      ≤ 2 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2
                * sig4 (Work.Spaces.gam α) θ))
        + 8 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ)) := by
  have hsum := Tk_le_two_terms α hα f hpt hR hRz
  -- Step 1: the inner `θ`-integral of the sum splits into the two weighted integrals.
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          (2 * (Work.Spaces.w z) ^ 2 *
              ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
            + 8 * (Work.Spaces.w z) ^ 2 *
              ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ)))
        = 2 * ((Work.Spaces.w z) ^ 2 *
              (∫ θ in Work.Spaces.Iθ,
                (deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2
                  * sig4 (Work.Spaces.gam α) θ))
            + 8 * ((Work.Spaces.w z) ^ 2 *
              (∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ)) := by
    intro z hz
    have e : (fun θ => 2 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
          + 8 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ))
        = (fun θ => (fun θ => 2 * (Work.Spaces.w z) ^ 2 *
              ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2
                * sig4 (Work.Spaces.gam α) θ)) θ
          + (fun θ => 8 * (Work.Spaces.w z) ^ 2 *
              ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ)) θ) := rfl
    rw [e, MeasureTheory.integral_add (hpθ z hz) (hqθ z hz),
      MeasureTheory.integral_const_mul (2 * (Work.Spaces.w z) ^ 2) (fun θ =>
        (deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ),
      MeasureTheory.integral_const_mul (8 * (Work.Spaces.w z) ^ 2) (fun θ =>
        (deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ)]
    ring
  -- Step 2: the outer `z`-integral, after replacing the inner integral by the split form.
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (2 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
          + 8 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ)))
      = 2 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2
                * sig4 (Work.Spaces.gam α) θ))
        + 8 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ)) := by
    have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (2 * (Work.Spaces.w z) ^ 2 *
              ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
            + 8 * (Work.Spaces.w z) ^ 2 *
              ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ)))
        = ∫ z in Work.Spaces.Iz,
            (2 * ((Work.Spaces.w z) ^ 2 *
                (∫ θ in Work.Spaces.Iθ,
                  (deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2
                    * sig4 (Work.Spaces.gam α) θ))
              + 8 * ((Work.Spaces.w z) ^ 2 *
                (∫ θ in Work.Spaces.Iθ,
                  (deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ))) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      exact hinner z hz
    have hpz' : MeasureTheory.Integrable (fun z => 2 * ((Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      hpz.congr (Filter.Eventually.of_forall fun z => by ring)
    have hqz' : MeasureTheory.Integrable (fun z => 8 * ((Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      hqz.congr (Filter.Eventually.of_forall fun z => by ring)
    rw [h1, MeasureTheory.integral_add hpz' hqz',
      MeasureTheory.integral_const_mul (2 : ℝ) (fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)),
      MeasureTheory.integral_const_mul (8 : ℝ) (fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ))]
  exact le_trans hsum (le_of_eq houter)

/-- **`Y₁`**: the level-`0` (`η`-weighted) estimate for the radially shifted datum
`(D_zF, D_zΨ)`.  `EllWeak0` (witness as the *outer* hypothesis `h0`) applied to the shifted class
membership (taken here as a hypothesis so that this file need not import `Mine.ShiftLevelOne`,
whose closure currently contains another agent's module under construction) gives
`HkSq α 0 (∂_θ²(D_zΨ)) ≤ C₁·HkSq α 0 (D_zF)`; the two `HkSq α 0` are rewritten as iterated
integrals (`rad_term_eq`), and `HkSq α 0 (D_zF) ≤ HkSq α 2 F` is the `i = 1` slot
(`Work.Spaces.L2Sq_DzIter_le_HkSq`). -/
theorem Y1TwoD (h0 : ∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 (Work.Spaces.DzIter 1 F)
        (Work.Spaces.DzIter 1 Ψ) →
      Work.Spaces.HkMem α 2 F →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
            Work.FTS.EllipticEst.sEta θ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := h0
  refine ⟨C₁ + 1, by linarith, ?_⟩
  intro α F Ψ hα hα4 hshift hmemF
  have hZero : ∀ (g : ℝ → ℝ → ℝ) (z θ : ℝ), Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    intro g z θ
    simp [Work.Spaces.HkIntegrand]
  have hHk : ∀ g : ℝ → ℝ → ℝ, Work.Spaces.HkSq α 0 g
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    intro g
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
        = ∫ θ in Work.Spaces.Iθ,
            (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
      exact hZero g z θ
    have h2 : (∫ θ in Work.Spaces.Iθ,
            (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
      exact rad_term_eq hθ z (g z θ)
    rw [h1, h2, MeasureTheory.integral_const_mul]
  have hL2 : ∀ g : ℝ → ℝ → ℝ, Work.Spaces.HkSq α 0 g
      = Work.Spaces.L2Sq (fun z θ =>
          g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) := by
    intro g
    rw [Work.Spaces.HkSq, Work.Spaces.L2Sq]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => hZero g z θ)
  have hE := hC₁ α (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) hα hα4 hshift
  have hE2 : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
      ≤ C₁ * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 F) := by
    have hnn : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
      mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 _)
    linarith [hE]
  rw [hHk (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)), hHk (Work.Spaces.DzIter 1 F)] at hE2
  have hle : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 1 F z θ) ^ 2 *
          Work.FTS.EllipticEst.sEta θ)) ≤ Work.Spaces.HkSq α 2 F := by
    rw [← hHk (Work.Spaces.DzIter 1 F)]
    rw [hL2 (Work.Spaces.DzIter 1 F)]
    exact Work.Spaces.L2Sq_DzIter_le_HkSq α 2 F hmemF 1 (by norm_num)
  calc (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
          Work.FTS.EllipticEst.sEta θ))
      ≤ C₁ * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 1 F z θ) ^ 2 *
          Work.FTS.EllipticEst.sEta θ)) := hE2
    _ ≤ C₁ * Work.Spaces.HkSq α 2 F := mul_le_mul_of_nonneg_left hle hC₁pos.le
    _ ≤ (C₁ + 1) * Work.Spaces.HkSq α 2 F := by
        have hN := Work.Spaces.HkSq_nonneg α 2 F
        nlinarith [hN]

-- `TopSlotTwo` (statement unchanged, proof to be assembled from the delegated pieces).

theorem TopSlotTwo : (∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) →
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 2 (Work.Spaces.pthIter 2 Ψ))
        ≤ C * Work.Spaces.HkNorm α 2 F := by
  intro h0
  obtain ⟨CA, hCApos, hA⟩ := Work.FTS.EllipticEst.TopSlotTwoFts.Tk_A_le h0
  obtain ⟨CB, hCBpos, hB⟩ := Work.FTS.EllipticEst.TopSlotTwoFts.Tk_B_le h0
  refine ⟨Real.sqrt CA + Real.sqrt CB + 1, by positivity, fun α F Ψ hα hα4 hwk => ?_⟩
  have h1 : Work.FTS.EllipticEst.remov.Step.Tk α 2
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ≤ CA * Work.Spaces.HkSq α 2 F :=
    hA α F Ψ hα hα4 hwk
  have h2 : Work.FTS.EllipticEst.remov.Step.Tk α 2 (Work.Spaces.pthIter 2 Ψ)
      ≤ CB * Work.Spaces.HkSq α 2 F := hB α F Ψ hα hα4 hwk
  have hN : (0 : ℝ) ≤ Work.Spaces.HkNorm α 2 F := Work.Spaces.HkNorm_nonneg α 2 F
  have hsA : Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      ≤ Real.sqrt CA * Work.Spaces.HkNorm α 2 F := by
    refine le_trans (Real.sqrt_le_sqrt h1) ?_
    rw [Real.sqrt_mul hCApos.le]
    rfl
  have hsB : Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 2 (Work.Spaces.pthIter 2 Ψ))
      ≤ Real.sqrt CB * Work.Spaces.HkNorm α 2 F := by
    refine le_trans (Real.sqrt_le_sqrt h2) ?_
    rw [Real.sqrt_mul hCBpos.le]
    rfl
  have hA2 : α ^ 2 ≤ 1 := by nlinarith [hα4, hα]
  have hstep : α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 2 (Work.Spaces.pthIter 2 Ψ))
      ≤ α ^ 2 * (Real.sqrt CA * Work.Spaces.HkNorm α 2 F)
        + Real.sqrt CB * Work.Spaces.HkNorm α 2 F := by
    have h := mul_le_mul_of_nonneg_left hsA (sq_nonneg α)
    linarith [h, hsB]
  have hfinal : α ^ 2 * (Real.sqrt CA * Work.Spaces.HkNorm α 2 F)
        + Real.sqrt CB * Work.Spaces.HkNorm α 2 F
      ≤ (Real.sqrt CA + Real.sqrt CB + 1) * Work.Spaces.HkNorm α 2 F := by
    have hCA : (0 : ℝ) ≤ Real.sqrt CA := Real.sqrt_nonneg _
    have hkey : α ^ 2 * (Real.sqrt CA * Work.Spaces.HkNorm α 2 F)
        ≤ Real.sqrt CA * Work.Spaces.HkNorm α 2 F := by
      have h0' : (0 : ℝ) ≤ Real.sqrt CA * Work.Spaces.HkNorm α 2 F :=
        mul_nonneg hCA hN
      nlinarith [hA2, h0']
    have hexp : (Real.sqrt CA + Real.sqrt CB + 1) * Work.Spaces.HkNorm α 2 F
        = Real.sqrt CA * Work.Spaces.HkNorm α 2 F
          + Real.sqrt CB * Work.Spaces.HkNorm α 2 F + Work.Spaces.HkNorm α 2 F := by ring
    rw [hexp]
    linarith [hkey, hN]
  linarith [hstep, hfinal]


end Work.FTS.EllipticEst.Mine
