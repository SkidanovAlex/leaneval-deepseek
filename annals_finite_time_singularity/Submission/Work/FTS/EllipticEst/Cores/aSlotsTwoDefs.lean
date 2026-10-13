/-
Copyright: work module for the Elgindi finite-time singularity project.

**STATE (latest stretch — read `Cores/NOTES_aSlotsTwo_T1_T3_done_T2_wall.md` first).**
Of the three summands of the target's left-hand side, two are PROVED in separate, `sorry`-free
modules:

* `Cores/aSlotsTwoT1.lean` — `α⁴ · Tk α 1 (z²∂_z²Ψ) ≤ C HkSq α 2 F`;
* `Cores/aSlotsTwoT3.lean` — `α⁴ · Tk α 2 (z²∂_z²Ψ) ≤ C HkSq α 2 F` (it cites
  `TopSlotTwoFts.Tk_A_le`; the notes give a `TopSlotTwoFts`-free fallback proof);

so the target reduces to the single middle summand `α⁴ Tk α 1 (D_z (z²∂_z²Ψ)) ≤ C HkSq α 2 F`,
the workspace's known open *shifted `A`-slot* `EllTwoAsm.AShiftSlotTwo`.  Its recorded reduction
(`AShiftSlotTwo_of_aeSteps`) goes through `H2W.Ae.Step2`, `H2W.Ae.Step3` and `TT.interpGamma`;
`Step3` is proved, but the route through `Step2` is **blocked**: `remov.AeI1Paper` is mis-stated
(it omits the mixed-derivative honesty `HkMem α 0 (z ∂_z∂_θu)`).  The notes contain the
model-level analysis of why this slot is genuinely harder than the other two (it needs the
spectral/symbol mechanism, not just the level-0 estimates).

# `Cores/aSlotsTwo` — the `α⁴`-weighted `A`-slots of the level-`2` elliptic estimate

The target of this file is the statement (unchanged, at the bottom)

```
theorem aSlotsTwo (h0 : ∃ C, 0 < C ∧ TT.EllWeak0 C) :
  ∃ C > 0, ∀ α F Ψ, 0 < α → α ≤ 1/4 → TT.EllWeakPos α 2 F Ψ →
    α⁴ (Tk α 1 A + 3 Tk α 1 (D_z A) + Tk α 2 A) ≤ C · HkSq α 2 F,      A := z²∂_z²Ψ,
```

i.e. the `A`-half of the `Tk`-residual of Elgindi's `prop:H2` at level `2`
(`Tk α k f = ∫∫ (D_θ^k f · Wt α)²`).

## The reduction carried out here (sorry-free)

Write `A := z²∂_z²Ψ`.  The three summands of the left-hand side are

* `Tk α 1 A` — the level-`1` `A`-slot of the datum `(F, Ψ)`;
* `Tk α 1 (D_z A)` — because `D_z A = z²∂_z²(D_z Ψ)` on the open quadrant
  (`DzAmgm.ZsqPz2Comm`, i.e. `Tk_one_Dz_A_eq` below), this is the level-`1` `A`-slot of the
  radially shifted datum `(D_z F, D_z Ψ)`, and the weak class is stable under the radial shift
  (`Cores.Pieces.TL2.weakShiftTwoOne`, proved, clean);
* `Tk α 2 A` — the level-`2` `A`-top-slot (the paper's Step 5 slot of `A`).

The file isolates the two *analytic* inputs which the present state of the library does not
supply — they are the two open gaps recorded in `Cores/NOTES_topSlotsTwo.md` §3–4 and
`Mine/NOTES_ASlotOne.md` — and *proves* the bookkeeping that turns them into the target:

* `AslotLvl1` — the level-`1` `A`-slot `α²√(Tk α 1 (z²∂_z²Ψ)) ≤ C|F|_{ℋ¹}` of the weak class
  (`= Mine.ASlotOne`, `AeMom.aslotOne`, `Dispatch.aslot_one`); its notes record that every
  naive norm chain closes only as `X ≤ X + C`, the missing ingredient being the paper's Step-4
  pairing (the negative-definite bracket in the variable `Ψ/cos θ`);
* `AslotLvl2` — the level-`2` `A`-top-slot `α⁴ Tk α 2 (z²∂_z²Ψ) ≤ C|F|²_{ℋ²}`; by the *proved*
  `Cores.Pieces.TL2.A_top_slot_two` this follows from the two level-`1` bounds
  `α²|z²∂_z²Ψ|_{ℋ¹} + |∂_θθΨ|_{ℋ¹} ≤ D|F|_{ℋ²}` (for the datum and for its radial shift), i.e.
  from `AslotLvl1` together with the level-`1` `B`-slot (`Mine.BSlotOne`).

Everything else — the descent `EllWeakPos α 2 → EllWeakPos α 1`, the radial shift of the class,
`HkSq α 1 (D_z F) ≤ 6 HkSq α 2 F` and `HkSq α 1 F ≤ HkSq α 2 F` — is proved here from the clean
library.
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.remov.Baux.Tk_congr_open
import Submission.Work.FTS.EllipticEst.remov.HkSq_Dz_shift_le
import Submission.Work.FTS.EllipticEst.remov.smoothOpen_slices_weak
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.Cores.Pieces.TL2.shiftZeroSlots
import Submission.Work.FTS.EllipticEst.Cores.Pieces.TL2.weakShiftTwoOne
import Submission.Work.FTS.EllipticEst.Cores.pPureShiftTwoAlpha4
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDescent

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## The two analytic inputs -/

/-- **The level-`1` `A`-slot** (`A = z²∂_z²Ψ`) of the weak class, conditional on the level-`0`
estimate: `α²√(Tk α 1 A) ≤ C|F|_{ℋ¹}`.  This is the statement of `Mine.ASlotOne`
(also `AeMom.aslotOne`, `Dispatch.aslot_one`). -/
def AslotLvl1 : Prop :=
  (∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) →
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 1 F Ψ →
      α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        ≤ C * Work.Spaces.HkNorm α 1 F

/-- **The level-`2` `A`-top-slot**: `α⁴ Tk α 2 (z²∂_z²Ψ) ≤ C|F|²_{ℋ²}` for the weak class. -/
def AslotLvl2 : Prop :=
  (∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀) →
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        ≤ C * Work.Spaces.HkSq α 2 F

/-! ## The identification of the shifted `A`-slot -/

/-- **`D_z (z²∂_z²Ψ) = z²∂_z²(D_z Ψ)` on the open quadrant**: `DzAmgm.ZsqPz2Comm` at
`(m,i) = (1,0)`. -/
theorem Dz_zsq_pzIter_two_agree {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) := by
  intro z θ hz hθ hlt
  have h := Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hΨ 1 0
    (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hz, ⟨hθ, hlt⟩⟩)
  exact h.symm

/-- **The second `Tk`-slot is the level-`1` `A`-slot of the radially shifted datum.** -/
theorem Tk_one_Dz_A_eq {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.remov.Step.Tk α 1
        (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      = Work.FTS.EllipticEst.remov.Step.Tk α 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
  Work.FTS.EllipticEst.remov.Baux.Tk_congr_open
    (fun z θ hz hθ hlt => Dz_zsq_pzIter_two_agree hΨ z θ hz hθ hlt)

/-! ## The (clean) level-`0` slots of the radially shifted datum

`Cores/Pieces/TL2/shiftZeroSlots` proves the level-`0` slots of `D_z^j Ψ` for every `j ≤ k`, but
its *instantiation* passes the still-`sorry` dilation estimate `Dil.HkMem_dq_le`, so that module
is `sorryAx`-tainted.  The underlying proof `shiftZeroSlots_bound`/`shiftZeroSlots_aux` is
*parameterised* over the dilation estimate, and the estimate is proved (cleanly, elsewhere) as
`Cores.dilEstimate_fts` (`Cores/pPureShiftTwoAlpha4.lean`, from
`Cores.pPureShiftAux.HkMem_dq_and_HkSq_dq_le_self`).  Feeding the proved one gives an
axiom-clean version of the whole interface. -/

/-- **The level-`0` slots of the `j`-times radially shifted datum**, axiom-clean. -/
theorem shiftZeroSlots_clean (k j : ℕ) (hj : j ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      (∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀) →
      α ^ 4 * Work.Spaces.HkSq α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ)
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
        ≤ C * Work.Spaces.HkSq α k F :=
  Work.FTS.EllipticEst.Cores.Pieces.TL2.shiftZeroSlots_aux
    (Work.FTS.EllipticEst.Cores.dilEstimate_fts)
    (Work.FTS.EllipticEst.Cores.Dil.dqIterTendsto) k j hj

/-- **The twice shifted level-`0` `B`-slot** (`j = 2`, `k = 2`), axiom-clean: this is the input
`X₂` of the route through `Mine.Tk_le_two_split`. -/
theorem HkSq_zero_pthIter_two_DzIter_two_le
    (h0 : ∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C, hCpos, hC⟩ := shiftZeroSlots_clean 2 2 le_rfl
  refine ⟨C, hCpos, ?_⟩
  intro α F Ψ hα hα4 hwk
  have h := hC α F Ψ hα hα4 hwk h0
  have hnn : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) :=
    mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg _ _ _)
  linarith

/-- **The once shifted level-`0` `B`-slot** (`j = 1`, `k = 2`), axiom-clean: the input `X₁`. -/
theorem HkSq_zero_pthIter_two_DzIter_one_le
    (h0 : ∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C, hCpos, hC⟩ := shiftZeroSlots_clean 2 1 (by norm_num)
  refine ⟨C, hCpos, ?_⟩
  intro α F Ψ hα hα4 hwk
  have h := hC α F Ψ hα hα4 hwk h0
  have hnn : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
    mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg _ _ _)
  linarith

/-! ## Plumbing for the `Tk α 2 A`-reduction: a.e.-measurability of the slots

The forward comparison `Mine.Tk_le_two_split` / `Mine.Tk_le_two_terms` needs the (slice and
outer) integrability of the majorant `2 w(z)² (∂_θ²A)² σ₄(θ) + 8 (D_θ A · Wt)²`, i.e.
`a.e.`-strong measurability of the two pieces together with domination by honest `ℋ`-slots.
The mixed piece is handled by the *proved* `Mine.B_top_slot_bound.aesm_mixed_slot` /
`integrableOn_mixed_slot_of_HkMem`; the radial piece `(∂_θ²A)² w² σ₄` is handled here: `A` is
`C^∞` on the open quadrant, hence so is `∂_θ²A` *jointly*, and
`Work.Spaces.aesm_of_continuousOn_Qd` / `aesm_slice_of_continuousOn_Qd` apply. -/

/-- `∂_θ²A = pth (pth A)` is smooth on the open quadrant when `A` is. -/
theorem smoothOpen_pthIter_two {A : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 A) := by
  rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  exact (Work.FTS.EllipticEst.SmoothOpen.pth hA).pth

/-- The weight `w(z)²·sin(2θ)^{4-γ}` is continuous on the open quadrant. -/
theorem continuousOn_w_sq_sig4 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (4 - Work.Spaces.gam α))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        = fun p : ℝ × ℝ => (((1 + p.1) ^ 2 / p.1 ^ 2)) ^ 2 := by
      funext p; rfl
    rw [hfun]
    exact ContinuousOn.pow (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2
        (ne_of_gt (Set.mem_Ioi.mp hp.1)))) 2
  have hs : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (4 - Work.Spaces.gam α))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
        (by
          change (0 : ℝ) < 2 * p.2
          have h : (0 : ℝ) < p.2 := (Set.mem_Ioo.mp hp.2).1
          linarith)
        (by
          change 2 * p.2 < Real.pi
          have h : p.2 < Real.pi / 2 := (Set.mem_Ioo.mp hp.2).2
          linarith [h, Real.pi_pos]))))
  exact hw.mul hs

/-- **The radial piece is a.e. strongly measurable**, on the product measure and on every
vertical slice. -/
theorem aesm_pthIter_two_A_sig4 (α : ℝ) {A : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.pthIter 2 A p.1 p.2) ^ 2
        * ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (4 - Work.Spaces.gam α)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    ∧ ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.pthIter 2 A z θ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hpth : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 A) :=
    smoothOpen_pthIter_two hA
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pthIter 2 A p.1 p.2) ^ 2
      * ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (4 - Work.Spaces.gam α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (ContinuousOn.pow hpth.continuousOn 2).mul (continuousOn_w_sq_sig4 α)
  refine ⟨Work.Spaces.aesm_of_continuousOn_Qd _ hcont, fun z hz => ?_⟩
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hzero : (fun θ : ℝ => (Work.Spaces.pthIter 2 A z θ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)))
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [← hz0, Work.Spaces.w]
      norm_num
    rw [hzero]
    exact aestronglyMeasurable_const
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos

/-! ## A local weight identity (clean cone)

`sin(2θ)²·Wt(α,z,θ)² = w(z)²·sin(2θ)^{2-γ}`, i.e. `sin(2θ)²·Wt² = w²·σ₂` where
`σ₂ = sig2 γ`.  A local copy so that the integrability plumbing depends on no module outside
this file's own (clean) import cone; the identity is the one used to identify the `σ₂`-weighted
plain `θ`-derivative slot with `(D_θA·Wt)²`. -/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- **The level-`1` weight identity.** -/
theorem sin_sq_mul_Wt_sq_self (α z θ : ℝ) (hα4 : α ≤ 1 / 4) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ' hθ
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ (2 : ℕ)
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_mul_natCast hs (-(Work.Spaces.gam α / 2)) 2]
    congr 1
    push_cast
    ring
  have htwo : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
    have hne : ((2 : ℕ) : ℝ) + (-(Work.Spaces.gam α)) ≠ 0 := by
      rw [Work.Spaces.gam]
      push_cast
      intro hc
      linarith
    rw [← Real.rpow_natCast (Real.sin (2 * θ)) 2,
      ← Real.rpow_add' (x := Real.sin (2 * θ)) hs (y := ((2 : ℕ) : ℝ))
        (z := -(Work.Spaces.gam α)) hne]
    congr 1 <;> push_cast <;> ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, h1]
  calc (Real.sin (2 * θ)) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = (Work.Spaces.w z) ^ 2
          * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by rw [htwo]

/-! ## Item 2: the reverse comparison of the second-order `θ`-slot

`(∂_θ²f)² · sin(2θ)^{4-γ} · w² ≤ 2 (D_θ²f · Wt)² + 8 (D_θf · Wt)²`, from the expansion
`D_θ²f = 2 cos(2θ) · D_θ f + sin(2θ)² · ∂_θ²f` and `cos² ≤ 1`.  A local copy (both the
expansion and the comparison) so that the integrability plumbing below depends on no module
outside this file's own clean import cone. -/

/-- **The expansion of `D_θ²`**: `D_θ² f = 2 cos(2θ) · D_θ f + sin(2θ)² · ∂_θ² f`. -/
theorem DthIter_two_eq_self (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth f z θ') θ) :
    Work.Spaces.DthIter 2 f z θ
      = 2 * Real.cos (2 * θ) * Work.Spaces.Dth f z θ
        + (Real.sin (2 * θ)) ^ 2 * Work.Spaces.pthIter 2 f z θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => (2 : ℝ) * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h3 := (Real.hasDerivAt_sin (2 * θ)).comp θ h2
    simpa [Function.comp_def, mul_comm] using h3
  have hg : HasDerivAt (fun θ' : ℝ => Work.Spaces.pth f z θ')
      (Work.Spaces.pthIter 2 f z θ) θ := h.hasDerivAt
  have hmul := hsin.mul hg
  have hderiv : deriv (fun θ' => Real.sin (2 * θ') * Work.Spaces.pth f z θ') θ
      = 2 * Real.cos (2 * θ) * Work.Spaces.pth f z θ
        + Real.sin (2 * θ) * Work.Spaces.pthIter 2 f z θ := by
    rw [show (fun θ' : ℝ => Real.sin (2 * θ') * Work.Spaces.pth f z θ')
        = (fun θ' : ℝ => Real.sin (2 * θ')) * (fun θ' : ℝ => Work.Spaces.pth f z θ')
        from rfl]
    exact hmul.deriv
  show Real.sin (2 * θ)
      * deriv (fun θ' => Real.sin (2 * θ') * Work.Spaces.pth f z θ') θ = _
  rw [hderiv]
  simp only [Work.Spaces.Dth]
  ring

/-- **The reverse comparison** (local copy): the bare weighted second `θ`-derivative is
dominated by the two `D_θ`-slots. -/
theorem pthIter_two_sq_sig4_le_self (α : ℝ) (hα4 : α ≤ 1 / 4) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ)
    (h2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth f z θ') θ) :
    (Work.Spaces.pthIter 2 f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)
        * (Work.Spaces.w z) ^ 2
      ≤ 2 * (Work.Spaces.DthIter 2 f z θ * Work.Spaces.Wt α z θ) ^ 2
        + 8 * (Work.Spaces.DthIter 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ' hθ
  have hc : (Real.cos (2 * θ)) ^ 2 ≤ 1 := Real.cos_sq_le_one (2 * θ)
  have hexp := DthIter_two_eq_self f (z := z) (θ := θ) h2
  -- the weight identity `s⁴ · (Wt)² = w² · s^{4-γ}`
  have hs4 : (Real.sin (2 * θ)) ^ 4 * (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := by
    have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ (2 : ℕ)
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [← Real.rpow_mul_natCast hs (-(Work.Spaces.gam α / 2)) 2]
      congr 1
      push_cast
      ring
    have h2 : (Real.sin (2 * θ)) ^ 4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := by
      have hne : ((4 : ℕ) : ℝ) + (-(Work.Spaces.gam α)) ≠ 0 := by
        rw [Work.Spaces.gam]
        push_cast
        intro hc'
        linarith
      rw [← Real.rpow_natCast (Real.sin (2 * θ)) 4,
        ← Real.rpow_add' (x := Real.sin (2 * θ)) hs (y := ((4 : ℕ) : ℝ))
          (z := -(Work.Spaces.gam α)) hne]
      congr 1 <;> push_cast <;> ring
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, h1]
    calc (Real.sin (2 * θ)) ^ 4
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        = (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ 4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
      _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := by rw [h2]
  -- the key identity: `sin(2θ)² · ∂_θ²f = D_θ²f - 2cos(2θ)·D_θf`
  have hkey : (Real.sin (2 * θ)) ^ 2 * Work.Spaces.pthIter 2 f z θ
      = Work.Spaces.DthIter 2 f z θ
        - 2 * Real.cos (2 * θ) * Work.Spaces.DthIter 1 f z θ := by
    rw [hexp]
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth]
    ring
  -- reduce to the algebraic core
  have h1 : (Work.Spaces.pthIter 2 f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)
        * (Work.Spaces.w z) ^ 2
      = ((Real.sin (2 * θ)) ^ 2 * Work.Spaces.pthIter 2 f z θ) ^ 2
        * (Work.Spaces.Wt α z θ) ^ 2 := by
    rw [show (Work.Spaces.pthIter 2 f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) * (Work.Spaces.w z) ^ 2
        = (Work.Spaces.pthIter 2 f z θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)) by ring,
      ← hs4]
    ring
  rw [h1, hkey]
  -- the algebraic core
  have hstep : (Work.Spaces.DthIter 2 f z θ
        - 2 * Real.cos (2 * θ) * Work.Spaces.DthIter 1 f z θ) ^ 2
      ≤ 2 * (Work.Spaces.DthIter 2 f z θ) ^ 2
        + 8 * (Real.cos (2 * θ)) ^ 2 * (Work.Spaces.DthIter 1 f z θ) ^ 2 :=
    by nlinarith [sq_nonneg (Work.Spaces.DthIter 2 f z θ
      + 2 * Real.cos (2 * θ) * Work.Spaces.DthIter 1 f z θ)]
  have hstep2 : (2 * (Work.Spaces.DthIter 2 f z θ) ^ 2
        + 8 * (Real.cos (2 * θ)) ^ 2 * (Work.Spaces.DthIter 1 f z θ) ^ 2)
        * (Work.Spaces.Wt α z θ) ^ 2
      ≤ (2 * (Work.Spaces.DthIter 2 f z θ) ^ 2
        + 8 * (Work.Spaces.DthIter 1 f z θ) ^ 2) * (Work.Spaces.Wt α z θ) ^ 2 := by
    have hW2 : 0 ≤ (Work.Spaces.Wt α z θ) ^ 2 := sq_nonneg _
    have hle : (Real.cos (2 * θ)) ^ 2 * (Work.Spaces.DthIter 1 f z θ) ^ 2
        ≤ 1 * (Work.Spaces.DthIter 1 f z θ) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    nlinarith [hW2, hle]
  have hmain : (Work.Spaces.DthIter 2 f z θ
        - 2 * Real.cos (2 * θ) * Work.Spaces.DthIter 1 f z θ) ^ 2
        * (Work.Spaces.Wt α z θ) ^ 2
      ≤ (2 * (Work.Spaces.DthIter 2 f z θ) ^ 2
        + 8 * (Work.Spaces.DthIter 1 f z θ) ^ 2) * (Work.Spaces.Wt α z θ) ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_right hstep (sq_nonneg _)) hstep2
  refine le_trans hmain ?_
  ring_nf
  linarith [sq_nonneg (Work.Spaces.DthIter 2 f z θ * Work.Spaces.Wt α z θ),
    sq_nonneg (Work.Spaces.DthIter 1 f z θ * Work.Spaces.Wt α z θ)]

/-! ## The assembly -/

/-- **The target from the two slot inputs.** -/
theorem aSlotsTwo_of_pieces
    (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C)
    (hA : AslotLvl1) (hT : AslotLvl2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * (Work.FTS.EllipticEst.remov.Step.Tk α 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1
            (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          + Work.FTS.EllipticEst.remov.Step.Tk α 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C₁, hC₁pos, hA⟩ := hA h0
  obtain ⟨C₂, hC₂pos, hT⟩ := hT h0
  refine ⟨21 * C₁ ^ 2 + C₂ + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 hwk
  -- the smoothness of the four fields on the open quadrant
  obtain ⟨hFso, hΨso, hAso, hBso⟩ :=
    Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 0
  have hFsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hFso
  have hAsm : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hAso
  have hBsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hBso
  -- the datum at level `1`, and its radial shift
  have h1 : Work.FTS.EllipticEst.TT.EllWeakPos α 1 F Ψ :=
    ⟨hwk.eq, hwk.zero, hwk.pi_half, hwk.orthF, hwk.orthPsi, hwk.smooth,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 1) (l := 2)
        (by norm_num) hFsm hwk.memF,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 1) (l := 2)
        (by norm_num) hAsm hwk.memA,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 1) (l := 2)
        (by norm_num) hBsm hwk.memB,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 1) (l := 2)
        (by norm_num) (Work.FTS.EllipticEst.TT.smoothOpen_diagHon hBsm) hwk.memZPth2⟩
  have hshift : Work.FTS.EllipticEst.TT.EllWeakPos α 1
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
    Work.FTS.EllipticEst.Cores.Pieces.TL2.weakShiftTwoOne (α := α) (k := 2)
      (by norm_num) hwk
  -- the three slot estimates
  have e₁ := hA α F Ψ hα hα4 h1
  have e₂ := hA α (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) hα hα4 hshift
  have e₃ := hT α F Ψ hα hα4 hwk
  -- the two norm comparisons
  have hnorm₁ : Work.Spaces.HkNorm α 1 F ≤ Work.Spaces.HkNorm α 2 F := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt
      (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num : 1 ≤ 2) hwk.memF)
  have hnorm₂ : Work.Spaces.HkNorm α 1 (Work.Spaces.DzIter 1 F)
      ≤ Real.sqrt 6 * Work.Spaces.HkNorm α 2 F := by
    have hz := Work.FTS.EllipticEst.remov.HkSq_Dz_shift_le (k := 2) (by norm_num) α F hFsm
      hwk.memF
    have h6 : Work.Spaces.HkSq α 1 (Work.Spaces.DzIter 1 F)
        ≤ 6 * Work.Spaces.HkSq α 2 F := by
      have h' : Work.Spaces.HkSq α (2 - 1) (Work.Spaces.Dz F)
          ≤ (((2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) * Work.Spaces.HkSq α 2 F := hz
      norm_num at h'
      exact h'
    calc Work.Spaces.HkNorm α 1 (Work.Spaces.DzIter 1 F)
        = Real.sqrt (Work.Spaces.HkSq α 1 (Work.Spaces.DzIter 1 F)) := rfl
      _ ≤ Real.sqrt (6 * Work.Spaces.HkSq α 2 F) := Real.sqrt_le_sqrt h6
      _ = Real.sqrt 6 * Real.sqrt (Work.Spaces.HkSq α 2 F) := Real.sqrt_mul (by norm_num) _
      _ = Real.sqrt 6 * Work.Spaces.HkNorm α 2 F := rfl
  -- the three squared bounds
  have hsq₁ : α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      ≤ C₁ ^ 2 * Work.Spaces.HkSq α 2 F := by
    have hnn : 0 ≤ Work.FTS.EllipticEst.remov.Step.Tk α 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.FTS.EllipticEst.remov.Step.Tk_nonneg _ _ _
    have hx : 0 ≤ α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      mul_nonneg (sq_nonneg α) (Real.sqrt_nonneg _)
    have hy : 0 ≤ C₁ * Work.Spaces.HkNorm α 2 F :=
      mul_nonneg hC₁pos.le (Work.Spaces.HkNorm_nonneg α 2 F)
    have hle : α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        ≤ C₁ * Work.Spaces.HkNorm α 2 F :=
      le_trans e₁ (mul_le_mul_of_nonneg_left hnorm₁ hC₁pos.le)
    have hsq : (α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) ^ 2
        ≤ (C₁ * Work.Spaces.HkNorm α 2 F) ^ 2 := by nlinarith
    have hlhs : (α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) ^ 2
        = α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
      rw [mul_pow, Real.sq_sqrt hnn]
      ring
    have hrhs : (C₁ * Work.Spaces.HkNorm α 2 F) ^ 2
        = C₁ ^ 2 * Work.Spaces.HkSq α 2 F := by
      rw [mul_pow, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 2 F)]
    rw [hlhs, hrhs] at hsq
    exact hsq
  have hsq₂ : α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
        (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      ≤ 6 * C₁ ^ 2 * Work.Spaces.HkSq α 2 F := by
    have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
      Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
    rw [Tk_one_Dz_A_eq (α := α) (Ψ := Ψ) hΨsm]
    have hnn : 0 ≤ Work.FTS.EllipticEst.remov.Step.Tk α 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
      Work.FTS.EllipticEst.remov.Step.Tk_nonneg _ _ _
    have hle : α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ))
        ≤ C₁ * (Real.sqrt 6 * Work.Spaces.HkNorm α 2 F) :=
      le_trans e₂ (mul_le_mul_of_nonneg_left hnorm₂ hC₁pos.le)
    have hx : 0 ≤ α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)) :=
      mul_nonneg (sq_nonneg α) (Real.sqrt_nonneg _)
    have hy : 0 ≤ C₁ * (Real.sqrt 6 * Work.Spaces.HkNorm α 2 F) :=
      mul_nonneg hC₁pos.le (mul_nonneg (Real.sqrt_nonneg 6)
        (Work.Spaces.HkNorm_nonneg α 2 F))
    have hsq : (α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ))) ^ 2
        ≤ (C₁ * (Real.sqrt 6 * Work.Spaces.HkNorm α 2 F)) ^ 2 := by nlinarith
    have hlhs : (α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ))) ^ 2
        = α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) := by
      rw [mul_pow, Real.sq_sqrt hnn]
      ring
    have hrhs : (C₁ * (Real.sqrt 6 * Work.Spaces.HkNorm α 2 F)) ^ 2
        = 6 * C₁ ^ 2 * Work.Spaces.HkSq α 2 F := by
      rw [mul_pow, mul_pow, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 2 F),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
      ring
    rw [hlhs, hrhs] at hsq
    exact hsq
  -- the final arithmetic
  have hnn : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  rw [mul_add, mul_add]
  have hshape : α ^ 4 * (3 * Work.FTS.EllipticEst.remov.Step.Tk α 1
        (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
      = 3 * (α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
        (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) := by ring
  rw [hshape]
  nlinarith [hsq₁, hsq₂, e₃, hnn]

end

end Work.FTS.EllipticEst.Cores
