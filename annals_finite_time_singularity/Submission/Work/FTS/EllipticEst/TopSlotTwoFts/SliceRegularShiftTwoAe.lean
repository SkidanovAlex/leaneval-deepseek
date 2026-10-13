import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.FTS.EllipticEst.H2W.Fstar_DzIter_two_F
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.FstarDzIterFourAe
import Submission.Work.H2W.momentChainAe
import Submission.Work.FTS.EllipticEst.H2W.slot11_fix.slot11_Acont_clean

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# Slice regularity of the twice radially shifted solution, a.e. in `z`

The target is

```
theorem SliceRegularShiftTwoAe {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hwk : TT.EllWeakPos α 2 F Ψ) :
    ∀ᵐ z ∂(volume.restrict (Ioi 0)),
      ContinuousOn (fun θ => DzIter 2 Ψ z θ) (Icc 0 (π/2)) ∧
      DzIter 2 Ψ z 0 = 0 ∧ DzIter 2 Ψ z (π/2) = 0 ∧
      IntegrableOn (fun θ => (pthIter 2 (DzIter 2 Ψ) z θ) ^ 2 * sEta θ) Iθ ∧
      IntegrableOn (fun θ => (deriv (fun t => DzIter 2 Ψ z t) θ) ^ 2) Iθ ∧
      IntegrableOn (fun θ => (DzIter 2 Ψ z θ) ^ 2) Iθ
```

i.e. the angular slice `θ ↦ D_z²Ψ(z,·)` is, for almost every `z > 0`, continuous on the
closed angular interval with vanishing endpoints, and has its three relevant `θ`-energies
(the `η`-weighted square of the second `θ`-derivative, and the plain squares of the first
`θ`-derivative and of the function itself) honest.

## Route

* **Conjunct 1** (`ContinuousOn`).  `D_z²Ψ = D_zΨ + z²∂_z²Ψ` on the open interval; the
  `D_zΨ`-slice is continuous on `[0,π/2]` for *every* `z > 0` (`Work.H2W.weakSliceContinuousKit`)
  and the `z²∂_z²Ψ`-slice for almost every `z > 0` (its two one-sided endpoint limits are
  controlled by the moments `F_*(D_z²F)`, `F_*(D_z⁴Ψ)`, which vanish a.e.).  This is exactly
  `Work.FTS.EllipticEst.H2W.slot11_fix.slot11_Acont_clean`, the *clean* (import-graph
  unpolluted) copy of `Work.FTS.EllipticEst.H2W.slot11_Acont` / `Work.H2W.weakSliceZContinuousAe`;
  we only convert its measure `volume.restrict Iz` into `volume.restrict (Ioi 0)` (the two
  differ by the null set `{0}`) and drop its first conjunct.

* **Conjuncts 2, 3** (endpoint values).  `Ψ · 0` and `Ψ · (π/2)` vanish identically
  (`EllWeakPos.zero`, `EllWeakPos.pi_half`), so all their `z`-derivatives vanish too.

* **Conjunct 4** (the `η`-weighted second `θ`-derivative).  On the open interval
  `pthIter 2 (D_z²Ψ) = D_z²(pthIter 2 Ψ)` (Clairaut,
  `remov.ws_pthIter_two_DzIter`), and `(D_z²(pthIter 2 Ψ))²·sEta` is the `i = 2` slot of
  `HkMem α 2 (pthIter 2 Ψ)` (the field `EllWeakPos.memB`) by `remov.ws_slot_slice`.

* **Conjuncts 5, 6** (the plain squares).  `abs_le_of_sq_mul_sEta` (conjunct 4 gives the
  weighted square of the second `θ`-derivative) bounds the slice and its `θ`-derivative on the
  open interval by a constant `C`; both are then dominated by the constant `C²` on the
  finite-measure `Iθ`.
-/

namespace Work.FTS.EllipticEst.TopSlotTwoFts

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

variable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}

/-! ## The two endpoint values of the `D_z²Ψ`-slice -/

/-- The slice `θ ↦ D_z²Ψ(z,θ)` vanishes at `θ = 0`: it is `z` times the `z`-derivative of the
identically vanishing function `z' ↦ D_zΨ(z',0)`. -/
theorem dzIter_two_zero_left (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.DzIter 2 Ψ z 0 = 0 := by
  have hfun : (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' 0) = fun _ => (0 : ℝ) :=
    funext fun z' => Work.H2W.dz_zero_at_zero h z'
  show z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z 0 = 0
  rw [show Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z 0
      = deriv (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' 0) z from rfl, hfun, deriv_const,
    mul_zero]

/-- The slice `θ ↦ D_z²Ψ(z,θ)` vanishes at `θ = π/2`. -/
theorem dzIter_two_zero_right (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.DzIter 2 Ψ z (Real.pi / 2) = 0 := by
  have hfun : (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
    funext fun z' => Work.H2W.dz_zero_at_pi_half h z'
  show z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z (Real.pi / 2) = 0
  rw [show Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z (Real.pi / 2)
      = deriv (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' (Real.pi / 2)) z from rfl, hfun,
    deriv_const, mul_zero]

/-! ## The `i = 2` slot of `HkMem α 2 (∂_θ²Ψ)` -/

/-- **The `η`-weighted square of the second `θ`-derivative of the twice shifted slice.**

`∂_θ²(D_z²Ψ(z,·)) = pthIter 2 (D_z²Ψ) z` and, on the open interval, this equals
`D_z²(∂_θ²Ψ) z` (`remov.ws_pthIter_two_DzIter`, Clairaut); the latter's `η`-weighted square is
the `i = 2` summand of the weighted integrand of `HkMem α 2 (pthIter 2 Ψ)` (the field `memB`), so
it is integrable by `remov.ws_slot_slice`. -/
theorem pthIter_two_DzIter_two_sq_mul_sEta (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  have hbase := Work.FTS.EllipticEst.remov.ws_slot_slice (hΨ.pth).pth hwk.memB 2 (le_refl 2) hz
  refine hbase.congr ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  rw [Work.FTS.EllipticEst.remov.ws_pthIter_two_DzIter hΨ 2 hz hθ]
  rfl

/-! ## The target -/

theorem SliceRegularShiftTwoAe {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => Work.Spaces.DzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2)) ∧
      Work.Spaces.DzIter 2 Ψ z 0 = 0 ∧ Work.Spaces.DzIter 2 Ψ z (Real.pi / 2) = 0 ∧
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => Work.Spaces.DzIter 2 Ψ z t) θ) ^ 2) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.DzIter 2 Ψ z θ) ^ 2) Work.Spaces.Iθ := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  -- the a.e. slice continuity, transported from `volume.restrict Iz` to `volume.restrict (Ioi 0)`
  have hcont := Work.FTS.EllipticEst.H2W.slot11_fix.slot11_Acont_clean α F Ψ hα hα4 hwk
  rw [Work.Spaces.Iz] at hcont
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici] at hcont
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hcont] with z hzcont hzIoi
  have hz : 0 < z := hzIoi
  -- the weighted square of the second `θ`-derivative, and the resulting `L∞` bound
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => deriv (fun t => deriv (fun t' => Work.Spaces.DzIter 2 Ψ z t') t) θ ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    pthIter_two_DzIter_two_sq_mul_sEta (α := α) (F := F) (Ψ := Ψ) hwk hz
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.remov.abs_le_of_sq_mul_sEta
    (Work.FTS.EllipticEst.remov.ws_contDiffOn_slice (hΨ.DzIter 2) hz) h2
  refine ⟨(hzcont (le_of_lt hz) hz).2, dzIter_two_zero_left hwk z, dzIter_two_zero_right hwk z,
    pthIter_two_DzIter_two_sq_mul_sEta hwk hz, ?_, ?_⟩
  · -- conjunct 5: the plain square of the first `θ`-derivative
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (C := C ^ 2)
        (Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top) (by simp))
      ((measurable_deriv (fun t => Work.Spaces.DzIter 2 Ψ z t)).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : 0 ≤ (C - deriv (fun t => Work.Spaces.DzIter 2 Ψ z t) θ)
        * (C + deriv (fun t => Work.Spaces.DzIter 2 Ψ z t) θ) :=
      mul_nonneg
        (by linarith [le_abs_self (deriv (fun t => Work.Spaces.DzIter 2 Ψ z t) θ),
          (hC θ hθ).1])
        (by linarith [neg_le_abs (deriv (fun t => Work.Spaces.DzIter 2 Ψ z t) θ),
          (hC θ hθ).1])
    nlinarith [h1]
  · -- conjunct 6: the plain square of the slice
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (C := C ^ 2)
        (Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top) (by simp))
      ((Work.FTS.EllipticEst.remov.ws_aesm_slice (hΨ.DzIter 2) hz).pow 2) ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : 0 ≤ (C - Work.Spaces.DzIter 2 Ψ z θ) * (C + Work.Spaces.DzIter 2 Ψ z θ) :=
      mul_nonneg
        (by linarith [le_abs_self (Work.Spaces.DzIter 2 Ψ z θ), (hC θ hθ).2])
        (by linarith [neg_le_abs (Work.Spaces.DzIter 2 Ψ z θ), (hC θ hθ).2])
    nlinarith [h1]

end Work.FTS.EllipticEst.TopSlotTwoFts
