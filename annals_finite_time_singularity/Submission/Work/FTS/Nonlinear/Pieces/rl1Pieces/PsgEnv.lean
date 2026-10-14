import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.FstarDzIterFourAe
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.VocabO
import Submission.Work.H2W.momentChainAe
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.TopSlotTwoFts.SliceRegularShiftTwoAe =====
section

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
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEnv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## Generic reduction lemmas -/

/-- **Row reduction with a constant coefficient.**  If `|K θ · N(r,θ)| ≤ c·|k(r,θ)|` pointwise
(with `c ≥ 0`), then the `rl¹`-norm of `N` is at most `ofReal c` times that of `k`. -/
theorem rl1_row_le {N k : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hpt : ∀ r : ℝ, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * N r θ| ≤ c * |k r θ|)
    {B : ENNReal}
    (hk : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)) ≤ B) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ENNReal.ofReal c * B := by
  have hinner : ∀ r : ℝ, 0 < r →
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal c * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|) := by
    intro r hr
    have h1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal c * ENNReal.ofReal |k r θ| := by
      refine MeasureTheory.lintegral_mono_ae ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        rw [← ENNReal.ofReal_mul hc]
        exact ENNReal.ofReal_le_ofReal (hpt r hr θ hθ))
    rwa [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h1
  have hA : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (ENNReal.ofReal c * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_le_mul' le_rfl (hinner r hr)
  have hB : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (ENNReal.ofReal c * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)))
      = ENNReal.ofReal c * (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)) := by
    rw [show (fun r : ℝ => ENNReal.ofReal r⁻¹ *
        (ENNReal.ofReal c * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)))
        = (fun r : ℝ => ENNReal.ofReal c * (ENNReal.ofReal r⁻¹ *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|))) from by funext r; ring]
    exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  exact le_trans hA (le_trans (le_of_eq hB) (mul_le_mul' le_rfl hk))

/-- **Row reduction with the radial factor `r/(1+r)²`.**  Since `r⁻¹·r/(1+r)² = 1/(1+r)² ≤ r⁻¹`
on `r > 0`, a pointwise bound `|K θ·N| ≤ c·(r/(1+r)²)·|k|` gives the same `rl¹`-bound. -/
theorem rl1_row_le_radial {N k : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hpt : ∀ r : ℝ, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * N r θ| ≤ c * (r / (1 + r) ^ 2) * |k r θ|)
    {B : ENNReal}
    (hk : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)) ≤ B) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ENNReal.ofReal c * B := by
  have hinner : ∀ r : ℝ, 0 < r →
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal (c * (r / (1 + r) ^ 2))
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|) := by
    intro r hr
    have h1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (c * (r / (1 + r) ^ 2)) * ENNReal.ofReal |k r θ| := by
      refine MeasureTheory.lintegral_mono_ae ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        rw [← ENNReal.ofReal_mul (mul_nonneg hc (by positivity))]
        exact ENNReal.ofReal_le_ofReal (hpt r hr θ hθ))
    rwa [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h1
  have hrad : ∀ r : ℝ, 0 < r → r⁻¹ * (c * (r / (1 + r) ^ 2)) ≤ c * r⁻¹ := by
    intro r hr
    have h2 : r⁻¹ * (r / (1 + r) ^ 2) = ((1 + r) ^ 2)⁻¹ := by
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hr), one_mul]
    have hle : ((1 + r) ^ 2)⁻¹ ≤ r⁻¹ := by
      rw [inv_le_inv₀ (by positivity : (0 : ℝ) < (1 + r) ^ 2) hr]
      nlinarith [sq_nonneg r]
    rw [show r⁻¹ * (c * (r / (1 + r) ^ 2))
        = c * (r⁻¹ * (r / (1 + r) ^ 2)) from by ring, h2]
    exact mul_le_mul_of_nonneg_left hle hc
  have hA : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal c *
        (ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    refine le_trans (mul_le_mul' le_rfl (hinner r hr0)) ?_
    have hstep : ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (c * (r / (1 + r) ^ 2))
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|))
        = ENNReal.ofReal (r⁻¹ * (c * (r / (1 + r) ^ 2)))
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|) := by
      rw [show ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (c * (r / (1 + r) ^ 2))
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|))
          = (ENNReal.ofReal r⁻¹ * ENNReal.ofReal (c * (r / (1 + r) ^ 2)))
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|) from by rw [← mul_assoc]]
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr0.le)]
    rw [hstep]
    refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hrad r hr0)) le_rfl) ?_
    rw [ENNReal.ofReal_mul hc]
    exact le_of_eq (by ring)
  have hB : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal c *
        (ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)))
      = ENNReal.ofReal c * (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)) :=
    MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  exact le_trans hA (le_trans (le_of_eq hB) (mul_le_mul' le_rfl hk))

/-! ## Scalar arithmetic facts -/

/-- `α ≤ √α` for `0 < α ≤ 1`. -/
lemma alpha_le_sqrt_self {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : α ≤ Real.sqrt α := by
  have h := Real.sq_sqrt hα.le
  have h2 : α ^ 2 ≤ α := by nlinarith
  nlinarith [Real.sqrt_nonneg α]

/-- `α·√(10/α) = √10·√α` for `α > 0`. -/
lemma alpha_mul_sqrt_div {α : ℝ} (hα : 0 < α) :
    α * Real.sqrt (10 / α) = Real.sqrt 10 * Real.sqrt α := by
  have hdiv : 0 ≤ 10 / α := div_nonneg (by norm_num) hα.le
  have hstep : Real.sqrt (10 / α) * Real.sqrt (α ^ 2) = Real.sqrt (10 / α * α ^ 2) :=
    (Real.sqrt_mul hdiv (α ^ 2)).symm
  rw [Real.sqrt_sq hα.le] at hstep
  have h1 : Real.sqrt (10 / α) * α = Real.sqrt (10 * α) := by
    rw [hstep]
    congr 1
    rw [div_mul_eq_mul_div, mul_div_assoc, pow_two, mul_div_cancel_left₀ α (ne_of_gt hα)]
  rw [mul_comm α (Real.sqrt (10 / α)), h1, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10)]

/-- `√10 ≤ 4`. -/
lemma sqrt_ten_le_four : Real.sqrt 10 ≤ 4 := by
  have h := Real.sqrt_le_sqrt (show (10 : ℝ) ≤ 16 by norm_num)
  have h16 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [h16] at h

/-! ## The target -/

theorem PsgEnv {α₂ Ci Ce Cs : ℝ} :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.N4Norm Ci α₂ →
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg →
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g r θ|))
        ≤ ENNReal.ofReal (K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs g r θ|))
        ≤ ENNReal.ofReal (K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs g r θ|))
        ≤ ENNReal.ofReal (K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4sg α g r θ|))
        ≤ ENNReal.ofReal (K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5sg α g r θ|))
        ≤ ENNReal.ofReal (K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) := by
  refine ⟨1000 * (max Cs 0 + 1), ?_, ?_⟩
  · have h := le_max_right Cs 0
    nlinarith [h]
  intro α g Φs Φg hα hα1 hαα₂ hN hgal hs hell
  -- ### the data
  obtain ⟨hsm, hmem, _⟩ :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (show (4 : ℕ) ≤ 6 by norm_num)
  obtain ⟨hrow1, hrow2, hrow3, hrow4, hrow5⟩ := sgRowsPtwise hα hα1 hs
  have hG := Work.FTS.Nonlinear.Pieces.rl1Tools.envG hα hsm hmem
  have hDz := Work.FTS.Nonlinear.Pieces.rl1Tools.envDz hα hsm hmem
  have hPth := envPth hα hα1 hsm hmem
  -- ### the numbers
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hCs0 : 0 ≤ max Cs 0 := le_max_right Cs 0
  have hCs1 : 0 < max Cs 0 + 1 := by linarith
  have hsq : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hAs : α ≤ Real.sqrt α := alpha_le_sqrt_self hα hα1
  have hA1 : α * Work.FTS.Nonlin.Xn α g ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
    mul_le_mul_of_nonneg_right hAs hX0
  have hpow : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hB1 : Real.sqrt α * Work.FTS.Nonlin.Xn α g
      ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
        + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := by
    have h1 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
      mul_nonneg hpow (sq_nonneg _)
    have h2 : (0 : ℝ) ≤ α ^ 2 := by positivity
    linarith
  have hA2 : α ^ 2 * Work.FTS.Nonlin.Xn α g
      ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
        + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := by
    have ha2 : (0 : ℝ) ≤ α ^ 2 := by positivity
    have hspos : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
      mul_nonneg hpow (sq_nonneg _)
    have hqpos : (0 : ℝ) ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g := mul_nonneg hsq hX0
    rcases lt_or_ge (Work.FTS.Nonlin.Xn α g) 1 with h1 | h1
    · have h2 : α ^ 2 * Work.FTS.Nonlin.Xn α g ≤ α ^ 2 := by
        have h3 := mul_le_mul_of_nonneg_left (le_of_lt h1) ha2
        simpa using h3
      linarith
    · have h1' : 1 ≤ Work.FTS.Nonlin.Xn α g := h1
      have hx : Work.FTS.Nonlin.Xn α g ≤ Work.FTS.Nonlin.Xn α g ^ 2 := by nlinarith
      have h3 : α ^ 2 ≤ α ^ (-(3 / 2 : ℝ)) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (x := α) (y := (2 : ℝ))
          (z := -(3 / 2 : ℝ)) (by norm_num : (-(3 / 2 : ℝ)) ≤ 2)
        simpa using h
      have h4 : α ^ 2 * Work.FTS.Nonlin.Xn α g
          ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
        mul_le_mul h3 hx hX0 hpow
      linarith
  have hAalpha : α * Work.FTS.Nonlin.Xn α g
      ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
        + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
    le_trans hA1 hB1
  -- ### the absorption of a constant times one of the three shapes
  have key : ∀ c S : ℝ, 0 ≤ c → 0 ≤ S →
      S ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 →
      c ≤ 1000 * (max Cs 0 + 1) →
      c * S ≤ (1000 * (max Cs 0 + 1)) * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
    intro c S hc0 hS0 hSenv hcK
    have henv0' : 0 ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
        + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := le_trans hS0 hSenv
    exact le_trans (mul_le_mul_of_nonneg_left hSenv hc0)
      (mul_le_mul_of_nonneg_right hcK henv0')
  have hc1 : 12 * max Cs 0 ≤ 1000 * (max Cs 0 + 1) := by nlinarith [hCs0]
  have hc2 : 240 * Real.sqrt 10 * max Cs 0 ≤ 1000 * (max Cs 0 + 1) := by
    have hs4 := sqrt_ten_le_four
    nlinarith [hCs0, Real.sqrt_nonneg 10]
  have hc4 : 30 * Real.sqrt 10 ≤ 1000 * (max Cs 0 + 1) := by
    have hs4 := sqrt_ten_le_four
    nlinarith [hCs1, Real.sqrt_nonneg 10]
  have hc5 : (12 : ℝ) ≤ 1000 * (max Cs 0 + 1) := by nlinarith [hCs1]
  -- ### the five rows
  have hb1 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g r θ|))
      ≤ ENNReal.ofReal (1000 * (max Cs 0 + 1) * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) := by
    have h1 := rl1_row_le (N := Work.FTS.Nonlin.N1sg α Φs g) (k := g)
      (c := 6 * max Cs 0 * α)
      (mul_nonneg (mul_nonneg (by norm_num) hCs0) hα.le) hrow1 hG
    have h2 : ENNReal.ofReal (6 * max Cs 0 * α) * ENNReal.ofReal (2 * Work.FTS.Nonlin.Xn α g)
        = ENNReal.ofReal ((12 * max Cs 0) * (α * Work.FTS.Nonlin.Xn α g)) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hCs0) hα.le)]
      congr 1
      ring
    refine le_trans h1 (le_trans (le_of_eq h2) ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    exact key (12 * max Cs 0) (α * Work.FTS.Nonlin.Xn α g)
      (mul_nonneg (by norm_num) hCs0) (mul_nonneg hα.le hX0) hAalpha hc1
  have hb2 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs g r θ|))
      ≤ ENNReal.ofReal (1000 * (max Cs 0 + 1) * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) := by
    have h1 := rl1_row_le (N := Work.FTS.Nonlin.N2sg α Φs g) (k := Work.Spaces.pth g)
      (c := 24 * max Cs 0 * α)
      (mul_nonneg (mul_nonneg (by norm_num) hCs0) hα.le) hrow2 hPth
    have h2 : ENNReal.ofReal (24 * max Cs 0 * α) *
          ENNReal.ofReal (10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g)
        = ENNReal.ofReal ((240 * Real.sqrt 10 * max Cs 0)
            * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hCs0) hα.le)]
      congr 1
      have e1 : (24 : ℝ) * max Cs 0 * α * (10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g)
          = 240 * (max Cs 0 * (α * Real.sqrt (10 / α))) * Work.FTS.Nonlin.Xn α g := by ring
      rw [e1, alpha_mul_sqrt_div hα]
      ring
    refine le_trans h1 (le_trans (le_of_eq h2) ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    exact key (240 * Real.sqrt 10 * max Cs 0) (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 10)) hCs0)
      (mul_nonneg hsq hX0) hB1 hc2
  have hb3 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs g r θ|))
      ≤ ENNReal.ofReal (1000 * (max Cs 0 + 1) * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) := by
    have h1 := rl1_row_le (N := Work.FTS.Nonlin.N3sg α Φs g) (k := Work.Spaces.Dz g)
      (c := 6 * max Cs 0 * α ^ 2)
      (mul_nonneg (mul_nonneg (by norm_num) hCs0) (by positivity)) hrow3 hDz
    have h2 : ENNReal.ofReal (6 * max Cs 0 * α ^ 2) *
          ENNReal.ofReal (2 * Work.FTS.Nonlin.Xn α g)
        = ENNReal.ofReal ((12 * max Cs 0) * (α ^ 2 * Work.FTS.Nonlin.Xn α g)) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hCs0) (by positivity))]
      congr 1
      ring
    refine le_trans h1 (le_trans (le_of_eq h2) ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    exact key (12 * max Cs 0) (α ^ 2 * Work.FTS.Nonlin.Xn α g)
      (mul_nonneg (by norm_num) hCs0) (mul_nonneg (by positivity) hX0) hA2 hc1
  have hb4 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4sg α g r θ|))
      ≤ ENNReal.ofReal (1000 * (max Cs 0 + 1) * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) := by
    have h1 := rl1_row_le_radial (N := Work.FTS.Nonlin.N4sg α g) (k := Work.Spaces.pth g)
      (c := 3 * α) (by positivity) hrow4 hPth
    have h2 : ENNReal.ofReal (3 * α) *
          ENNReal.ofReal (10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g)
        = ENNReal.ofReal ((30 * Real.sqrt 10) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3 * α)]
      congr 1
      have e1 : (3 : ℝ) * α * (10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g)
          = 30 * (α * Real.sqrt (10 / α)) * Work.FTS.Nonlin.Xn α g := by ring
      rw [e1, alpha_mul_sqrt_div hα]
      ring
    refine le_trans h1 (le_trans (le_of_eq h2) ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    exact key (30 * Real.sqrt 10) (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg 10)) (mul_nonneg hsq hX0) hB1 hc4
  have hb5 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5sg α g r θ|))
      ≤ ENNReal.ofReal (1000 * (max Cs 0 + 1) * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) := by
    have h1 := rl1_row_le_radial (N := Work.FTS.Nonlin.N5sg α g) (k := g)
      (c := 6 * α) (by positivity) hrow5 hG
    have h2 : ENNReal.ofReal (6 * α) * ENNReal.ofReal (2 * Work.FTS.Nonlin.Xn α g)
        = ENNReal.ofReal ((12 : ℝ) * (α * Work.FTS.Nonlin.Xn α g)) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 6 * α)]
      congr 1
      ring
    refine le_trans h1 (le_trans (le_of_eq h2) ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    exact key 12 (α * Work.FTS.Nonlin.Xn α g) (by norm_num) (mul_nonneg hα.le hX0) hAalpha hc5
  exact ⟨hb1, hb2, hb3, hb4, hb5⟩

end Work.FTS.Nonlinear.Pieces.rl1Pieces
end
end
