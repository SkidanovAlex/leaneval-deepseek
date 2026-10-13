import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Blocks.HkNorm_Dz_amgm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.Honesty.CapstoneMeasurability`

The two **measurability inputs** of the modal-series honesty capstones

* `Work.FTS.ClassC.HonestCut.HkMem_zero_psiSeries_of_capstone`,
* `Work.FTS.ClassC.HonestCut.HkMem_zero_zpz_psiSeries_of_capstone`,
* `Work.FTS.ClassC.HonestCut.HkMem_zero_Q_psiSeries_of_capstone`,
* `Work.FTS.ClassC.HonestCut.HkMem_zero_pth2_psiSeries_of_capstone`,
* `Work.FTS.ClassC.HonestCut.HkMem_zero_zpz_pth2_psiSeries_of_capstone`,
* `Work.FTS.PhiStar.Honesty.HkMem_zsq_pzIter2_psiSeries_of_capstone`

are

```
hslmeas : ∀ z ∈ Iz, AEMeasurable (fun θ => ENNReal.ofReal (HkIntegrand α 0 G z θ))
                     (volume.restrict Iθ)
hmeas   : AEMeasurable (fun z => ∫⁻ θ in Iθ, ENNReal.ofReal (HkIntegrand α 0 G z θ))
                     (volume.restrict (Ioi 0))
```

where `G` is the slot under consideration (`Ψ`, `z²∂_z²Ψ`, `∂_θ²Ψ`, `z∂_z∂_θ²Ψ`, …).  Both are
*unconditional* once the slot is `C^∞` on the open quadrant (`SmoothOpen G`), and this file
proves them in that generality:

* `aesm_ofReal_HkIntegrand_prod` — the uncurried integrand `(z,θ) ↦ ofReal (HkIntegrand …)` is
  a.e. strongly measurable for the product of the restricted measures (continuity on the open
  quadrant plus the null-set identification `Iz ↔ Ioi 0`, `Iθ ↔ Ioo 0 (π/2)`);
* `aemeasurable_lintegral_HkIntegrand` — Fubini's measurability theorem for the `θ`-lower
  integral, giving `hmeas`;
* `aemeasurable_slice_HkIntegrand` — the slice version, giving `hslmeas`
  (`z = 0` is the constant `0`; for `z > 0` the slice of a function continuous on the open
  quadrant is continuous on `(0,π/2)`, a conull subset of `Iθ`);
* `smoothOpen_z_mul` — the missing smoothness closure (multiplication by the `z`-coordinate),
  used to feed the `z∂_z∂_θ²Ψ` slot;
* `capstoneMeasurability` — the two inputs bundled in exactly the capstones' shape, for an
  arbitrary `SmoothOpen` slot;
* `capstoneMeasurability_zsqPz2`, `…_pthIter2`, `…_zpz_pthIter2` — the three slot instances
  (radial second derivative, angular second derivative, mixed diagonal second derivative) for a
  `SmoothOpen Ψ`.

Nothing here is analytic: the file is pure measurability bookkeeping and carries no `sorry`.
-/

noncomputable section
open scoped Real Topology ENNReal BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

local notation "Iz" => Work.Spaces.Iz
local notation "Iθ" => Work.Spaces.Iθ

/-! ## Smoothness closure under multiplication by `z` -/

/-- `SmoothOpen` is closed under multiplication by the `z`-coordinate. -/
theorem smoothOpen_z_mul {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => z * G z θ)) Work.FTS.EllipticEst.Q0
  have h1 : Function.uncurry (fun z θ : ℝ => z * G z θ)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry G p := rfl
  rw [h1]
  exact (contDiffOn_fst (𝕜 := ℝ) (n := Work.Stability.smoothOrder)).mul hG

/-! ## The uncurried integrand is a.e. strongly measurable -/

/-- The uncurried `ENNReal`-valued `ℋ^k`-integrand of a datum `C^∞` on the open quadrant is
a.e. strongly measurable for the product of the two restricted measures. -/
theorem aesm_ofReal_HkIntegrand_prod (α : ℝ) (k : ℕ) {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G p.1 p.2))
      ((MeasureTheory.volume.restrict Iz).prod (MeasureTheory.volume.restrict Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k G p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hG.continuousOn_HkIntegrand α k
  have hcont' : ContinuousOn
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G p.1 p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ENNReal.continuous_ofReal.comp_continuousOn hcont
  have hUm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hmain : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G p.1 p.2))
      ((volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :=
    hcont'.aestronglyMeasurable hUm
  have hz : Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprod : (Iz ×ˢ Iθ : Set (ℝ × ℝ)) =ᵐ[volume.prod volume]
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  exact hmain.aemeasurable

/-! ## The `θ`-lower integral is a.e. measurable in `z` -/

/-- **`hmeas`**: for a slot `C^∞` on the open quadrant, the `θ`-lower integral of the `ENNReal`
`ℋ^k`-integrand is a.e. measurable on `(0,∞)`. -/
theorem aemeasurable_lintegral_HkIntegrand (α : ℝ) (k : ℕ) {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    AEMeasurable (fun z : ℝ => ∫⁻ θ in Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have h1 : AEMeasurable (fun z : ℝ => ∫⁻ θ in Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ))
      (MeasureTheory.volume.restrict Iz) :=
    (aesm_ofReal_HkIntegrand_prod α k hG).lintegral_prod_right
  have hmeas : MeasureTheory.volume.restrict Iz
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.restrict_Ioi_eq_restrict_Ici (μ := volume) (a := (0 : ℝ))).symm
  rwa [hmeas] at h1

/-! ## The `θ`-slices -/

/-- **`hslmeas`**: for a slot `C^∞` on the open quadrant, every `θ`-slice of the `ENNReal`
`ℋ^k`-integrand is a.e. measurable. -/
theorem aemeasurable_slice_ofReal_HkIntegrand (α : ℝ) (k : ℕ) {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    ∀ z ∈ Iz, AEMeasurable (fun θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ))
      (MeasureTheory.volume.restrict Iθ) := by
  intro z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
  · subst h0
    have hzero : (fun θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G 0 θ))
        = fun _ : ℝ => (0 : ℝ≥0∞) := by
      funext θ
      have : Work.Spaces.HkIntegrand α k G 0 θ = 0 := by
        simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]
      rw [this, ENNReal.ofReal_zero]
    rw [hzero]
    exact aemeasurable_const
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k G p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hG.continuousOn_HkIntegrand α k
    have hs := Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k G p.1 p.2) hcont hpos
    exact hs.aemeasurable.ennreal_ofReal

/-! ## The two inputs in the capstones' shape -/

/-- **The measurability package consumed by the honesty capstones**, for an arbitrary slot `G`
which is `C^∞` on the open quadrant.  The pair is `(hslmeas, hmeas)` with
`σ`-integrand `HkIntegrand α 0 G`. -/
theorem capstoneMeasurability (α : ℝ) (k : ℕ) {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    (∀ z ∈ Iz, AEMeasurable (fun θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 G z θ))
        (MeasureTheory.volume.restrict Iθ)) ∧
      AEMeasurable (fun z : ℝ => ∫⁻ θ in Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 G z θ))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
  ⟨aemeasurable_slice_ofReal_HkIntegrand α 0 hG, aemeasurable_lintegral_HkIntegrand α 0 hG⟩

/-! ## The three second-order slots of a `SmoothOpen` datum -/

/-- `hslmeas`/`hmeas` for the **radial second-order slot** `z²∂_z²Ψ`. -/
theorem capstoneMeasurability_zsqPz2 (α : ℝ) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    (∀ z ∈ Iz, AEMeasurable (fun θ : ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ))
        (MeasureTheory.volume.restrict Iθ)) ∧
      AEMeasurable (fun z : ℝ => ∫⁻ θ in Iθ, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
  capstoneMeasurability α 0 (Work.FTS.EllipticEst.Blocks.smooth_zsqPz2 Ψ hΨ)

/-- `hslmeas`/`hmeas` for the **angular second-order slot** `∂_θ²Ψ`. -/
theorem capstoneMeasurability_pthIter2 (α : ℝ) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    (∀ z ∈ Iz, AEMeasurable (fun θ : ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ))
        (MeasureTheory.volume.restrict Iθ)) ∧
      AEMeasurable (fun z : ℝ => ∫⁻ θ in Iθ, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have h : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := by
    have hp : Work.Spaces.pthIter 2 Ψ = Work.Spaces.pth (Work.Spaces.pthIter 1 Ψ) := rfl
    rw [hp]
    exact (hΨ.pth).pth
  exact capstoneMeasurability α 0 h

/-- `hslmeas`/`hmeas` for the **mixed second-order slot** `z∂_z∂_θ²Ψ`. -/
theorem capstoneMeasurability_zpz_pthIter2 (α : ℝ) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    (∀ z ∈ Iz, AEMeasurable (fun θ : ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0
          (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z θ))
        (MeasureTheory.volume.restrict Iθ)) ∧
      AEMeasurable (fun z : ℝ => ∫⁻ θ in Iθ, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0
          (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z θ))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hpth : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := by
    have hp : Work.Spaces.pthIter 2 Ψ = Work.Spaces.pth (Work.Spaces.pthIter 1 Ψ) := rfl
    rw [hp]
    exact (hΨ.pth).pth
  exact capstoneMeasurability α 0 (smoothOpen_z_mul hpth.pz)

end Work.FTS.PhiStar.Honesty
