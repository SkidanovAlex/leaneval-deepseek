import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.StrongEps.EpsE4Thr.EnergyDiagAssembly
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.SlotSumRadAOpen
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAsm
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.EnergyDiagAssemblyIoo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- Differentiability at every interior point gives continuity on the open interval. -/
theorem continuousOn_Ioo_of_hasDerivAt_Ioo {φ ψ : ℝ → ℝ} {T : ℝ}
    (h : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt φ (ψ s) s) :
    ContinuousOn φ (Set.Ioo (0 : ℝ) T) :=
  fun s hs => (h s hs).continuousAt.continuousWithinAt

/-- **The `L²`-route data of a curve and its derivative family with *interior* continuity.** -/
structure DiagCurveI (ρ : ℝ → ℝ → ℝ) (u udot : ℝ → Fn) (τ T : ℝ) : Prop where
  ρmeas : AEMeasurable (Function.uncurry ρ) mup
  ρnn : ∀ᵐ p ∂mup, 0 ≤ ρ p.1 p.2
  int_diag : ∀ s ∈ Set.Icc (0 : ℝ) T,
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (u s p.1 p.2) ^ 2 * ρ p.1 p.2) mup
  int_diagd : ∀ s ∈ Set.Icc (0 : ℝ) T,
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (udot s p.1 p.2) ^ 2 * ρ p.1 p.2) mup
  aesm : MeasureTheory.AEStronglyMeasurable
    (fun q : ℝ × (ℝ × ℝ) => u q.1 q.2.1 q.2.2)
    ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup)
  aesmd : MeasureTheory.AEStronglyMeasurable
    (fun q : ℝ × (ℝ × ℝ) => udot q.1 q.2.1 q.2.2)
    ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup)
  deriv : ∀ᵐ p ∂mup, ∀ s ∈ Set.Ioo (0 : ℝ) T,
    HasDerivAt (fun t : ℝ => u t p.1 p.2) (udot s p.1 p.2) s
  bdd : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
    ∫ p : ℝ × ℝ, (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂mup ≤ K
  contU : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
    (udot σ p.1 p.2 - udot τ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂mup) (nhds τ) (nhds 0)
  int_cross : MeasureTheory.Integrable
    (fun p : ℝ × ℝ => udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2) mup


/-- The `Ioo`-continuity is *free* from `deriv`. -/
theorem DiagCurveI.cont {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Fn} {τ T : ℝ}
    (h : DiagCurveI ρ u udot τ T) :
    ∀ᵐ p ∂mup, ContinuousOn (fun s : ℝ => u s p.1 p.2) (Set.Ioo (0 : ℝ) T) :=
  h.deriv.mono fun _ hp => continuousOn_Ioo_of_hasDerivAt_Ioo hp




end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.LGammaTMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongEps.EpsZero.ClassCHk.LGammaTMem`

`𝓛_Γ^T w` is `ℋ⁴`-honest for every profile `w` of the open-quadrant class `ClassC`.

## Route

`𝓛_Γ^T = 𝓛̂ + Corr` (`Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr`), and the two summands are
handled separately.

* `𝓛̂ w` is handled by the ready-made `StrongPersist.H6Aux.Lhat_mem` (`SmoothOpen w` +
  `HkMem α 5 w`, both from `ClassC`), which is itself a `HkMem_of_majorant` argument.
* `Corr α w = Γ(θ)·radA α w (z)` is a *separated* product of an angular and a radial function, so
  the pointwise separation `GalFields.Norm.HkIntegrand_Corr_le` gives

    `HkIntegrand α 4 (Corr α w) z θ ≤ slot5 (radA α w) z · afac4 α θ`   (`θ ∈ Iθ`),

  with `slot5 B z = Σ_{j≤4}(D_z^j B z · w z)²` and
  `afac4 α θ = sin(2θ)^{-η} + 4·(10⁵α)²·sin(2θ)^{2α/5-γ}`.  The angular factor is integrable on
  `Iθ` with a bound uniform in `α` (`GalFields.Norm.ang_fac_integrable_bound`), and the radial slot
  sum is integrable on `Iz` — this is the content of `SlotSumRadAOpen`
  (the open-quadrant re-run of `StrongPersist.H6Aux.Alt_SlotSum_radA_le`, whose class `H6Adm` is
  used only through `SmoothOpen`, `HkMem α 7` and `L₁₂(·)(0) = 0`, all three of which `ClassC`
  supplies) — combined with the trivial domination `slot5 ≤ SlotSum` (`SlotSum B z =
  Σ_{q≤6}(D_z^q B z · w z)²`).

  `HkMem α 4 (Corr α w)` then follows from `LocData.HkMem_of_majorant`, whose continuity hypothesis
  is the level-four smoothness of `Corr α w` on the open quadrant
  (`GalFields.Norm.radA_Corr_contDiffOn_four`).

The final step is the `ℋ⁴`-additivity `OpenPkg.HkMem_add_of_contDiffOn_four`.

All inputs are `sorry`-free and rest on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsZero.ClassCHk

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two summands of `𝓛_Γ^T` -/

/-- `ℋ⁵`-honesty of a `ClassC` profile (from the `ℋ⁷`-field by monotonicity). -/
theorem hkMem_five_of_classC {α : ℝ} {w : Fn} (hw : Work.FTS.ClassC.ClassC α w) :
    Work.Spaces.HkMem α 5 w :=
  Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (k := 5) (k' := 7) (by norm_num)
    hw.reg hw.mem

/-- **The clean part.**  `𝓛̂ w ∈ ℋ⁴` for `ClassC` data: `SmoothOpen w` and `HkMem α 5 w` are
exactly the two hypotheses of `StrongPersist.H6Aux.Lhat_mem`. -/
theorem HkMem_Lhat_of_classC {α : ℝ} (hα : 0 < α) {w : Fn}
    (hw : Work.FTS.ClassC.ClassC α w) :
    Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Lhat w) :=
  Work.FTS.StrongPersist.H6Aux.Lhat_mem α hα 4 hw.reg (hkMem_five_of_classC hw)

/-- **The transfer part is `C⁴` on the open quadrant.**  `Corr α w = Γ(θ)·radA α w (z)` is a
product of the angular profile `Γ` and the radial profile `radA`, and the level-four smoothness of
the two factors is `GalFields.Norm.radA_Corr_contDiffOn_four`. -/
theorem contDiffOn_Corr_of_classC {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {w : Fn}
    (hw : Work.FTS.ClassC.ClassC α w) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Corr α w))
      Work.FTS.EllipticEst.Q0 :=
  (Work.FTS.GalFields.Norm.radA_Corr_contDiffOn_four hα hα1 hw.reg
    (Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (k := 5) (k' := 7) (by norm_num)
      hw.reg hw.mem)).2

/-! ## Integrability of the radial slot sum `slot5 (radA α w)` -/

/-- The level-six slot sum dominates the level-four one: `slot5 B z ≤ SlotSum B z` pointwise. -/
theorem slot5_le_SlotSum (B : ℝ → ℝ) (z : ℝ) :
    Work.FTS.GalFields.Norm.slot5 B z ≤ Work.FTS.StrongPersist.SlotSum B z := by
  rw [Work.FTS.StrongPersist.H6Aux.Alt_SlotSum_eq B z]
  rw [Work.FTS.GalFields.Norm.slot5]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by norm_num)) ?_
  intro q _ _
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **Integrability of the level-four radial slot sum of `radA α w`** for `ClassC` data.  This is
`SlotSumRadAOpen` (the open-quadrant slot bound at level six) combined with the trivial domination
`slot5 ≤ SlotSum` and the a.e. strong measurability of `slot5 (radA α w)`
(continuity on `(0,∞)` from the level-four smoothness of `radA`). -/
theorem integrableOn_slot5_radA_of_classC {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {w : Fn}
    (hw : Work.FTS.ClassC.ClassC α w) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α w) z)
      Work.Spaces.Iz := by
  obtain ⟨_C, _hC, hb⟩ := SlotSumRadAOpen
  obtain ⟨hInt, _hBd⟩ := hb α (Set.mem_Ioc.mpr ⟨hα, hα1⟩) w hw.reg hw.mem hw.l12
  refine MeasureTheory.Integrable.mono' hInt ?_ ?_
  · have hrad : ContDiffOn ℝ 4 (Work.FTS.CoercivityFix.Transfer.radA α w) (Set.Ioi (0 : ℝ)) :=
      (Work.FTS.GalFields.Norm.radA_Corr_contDiffOn_four hα hα1 hw.reg
        (hkMem_five_of_classC hw)).1
    have hcont : ContinuousOn (fun z : ℝ => ∑ q ∈ Finset.range (4 + 1),
        (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α w) z) ^ 2
          * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.StrongPersist.H6Aux.Alt_continuousOn_slotSum (n := 4) hrad
    have heq : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
        = MeasureTheory.volume.restrict Work.Spaces.Iz := by
      rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
    have hfun : Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α w)
        = fun z : ℝ => ∑ q ∈ Finset.range (4 + 1),
            (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α w) z) ^ 2
              * (Work.Spaces.w z) ^ 2 := rfl
    rw [hfun, ← heq]
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z _
    rw [Real.norm_of_nonneg (Work.FTS.GalFields.Norm.slot5_nonneg _ z)]
    exact slot5_le_SlotSum _ z

/-- **The transfer part.**  `Corr α w ∈ ℋ⁴` for `ClassC` data, by domination
(`LocData.HkMem_of_majorant`) with the separated majorant `slot5 (radA α w) z · afac4 α θ`. -/
theorem HkMem_Corr_of_classC {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {w : Fn}
    (hw : Work.FTS.ClassC.ClassC α w) :
    Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Corr α w) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4
      (Work.FTS.CoercivityFix.Corr α w) p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α (n := 4) (k := 4) le_rfl
      (contDiffOn_Corr_of_classC hα hα1 hw)
  obtain ⟨_Kang, _hKang, hang⟩ := Work.FTS.GalFields.Norm.ang_fac_integrable_bound
  obtain ⟨hangInt, _hangBd⟩ := hang α hα hα1
  have hangInt' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.GalFields.Norm.afac4 α θ) Work.Spaces.Iθ := hangInt
  have hslot := integrableOn_slot5_radA_of_classC hα hα1 hw
  refine Work.FTS.LocData.HkMem_of_majorant α 4
    (f := Work.FTS.CoercivityFix.Corr α w)
    (M := fun z θ => Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α w) z
      * Work.FTS.GalFields.Norm.afac4 α θ) hcont ?_ ?_ ?_
  · intro z _
    exact hangInt'.const_mul _
  · have heq : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α w) z
          * Work.FTS.GalFields.Norm.afac4 α θ)
        = fun z : ℝ => Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α w) z
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.GalFields.Norm.afac4 α θ) := by
      funext z
      exact MeasureTheory.integral_const_mul _ _
    rw [heq]
    exact hslot.mul_const _
  · intro z _ θ hθ
    exact Work.FTS.GalFields.Norm.HkIntegrand_Corr_le hα hα1 w hθ

/-! ## The target -/

theorem LGammaTMem {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {w Φg : Work.FTS.Galerkin.Fn} (hw : Work.FTS.ClassC.ClassC α w)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) :
    Work.Spaces.HkMem α 4 (Work.Coercivity.LGammaT α w) := by
  have hL := HkMem_Lhat_of_classC hα hw
  have hC := HkMem_Corr_of_classC hα hα1 hw
  have hsmL : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Lhat w))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hw.reg).forall 4
  have hsmC := contDiffOn_Corr_of_classC hα hα1 hw
  have hsum := Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four hsmL hsmC hL hC
  rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α w]
  exact hsum

end Work.FTS.StrongEps.EpsZero.ClassCHk
end
end
