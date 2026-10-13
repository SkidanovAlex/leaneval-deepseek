/-
# `H6Pair6Aux/RowMuAux/SlotDataOpen` — the angular slot data of an open-quadrant datum

The `rl¹`-pieces of `N` are bounded in `Fa` against the angular energies of the three slots
`B ∈ {f, D_θf, D_zf}` of the perturbation datum `f`.  At level four the corresponding data
(`Work.FTS.NonlinRows.Rl1.slot0/1/2`) were derived for the *closed*-quadrant class
`SmoothQuad` (which the honest slices of this route do **not** satisfy); here they are derived
from the honest class

  `SmoothOpen f`  (`f` is `C^∞` on the open quadrant)  and  `HkMem α 4 f`,

which is exactly what `H6Adm α f` (via `H6Adm.reg`) and the order-seven honesty of `L6Ctx`
supply.

Everything rests on the three pointwise Hardy comparisons of
`Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux`

  `slot_g/slot_dth/slot_dz :  w r · (B r θ)² ≤ HkIntegrand α 4 f r θ`  (`r > 0`, `θ ∈ (0,π/2)`),

the integrability of the slices being read off from `HkMem α 4 f` and the `r`-a.e. strong
measurability of the energies from the continuity of the slices on the open quadrant.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.NonlinRows.Rl1.ggBounds
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux (ae_Iθ_of_forall_Ioo)

/-- Positivity of the radial weight on `r > 0`. -/
theorem w_pos' {r : ℝ} (hr : 0 < r) : 0 < Work.Spaces.w r :=
  lt_of_lt_of_le zero_lt_one (Work.FTS.NonlinRows.Rl1.one_le_w' hr)

/-- Measurability of the radial weight. -/
theorem w_measurable : Measurable (Work.Spaces.w) := by
  unfold Work.Spaces.w
  fun_prop

/-- The angular integral of the `ℋ⁴`-integrand of a datum is integrable on `r > 0`. -/
theorem HkEner_integrableOn {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.IntegrableOn (fun r => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 f r θ) (Set.Ioi (0 : ℝ)) :=
  hmem.2.mono_set Set.Ioi_subset_Ici_self

theorem HkEner_aemeasurable {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 f) :
    AEMeasurable (fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  (HkEner_integrableOn hmem).aemeasurable

theorem HkEner_nonneg {α : ℝ} {f : ℝ → ℝ → ℝ} (r : ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ :=
  MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f r θ

/-- `Iθ`-integrability of the square of a slot. -/
theorem slot_sq_integrableOn {α : ℝ} {f B : ℝ → ℝ → ℝ} {r : ℝ} (hmem : Work.Spaces.HkMem α 4 f)
    (hB : ContinuousOn (Function.uncurry B) Work.Construction.Qd) (hr : 0 < r)
    (hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.w r * (B r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ) :
    MeasureTheory.IntegrableOn (fun θ => (B r θ) ^ 2) Work.Spaces.Iθ := by
  have hInt : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f r θ)
      Work.Spaces.Iθ := hmem.1 r (le_of_lt hr)
  have hslice : MeasureTheory.AEStronglyMeasurable (fun θ => B r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry B) hB hr
  have hw : 0 < Work.Spaces.w r := w_pos' hr
  refine MeasureTheory.Integrable.mono' (hInt.const_mul ((Work.Spaces.w r)⁻¹))
    (hslice.pow 2) ?_
  refine ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), inv_mul_eq_div, le_div_iff₀ hw]
  have h := hpt θ hθ
  linarith [h]

/-- **The integrated Hardy comparison of a slot with the `ℋ⁴`-integrand.** -/
theorem slot_energy_le {α : ℝ} {f B : ℝ → ℝ → ℝ} {r : ℝ} (hmem : Work.Spaces.HkMem α 4 f)
    (hB : ContinuousOn (Function.uncurry B) Work.Construction.Qd) (hr : 0 < r)
    (hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.w r * (B r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ) :
    Work.Spaces.w r * (∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ := by
  have hInt : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f r θ)
      Work.Spaces.Iθ := hmem.1 r (le_of_lt hr)
  have hsq := slot_sq_integrableOn hmem hB hr hpt
  have hmono : (∫ θ in Work.Spaces.Iθ, Work.Spaces.w r * (B r θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ := by
    refine MeasureTheory.integral_mono_ae (hsq.const_mul _) hInt ?_
    exact ae_Iθ_of_forall_Ioo hpt
  rwa [MeasureTheory.integral_const_mul] at hmono

/-- The three pointwise comparisons, in the shape the generic lemmas want. -/
theorem slot_hpt_g {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) {r : ℝ} (hr : 0 < r) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.w r * (f r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ :=
  fun θ hθ => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_g hα hr hθ f

theorem slot_hpt_dth {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) {r : ℝ} (hr : 0 < r) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.w r * (Work.Spaces.Dth f r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ :=
  fun θ hθ => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_dth hα hr hθ f

theorem slot_hpt_dz {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) {r : ℝ} (hr : 0 < r) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.w r * (Work.Spaces.Dz f r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ :=
  fun θ hθ => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_dz hα hr hθ f

/-- **`r`-a.e. strong measurability of the angular energy of a slot.**  `PsgAux.slot_aemeasurable`
gives the measurability of the *Lebesgue* integral of the squared slice; the Bochner integral
coincides with it because the slice is integrable (at every `r > 0`, by the Hardy comparison). -/
theorem slot_energy_aemeasurable {α : ℝ} {f B : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 f)
    (hBc : ContinuousOn (Function.uncurry B) Work.Construction.Qd)
    (hpt : ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.w r * (B r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ) :
    AEMeasurable (fun r => ∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have h1 : AEMeasurable (fun r => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_aemeasurable hBc
  have h2 : AEMeasurable
      (fun r => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine h1.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => ?_)
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (slot_sq_integrableOn hmem hBc hr (hpt r hr))
      (Eventually.of_forall fun θ => sq_nonneg _)).symm
  refine (ENNReal.measurable_toReal.comp_aemeasurable h2).congr ?_
  filter_upwards with r
  exact ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)

/-! ## The `SlotData` bundles (the shape consumed by the `rl¹`-engines) -/

/-- **The generic bundle.**  For a slot `B` of a datum `f` with
`w r · (B r θ)² ≤ HkIntegrand α 4 f r θ` on the open quadrant, the angular energy
`Φ r = ∫_θ (B r θ)²` carries all the slot data used by the `rl¹`-engines, with `Xs = |f|²_{ℋ⁴}`. -/
theorem slotData_of_hpt {α : ℝ} {f B : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 f)
    (hBc : ContinuousOn (Function.uncurry B) Work.Construction.Qd)
    (hpt : ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.w r * (B r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ) :
    Work.FTS.NonlinRows.Rl1.SlotData α B
      (fun r => ∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2) (Work.Spaces.HkSq α 4 f) := by
  have hΦnn : ∀ r, 0 ≤ ∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2 :=
    fun r => MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hle : ∀ r, 0 < r → Work.Spaces.w r * (∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ :=
    fun r hr => slot_energy_le hmem hBc hr (hpt r hr)
  have hΨint := HkEner_integrableOn hmem
  have hΦmeas : AEMeasurable (fun r => ∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    slot_energy_aemeasurable hmem hBc hpt
  have hwΦmeas : AEMeasurable
      (fun r => Work.Spaces.w r * ∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    w_measurable.aemeasurable.mul hΦmeas
  have hwΦle : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Work.Spaces.w r * (∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => hle r hr)
  have hΦle_w : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2)
        ≤ Work.Spaces.w r * ∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => by
      simpa using mul_le_mul_of_nonneg_right (Work.FTS.NonlinRows.Rl1.one_le_w' hr) (hΦnn r))
  have hIntw : MeasureTheory.IntegrableOn
      (fun r => Work.Spaces.w r * ∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2) (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Integrable.mono' hΨint hwΦmeas.aestronglyMeasurable ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (w_pos' hr).le (hΦnn r))]
    exact hle r hr
  have hInt : MeasureTheory.IntegrableOn
      (fun r => ∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2) (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Integrable.mono' hΨint hΦmeas.aestronglyMeasurable ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => ?_)
    rw [Real.norm_of_nonneg (hΦnn r)]
    exact le_trans (by
      simpa using mul_le_mul_of_nonneg_right (Work.FTS.NonlinRows.Rl1.one_le_w' hr) (hΦnn r))
      (hle r hr)
  have hHkval : (∫ r in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 f r θ) = Work.Spaces.HkSq α 4 f := by
    rw [Work.Spaces.HkSq, Work.Spaces.Iz]
    exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici
  refine ⟨hΦnn, ?_, ?_, hΦmeas, hInt, hIntw, ?_, ?_⟩
  · intro r hr
    exact Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry B) hBc hr
  · intro r hr
    exact slot_sq_integrableOn hmem hBc hr (hpt r hr)
  · rw [← hHkval]
    exact (MeasureTheory.integral_mono_ae hInt hIntw hΦle_w).trans
      (MeasureTheory.integral_mono_ae hIntw hΨint hwΦle)
  · rw [← hHkval]
    exact MeasureTheory.integral_mono_ae hIntw hΨint hwΦle

/-- The slot data of the `(0,0)`-slot `f`. -/
theorem slotData_open_g {α : ℝ} {f : Fn} (hα : 0 < α)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    Work.FTS.NonlinRows.Rl1.SlotData α f (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f)
      (Work.Spaces.HkSq α 4 f) :=
  slotData_of_hpt hmem hso.continuousOn (fun r hr => slot_hpt_g hα hr)

/-- The slot data of the `(0,1)`-slot `D_θf`. -/
theorem slotData_open_dth {α : ℝ} {f : Fn} (hα : 0 < α)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    Work.FTS.NonlinRows.Rl1.SlotData α (Work.Spaces.Dth f)
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 f) (Work.Spaces.HkSq α 4 f) :=
  slotData_of_hpt hmem hso.Dth.continuousOn (fun r hr => slot_hpt_dth hα hr)

/-- The slot data of the `(1,0)`-slot `D_zf`. -/
theorem slotData_open_dz {α : ℝ} {f : Fn} (hα : 0 < α)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    Work.FTS.NonlinRows.Rl1.SlotData α (Work.Spaces.Dz f)
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi2 f) (Work.Spaces.HkSq α 4 f) :=
  slotData_of_hpt hmem hso.Dz.continuousOn (fun r hr => slot_hpt_dz hα hr)

end

end Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux
