import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.TransportS.HardDefs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingSup
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `fkRowDthZeroSlot` — integrability of the `(FK f)·ρ·(D_z^6D_θ f)·(D_z^6 f)` slot

This is the integrability side-condition of the level-six `(f,K)`-row at the slot
`(a,b) = (1,6)`: for a datum `f` in the level-six class `T6Coef.DatData α f M` and a leaf
weight `ρ` of the order-zero slot (`IsLeafW α 0 ρ`, i.e. `ρ` is `w²sin(2θ)^{-η}` or `w²`),

  `p ↦ FK f p.1 · (ρ p.1 p.2 · D_z^6D_θf p.1 p.2 · D_z^6f p.1 p.2)`

is integrable for the product of the restrictions of Lebesgue measure to `Iz` and `Iθ`.

The content is a pointwise domination: `|FK f| ≤ CM` (`fkSliceSup`) and, by AM–GM,
`ρ·|D_z^6D_θf|·|D_z^6f| ≤ ρ(D_z^6D_θf)²/2 + ρ(D_z^6f)²/2 ≤ HkIntegrand α 7 f`, because the
leaf weight `ρ` is dominated both by the `η`-block weight `w²sin(2θ)^{-η}` (which is the
weight of the pure `D_z^6`-slot of `ℋ^6`) and by the `γ`-block weight `Wt²` (the weight of
the mixed `D_z^6D_θ`-slot of `ℋ^7`), and `HkIntegrand α 6 f ≤ HkIntegrand α 7 f`.  The
result follows from `Integrable.mono'` once the joint integrability of `uncurry
(HkIntegrand α 7 f)` is available — that is the Tonelli bookkeeping of
`HkIntegrand_prod_integrable_open` below.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option autoImplicit false

/-! ## Elementary helpers -/

/-- Almost everywhere with respect to `(volume|Iz).prod (volume|Iθ)`, a point lies in the open
quadrant.  (`Iz = [0,∞)` and `Iθ = [0,π/2]` agree with the open half-line/interval up to the
null coordinate hyperplanes.) -/
private theorem ae_mem_openQuadrant :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hz : (Work.Spaces.Iz : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  have hθ : (Work.Spaces.Iθ : Set ℝ) =ᵐ[MeasureTheory.volume]
      Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm
  have hprod : ((Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume]
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_mem (isOpen_Ioi.prod isOpen_Ioo).measurableSet

/-- **Joint integrability of the uncurried `ℋ^k`-integrand.**  For a datum which is `C^∞` on
the open quadrant and honestly in `ℋ^k`, the `ℋ^k`-integrand is integrable for the product of
the restrictions of Lebesgue measure to `Iz` and `Iθ`.  Routed through
`Work.Spaces.integrable_prod_of_iterated` (nonnegative Tonelli): the integrand is nonnegative,
a.e. strongly measurable (continuous on the open quadrant), its angular slices are integrable
(`HkMem.1`) and its radial marginal is integrable (`HkMem.2`). -/
private theorem HkIntegrand_prod_integrable_open (α : ℝ) (k : ℕ) {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hmg : Work.Spaces.HkMem α k g) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  haveI : MeasureTheory.SFinite (MeasureTheory.volume.restrict Work.Spaces.Iz) := inferInstance
  haveI : MeasureTheory.SFinite (MeasureTheory.volume.restrict Work.Spaces.Iθ) := inferInstance
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (Work.Spaces.HkIntegrand α k g))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (hsg.continuousOn_HkIntegrand α k)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α k g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) fun z hz => hmg.1 z hz
  exact (Work.Spaces.integrable_prod_of_iterated
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k g z θ) haesm hslice hmg.2).1

/-- Every leaf weight is continuous on the open quadrant (it is one of the canonical weights
`w²sin(2θ)^{-q}`, `q ∈ {0, η, γ}`). -/
private theorem leaf_continuousOn_openQuadrant {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rcases hρ with rfl | rfl | ⟨_ha, rfl⟩
  · simpa only [Work.FTS.TransportS.leafEta, Work.FTS.TransportS.SlotT2.canonW]
      using Work.FTS.TransportS.SlotT2.continuousOn_canonW Work.Spaces.eta
  · have h : Work.FTS.TransportS.leafOne = Work.FTS.TransportS.SlotT2.canonW 0 := by
      funext z θ
      simp [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW]
    rw [h]
    exact Work.FTS.TransportS.SlotT2.continuousOn_canonW 0
  · simpa only [Work.FTS.TransportS.leafGam, Work.FTS.TransportS.SlotT2.canonW]
      using Work.FTS.TransportS.SlotT2.continuousOn_canonW (Work.Spaces.gam α)

/-- The angular moment `z ↦ FK f z` is continuous on the open quadrant as a function of
`(z,θ)` (it only depends on `z`). -/
private theorem fk_continuousOn_openQuadrant {f : ℝ → ℝ → ℝ}
    (h : ContinuousOn (fun z => Work.Construction.FK f z) (Set.Ioi 0)) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Construction.FK f p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  h.comp continuous_fst.continuousOn (fun _ hp => hp.1)

/-- `|a·b| ≤ (a² + b²)/2`. -/
private theorem abs_mul_le_half_sq_add (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * (|a| * |b|) ≤ a ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  rw [abs_mul]
  linarith

/-! ## The two pointwise slot dominations -/

/-- The leaf weights of the order-zero slot are dominated by the square of the `η`-block weight
`Whz = w/sin(2θ)^{η/2}` on the open quadrant.  (`leafGam` is excluded by `IsLeafW α 0`.) -/
private theorem leaf_le_Whz_sq {α : ℝ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α 0 ρ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ρ z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  rcases hρ with rfl | rfl | ⟨ha, _⟩
  · rw [Work.FTS.TransportS.leafEta, Work.FTS.H2.hbi_Whz_sq z θ hs]
  · rw [Work.FTS.TransportS.leafOne, Work.FTS.H2.hbi_Whz_sq z θ hs]
    exact le_mul_of_one_le_right (sq_nonneg _)
      (Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ)
  · exact absurd ha (by omega)

/-- Every leaf weight is dominated by the square of the `γ`-block weight `Wt` on the open
quadrant. -/
private theorem leaf_le_Wt_sq {α : ℝ} (hα : 0 < α) {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α 0 ρ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ρ z θ ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  have h1 : ρ z θ ≤ Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    (leaf_le_Whz_sq hρ hθ).trans (le_of_eq (Work.FTS.H2.hbi_Whz_sq z θ hs))
  rw [Work.Spaces.bt_Wt_sq α z θ hα hθI]
  exact h1.trans (mul_le_mul_of_nonneg_left (fkSliceSup_sin_rpow_le hα hθ) (sq_nonneg _))

/-! ## The target -/

theorem fkRowDthZeroSlot : ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      Work.FTS.TransportS.IsLeafW α 0 ρ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ =>
          Work.Construction.FK f p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed 6 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup
  intro α hα f M ρ hD hρ
  have hα0 : 0 < α := hα.1
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hD.bdd
  have hCM : 0 ≤ C * M := mul_nonneg hCpos.le hM0
  have hfkbd : ∀ z : ℝ, 0 < z → |Work.Construction.FK f z| ≤ C * M :=
    (hC α hα f M hD).1
  have hfkcont : ContinuousOn (fun z => Work.Construction.FK f z) (Set.Ioi 0) :=
    (hC α hα f M hD).2.1
  refine MeasureTheory.Integrable.mono'
    (g := fun p : ℝ × ℝ => (C * M) * Work.Spaces.HkIntegrand α 7 f p.1 p.2) ?_ ?_ ?_
  · -- the majorant is integrable
    exact (HkIntegrand_prod_integrable_open α 7 hD.sm hD.h7).const_mul (C * M)
  · -- a.e. strong measurability of the slot
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    exact (fk_continuousOn_openQuadrant hfkcont).mul
      (((leaf_continuousOn_openQuadrant hρ).mul
        (hD.sm.mixed 6 1).continuousOn).mul (hD.sm.mixed 6 0).continuousOn)
  · -- the pointwise domination, a.e.
    filter_upwards [ae_mem_openQuadrant] with p hp
    obtain ⟨hz, hθ⟩ := hp
    have hθI : p.2 ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hs : 0 ≤ Real.sin (2 * p.2) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
    have hρnn : 0 ≤ ρ p.1 p.2 :=
      (Work.FTS.TransportS.IsLeafW_le α hα0 hρ).1 p.1 p.2 hz hθ.1 hθ.2
    -- the mixed slot `D_z^6D_θf` against the `γ`-weight
    have hb1 : ρ p.1 p.2 * (Work.Spaces.mixed 6 1 f p.1 p.2) ^ 2
        ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by
      have hle := leaf_le_Wt_sq (α := α) hα0 hρ hz hθ
      have hsq := Work.Spaces.sq_le_HkIntegrand_mixed α 7 f p.1 p.2 1 6 (le_refl 1)
        (by norm_num)
      calc ρ p.1 p.2 * (Work.Spaces.mixed 6 1 f p.1 p.2) ^ 2
          ≤ (Work.Spaces.Wt α p.1 p.2) ^ 2 * (Work.Spaces.mixed 6 1 f p.1 p.2) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = (Work.Spaces.mixed 6 1 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 := hsq
    -- the pure radial slot `D_z^6f` against the `η`-weight
    have hb0 : ρ p.1 p.2 * (Work.Spaces.mixed 6 0 f p.1 p.2) ^ 2
        ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by
      have hle := leaf_le_Whz_sq hρ (z := p.1) (θ := p.2) hθ
      have hsq := fkSliceSup_dz_slot_le α 7 f hz hθ (j := 6) (by norm_num)
      rw [Work.Spaces.mixed_zero_right]
      calc ρ p.1 p.2 * (Work.Spaces.DzIter 6 f p.1 p.2) ^ 2
          ≤ (Work.FTS.H2.Whz p.1 p.2) ^ 2 * (Work.Spaces.DzIter 6 f p.1 p.2) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = (Work.Spaces.DzIter 6 f p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2
              * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
            rw [Work.FTS.H2.hbi_Whz_sq p.1 p.2 hs]; ring
        _ ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 := hsq
    -- AM–GM and the two slot bounds
    have hmain : |ρ p.1 p.2 * Work.Spaces.mixed 6 1 f p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2|
        ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by
      have habs : |ρ p.1 p.2 * Work.Spaces.mixed 6 1 f p.1 p.2
            * Work.Spaces.mixed 6 0 f p.1 p.2|
          = ρ p.1 p.2 * |Work.Spaces.mixed 6 1 f p.1 p.2
              * Work.Spaces.mixed 6 0 f p.1 p.2| := by
        simp only [abs_mul, abs_of_nonneg hρnn]
        ring
      rw [habs]
      calc ρ p.1 p.2 * |Work.Spaces.mixed 6 1 f p.1 p.2
              * Work.Spaces.mixed 6 0 f p.1 p.2|
          ≤ ρ p.1 p.2 * (((Work.Spaces.mixed 6 1 f p.1 p.2) ^ 2
                + (Work.Spaces.mixed 6 0 f p.1 p.2) ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left (abs_mul_le_half_sq_add _ _) hρnn
        _ = (ρ p.1 p.2 * (Work.Spaces.mixed 6 1 f p.1 p.2) ^ 2
              + ρ p.1 p.2 * (Work.Spaces.mixed 6 0 f p.1 p.2) ^ 2) / 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by linarith [hb1, hb0]
    rw [Real.norm_eq_abs]
    calc |Work.Construction.FK f p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed 6 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2)|
        = |Work.Construction.FK f p.1| * |ρ p.1 p.2 * Work.Spaces.mixed 6 1 f p.1 p.2
            * Work.Spaces.mixed 6 0 f p.1 p.2| := by rw [abs_mul]
      _ ≤ (C * M) * Work.Spaces.HkIntegrand α 7 f p.1 p.2 :=
          mul_le_mul (hfkbd p.1 hz) hmain (abs_nonneg _) hCM

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
