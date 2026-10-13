/-
Energy bounds with integrability for a `canonW q`-weighted slot.

The single engine is `slot_energy`: if the weighted square `canonW q z θ * (X z θ)²` is
(pointwise on `Iz × Iθ`) dominated by the level-`k` `ℋ`-integrand of a datum `g` with
`HkMem α k g`, and its uncurried version is continuous on the open quadrant, then both the
angular slices and the `z`-marginal are integrable and the iterated integral is at most
`HkSq α k g`.

The instantiations `canonW_energy_mixed6`, `canonW_energy_mixed4`, `canonW_energy_z_pos6`,
`canonW_energy_z6` feed the pointwise slot dominations of `Wgt.lean`
(`canonW_mul_mixed_le6`, `canonW_mul_mixed_le4`, `canonW_mul_z_pos_le6`, `canonW_mul_z_le6`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Wgt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_mono canonW_zero_z)

set_option maxHeartbeats 1600000

/-! ## The engine -/

/-- **Energy and integrability of a dominated weighted slot.** -/
theorem slot_energy {α : ℝ} {k : ℕ} {g X : ℝ → ℝ → ℝ} {q : ℝ}
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g)
    (hcont : ContinuousOn (Function.uncurry (fun z θ => canonW q z θ * (X z θ) ^ 2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hdom : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      canonW q z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => canonW q z θ * (X z θ) ^ 2) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (X z θ) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (X z θ) ^ 2) ≤ Work.Spaces.HkSq α k g := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => canonW q z θ * (X z θ) ^ 2) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0,
        show (fun θ : ℝ => canonW q 0 θ * (X 0 θ) ^ 2) = fun _ => (0 : ℝ) from
          funext (fun θ => by rw [canonW_zero_z, zero_mul])]
      exact integrableOn_zero
    · refine MeasureTheory.Integrable.mono' (hmem.1 z hz)
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos) ?_
      rw [restrict_Iθ_eq_Ioo]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (canonW_nonneg (Set.Ioo_subset_Icc_self hθ))
        (sq_nonneg _))]
      exact hdom z hz θ hθ
  refine ⟨hsl, ?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hmem.2
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (Work.Spaces.aesm_of_continuousOn_Qd _ hcont)) ?_
    rw [restrict_Iz_eq_Ioi]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_eq_abs]
    refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
    refine integral_Iθ_mono_ae (f := fun θ => |canonW q z θ * (X z θ) ^ 2|)
      (g := fun θ => Work.Spaces.HkIntegrand α k g z θ)
      (fun θ hθ => by
        rw [abs_of_nonneg (mul_nonneg (canonW_nonneg (Set.Ioo_subset_Icc_self hθ))
          (sq_nonneg _))]
        exact hdom z (Set.mem_Ici.mpr hz.le) θ hθ)
      (fun _ _ => abs_nonneg _)
      (hmem.1 z (Set.mem_Ici.mpr hz.le))
  · rw [Work.Spaces.HkSq]
    refine integral_Iz_mono_ae
      (f := fun z => ∫ θ in Work.Spaces.Iθ, canonW q z θ * (X z θ) ^ 2)
      (g := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      (fun z hz => ?_) (fun z hz => ?_) hmem.2
    · exact integral_Iθ_mono_ae (f := fun θ => canonW q z θ * (X z θ) ^ 2)
        (g := fun θ => Work.Spaces.HkIntegrand α k g z θ)
        (fun θ hθ => hdom z (Set.mem_Ici.mpr hz.le) θ hθ)
        (fun θ hθ => mul_nonneg (canonW_nonneg (Set.Ioo_subset_Icc_self hθ)) (sq_nonneg _))
        (hmem.1 z (Set.mem_Ici.mpr hz.le))
    · exact MeasureTheory.setIntegral_nonneg hIθm
        (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _))

/-! ## The instantiations -/

/-- Energy and integrability for the mixed slot `mixed j' i' g` (`1 ≤ i'`, `i' + j' ≤ 6`),
weighted by `canonW q` with `0 ≤ q ≤ γ`. -/
theorem canonW_energy_mixed6 {α : ℝ} (hα : 0 < α) {q : ℝ} (hq0 : 0 ≤ q)
    (hqγ : q ≤ Work.Spaces.gam α) {g : ℝ → ℝ → ℝ}
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    {j' i' : ℕ} (hi : 1 ≤ i') (hij : i' + j' ≤ 6) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => canonW q z θ * (Work.Spaces.mixed j' i' g z θ) ^ 2) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed j' i' g z θ) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed j' i' g z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 g :=
  slot_energy (X := Work.Spaces.mixed j' i' g) hgsm hgm
    (continuousOn_canonW_slot_mixed (j' := j') (i' := i') hgsm)
    (fun _ _ θ hθ => canonW_mul_mixed_le6 hα hq0 hqγ hi hij (Set.Ioo_subset_Icc_self hθ))

/-- Energy and integrability for the mixed slot `mixed j' i' g` of order `≤ 4`, weighted by
`canonW q` with `0 ≤ q ≤ γ`. -/
theorem canonW_energy_mixed4 {α : ℝ} (hα : 0 < α) {q : ℝ} (hq0 : 0 ≤ q)
    (hqγ : q ≤ Work.Spaces.gam α) {g : ℝ → ℝ → ℝ}
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 4 g)
    {j' i' : ℕ} (hi : 1 ≤ i') (hij : i' + j' ≤ 4) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => canonW q z θ * (Work.Spaces.mixed j' i' g z θ) ^ 2) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed j' i' g z θ) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed j' i' g z θ) ^ 2) ≤ Work.Spaces.HkSq α 4 g :=
  slot_energy (X := Work.Spaces.mixed j' i' g) hgsm hgm
    (continuousOn_canonW_slot_mixed (j' := j') (i' := i') hgsm)
    (fun z hz _ hθ => canonW_mul_mixed_le4 hα hq0 hqγ hi hij hz (Set.Ioo_subset_Icc_self hθ))

/-- Energy and integrability for the pure `D_z`-slot `D_z^{j'} g` (`j' ≤ 6`), weighted by
`canonW q` with `0 < q ≤ η`. -/
theorem canonW_energy_z_pos6 {α : ℝ} {q : ℝ} (hq0 : 0 < q) (hqη : q ≤ Work.Spaces.eta)
    {g : ℝ → ℝ → ℝ} (hgsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hgm : Work.Spaces.HkMem α 6 g) {j' : ℕ} (hj : j' ≤ 6) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => canonW q z θ * (Work.Spaces.DzIter j' g z θ) ^ 2) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.DzIter j' g z θ) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.DzIter j' g z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 g :=
  slot_energy (X := Work.Spaces.DzIter j' g) hgsm hgm
    (continuousOn_canonW_slot_z (j' := j') hgsm)
    (fun _ _ θ hθ => canonW_mul_z_pos_le6 hq0 hqη hj hθ)

/-- Energy and integrability for the pure `D_z`-slot `D_z^{j'} g` (`j' ≤ 6`), weighted by
`canonW q` with `0 ≤ q ≤ η`. -/
theorem canonW_energy_z6 {α : ℝ} {q : ℝ} (hq0 : 0 ≤ q) (hqη : q ≤ Work.Spaces.eta)
    {g : ℝ → ℝ → ℝ} (hgsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hgm : Work.Spaces.HkMem α 6 g) {j' : ℕ} (hj : j' ≤ 6) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => canonW q z θ * (Work.Spaces.DzIter j' g z θ) ^ 2) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.DzIter j' g z θ) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.DzIter j' g z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 g :=
  slot_energy (X := Work.Spaces.DzIter j' g) hgsm hgm
    (continuousOn_canonW_slot_z (j' := j') hgsm)
    (fun z hz θ hθ => canonW_mul_z_le6 hq0 hqη hj hθ)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
