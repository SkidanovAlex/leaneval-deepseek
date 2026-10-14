import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.NonlinRows.NRow14T2
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SmainHon
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_MuLamOK.Defs
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_theta
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.mixed_mul_le
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.En =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Integ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

set_option maxHeartbeats 1600000

/-- If `F` is continuous on the open quadrant, vanishes at `z = 0`, and is dominated on the
open quadrant by `H` whose angular slices and `z`-marginal are integrable, then the angular
slices and the marginal of `F` are integrable. -/
theorem integrableConjuncts {F H : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)))
    (hH : MeasureTheory.AEStronglyMeasurable (Function.uncurry H)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hzero : ∀ θ : ℝ, F 0 θ = 0)
    (hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => H z θ) Work.Spaces.Iθ)
    (hmarg : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, H z θ) Work.Spaces.Iz)
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |F z θ| ≤ H z θ) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => F z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, F z θ) Work.Spaces.Iz := by
  have hFU : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => F z θ) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      rw [show (fun θ : ℝ => F 0 θ) = fun _ => (0 : ℝ) from funext hzero]
      exact integrableOn_zero
    · refine MeasureTheory.Integrable.mono' (hsl z hz)
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hF hzpos) ?_
      rw [restrict_Iθ_eq_Ioo]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs]
      exact hpt z θ hzpos hθ.1 hθ.2
  refine ⟨hFU, ?_⟩
  refine MeasureTheory.Integrable.mono' hmarg
    (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (Work.Spaces.aesm_of_continuousOn_Qd _ hF)) ?_
  rw [restrict_Iz_eq_Ioi]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  rw [Real.norm_eq_abs]
  refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have habs : MeasureTheory.IntegrableOn (fun θ => |F z θ|) Work.Spaces.Iθ := (hFU z hzI).norm
  refine MeasureTheory.integral_mono_ae habs (hsl z hzI) ?_
  rw [restrict_Iθ_eq_Ioo]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => hpt z θ hz hθ.1 hθ.2)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L3Nsg1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1600000

namespace Work.FTS.StrongPersist.L3Rhs

theorem L3Nsg1 : ∃ C : ℝ, 0 < C ∧
    ∀ (α Cs M : ℝ) (Φs f : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.StrongPersist.H6Adm α f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      Work.Spaces.HkMem α 3 (Work.FTS.Nonlin.N1sg α Φs f) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f)
        ≤ C * (1 + |Cs|) * α ^ (-(1 : ℝ)) * (1 + M) := by
  obtain ⟨Cw, hCw, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨Cp, hCp, hphib⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  refine ⟨2 * Cw * Cp + 1, by positivity, ?_⟩
  intro α Cs M Φs f hα hα1 hs hadm hM
  -- the weighted star coefficient `H` and its `𝒲^{4,∞}`-bounds
  obtain ⟨hHmem, hHle⟩ := Work.FTS.NonlinRows.starH_mem_of_StarPkgo2 hs
  have hHsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.NonlinRows.StarH α Φs) :=
    Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen hα hα1 hs.toStarPkgo
  -- the modulation factors through the bounded radial factor `φ(z) = z/(1+z)`
  have hf4 : Work.FTS.VocabO.HQo α 4 f :=
    ⟨hadm.reg.1, Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hadm.reg.1
      hadm.reg.2⟩
  obtain ⟨hGmem, hGbnd⟩ := hphib (g := f) hα hα1 hf4
  have hGsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * f z θ) := by
    have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) := by
      simpa only [Work.FTS.NonlinRows.NRow10aux.phiF] using
        Work.FTS.NonlinRows.NRow10aux.phiSelf_smoothOpen
    exact Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul h1 hadm.reg.1
  -- the level-four `𝒲^{4,∞}`-priced product rule
  obtain ⟨hPmem4, hPbd4⟩ := hwprod α hα hα1 (Work.FTS.NonlinRows.StarH α Φs)
      (fun z θ => z / (1 + z) * f z θ) hHsm hHmem ⟨hGsm, hGmem⟩
  have hPsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ)) :=
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul hHsm hGsm
  -- the row is `2` times the product on the open quadrant
  have hagree : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      2 * (Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ))
        = Work.FTS.Nonlin.N1sg α Φs f z θ := by
    intro z θ hz _ _
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := by positivity
    simp only [Work.FTS.Nonlin.N1sg, Work.FTS.NonlinRows.StarH]
    field_simp
    ring
  -- elementary facts about the data
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Real.sqrt_nonneg _
  have hM0 : 0 ≤ M := le_trans hXn0 hM
  have hHle' : Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.StarH α Φs) ≤ max Cs 0 * α :=
    le_trans hHle (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
  have hGbnd' : Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * f z θ) ≤ Cp * M :=
    le_trans hGbnd (mul_le_mul_of_nonneg_left hM hCp.le)
  have hXG0 : 0 ≤ Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * f z θ) := Real.sqrt_nonneg _
  have hq0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hCsα : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right Cs 0) hα.le
  -- the level-four estimate, priced by `max Cs 0 * α` and `Cp * M`
  have hstep : Work.Spaces.HkNorm α 4
      (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ))
      ≤ Cw * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α) * (Cp * M) := by
    refine le_trans hPbd4 ?_
    calc Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.StarH α Φs)
            * Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * f z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α)
            * Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * f z θ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hHle' (mul_nonneg hCw.le hq0)) hXG0
      _ ≤ Cw * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α) * (Cp * M) :=
          mul_le_mul_of_nonneg_left hGbnd' (mul_nonneg (mul_nonneg hCw.le hq0) hCsα)
  constructor
  · -- `ℋ³`-membership: descend from level four, scale by `2`, transfer along `Q0`
    have hPmem3 : Work.Spaces.HkMem α 3
        (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ)) :=
      Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hPsm hPmem4
    have h2P : Work.Spaces.HkMem α 3
        (fun z θ => 2 * (Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ))) :=
      Work.FTS.Nonlinear.Pieces.Rl1.HkMem_const_mul_of 2 hPmem3
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 3 h2P ?_
    intro z hz θ hθ
    exact hagree z θ hz hθ.1 hθ.2
  · -- the norm bound
    have hPbd3 : Work.Spaces.HkNorm α 3
        (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ))
        ≤ Work.Spaces.HkNorm α 4
        (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ)) :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 4) (k' := 3) (by norm_num) hPmem4
    have hSeq : Work.Spaces.HkSq α 3 (Work.FTS.Nonlin.N1sg α Φs f)
        = Work.Spaces.HkSq α 3
          (fun z θ => 2 * (Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ))) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 3
        (fun z θ hz hθ0 hθ1 => (hagree z θ hz hθ0 hθ1).symm)
    have hnorm_eq : Work.Spaces.HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f)
        = 2 * Work.Spaces.HkNorm α 3
          (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ)) := by
      rw [show Work.Spaces.HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f)
            = Work.Spaces.HkNorm α 3
              (fun z θ => 2 * (Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ)))
            from by simp only [Work.Spaces.HkNorm, hSeq],
        show (fun z θ => 2 * (Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ)))
            = (2 : ℝ) • (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ))
            from by funext z θ; simp,
        Work.FTS.EllipticEst.HkNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have harith : 2 * (Cw * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α) * (Cp * M))
        ≤ (2 * Cw * Cp + 1) * (1 + |Cs|) * α ^ (-(1 : ℝ)) * (1 + M) := by
      have hqα : α ^ (-(1 / 2 : ℝ)) * α ≤ 1 := by
        have h1 : α ^ (-(1 / 2 : ℝ)) * α ^ (1 : ℝ) ≤ 1 := by
          rw [← Real.rpow_add hα (-(1 / 2 : ℝ)) 1, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
          exact Real.rpow_le_one hα.le hα1 (by norm_num)
        rwa [Real.rpow_one] at h1
      have hR1 : max Cs 0 ≤ 1 + |Cs| :=
        max_le (le_trans (le_abs_self Cs) (by linarith [abs_nonneg Cs])) (by positivity)
      have hRM : max Cs 0 * M ≤ (1 + |Cs|) * (1 + M) :=
        mul_le_mul hR1 (by linarith) hM0 (by positivity)
      have hα1' : (1 : ℝ) ≤ α ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg_one]
        exact (one_le_inv₀ hα).mpr hα1
      have hnn : (0 : ℝ) ≤ 2 * Cw * Cp * (max Cs 0) * M := by positivity
      calc 2 * (Cw * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α) * (Cp * M))
          = 2 * Cw * Cp * (max Cs 0) * M * (α ^ (-(1 / 2 : ℝ)) * α) := by ring
        _ ≤ 2 * Cw * Cp * (max Cs 0) * M * 1 := mul_le_mul_of_nonneg_left hqα hnn
        _ = 2 * Cw * Cp * ((max Cs 0) * M) := by ring
        _ ≤ 2 * Cw * Cp * ((1 + |Cs|) * (1 + M)) :=
            mul_le_mul_of_nonneg_left hRM (by positivity)
        _ = 2 * Cw * Cp * (1 + |Cs|) * (1 + M) := by ring
        _ ≤ (2 * Cw * Cp + 1) * (1 + |Cs|) * (1 + M) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)
        _ ≤ (2 * Cw * Cp + 1) * (1 + |Cs|) * (1 + M) * α ^ (-(1 : ℝ)) :=
            le_mul_of_one_le_right (by positivity) hα1'
        _ = (2 * Cw * Cp + 1) * (1 + |Cs|) * α ^ (-(1 : ℝ)) * (1 + M) := by ring
    calc Work.Spaces.HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f)
        = 2 * Work.Spaces.HkNorm α 3
            (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ)) := hnorm_eq
      _ ≤ 2 * (Cw * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α) * (Cp * M)) :=
          mul_le_mul_of_nonneg_left (le_trans hPbd3 hstep) (by norm_num)
      _ ≤ (2 * Cw * Cp + 1) * (1 + |Cs|) * α ^ (-(1 : ℝ)) * (1 + M) := harith

end Work.FTS.StrongPersist.L3Rhs
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNgsBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (N1gs N2gs N3gs Xn)
open Work.Spaces (HkMem HkSq HkNorm WlInf WlInfMem)
open Work.FTS.EllipticEst (SmoothOpen)
open Work.FTS.VocabO (HQo)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## Elementary `rpow` facts at the half-integer exponent `-1/2` -/

private lemma rpow_neg_half_mul_le_one (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(1 / 2 : ℝ)) * α ≤ 1 := by
  have h1 : α ^ (-(1 / 2 : ℝ)) * α ^ (1 : ℝ) ≤ 1 := by
    rw [← Real.rpow_add hα0 (-(1 / 2 : ℝ)) 1,
      show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
    exact Real.rpow_le_one hα0.le hα1 (by norm_num)
  rwa [Real.rpow_one] at h1

private lemma rpow_neg_half_mul_sq_le_one (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(1 / 2 : ℝ)) * α ^ 2 ≤ 1 := by
  have hcast : (α : ℝ) ^ 2 = α ^ (2 : ℝ) := (Real.rpow_natCast α 2).symm
  rw [hcast, ← Real.rpow_add hα0 (-(1 / 2 : ℝ)) 2,
    show -(1 / 2 : ℝ) + 2 = 3 / 2 by norm_num]
  exact Real.rpow_le_one hα0.le hα1 (by norm_num)

/-! ## The generic piece bound -/

/-- **The level-three product bound.**  Given the level-four `𝒲^{4,∞}`-priced product rule
with constant `Cw`, a multiplier `m` that is `SmoothOpen` and of class `𝒲^{4,∞}` with
`|m|_{𝒲^{4,∞}} ≤ Bm`, and an `ℋ⁶`-function `hh` with `|hh|_{ℋ⁶} ≤ Bh`, the product
`c · (m · hh)` lies in `ℋ³` and

`|c · (m·hh)|_{ℋ³} ≤ |c| · Cw · α^{-1/2} · Bm · Bh`.

The proof is the chain `ℋ³ ⊂ ℋ⁴` (`HkNorm_mono_of_mem`), the product rule at level four, and
`ℋ⁴ ⊂ ℋ⁶` for the second factor. -/
private theorem ngs_piece_bound (Cw : ℝ) (hCw : 0 < Cw)
    (hwprod : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f g : Fn,
      SmoothOpen f → WlInfMem α 4 f → HQo α 4 g →
      HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Xn α (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * WlInf α 4 f * Xn α g)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {m hh : Fn} {Bm Bh : ℝ}
    (hmsm : SmoothOpen m) (hmW : WlInfMem α 4 m) (hmB : WlInf α 4 m ≤ Bm)
    (hhsm : SmoothOpen hh) (hhmem6 : HkMem α 6 hh) (hhbd : HkNorm α 6 hh ≤ Bh)
    (c : ℝ) :
    SmoothOpen (fun z θ => c * (m z θ * hh z θ)) ∧
    HkMem α 3 (fun z θ => c * (m z θ * hh z θ)) ∧
    HkNorm α 3 (fun z θ => c * (m z θ * hh z θ))
      ≤ |c| * (Cw * α ^ (-(1 / 2 : ℝ)) * Bm * Bh) := by
  have hmm4 : HkMem α 4 hh := HkMem_of_le_of_smoothOpen α (by norm_num) hhsm hhmem6
  obtain ⟨hmem4, hbd4⟩ := hwprod α hα0 hα1 m hh hmsm hmW ⟨hhsm, hmm4⟩
  have hbd6 : HkNorm α 4 hh ≤ Bh :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 4)
      (by norm_num) hhmem6) hhbd
  have hWnn : 0 ≤ WlInf α 4 m := Work.FTS.H2.WPQ.WlInf_nonneg' hmW
  have hBm0 : 0 ≤ Bm := le_trans hWnn hmB
  have hkey : Xn α (fun z θ => m z θ * hh z θ) ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Bm * Bh := by
    refine le_trans hbd4 ?_
    have h1 : WlInf α 4 m * Xn α hh ≤ Bm * Bh :=
      mul_le_mul hmB hbd6 (Work.Spaces.HkNorm_nonneg α 4 hh) hBm0
    have h2 : (0 : ℝ) ≤ Cw * α ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg hCw.le (Real.rpow_nonneg hα0.le _)
    calc Cw * α ^ (-(1 / 2 : ℝ)) * WlInf α 4 m * Xn α hh
        = Cw * α ^ (-(1 / 2 : ℝ)) * (WlInf α 4 m * Xn α hh) := by ring
      _ ≤ Cw * α ^ (-(1 / 2 : ℝ)) * (Bm * Bh) := mul_le_mul_of_nonneg_left h1 h2
      _ = Cw * α ^ (-(1 / 2 : ℝ)) * Bm * Bh := by ring
  have h3mem : HkMem α 3 (fun z θ => m z θ * hh z θ) :=
    HkMem_of_le_of_smoothOpen α (by norm_num) (hmsm.mul hhsm) hmem4
  have h34 : HkNorm α 3 (fun z θ => m z θ * hh z θ)
      ≤ HkNorm α 4 (fun z θ => m z θ * hh z θ) :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 4) (k' := 3) (by norm_num) hmem4
  refine ⟨?_, ?_, ?_⟩
  · exact Work.FTS.EllipticEst.SmoothOpen.const_mul' c (hmsm.mul hhsm)
  · exact Work.FTS.Nonlinear.Pieces.Rl1.HkMem_const_mul_of c h3mem
  · have heq : (fun z θ => c * (m z θ * hh z θ))
        = c • (fun z θ => m z θ * hh z θ) := by funext z θ; rfl
    rw [heq, Work.FTS.EllipticEst.HkNorm_smul]
    exact mul_le_mul_of_nonneg_left (le_trans h34 hkey) (abs_nonneg c)

theorem L3RhsNgsBound : ∃ C Cpow α₂ : ℝ, 0 < C ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (Ce M : ℝ) (f Φg : Work.FTS.Galerkin.Fn),
      Work.FTS.StrongPersist.EllPkgK α 6 Ce f Φg → Work.FTS.StrongPersist.H6Adm α f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.StrongPersist.L3Rhs.NGsSum α f Φg)) Work.FTS.EllipticEst.Q0 ∧
      Work.Spaces.HkMem α 3 (Work.FTS.StrongPersist.L3Rhs.NGsSum α f Φg) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.StrongPersist.L3Rhs.NGsSum α f Φg)
        ≤ C * (1 + |Ce|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by
  obtain ⟨Cw, hCw, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨CF, hCF, hFstar⟩ := Work.FTS.Nonlinear.FstarPkg.Fstar_W
  obtain ⟨CD, hCD, hDthFstar⟩ := Work.FTS.Nonlinear.FstarPkg.DthFstar_W
  obtain ⟨CZ, hCZ, hDzFstar⟩ := Work.FTS.Nonlinear.FstarPkg.DzFstar_W
  have hS0 : (0 : ℝ) < Cw * (CF + CD + CZ) := by
    have h1 : 0 < CF + CD + CZ := by linarith
    exact mul_pos hCw h1
  set Cc : ℝ := 16 * (Cw * (CF + CD + CZ)) + 1 with hCc
  have hCcpos : 0 < Cc := by rw [hCc]; linarith
  refine ⟨Cc, 0, 1, hCcpos, le_refl 0, one_pos, ?_⟩
  intro α hα Ce M f Φg hell hadm hM
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ### the three transported coefficients
  set RG : Fn := Work.Construction.Rop α (Work.Construction.PhiTil α f Φg) with hRG
  set UG : Fn := fun z θ =>
    Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ / Work.Construction.s2 θ with hUG
  set VG : Fn := Work.Construction.Vop (Work.Construction.PhiTil α f Φg) with hVG
  have hRsm : SmoothOpen RG := by rw [hRG]; exact hell.R.1.1
  have hRmem6 : HkMem α 6 RG := by rw [hRG]; exact hell.R.1.2
  have hRbd : HkNorm α 6 RG ≤ Ce * HkNorm α 6 f := by rw [hRG]; exact hell.R.2
  have hUsm : SmoothOpen UG := by rw [hUG]; exact hell.U.1.1
  have hUmem6 : HkMem α 6 UG := by rw [hUG]; exact hell.U.1.2
  have hUbd : HkNorm α 6 UG ≤ Ce * HkNorm α 6 f := by rw [hUG]; exact hell.U.2
  have hVsm : SmoothOpen VG := by rw [hVG]; exact hell.V.1.1
  have hVmem6 : HkMem α 6 VG := by rw [hVG]; exact hell.V.1.2
  have hVbd : HkNorm α 6 VG ≤ Ce * HkNorm α 6 f := by rw [hVG]; exact hell.V.2
  -- ### the `max Ce 0`-priced version (`Ce` may be negative)
  have hRbdc : HkNorm α 6 RG ≤ max Ce 0 * HkNorm α 6 f :=
    le_trans hRbd (mul_le_mul_of_nonneg_right (le_max_left Ce 0)
      (Work.Spaces.HkNorm_nonneg α 6 f))
  have hUbdc : HkNorm α 6 UG ≤ max Ce 0 * HkNorm α 6 f :=
    le_trans hUbd (mul_le_mul_of_nonneg_right (le_max_left Ce 0)
      (Work.Spaces.HkNorm_nonneg α 6 f))
  have hVbdc : HkNorm α 6 VG ≤ max Ce 0 * HkNorm α 6 f :=
    le_trans hVbd (mul_le_mul_of_nonneg_right (le_max_left Ce 0)
      (Work.Spaces.HkNorm_nonneg α 6 f))
  set Bh : ℝ := max Ce 0 * Work.Spaces.HkNorm α 6 f with hBh
  have hBh0 : 0 ≤ Bh := by
    rw [hBh]; exact mul_nonneg (le_max_right _ _) (Work.Spaces.HkNorm_nonneg α 6 f)
  -- ### the profile factors
  have hFsm : SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hFW := hFstar α hα0 hα1
  have hDW := hDthFstar α hα0 hα1
  have hZW := hDzFstar α hα0 hα1
  have hDthsm : SmoothOpen (Work.Spaces.Dth (Work.Construction.Fstar α)) := hFsm.Dth
  have hDzsm : SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFsm.Dz
  -- ### the three summands, in the shape of `ngs_piece_bound`
  set P1 : Fn := fun z θ => (2 : ℝ) * (Work.Construction.Fstar α z θ * RG z θ) with hP1
  set P2 : Fn := fun z θ => (-2 : ℝ) *
    (Work.Spaces.Dth (Work.Construction.Fstar α) z θ * UG z θ) with hP2
  set P3 : Fn := fun z θ => (-2 * α) *
    (Work.Spaces.Dz (Work.Construction.Fstar α) z θ * VG z θ) with hP3
  have hres1 := ngs_piece_bound Cw hCw hwprod hα0 hα1 hFsm hFW.1 hFW.2 hRsm hRmem6 hRbdc 2
  rw [← hP1] at hres1
  have hres2 := ngs_piece_bound Cw hCw hwprod hα0 hα1 hDthsm hDW.1 hDW.2 hUsm hUmem6 hUbdc (-2)
  rw [← hP2] at hres2
  have hres3 := ngs_piece_bound Cw hCw hwprod hα0 hα1 hDzsm hZW.1 hZW.2 hVsm hVmem6 hVbdc (-2 * α)
  rw [← hP3] at hres3
  have hP1sm : SmoothOpen P1 := hres1.1
  have hP1mem : HkMem α 3 P1 := hres1.2.1
  have hP1bd : HkNorm α 3 P1 ≤ 2 * (Cw * α ^ (-(1 / 2 : ℝ)) * (CF * α) * Bh) := by
    have h := hres1.2.2
    rw [show |(2 : ℝ)| = 2 by norm_num] at h
    exact h
  have hP2sm : SmoothOpen P2 := hres2.1
  have hP2mem : HkMem α 3 P2 := hres2.2.1
  have hP2bd : HkNorm α 3 P2 ≤ 2 * (Cw * α ^ (-(1 / 2 : ℝ)) * (CD * α ^ 2) * Bh) := by
    have h := hres2.2.2
    rw [show |(-2 : ℝ)| = 2 by norm_num] at h
    exact h
  have hP3sm : SmoothOpen P3 := hres3.1
  have hP3mem : HkMem α 3 P3 := hres3.2.1
  have hP3bd : HkNorm α 3 P3 ≤ 2 * α * (Cw * α ^ (-(1 / 2 : ℝ)) * (CZ * α) * Bh) := by
    have h := hres3.2.2
    rw [show |(-2 : ℝ) * α| = 2 * α by
      rw [abs_of_neg (by linarith : (-2 : ℝ) * α < 0)]
      ring] at h
    exact h
  -- ### identification of the three summands with `P1`, `P2`, `P3`
  have hN1 : N1gs α f Φg = P1 := by
    funext z θ
    simp only [Work.FTS.Nonlin.N1gs, Work.FTS.Nonlin.PhiTg, hRG, hP1]
    ring
  have hN2eq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      N2gs α f Φg z θ = P2 z θ := by
    intro z θ _ hθ hθ2
    have hs2 : Work.Construction.s2 θ ≠ 0 := by
      rw [Work.Construction.s2]
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
        (by linarith [Real.pi_pos]))
    have h1 : Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        = Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ := rfl
    simp only [Work.FTS.Nonlin.N2gs, Work.FTS.Nonlin.PhiTg, hUG, hP2, h1]
    field_simp
  have hN3 : N3gs α f Φg = P3 := by
    funext z θ
    simp only [Work.FTS.Nonlin.N3gs, Work.FTS.Nonlin.PhiTg, hVG, hP3]
    ring
  -- ### smoothness of the three summands on the open quadrant
  have hN1sm3 : ContDiffOn ℝ 3
      (Function.uncurry (N1gs α f Φg)) Work.FTS.EllipticEst.Q0 := by
    rw [hN1]; exact hP1sm.forall 3
  have hN2sm3 : ContDiffOn ℝ 3
      (Function.uncurry (N2gs α f Φg)) Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.congr (hP2sm.forall 3) ?_
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact hN2eq p.1 p.2 hz hθ0 hθ1
  have hN3sm3 : ContDiffOn ℝ 3
      (Function.uncurry (N3gs α f Φg)) Work.FTS.EllipticEst.Q0 := by
    rw [hN3]; exact hP3sm.forall 3
  -- ### `ℋ³`-membership of the three summands
  have hN1mem : HkMem α 3 (N1gs α f Φg) := by rw [hN1]; exact hP1mem
  have hN2mem : HkMem α 3 (N2gs α f Φg) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 3 hP2mem
      (fun z hz θ hθ => (hN2eq z θ hz hθ.1 hθ.2).symm)
  have hN3mem : HkMem α 3 (N3gs α f Φg) := by rw [hN3]; exact hP3mem
  -- ### the three bounds, in the common shape `2 Cw Cᵢ Bh`
  have hb1 : HkNorm α 3 (N1gs α f Φg) ≤ 2 * (Cw * CF) * Bh := by
    rw [hN1]
    refine le_trans hP1bd ?_
    have h1 : α ^ (-(1 / 2 : ℝ)) * α ≤ 1 := rpow_neg_half_mul_le_one α hα0 hα1
    have h2 : (0 : ℝ) ≤ Cw * CF := mul_nonneg hCw.le hCF.le
    have h3 : 0 ≤ (Cw * CF) * Bh := mul_nonneg h2 hBh0
    have h4 : Cw * α ^ (-(1 / 2 : ℝ)) * (CF * α) * Bh ≤ Cw * CF * Bh := by
      rw [show Cw * α ^ (-(1 / 2 : ℝ)) * (CF * α) * Bh
            = (Cw * CF) * (α ^ (-(1 / 2 : ℝ)) * α) * Bh by ring]
      calc (Cw * CF) * (α ^ (-(1 / 2 : ℝ)) * α) * Bh
          ≤ (Cw * CF) * 1 * Bh :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) hBh0
        _ = Cw * CF * Bh := by ring
    calc 2 * (Cw * α ^ (-(1 / 2 : ℝ)) * (CF * α) * Bh)
        ≤ 2 * (Cw * CF * Bh) := mul_le_mul_of_nonneg_left h4 (by norm_num)
      _ = 2 * (Cw * CF) * Bh := by ring
  have hb2 : HkNorm α 3 (N2gs α f Φg) ≤ 2 * (Cw * CD) * Bh := by
    have hsq : HkSq α 3 (N2gs α f Φg) = HkSq α 3 P2 :=
      Work.FTS.EllipticEst.HkSq_congr_open α 3
        (fun z θ hz hθ hθ2 => hN2eq z θ hz hθ hθ2)
    have hnorm : HkNorm α 3 (N2gs α f Φg) = HkNorm α 3 P2 := by
      simp only [HkNorm]
      rw [hsq]
    rw [hnorm]
    refine le_trans hP2bd ?_
    have h1 : α ^ (-(1 / 2 : ℝ)) * α ^ 2 ≤ 1 := rpow_neg_half_mul_sq_le_one α hα0 hα1
    have h2 : (0 : ℝ) ≤ Cw * CD := mul_nonneg hCw.le hCD.le
    have h3 : 0 ≤ (Cw * CD) * Bh := mul_nonneg h2 hBh0
    have h4 : Cw * α ^ (-(1 / 2 : ℝ)) * (CD * α ^ 2) * Bh ≤ Cw * CD * Bh := by
      rw [show Cw * α ^ (-(1 / 2 : ℝ)) * (CD * α ^ 2) * Bh
            = (Cw * CD) * (α ^ (-(1 / 2 : ℝ)) * α ^ 2) * Bh by ring]
      calc (Cw * CD) * (α ^ (-(1 / 2 : ℝ)) * α ^ 2) * Bh
          ≤ (Cw * CD) * 1 * Bh :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) hBh0
        _ = Cw * CD * Bh := by ring
    calc 2 * (Cw * α ^ (-(1 / 2 : ℝ)) * (CD * α ^ 2) * Bh)
        ≤ 2 * (Cw * CD * Bh) := mul_le_mul_of_nonneg_left h4 (by norm_num)
      _ = 2 * (Cw * CD) * Bh := by ring
  have hb3 : HkNorm α 3 (N3gs α f Φg) ≤ 2 * (Cw * CZ) * Bh := by
    rw [hN3]
    refine le_trans hP3bd ?_
    have h1 : α ^ (-(1 / 2 : ℝ)) * α ≤ 1 := rpow_neg_half_mul_le_one α hα0 hα1
    have h2 : (0 : ℝ) ≤ Cw * CZ := mul_nonneg hCw.le hCZ.le
    have h3 : 0 ≤ (2 * (Cw * CZ)) * Bh := mul_nonneg (by positivity) hBh0
    have h4 : 2 * α * (Cw * α ^ (-(1 / 2 : ℝ)) * (CZ * α) * Bh) ≤ 2 * (Cw * CZ) * Bh := by
      have h5 : α * (α ^ (-(1 / 2 : ℝ)) * α) ≤ 1 := by
        have h6 : 0 ≤ α ^ (-(1 / 2 : ℝ)) * α :=
          mul_nonneg (Real.rpow_nonneg hα0.le _) hα0.le
        exact le_trans (mul_le_mul hα1 h1 h6 (by norm_num : (0 : ℝ) ≤ 1)) (by norm_num)
      calc 2 * α * (Cw * α ^ (-(1 / 2 : ℝ)) * (CZ * α) * Bh)
          = (2 * (Cw * CZ) * Bh) * (α * (α ^ (-(1 / 2 : ℝ)) * α)) := by ring
        _ ≤ (2 * (Cw * CZ) * Bh) * 1 := mul_le_mul_of_nonneg_left h5 h3
        _ = 2 * (Cw * CZ) * Bh := by ring
    exact h4
  -- ### assembly
  have h12 := HkAddFin (α := α) (k := 3) hN1sm3 hN2sm3 hN1mem hN2mem
  have h12sm3 : ContDiffOn ℝ 3
      (Function.uncurry (fun z θ => N1gs α f Φg z θ + N2gs α f Φg z θ))
      Work.FTS.EllipticEst.Q0 := hN1sm3.add hN2sm3
  have h123 := HkAddFin (α := α) (k := 3) h12sm3 hN3sm3 h12.1 hN3mem
  -- ### the common scale `S`
  have hSnn : 0 ≤ Cw * (CF + CD + CZ) * Bh :=
    mul_nonneg (mul_nonneg hCw.le (by linarith)) hBh0
  have hb1' : HkNorm α 3 (N1gs α f Φg) ≤ 2 * (Cw * (CF + CD + CZ) * Bh) := by
    refine le_trans hb1 ?_
    have hle : Cw * CF * Bh ≤ Cw * (CF + CD + CZ) * Bh := by
      have h2 : 0 ≤ Cw * Bh := mul_nonneg hCw.le hBh0
      calc Cw * CF * Bh = (Cw * Bh) * CF := by ring
        _ ≤ (Cw * Bh) * (CF + CD + CZ) :=
            mul_le_mul_of_nonneg_left (by linarith) h2
        _ = Cw * (CF + CD + CZ) * Bh := by ring
    nlinarith [hle]
  have hb2' : HkNorm α 3 (N2gs α f Φg) ≤ 2 * (Cw * (CF + CD + CZ) * Bh) := by
    refine le_trans hb2 ?_
    have hle : Cw * CD * Bh ≤ Cw * (CF + CD + CZ) * Bh := by
      have h2 : 0 ≤ Cw * Bh := mul_nonneg hCw.le hBh0
      calc Cw * CD * Bh = (Cw * Bh) * CD := by ring
        _ ≤ (Cw * Bh) * (CF + CD + CZ) :=
            mul_le_mul_of_nonneg_left (by linarith) h2
        _ = Cw * (CF + CD + CZ) * Bh := by ring
    nlinarith [hle]
  have hb3' : HkNorm α 3 (N3gs α f Φg) ≤ 2 * (Cw * (CF + CD + CZ) * Bh) := by
    refine le_trans hb3 ?_
    have hle : Cw * CZ * Bh ≤ Cw * (CF + CD + CZ) * Bh := by
      have h2 : 0 ≤ Cw * Bh := mul_nonneg hCw.le hBh0
      calc Cw * CZ * Bh = (Cw * Bh) * CZ := by ring
        _ ≤ (Cw * Bh) * (CF + CD + CZ) :=
            mul_le_mul_of_nonneg_left (by linarith) h2
        _ = Cw * (CF + CD + CZ) * Bh := by ring
    nlinarith [hle]
  -- ### the `ℋ³` bound of the block
  have hnorm : HkNorm α 3 (NGsSum α f Φg) ≤ 16 * (Cw * (CF + CD + CZ) * Bh) := by
    refine le_trans h123.2 ?_
    have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hS4 : HkNorm α 3 (fun z θ => N1gs α f Φg z θ + N2gs α f Φg z θ)
        ≤ 6 * (Cw * (CF + CD + CZ) * Bh) := by
      refine le_trans h12.2 ?_
      have h2 : Real.sqrt 2 * (2 * (Cw * (CF + CD + CZ) * Bh)
          + 2 * (Cw * (CF + CD + CZ) * Bh)) ≤ 6 * (Cw * (CF + CD + CZ) * Bh) := by
        have hX : 0 ≤ Cw * (CF + CD + CZ) * Bh := hSnn
        nlinarith [hs2, hX, Real.sqrt_nonneg 2]
      exact le_trans (mul_le_mul_of_nonneg_left (by linarith [hb1', hb2'])
        (Real.sqrt_nonneg 2)) h2
    have hAB : HkNorm α 3 (fun z θ => N1gs α f Φg z θ + N2gs α f Φg z θ)
        + HkNorm α 3 (N3gs α f Φg)
        ≤ 6 * (Cw * (CF + CD + CZ) * Bh) + 2 * (Cw * (CF + CD + CZ) * Bh) := by
      linarith [hS4, hb3']
    have h3 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    refine le_trans (mul_le_mul_of_nonneg_left hAB h3) ?_
    nlinarith [hs2, hSnn, Real.sqrt_nonneg 2]
  -- ### the final constant bookkeeping
  have hfin : 16 * (Cw * (CF + CD + CZ) * Bh)
      ≤ Cc * (1 + |Ce|) ^ 4 * α ^ (-(0 : ℝ)) * (1 + M) ^ 4
          * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by
    have hKc_le : max Ce 0 ≤ (1 + |Ce|) ^ 4 := by
      have h1 : max Ce 0 ≤ |Ce| := max_le (le_abs_self Ce) (abs_nonneg Ce)
      have h3 : (1 : ℝ) ≤ 1 + |Ce| := by linarith [abs_nonneg Ce]
      have h4 : 1 + |Ce| ≤ (1 + |Ce|) ^ 4 := by
        have h5 : (1 : ℝ) ≤ (1 + |Ce|) ^ 3 := one_le_pow₀ h3 (n := 3)
        nlinarith [h3, h5]
      linarith
    have hXn_le : Work.FTS.StrongPersist.Xn6 α f
        ≤ (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by
      have h0 : 0 ≤ Work.FTS.StrongPersist.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
      nlinarith [h0]
    have hM1 : (1 : ℝ) ≤ (1 + M) ^ 4 :=
      one_le_pow₀ (by have h0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hM
                      linarith) (n := 4)
    have hCc0 : 0 ≤ Cc := hCcpos.le
    have hCc_le : 16 * (Cw * (CF + CD + CZ)) ≤ Cc := by rw [hCc]; linarith
    have hKc0 : 0 ≤ max Ce 0 := le_max_right _ _
    have hXn0 : 0 ≤ Work.FTS.StrongPersist.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
    have hU0 : 0 ≤ α ^ (-(0 : ℝ)) := Real.rpow_nonneg hα0.le _
    have ha0 : α ^ (-(0 : ℝ)) = 1 := by rw [neg_zero, Real.rpow_zero]
    -- step 1: pull `Bh` apart, bound the numeric factor by `Cc`
    have hs1 : 16 * (Cw * (CF + CD + CZ) * Bh)
        = 16 * (Cw * (CF + CD + CZ)) * (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f := by
      rw [hBh]; ring
    rw [hs1]
    have hA : 16 * (Cw * (CF + CD + CZ)) * (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f
        ≤ Cc * (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f := by
      have h1 : 0 ≤ (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f := mul_nonneg hKc0 hXn0
      calc 16 * (Cw * (CF + CD + CZ)) * (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f
          = (16 * (Cw * (CF + CD + CZ))) * ((max Ce 0)
              * Work.FTS.StrongPersist.Xn6 α f) := by ring
        _ ≤ Cc * ((max Ce 0) * Work.FTS.StrongPersist.Xn6 α f) :=
            mul_le_mul_of_nonneg_right hCc_le h1
        _ = Cc * (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f := by ring
    refine le_trans hA ?_
    have hB : Cc * (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f
        ≤ Cc * (1 + |Ce|) ^ 4 * Work.FTS.StrongPersist.Xn6 α f := by
      have h1 : (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f
          ≤ (1 + |Ce|) ^ 4 * Work.FTS.StrongPersist.Xn6 α f :=
        mul_le_mul_of_nonneg_right hKc_le hXn0
      calc Cc * (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f
          = Cc * ((max Ce 0) * Work.FTS.StrongPersist.Xn6 α f) := by ring
        _ ≤ Cc * ((1 + |Ce|) ^ 4 * Work.FTS.StrongPersist.Xn6 α f) :=
            mul_le_mul_of_nonneg_left h1 hCc0
        _ = Cc * (1 + |Ce|) ^ 4 * Work.FTS.StrongPersist.Xn6 α f := by ring
    refine le_trans hB ?_
    have hC : Cc * (1 + |Ce|) ^ 4 * Work.FTS.StrongPersist.Xn6 α f
        ≤ Cc * (1 + |Ce|) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 :=
      mul_le_mul_of_nonneg_left hXn_le
        (mul_nonneg hCc0 (by positivity))
    refine le_trans hC ?_
    rw [ha0]
    have hD0 : 0 ≤ Cc * (1 + |Ce|) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 :=
      mul_nonneg (mul_nonneg hCc0 (by positivity)) (by positivity)
    calc Cc * (1 + |Ce|) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2
        = (Cc * (1 + |Ce|) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2) * 1 := by ring
      _ ≤ (Cc * (1 + |Ce|) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2) * (1 + M) ^ 4 :=
          mul_le_mul_of_nonneg_left hM1 hD0
      _ = Cc * (1 + |Ce|) ^ 4 * 1 * (1 + M) ^ 4
            * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by ring
  exact ⟨h12sm3.add hN3sm3, h123.1, le_trans hnorm hfin⟩

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.N5ssPriced =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

/-- **Priced row 26**: the `ℋ⁴`-honesty and the `α²`-bound of the profile-only star piece
`N₅^{**} = -sin²θ · FK(F_*) · F_*`, with a *constant* independent of all data.

This piece does not involve `g`, `Φs` or `Φg` at all: it is the explicit function
`-(4α²/c(α)) · (sin²θ · Γ(θ)) · (z²/(1+z)⁴)`, an angular `×` radial product.  The corresponding
row of the open vocabulary is `Work.FTS.Nonlinear.Open.Row26`, whose statement carries the
interfaces `N4Norm'`, `N4Extra'`, `GalClass α g`, `StarPkgo α Cs Φs`, `EllPkgGo α Ce g Φg` and the
hypotheses `0 < α`, `α ≤ 1`, `α ≤ α₂` — but its proof uses *only* `0 < α` and `α ≤ 1` (the file's
own header says "The hypotheses `g`, `Φs`, `Φg` (and hence the interfaces) are irrelevant for this
row").  The body works with the explicit factorisation `N5ss α = fun z θ => a θ * r z` with
`r z = Work.Spaces.hKer z ^ 2`, the angular jet bound `dthIter_sinSq_Gam_le_sharp`, and the
`AngRadHkMem`/`Xn_ang_rad_le_gen`/`hkerSq_radial_alt` machinery whose constants are independent of
every hypothesis.  So the proof is a verbatim copy of that proof with the interface hypotheses
dropped. -/
theorem N5ssPriced : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5ss α) ∧
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5ss α) ≤ C * α ^ 2 := by
  obtain ⟨Csh, hCshpos, hCsh⟩ := Work.FTS.Nonlinear.Open.Row26Ang
  obtain ⟨Cr, hCrpos, hCr⟩ := Work.FTS.Nonlinear.Pieces.RNP.hkerSq_radial_alt
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
  refine ⟨Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * Cr) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * Cr) := by
      positivity
    linarith
  · intro α hαIoc
    have hα : 0 < α := hαIoc.1
    have hα1 : α ≤ 1 := hαIoc.2
    have hcge : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    -- the angular profile, the radial factor and the angular majorant
    set psi : ℝ → ℝ := fun θ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ with hpsi
    set r : ℝ → ℝ := fun z => (-(4 * α ^ 2 / Work.Spaces.c α)) * Work.Spaces.hKer z ^ 2 with hr
    set G : ℝ → ℝ := fun θ => Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) with hG
    -- ### the factorisation of the piece
    have hfac : Work.FTS.Nonlin.N5ss α = fun z θ => psi θ * r z := by
      funext z θ
      rw [hpsi, hr]
      simp only [Work.FTS.Nonlin.N5ss]
      rw [Work.FTS.Nonlin.FK_Fstar hα hα1]
      simp only [Work.Construction.Fstar, Work.FM.Fstar, Work.Spaces.hKer_apply]
      ring
    -- ### smoothness of the two factors
    have hSOsin2 : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Real.sin θ ^ 2) := by
      have h1 := Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
        Work.FTS.Nonlinear.Open.row25_smoothOpen_neg_sinSq
      rw [show (fun _ (θ : ℝ) => (-1 : ℝ) * (-(Real.sin θ ^ 2)))
          = fun _ (θ : ℝ) => Real.sin θ ^ 2 from by
        funext z θ; ring] at h1
      exact h1
    have hSOpsi : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => psi θ) := by
      rw [hpsi]
      exact Work.FTS.Nonlinear.Open.row25_smoothOpen_ang_mul hSOsin2
        (Work.FTS.Nonlinear.Open.row25_smoothOpen_Gam α)
    have hrSO : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => r z) := by
      rw [hr]
      refine Work.FTS.NonlinRows.smoothOpen_const_mul (-(4 * α ^ 2 / Work.Spaces.c α)) ?_
      refine Work.FTS.NonlinRows.smoothOpen_radial fun n => ?_
      have h := Work.FTS.Nonlinear.Open.row25_contDiffOn_hKer n
      simpa only [pow_two] using h.mul h
    -- ### the two angular bounds
    have ha0 : ∀ θ ∈ Work.Spaces.Iθ, |psi θ| ≤ 1 := by
      intro θ hθ
      simpa only [hpsi, Work.FTS.Nonlinear.Pieces.RNP.psiB] using
        Work.FTS.Nonlinear.Pieces.RNP.psiB_abs_le_one (α := α) hα hθ
    have ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => psi θ') 0 θ| ≤ Csh * G θ := by
      intro i hi1 hi4 θ hθ
      have h := hCsh α hα hα1 i hi1 hi4 θ hθ
      simpa only [hpsi, hG] using h
    -- ### the angular majorant
    have hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ := by
      intro θ hθ
      have hGam := Work.Spaces.Gam_bounds α θ hα hθ
      have hs := Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
      rw [hG]
      exact mul_nonneg hGam.1 (by linarith)
    have hGint : MeasureTheory.IntegrableOn
        (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ := by
      have h := (hM α hα hα1).1
      rw [hG]
      simpa only [mul_pow, mul_assoc] using h
    have hm1 : ∫ θ in Work.Spaces.Iθ,
        G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ ≤ M := by
      have h := (hM α hα hα1).2
      rw [hG]
      simpa only [mul_pow, mul_assoc] using h
    -- ### the radial factor
    have hrmem : Work.Spaces.HkMem α 4 (fun z (_ : ℝ) => r z) := by
      rw [hr]
      exact Work.FTS.LocData.HkMem_const_mul α 4 (-(4 * α ^ 2 / Work.Spaces.c α))
        (hCr α hα hα1).1
    have hcoefabs : |-(4 * α ^ 2 / Work.Spaces.c α)| ≤ 40 * α ^ 2 := by
      rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * α ^ 2 / Work.Spaces.c α),
        div_le_iff₀ hcpos]
      nlinarith [hcge, sq_nonneg α, hα.le]
    have hXnr : Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z) ≤ 40 * α ^ 2 * Cr := by
      have h0 : Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => Work.Spaces.hKer z ^ 2) ≤ Cr :=
        (hCr α hα hα1).2
      have hrew : Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z)
          = |-(4 * α ^ 2 / Work.Spaces.c α)|
            * Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => Work.Spaces.hKer z ^ 2) := by
        rw [hr]
        exact Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α (-(4 * α ^ 2 / Work.Spaces.c α))
          (fun z (_ : ℝ) => Work.Spaces.hKer z ^ 2)
      rw [hrew]
      exact mul_le_mul hcoefabs h0 (Work.Spaces.HkNorm_nonneg α 4 _) (by positivity)
    -- ### the honesty and the norm
    have hHk : Work.Spaces.HkMem α 4 (fun z θ => psi θ * r z) :=
      Work.FTS.NonlinRows.AuxAngRad.HkMem_ang_rad (α := α) (a := psi) (r := r) (G := G)
        (B0 := 1) (B1 := Csh) hSOpsi hrSO hGnn hGint ha0 ha1 hrmem
    have hXn := Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen α hα psi r G
      (B0 := 1) (B1 := Csh) (M1 := M) (by norm_num) hCshpos.le hMpos.le hGnn ha0 ha1
      hGint hm1 hrmem
    rw [hfac]
    refine ⟨hHk, ?_⟩
    calc Work.FTS.Nonlin.Xn α (fun z θ => psi θ * r z)
        ≤ Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M)
            * Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z) := hXn
      _ ≤ Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * α ^ 2 * Cr) :=
          mul_le_mul_of_nonneg_left hXnr (Real.sqrt_nonneg _)
      _ = (Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * Cr)) * α ^ 2 := by ring
      _ ≤ (Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * Cr) + 1) * α ^ 2 := by
          have h1 : (0 : ℝ) ≤ Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * Cr) := by
            positivity
          nlinarith [h1, sq_nonneg α]

end Work.FTS.StrongPersist.L3Rhs
end
-- ===== merged: Submission.Work.FTS_MuLamOK.Conversion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLamOK

open Work.FTS.Galerkin (Fn Fam slice muDyn lamDyn)

set_option autoImplicit false

/-! ## The scale conversion -/

/-- **The envelope converts.**  For `0 < α ≤ 1`, `0 ≤ X ≤ C₀α²` and `0 ≤ K`,
`K(α² + √α·X + α^{-3/2}X²) ≤ K(1 + C₀ + C₀²)α²`. -/
theorem envelope_le {α C₀ K X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK0 : 0 ≤ K)
    (hX0 : 0 ≤ X) (hX : X ≤ C₀ * α ^ 2) :
    K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)
      ≤ K * (1 + C₀ + C₀ ^ 2) * α ^ 2 := by
  have hC₀α2 : (0 : ℝ) ≤ C₀ * α ^ 2 := le_trans hX0 hX
  have hX2 : X ^ 2 ≤ C₀ ^ 2 * α ^ 4 := by
    have h := mul_self_le_mul_self hX0 hX
    nlinarith [h, hC₀α2]
  have h1 : Real.sqrt α * X ≤ C₀ * α ^ 2 := by
    have hsq : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
    have h := mul_le_mul hsq hX hX0 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have h2 : α ^ (-(3 / 2 : ℝ)) * X ^ 2 ≤ C₀ ^ 2 * α ^ 2 := by
    have hle : α ^ (-(3 / 2 : ℝ)) ≤ α ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
    have hid : α ^ (-(2 : ℝ)) * α ^ 4 = α ^ 2 := by
      rw [← Real.rpow_natCast α 4, ← Real.rpow_add hα]
      norm_num
    calc α ^ (-(3 / 2 : ℝ)) * X ^ 2 ≤ α ^ (-(2 : ℝ)) * X ^ 2 :=
          mul_le_mul_of_nonneg_right hle (sq_nonneg X)
      _ ≤ α ^ (-(2 : ℝ)) * (C₀ ^ 2 * α ^ 4) :=
          mul_le_mul_of_nonneg_left hX2 (Real.rpow_nonneg hα.le _)
      _ = C₀ ^ 2 * α ^ 2 := by
        rw [show α ^ (-(2 : ℝ)) * (C₀ ^ 2 * α ^ 4) = C₀ ^ 2 * (α ^ (-(2 : ℝ)) * α ^ 4) by ring,
          hid]
  have hsum : α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2
      ≤ (1 + C₀ + C₀ ^ 2) * α ^ 2 := by linarith
  calc K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)
      ≤ K * ((1 + C₀ + C₀ ^ 2) * α ^ 2) := mul_le_mul_of_nonneg_left hsum hK0
    _ = K * (1 + C₀ + C₀ ^ 2) * α ^ 2 := by ring

/-- The transport envelope converts: `K X ≤ (K C₀) α²` for `X ≤ C₀α²`. -/
theorem envelope_transport_le {α C₀ K X : ℝ} (hK0 : 0 ≤ K) (hX : X ≤ C₀ * α ^ 2) :
    K * X ≤ K * C₀ * α ^ 2 := by
  calc K * X ≤ K * (C₀ * α ^ 2) := mul_le_mul_of_nonneg_left hX hK0
    _ = K * C₀ * α ^ 2 := by ring

/-! ## The three scaled zero modes from the three row envelopes -/




/-! ## The same three conversions, for rows quantified over the class `ClassC` only

The `N`-row needs the elliptic package `EllPkgGo α Ce f (E f)` as a hypothesis, and that package
is only available on the class `ClassC`; so the interface form of the three rows
(`RowReduction.MuLamOK_of_rowEnvelopes`) takes them quantified over `ClassC α f`.  These three
variants are the ones matching that interface. -/

/-- **`ZeroMode0` from the `N₀`-row envelope, `ClassC`-quantified row.** -/
theorem ZeroMode0_of_row_classC {α C₀ K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    (hrow : ∀ f : Fn, Work.FTS.ClassC.ClassC α f →
      |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
        ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2)) :
    ZeroMode0 α C₀ (K * (1 + C₀ + C₀ ^ 2)) := by
  intro f hf hX
  exact le_trans (hrow f hf) (envelope_le hα hα1 hK (Work.Spaces.HkNorm_nonneg α 4 f) hX)

/-- **`ZeroMode1` from the `N`-row envelope, `ClassC`-quantified row.** -/
theorem ZeroMode1_of_row_classC {α C₀ K : ℝ} {Φs : Fn} {E : Fn → Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hK : 0 ≤ K)
    (hrow : ∀ f : Fn, Work.FTS.ClassC.ClassC α f →
      |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
          (fun z θ => Φs z θ + E f z θ)) 0|
        ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2)) :
    ZeroMode1 α C₀ (K * (1 + C₀ + C₀ ^ 2)) Φs E := by
  intro f hf hX
  exact le_trans (hrow f hf) (envelope_le hα hα1 hK (Work.Spaces.HkNorm_nonneg α 4 f) hX)

/-- **`ZeroMode2` from the transport-row envelope, `ClassC`-quantified row.** -/
theorem ZeroMode2_of_row_classC {α C₀ K : ℝ} (hK : 0 ≤ K)
    (hrow : ∀ f : Fn, Work.FTS.ClassC.ClassC α f →
      |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0|
        ≤ K * Work.FTS.Nonlin.Xn α f) :
    ZeroMode2 α C₀ (K * C₀) := by
  intro f hf hX
  exact le_trans (hrow f hf) (envelope_transport_le hK hX)

/-! ## Monotonicity in the constant -/

theorem ZeroMode0.mono {α C₀ K K' : ℝ} (h : ZeroMode0 α C₀ K) (hKK : K ≤ K') :
    ZeroMode0 α C₀ K' := fun f hf hX => le_trans (h f hf hX) (mul_le_mul_of_nonneg_right hKK
  (sq_nonneg α))

theorem ZeroMode1.mono {α C₀ K K' : ℝ} {Φs : Fn} {E : Fn → Fn} (h : ZeroMode1 α C₀ K Φs E)
    (hKK : K ≤ K') : ZeroMode1 α C₀ K' Φs E := fun f hf hX =>
  le_trans (h f hf hX) (mul_le_mul_of_nonneg_right hKK (sq_nonneg α))

theorem ZeroMode2.mono {α C₀ K K' : ℝ} (h : ZeroMode2 α C₀ K) (hKK : K ≤ K') :
    ZeroMode2 α C₀ K' := fun f hf hX => le_trans (h f hf hX) (mul_le_mul_of_nonneg_right hKK
  (sq_nonneg α))

end Work.FTS_MuLamOK
end
end
