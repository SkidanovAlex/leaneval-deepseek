import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.PhiStar.EllExistHalf
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Aux.RStep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T4bRowSlot
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingSup
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.StrongPersist.SP6.EH6
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.ClassCHon.hkMem_zero_psiSeries_of_source =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "w" => Work.Spaces.w
local notation "sEta" => Work.FTS.EllipticEst.sEta
local notation "psiSeries" => Work.FTS.PhiStar.Series.psiSeries
local notation "psiTrunc" => Work.FTS.PhiStar.Series.psiTrunc
local notation "acoeff" => Work.FTS.PhiStar.Series.acoeff
local notation "cmode" => Work.FTS.PhiStar.Series.cmode
local notation "eNorm" => Work.EllipticEst.ModalSolution.eNorm

/-- `sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
private theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ sEta θ :=
  Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _

/-- **The level-`0` honesty and energy bound of `psiSeries α F`, from the two per-mode facts,
the slice integrabilities, the coefficient summability and the three measurabilities.**

This is the whole analytic content of `hkMem_zero_psiSeries_of_source`; the wrapping theorem
below supplies its hypotheses from the source-side lemmas of the area. -/
theorem hkMem_zero_psiSeries_aux {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF0 : Work.Spaces.HkMem α 0 F)
    (hmom : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0)
    (hint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Iθ)
    (hintσ : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * sEta θ) Iθ)
    (hint_a : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun z => (acoeff α m F z) ^ 2 * (w z) ^ 2) Iz)
    (hper : ∀ m : ℕ, Work.FTS.ClassC.muSeq α m *
        Real.sqrt (∫ z in Iz, (acoeff α m F z) ^ 2 * (w z) ^ 2)
      ≤ Real.sqrt (∫ z in Iz,
          (Real.sqrt (eNorm m) * cmode m F z) ^ 2 * (w z) ^ 2))
    (hmeasT : ∀ N : ℕ, AEMeasurable (fun z : ℝ => ∫⁻ θ in Iθ,
        ENNReal.ofReal ((psiTrunc α F N z θ) ^ 2 * (w z) ^ 2 * sEta θ))
      (MeasureTheory.volume.restrict Iz))
    (hslmeas : ∀ z ∈ Iz, AEMeasurable (fun θ : ℝ =>
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      (MeasureTheory.volume.restrict Iθ))
    (hmeasS : AEMeasurable (fun z : ℝ => ∫⁻ θ in Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hcoef : ∀ z : ℝ, 0 < z → Summable (fun m : ℕ =>
      ((m : ℝ) + 1) * |acoeff α m F z|)) :
    Work.Spaces.HkMem α 0 (psiSeries α F) ∧
      ∃ C : ℝ, 0 < C ∧ Work.Spaces.HkSq α 0 (psiSeries α F)
        ≤ C * Work.Spaces.HkSq α 0 F := by
  have hα1 : α ≤ 1 := by linarith
  -- ## the pointwise convergence of the truncations
  have hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.PhiStar.integrableOn_sq_Q0_of_HkMem hF0 hsm
  have hconv : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun N : ℕ => psiTrunc α F N z θ) Filter.atTop
        (nhds (psiSeries α F z θ)) := fun z hz θ hθ =>
    Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries hα hα1 hmom hsm hL2 hz hθ
  -- ## nonnegativity of the source energy and of the angular mass
  have hHkSqF : 0 ≤ Work.Spaces.HkSq α 0 F := by
    rw [Work.Spaces.HkSq]
    exact integral_nonneg fun z => integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 0 F z θ
  have hσnn : 0 ≤ ∫ θ in Iθ, sEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => sEta_nonneg_Iθ hθ)
  set e : ℝ := 72 * (∫ θ in Iθ, sEta θ) with he
  have he0 : 0 ≤ e := by rw [he]; linarith
  set C₀ : ℝ := e * Work.Spaces.HkSq α 0 F with hC₀
  have hC₀nn : 0 ≤ C₀ := by rw [hC₀]; exact mul_nonneg he0 hHkSqF
  -- ## the truncated `lintegral` bound, uniformly in `N`
  have hbd : ∀ N : ℕ, (∫⁻ z in Iz, ∫⁻ θ in Iθ,
      ENNReal.ofReal ((psiTrunc α F N z θ) ^ 2 * (w z) ^ 2 * sEta θ))
        ≤ ENNReal.ofReal C₀ := by
    intro N
    have h1 := Work.FTS.ClassC.lintegral_psiTrunc_le α F N hsm hF0 hint hintσ
      (fun m _ => hint_a m) (μ := fun m => Work.FTS.ClassC.muSeq α m)
      (fun m => Work.FTS.ClassC.muSeq_pos hα hα4 m) (fun m _ => hper m)
    have h2 := Work.FTS.ClassC.modeSum_muSeq_sum_le α hα hα4 N
    have hK0 : 0 ≤ 9 * (∫ θ in Iθ, sEta θ) := by linarith
    have hS0 : 0 ≤ ∑ m ∈ Finset.range (N + 1),
        (((m : ℝ) + 1) / Work.FTS.ClassC.muSeq α m) ^ 2 :=
      Finset.sum_nonneg fun m _ => sq_nonneg _
    have h3 : 9 * (∫ θ in Iθ, sEta θ) *
          (∑ m ∈ Finset.range (N + 1),
            (((m : ℝ) + 1) / Work.FTS.ClassC.muSeq α m) ^ 2)
          * Work.Spaces.HkSq α 0 F ≤ C₀ := by
      rw [hC₀, he]
      have h8 : (∑ m ∈ Finset.range (N + 1),
            (((m : ℝ) + 1) / Work.FTS.ClassC.muSeq α m) ^ 2) ≤ 8 := h2
      nlinarith [hHkSqF, hσnn, hK0, hS0, h8]
    exact h1.trans (ENNReal.ofReal_le_ofReal h3)
  -- ## Fatou in the truncation parameter
  have hfinExpl : (∫⁻ z in Iz, ∫⁻ θ in Iθ,
      ENNReal.ofReal ((psiSeries α F z θ) ^ 2 * (w z) ^ 2 * sEta θ))
        ≤ ENNReal.ofReal C₀ :=
    Work.FTS.ClassCHon.CmpSupp.lintegral_psiSeries_le_Iz hC₀nn hconv hmeasT hbd
  -- ## transfer to the `HkIntegrand` form used by the capstone
  have hz_eq : ∀ z : ℝ, (∫⁻ θ in Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      = (∫⁻ θ in Iθ,
        ENNReal.ofReal ((psiSeries α F z θ) ^ 2 * (w z) ^ 2 * sEta θ)) := by
    intro z
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq' hθ]
    rw [show w z ^ 2 * ((psiSeries α F z θ) ^ 2 * sEta θ)
        = (psiSeries α F z θ) ^ 2 * (w z) ^ 2 * sEta θ from by ring]
  have hfinIz : (∫⁻ z in Iz, ∫⁻ θ in Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      ≤ ENNReal.ofReal C₀ := by
    rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hz_eq)]
    exact hfinExpl
  have hfin : (∫⁻ z in Set.Ioi (0 : ℝ), ∫⁻ θ in Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      ≤ ENNReal.ofReal C₀ := by
    rw [MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
    exact hfinIz
  -- ## the honesty of the series, and the energy bound
  have hmemΨ : Work.Spaces.HkMem α 0 (psiSeries α F) :=
    Work.FTS.ClassC.HonestCut.HkMem_zero_psiSeries_of_capstone hC₀nn hslmeas hfin hmeasS hcoef
  refine ⟨hmemΨ, ⟨e + 1, by linarith, ?_⟩⟩
  have hC₁ : 0 ≤ (e + 1) * Work.Spaces.HkSq α 0 F :=
    mul_nonneg (by linarith) hHkSqF
  have hfin₁ : (∫⁻ z in Set.Ioi (0 : ℝ), ∫⁻ θ in Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      ≤ ENNReal.ofReal ((e + 1) * Work.Spaces.HkSq α 0 F) := by
    refine hfin.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [hHkSqF]
  exact Work.FTS.ClassCHon.CmpSupp.hkSq_le_of_lintegral hC₁ hmemΨ hfin₁

theorem hkMem_zero_psiSeries_of_source {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF : Work.Spaces.HkMem α 1 F)
    (hmom : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    Work.Spaces.HkMem α 0 (Work.FTS.PhiStar.Series.psiSeries α F) ∧
      ∃ C : ℝ, 0 < C ∧ Work.Spaces.HkSq α 0 (Work.FTS.PhiStar.Series.psiSeries α F)
        ≤ C * Work.Spaces.HkSq α 0 F := by
  -- ## descent in the order, and the extraction of the `z ∂_z F` slot
  have hsmForall : ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hsm
  have hF0 : Work.Spaces.HkMem α 0 F :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (k := 0) (l := 1) (by norm_num) hsmForall hF
  have hF1 : Work.Spaces.HkMem α 1 F := hF
  have hDz : Work.Spaces.HkMem α 0 (Work.Spaces.Dz F) :=
    Work.FTS.EllipticEst.Cores.HkMem_zero_of_DzIter_slot (k := 1) (i := 1) le_rfl hsm hF1
  -- ## the angular slice integrabilities of the source
  have hint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    fun z hz => Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem hF0 hz
  have hintσ : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ :=
    fun z hz => Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem hF0 hz
  -- ## the two per-mode facts and the three measurabilities
  obtain ⟨hint_a, hper⟩ :=
    Work.FTS.ClassCHon.perMode_data_of_source hα hα4 hsm hF0 hF1 hmom
  obtain ⟨hmeasT, hslmeas, hmeasS⟩ :=
    Work.FTS.ClassCHon.meas_bundle_open
      (Work.FTS.ClassCHon.aemeasurable_acoeff_of_source hα hα4 hsm hF0 hF1)
  -- ## the weighted `ℓ¹`-summability of the radial coefficients
  exact hkMem_zero_psiSeries_aux hα hα4 hsm hF0 hmom hint hintσ hint_a hper hmeasT hslmeas
    hmeasS (Work.FTS.ClassCHon.hcoef_source_general hα hα4 hsm hF0 hF1 hDz hmom)

end Work.FTS.ClassCHon
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.AprioriHalves =====
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
set_option linter.unusedVariables false




/-! ## Why there is no converse

`AprioriP ⟹ AprioriPSixth` is **not** available: to evaluate `AprioriP` at the `ℋ⁶`-half one must
supply the datum's *small-ball* condition, and the only place it appears in `AprioriP`'s own
conclusion is at `τ = 0` — reading it off requires applying `AprioriP` again, i.e. the argument is
circular.  The two halves are therefore genuinely *independent inputs* of the clause, not
projections of it; that is exactly why the barrier argument must be run **jointly** (each half's
hypothesis is the other's conclusion along the flow). -/

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.DecayMaj =====
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
open Work.FTS.StrongGlobal (Xn6)
open Work.FTS.StrongGlobal (Xn6)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The angular supremum of the low slots -/





/-! ## The packaging from a `SlotMaj` bound -/


/-- **The projected slice vanishes off the open quadrant** (both `Jeps` and `bump` do), which is
what makes the *junk angles* of `SlotMaj` harmless for the projected slices. -/
theorem Pz_Jeps_eq_zero_of_theta {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {f : Fn} {z θ : ℝ}
    (hθ : θ ∉ Set.Ioo 0 (π / 2)) : Pz (Jeps ρ ε f) z θ = 0 := by
  have hbox : ¬ (Real.pi / 4 < θ ∧ θ < 3 * Real.pi / 8) := fun hc =>
    hθ ⟨by linarith [Real.pi_pos, hc.1], by linarith [Real.pi_pos, hc.2]⟩
  have hb : bump z θ = 0 := by
    rw [bump_eq_zero_iff]
    right; right
    by_contra hcon
    push_neg at hcon
    exact hbox hcon
  rw [Pz_apply, Jeps_eq_zero_of_theta ρ ε f hθ, hb]
  ring


/-! ## Assembling `EpsDecay` from four `SlotMaj` bounds -/

/-- **`EpsDecay` from the four pointwise bounds.**  The five conjuncts of `EpsDecay` in
definitional order (bounded-block form, 2026-10-12: the three elliptic blocks `≤ 3` on the open
quadrant). -/
theorem EpsDecay_of_Maj {α : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {ε τ : ℝ} {g : Fam}
    {Maj : ℝ → ℝ}
    (h0 : ∀ z, 0 ≤ Maj z) (h1 : ∀ z, Maj z ≤ 1)
    (hint : IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hs : SlotMaj 1 Maj (slice (JfamP ρ ε g) τ))
    (hB :
      ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
        |Work.Construction.Rop α (Work.Construction.PhiTil α (slice (JfamP ρ ε g) τ)
            (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ| ≤ 3 ∧
        |Work.Construction.Uop α (Work.Construction.PhiTil α (slice (JfamP ρ ε g) τ)
            (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ
            / Work.Construction.s2 θ| ≤ 3 ∧
        |Work.Construction.Vop (Work.Construction.PhiTil α (slice (JfamP ρ ε g) τ)
            (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ| ≤ 3) :
    EpsDecay α ρ Φs E ε τ g Maj := ⟨h0, h1, hint, hs, hB⟩

/-! ## The repaired a-priori decay interface -/

/-- **The ball-carrying a-priori decay bound**: the honest form of `AprioriDecay`.  Its extra
clause is the *small ball* for the projected slices — exactly what `AprioriP` proves, and the
missing input that makes the pointwise domination producible (`Maj` must be chosen before the
solutions, so it can only be sized by a bound available *a priori*). -/
def AprioriDecayB (α : ℝ) (ρ : ℝ × ℝ → ℝ) (T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (C₀ : ℝ) (Maj : ℝ → ℝ) : Prop :=
  IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) ∧
    ∀ ε ∈ Set.Ioc 0 1, ∀ g : Fam, IsEpsSolP α ρ ε T Φs E g₀ g → EpsRegP α ρ ε T g →
      (∀ τ ∈ Set.Icc 0 T,
        Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2) →
      ∀ τ ∈ Set.Icc 0 T, EpsDecay α ρ Φs E ε τ g Maj


/-! ## The decay producer interface -/


/-! ## The corrected assembly of `EpsUniformMem` -/


end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.SlotPairingHkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The two endpoints `0`, `π/2` are null for `volume.restrict Iθ`: `θ` lies in the *open*
interval `(0, π/2)` almost everywhere. -/
private lemma ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  show ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))), θ ∈ Set.Ioo (0 : ℝ) (π / 2)
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hθ)

/-- **The level-six slot pairing is dominated by the average of the two `ℋ⁶`-squares.**

For every leaf weight `ρ` attached to the slot `a`, every slot `(a,b)` with `a + b ≤ 6`, and
any two `ℋ⁶`-data `u`, `f` (no smoothness assumed),

  `|∫_z ∫_θ ρ · D_z^bD_θ^a u · D_z^bD_θ^a f| ≤ (|u|²_{ℋ⁶} + |f|²_{ℋ⁶})/2`.

Route: at every `z ∈ [0,∞)` and almost every angle, `ρ` is nonnegative and each of the two
weighted squares is a slot of the `ℋ⁶`-integrand (`domLeaf_all`); AM–GM splits the product,
and the two integrations in the honest slices (`HkMem`) preserve the bound. -/
theorem SlotPairingHkSq {α : ℝ} (hα : 0 < α) {a b : ℕ} (hab : a + b ≤ 6)
      {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
      {u f : ℝ → ℝ → ℝ} (mu : Work.Spaces.HkMem α 6 u) (mf : Work.Spaces.HkMem α 6 f) :
      |Work.FTS.TransportS.slotPairing ρ a b u f|
        ≤ (Work.Spaces.HkSq α 6 u + Work.Spaces.HkSq α 6 f) / 2 := by
  -- ## the pointwise AM–GM bound, almost everywhere in `θ`, for every `z ∈ Iz`
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ|
        ≤ (Work.Spaces.HkIntegrand α 6 u z θ
            + Work.Spaces.HkIntegrand α 6 f z θ) / 2 := by
    intro z hz
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hρ0 : 0 ≤ ρ z θ := leaf_nonneg hρ z hθI
    have hu : ρ z θ * (Work.Spaces.mixed b a u z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 u z θ :=
      domLeaf_all hα hρ (f := u) (b' := b) (n := 6) (z := z) (θ := θ) hθ hab
    have hf : ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      domLeaf_all hα hρ (f := f) (b' := b) (n := 6) (z := z) (θ := θ) hθ hab
    have ham : |ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ|
        ≤ (ρ z θ * (Work.Spaces.mixed b a u z θ) ^ 2
            + ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) / 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
      have h1 : |Work.Spaces.mixed b a u z θ| * |Work.Spaces.mixed b a f z θ|
          ≤ ((Work.Spaces.mixed b a u z θ) ^ 2
              + (Work.Spaces.mixed b a f z θ) ^ 2) / 2 :=
        Work.Spaces.abs_mul_abs_le_half_add_sq _ _
      calc ρ z θ * |Work.Spaces.mixed b a u z θ| * |Work.Spaces.mixed b a f z θ|
          = ρ z θ * (|Work.Spaces.mixed b a u z θ|
              * |Work.Spaces.mixed b a f z θ|) := by ring
        _ ≤ ρ z θ * (((Work.Spaces.mixed b a u z θ) ^ 2
              + (Work.Spaces.mixed b a f z θ) ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left h1 hρ0
        _ = (ρ z θ * (Work.Spaces.mixed b a u z θ) ^ 2
              + ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) / 2 := by ring
    linarith [ham, hu, hf]
  -- ## the `θ`-integration at a fixed `z`
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ|
        ≤ ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 u z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)) / 2 := by
    intro z hz
    have hmaj : Integrable (fun θ => (Work.Spaces.HkIntegrand α 6 u z θ
        + Work.Spaces.HkIntegrand α 6 f z θ) / 2) (volume.restrict Work.Spaces.Iθ) :=
      ((mu.1 z hz).add (mf.1 z hz)).div_const 2
    have hnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] fun θ =>
        (Work.Spaces.HkIntegrand α 6 u z θ + Work.Spaces.HkIntegrand α 6 f z θ) / 2 :=
      Filter.Eventually.of_forall fun θ => div_nonneg (add_nonneg
        (Work.Spaces.HkIntegrand_nonneg α 6 u z θ)
        (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)) (by norm_num)
    calc |∫ θ in Work.Spaces.Iθ,
            ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ|
        ≤ ∫ θ in Work.Spaces.Iθ,
            |ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α 6 u z θ
            + Work.Spaces.HkIntegrand α 6 f z θ) / 2 :=
          Work.Spaces.integral_le_integral_of_ae_le_of_nonneg hmaj hnn (hpt z hz)
      _ = ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 u z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)) / 2 := by
          rw [MeasureTheory.integral_div,
            MeasureTheory.integral_add (mu.1 z hz) (mf.1 z hz)]
  -- ## the `z`-integration
  have hmajz : Integrable (fun z => ((∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 u z θ)
      + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)) / 2)
      (volume.restrict Work.Spaces.Iz) := (mu.2.add mf.2).div_const 2
  have hnnz : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz] fun z =>
      ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 u z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)) / 2 :=
    Filter.Eventually.of_forall fun z => div_nonneg (add_nonneg
      (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 u z θ)
      (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 f z θ)) (by norm_num)
  have hmain : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ|
      ≤ (Work.Spaces.HkSq α 6 u + Work.Spaces.HkSq α 6 f) / 2 := by
    calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ|
        ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ,
            ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ z in Work.Spaces.Iz, ((∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 6 u z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)) / 2 :=
          Work.Spaces.integral_le_integral_of_ae_le_of_nonneg hmajz hnnz
            (MeasureTheory.ae_restrict_of_forall_mem
              (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)
              fun z hz => hslice z hz)
      _ = (Work.Spaces.HkSq α 6 u + Work.Spaces.HkSq α 6 f) / 2 := by
          rw [MeasureTheory.integral_div, MeasureTheory.integral_add mu.2 mf.2]
          rfl
  rw [Work.FTS.TransportS.slotPairing]
  exact hmain

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMomentJetSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

/-!
# The weighted `L²`-price of the moment jet `D_z^b (FK f)`

`fkMomentJetSq` records that the `b`-th `D_z`-iterate of the angular moment `FK f` is an
element of the radial `L²(w²)`-space, priced by the full `ℋ⁶`-energy of the datum:

  `∫_z (D_z^b (FK f) z)² w(z)² dz ≤ C · HkSq α 6 f`,   `b ≤ 6`.

The proof is the two-step reduction already used for the pointwise companion
(`fkDzdIterSqLe`, `Npair6SupAux.DzIter_FK_eq_ae`):

* `D_z^b (FK f) = FK (D_z^b f)` almost everywhere in `z` (`DzIter_FK_eq_ae` composed with
  `Elliptic.DzIter_rad`), which is *exactly* what makes the weight `w²` harmless;
* the angular Cauchy–Schwarz bound `(FK (D_z^b f) z)² ≤ 16 ∫_θ (D_z^b f z θ)²`
  (`FKdzIter_sq_le`), applied at `z > 0`;
* the pointwise domination `w(z)² (D_z^b f z θ)² ≤ HkIntegrand α 6 f z θ` on the open
  quadrant (`dzIter_sq_w_sq_le_HkIntegrand_k`, since `b ≤ 6` is one of the `D_z`-slots of
  `ℋ⁶`), which after integrating in `θ` gives `∫_θ w² (D_z^b f)² ≤ ∫_θ HkIntegrand`.

The constant is the universal `16`; no `α`-dependence appears anywhere.
-/

/-- The angular moment `z ↦ FK (D_z^k f) z` of an open-quadrant datum is a.e. strongly
measurable on `Iz`: it is the `θ`-marginal of the jointly continuous (on the open quadrant)
function `(z,θ) ↦ D_z^k f z θ · K θ`. -/
private theorem aesm_FK_DzIter_aux {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => Work.Construction.FK (Work.Spaces.DzIter k f) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.DzIter k f p.1 p.2 * Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hF.DzIter k).continuousOn).mul (by unfold Work.Spaces.K; fun_prop)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have h := hjoint.integral_prod_right'
  simpa only [Work.Construction.FK] using h

/-- The radial weight squared, `z ↦ w z ^ 2`, is a.e. strongly measurable on `Iz` (it is
continuous on the open half-line, and `Iz` agrees with `Ioi 0` up to a null set). -/
private theorem aesm_w_sq_aux :
    MeasureTheory.AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    unfold Work.Spaces.w
    refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
    · fun_prop
    · fun_prop
    · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
  have h : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    hcont.aestronglyMeasurable (μ := MeasureTheory.volume) measurableSet_Ioi
  rw [show (MeasureTheory.volume.restrict Work.Spaces.Iz)
      = MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) from
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  exact h

theorem fkMomentJetSq : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    ∀ (b : ℕ), b ≤ 6 →
      MeasureTheory.IntegrableOn
          (fun z => (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α 6 f := by
  refine ⟨16, by norm_num, ?_⟩
  intro α hαmem f hsm hm6 b hb
  -- the a.e. identification `D_z^b (FK f) = FK (D_z^b f)`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z
        = Work.Construction.FK (Work.Spaces.DzIter b f) z := by
    have h := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae hsm hm6 b hb
    filter_upwards [h] with z hz
    rw [← Work.Elliptic.DzIter_rad (fun w => Work.Construction.FK f w) b z 0]
    exact hz 0
  -- the a.e. pointwise domination by `16 ∫_θ HkIntegrand α 6 f`
  have hdom : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
        * (Work.Spaces.w z) ^ 2
        ≤ 16 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
    have hae' : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz →
        Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z
          = Work.Construction.FK (Work.Spaces.DzIter b f) z :=
      (MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici).mp hae
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [hae', MeasureTheory.Measure.ae_ne (MeasureTheory.volume) (0:ℝ)]
      with z he hne hzI
    have he' := he hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hne)
    -- the angular Cauchy–Schwarz bound for the moment of the `b`-th derivative
    have hFK := FKdzIter_sq_le (α := α) hsm hm6 b hb hzpos
    -- the weighted angular energy is a slot of `ℋ⁶`
    have hIle : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b f z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
        (hm6.1 z hzI) ?_
      filter_upwards [ae_mem_Ioo_Iθ_k] with θ hθ
      have hsin : 0 < Real.sin (2*θ) := Real.sin_pos_of_pos_of_lt_pi
        (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      simpa only [mul_comm] using dzIter_sq_w_sq_le_HkIntegrand_k α 6 f z θ hsin b hb
    calc (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        = (Work.Construction.FK (Work.Spaces.DzIter b f) z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
          rw [he']
      _ ≤ (16 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
            * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hFK (sq_nonneg _)
      _ = 16 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b f z θ) ^ 2) := by
          rw [MeasureTheory.integral_const_mul]; ring
      _ ≤ 16 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ :=
          mul_le_mul_of_nonneg_left hIle (by norm_num)
  -- a.e. strong measurability of the integrand
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => (Work.Construction.FK (Work.Spaces.DzIter b f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (aesm_FK_DzIter_aux hsm b).pow 2 |>.mul aesm_w_sq_aux
    refine h1.congr ?_
    filter_upwards [hae] with z hz
    rw [hz]
  have hint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' (hm6.2.const_mul 16) haesm ?_
    filter_upwards [hdom] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hz
  refine ⟨hint, ?_⟩
  have hmain : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz,
          16 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      (hm6.2.const_mul 16) hdom
  refine le_trans hmain ?_
  rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
end
