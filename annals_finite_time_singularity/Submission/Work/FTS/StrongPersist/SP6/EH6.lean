import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.Honesty.cmode_decay_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.continuousOn_cmode_of_hkMem_one
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.EpsSqTools.Shift
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sigmaDivisibility
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Rhs.CoupledVf
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gLocal
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAsmA
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.EasyLeibIntBound
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.StrongPersist.StarPkg6Aux
import Submission.Work.FTS.StrongPersist.StarPkg6Fields
import Submission.Work.FTS.StrongPersist.hasDerivAt_wip_family
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.PkgJets.cosTailB
import Submission.Work.FTS_EllLimOK.PkgJets.hkMemOfJConv
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.ClassCHon.hcoef_source_general =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon

/-- **The weighted `ℓ¹`-summability of the modal coefficients of the decaying solution for a
general source** (the `hcoef` input of the level-`0` honesty capstones).

`acoeff α m F = radGreen α m (cmode m F)` is the decaying mode-`m` coefficient of
`psiSeries α F` (`Work.FTS.PhiStar.Series.Defs`).  For a source `F` which is `C^∞` on the open
quadrant, honest at levels `0` and `1`, with `z ∂_z F` honest at level `0`, and whose source
moment `Work.Elliptic.Fstar F` vanishes on `(0,∞)`, the family
`m ↦ ((m : ℝ) + 1) * |acoeff α m F z|` is summable for every `z > 0`.

This is the every-`z` (slicewise) piece of the level-`0` honesty of the modal solution: it is
exactly what `Work.FTS.ClassC.HonestCut.HkMem_zero_psiSeries_of_capstone` consumes.

Proof route (for the prover's convenience; not part of the statement).
Write `c_m := cmode m F`, `q := (2m+5)/α`, `p := 2m/α`.  The explicit Green formula gives
`a_m(z) = radGreen α m c_m z = (α(4m+5))⁻¹ (z^{-q}∫_0^z c_m t^{q-1} + z^{p}∫_z^∞ c_m t^{-p-1})`.
Split the first integral at `z/2` and the second at `2z`:
* on the compact middle `[z/2, 2z]` use `M_z,m := sup_{[z/2,2z]} |c_m|`, which by
  `Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass` and the *continuity of the
  `σ`-weighted slice mass* (`Work.FTS.ClassCHon.sliceMass_continuous`, whose extra hypothesis is
  `hDz`) is bounded by `√(K_z / eNorm m)` with `K_z := sup_{[z/2,2z]} ∫_θ (F t θ)² sin(2θ)^{-η}`
  — finite for each `z > 0` by continuity on the compact interval;
* the outer halves are bounded by Cauchy–Schwarz against `∫_t (c_m t w t)²` (using
  `(w t)^{-2} ≤ t^4`, valid for all `t > 0`), which by the integrated Bessel inequality
  (`Work.FTS.ClassC.sum_eNorm_cmode_sq_le_HkSq`) is at most `HkSq α 0 F / eNorm m`; the split
  produces the factors `2^{-q}` and `2^{-p}`, i.e. geometric decay in `m`
  (`q ≥ 2m/α ≥ 8m`, `p ≥ 8m`).
With `eNorm m ≥ m` this gives, for `m ≥ 1`, `(m+1)|a_m(z)| ≤ Λ(z)·(m^{-3/2} + 2^{-8m})`, and
every term is summable.  (`m = 0` contributes a single finite term.) -/
theorem hcoef_source_general {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF0 : Work.Spaces.HkMem α 0 F)
    (hF1 : Work.Spaces.HkMem α 1 F)
    (hDz : Work.Spaces.HkMem α 0 (Work.Spaces.Dz F))
    (hmom : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    ∀ z : ℝ, 0 < z → Summable (fun m : ℕ =>
      ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|) := by
  intro z hz
  -- the uniform-on-`[z/2,2z]` bound on the mode coefficients of the source
  obtain ⟨L, hL0, hLbd⟩ := Work.FTS.ClassCHon.Hcoef.cmode_slice_bound hsm hF0 hDz z hz
  -- the two constants of the dominating family
  set β : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 F) with hβdef
  have hβnn : 0 ≤ β := Real.sqrt_nonneg _
  have hβ0 : 0 ≤ β / α := div_nonneg hβnn hα.le
  -- comparison with the summable family `m ↦ L·m^{-3/2} + (β/α)·(1/2)^m`
  refine Summable.of_nonneg_of_le
    (g := fun m : ℕ => ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|)
    (f := fun m : ℕ => L * (m : ℝ) ^ (-(3 / 2 : ℝ)) + (β / α) * (1 / 2 : ℝ) ^ m)
    (fun m => mul_nonneg (by positivity) (abs_nonneg _)) ?_ ?_
  · intro m
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · -- `m = 0`: the coefficient vanishes by the vanishing source moment
      subst hm0
      rw [Work.FTS.PhiStar.Series.acoeff_zero_of_fstar α F hmom z hz, abs_zero]
      have h0 : (0 : ℝ) ^ (-(3 / 2 : ℝ)) = 0 := Real.zero_rpow (by norm_num)
      simp only [Nat.cast_zero, zero_add, mul_zero, pow_zero, mul_one, h0]
      exact hβ0
    · -- `m ≥ 1`: the split Green bound, then the two arithmetic reductions
      have hm : 1 ≤ m := hpos
      have hEpos : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
        Work.EllipticEst.ModalSolution.eNorm_pos m
      obtain ⟨hcint, hcbess⟩ := Work.FTS.ClassCHon.Hcoef.cmode_L2_bound (α := α) hsm hF0 m
      have hcm : MeasureTheory.AEStronglyMeasurable
          (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m F t * Work.Spaces.w t)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
        (Work.EllipticEst.ModalSolution.aesm_cmode hsm m).mul
          ((Work.FTS.ClassCHon.Hcoef.continuousOn_w_Ioi.aemeasurable
            measurableSet_Ioi).aestronglyMeasurable)
      have hBs : Real.sqrt (∫ t in Set.Ioi (0 : ℝ),
            (Work.FTS.PhiStar.Series.cmode m F t * Work.Spaces.w t) ^ 2)
          ≤ β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
        have hIle : (∫ t in Set.Ioi (0 : ℝ),
              (Work.FTS.PhiStar.Series.cmode m F t * Work.Spaces.w t) ^ 2)
            ≤ Work.Spaces.HkSq α 0 F / Work.EllipticEst.ModalSolution.eNorm m := by
          rw [le_div_iff₀ hEpos, mul_comm]
          exact hcbess
        calc Real.sqrt (∫ t in Set.Ioi (0 : ℝ),
              (Work.FTS.PhiStar.Series.cmode m F t * Work.Spaces.w t) ^ 2)
            ≤ Real.sqrt (Work.Spaces.HkSq α 0 F / Work.EllipticEst.ModalSolution.eNorm m) :=
              Real.sqrt_le_sqrt hIle
          _ = β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
              rw [hβdef, Real.sqrt_div (Work.Spaces.HkSq_nonneg α 0 F)
                (Work.EllipticEst.ModalSolution.eNorm m)]
      have hsplit := Work.FTS.ClassCHon.HcoefSplit.radGreen_split_le_gen (α := α) hα hα4 hm
        (c := fun t : ℝ => Work.FTS.PhiStar.Series.cmode m F t) (z := z)
        (L := L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
        (B := β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
        hz (div_nonneg hL0 (Real.sqrt_nonneg _)) (div_nonneg hβnn (Real.sqrt_nonneg _))
        (fun t ht => hLbd m t ht) hcint hcm hBs
      have hLterm := Work.FTS.ClassCHon.HcoefSplit.hcoef_Lterm_le (α := α) (L := L)
        hα hα4 hL0 hm
      have hBterm := Work.FTS.ClassCHon.HcoefSplit.hcoef_Bterm_le (α := α) (β := β)
        hα hα4 hβnn hm
      calc ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|
          = ((m : ℝ) + 1) * |Work.FTS.PhiStar.Radial.radGreen α m
              (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m F t) z| := rfl
        _ ≤ ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m *
              ((L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
                * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)
              + (β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
                * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
                      / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
                    + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
                      / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3)))) :=
            mul_le_mul_of_nonneg_left hsplit (by positivity)
        _ = ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m *
              ((L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
                * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)))
            + ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m *
              ((β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
                * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
                      / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
                    + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
                      / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3)))) := by ring
        _ ≤ L * (m : ℝ) ^ (-(3 / 2 : ℝ)) + (β / α) * (1 / 2 : ℝ) ^ m :=
            add_le_add hLterm hBterm
  · -- the dominating family is summable
    have hsum1 : Summable (fun m : ℕ => (m : ℝ) ^ (-(3 / 2 : ℝ))) := by
      have h0 : Summable (fun m : ℕ => ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
        Real.summable_nat_rpow_inv.mpr (by norm_num)
      convert h0 using 1
      ext m
      rw [Real.rpow_neg (Nat.cast_nonneg m)]
    have hsum2 : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ m) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    exact (hsum1.mul_left L).add (hsum2.mul_left (β / α))

end Work.FTS.ClassCHon
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.psiSeries_atTop_zero_of_cptQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology BigOperators

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-! ## Elementary arithmetic -/

/-- `rgK α m · (m+1) ≤ 1/(4α)`; this is what makes the majorant summable. -/
private lemma rgK_mul_succ_le {α : ℝ} (hα : 0 < α) (m : ℕ) :
    Work.FTS.EllExist.rgK α m * ((m : ℝ) + 1) ≤ 1 / (4 * α) := by
  have hden : 0 < α * (4 * (m : ℝ) + 5) := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    positivity
  have hden' : 0 < 4 * α := by positivity
  rw [Work.FTS.EllExist.rgK, one_div_mul_eq_div, div_le_div_iff₀ hden hden']
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- `Σ_m 1/(m+1)^4` converges. -/
private lemma summable_one_div_add_one_pow_four :
    Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 4) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) 1).mpr hbase
  simpa only [Nat.cast_add, Nat.cast_one] using hshift

/-- The arithmetic comparison behind the summability of the majorant. -/
private lemma bound_le_aux {α b K C : ℝ} (hα : 0 < α) (hK : 0 ≤ K) (hC : 0 ≤ C) (m : ℕ) :
    6 * (Work.FTS.EllExist.rgK α m * ((m : ℝ) + 1)) * ((K + C) / ((m : ℝ) + 1) ^ 4)
        * Real.sqrt b
      ≤ (3 * Real.sqrt b * (K + C) / (2 * α)) / ((m : ℝ) + 1) ^ 4 := by
  have hrk := rgK_mul_succ_le hα m
  have hden : 0 < ((m : ℝ) + 1) ^ 4 := by positivity
  have hKC : 0 ≤ K + C := by linarith
  have hb : (0 : ℝ) ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hstep : 6 * (Work.FTS.EllExist.rgK α m * ((m : ℝ) + 1)) ≤ 6 * (1 / (4 * α)) := by
    linarith
  have h1 : 6 * (Work.FTS.EllExist.rgK α m * ((m : ℝ) + 1))
        * ((K + C) / ((m : ℝ) + 1) ^ 4) * Real.sqrt b
      ≤ 6 * (1 / (4 * α)) * ((K + C) / ((m : ℝ) + 1) ^ 4) * Real.sqrt b := by
    have h2 := mul_le_mul_of_nonneg_right hstep (div_nonneg hKC hden.le)
    calc 6 * (Work.FTS.EllExist.rgK α m * ((m : ℝ) + 1))
            * ((K + C) / ((m : ℝ) + 1) ^ 4) * Real.sqrt b
        = (6 * (Work.FTS.EllExist.rgK α m * ((m : ℝ) + 1))
            * ((K + C) / ((m : ℝ) + 1) ^ 4)) * Real.sqrt b := by ring
      _ ≤ (6 * (1 / (4 * α)) * ((K + C) / ((m : ℝ) + 1) ^ 4)) * Real.sqrt b :=
          mul_le_mul_of_nonneg_right h2 hb
      _ = 6 * (1 / (4 * α)) * ((K + C) / ((m : ℝ) + 1) ^ 4) * Real.sqrt b := by ring
  refine le_trans h1 (le_of_eq ?_)
  have hαne : α ≠ 0 := hα.ne'
  have hdne : ((m : ℝ) + 1) ^ 4 ≠ 0 := hden.ne'
  field_simp
  ring

/-! ## The decay of the mode series -/

theorem psiSeries_atTop_zero_of_cptQ {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G) :
    ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z => Work.FTS.PhiStar.Series.psiSeries α G z θ)
        Filter.atTop (nhds 0) := by
  intro θ hθ
  -- ## the support box, the `m = 0` bound, the rapid decay
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, Hbox⟩ := hG.cpt.exists_box
  have hb0 : 0 ≤ b := le_of_lt (lt_trans ha hab)
  obtain ⟨K0, hK00, hK0b⟩ := Work.FTS.PhiStar.Honesty.CmodeZero.cmode_zero_abs_le_of_cptQ hG
  obtain ⟨C, hC0, hCb⟩ := Work.FTS.PhiStar.Honesty.cmode_decay_of_cptQ hG 0 4
  have hα1 : α ≤ 1 := by linarith
  -- ## the mode coefficients vanish when the slice does
  have hcmzero : ∀ (m : ℕ) (z : ℝ), z ∉ Set.Icc a b →
      Work.FTS.PhiStar.Series.cmode m G z = 0 := by
    intro m z hz
    have hslice : ∀ θ' : ℝ, G z θ' = 0 := by
      intro θ'
      by_contra hne
      exact hz (Hbox z θ' hne).1
    have hnum : (∫ θ' in (0 : ℝ)..(Real.pi / 2),
        G z θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ' * Real.cos θ') = 0 := by
      have h1 : (∫ θ' in (0 : ℝ)..(Real.pi / 2),
            G z θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ' * Real.cos θ')
          = ∫ θ' in (0 : ℝ)..(Real.pi / 2), (0 : ℝ) :=
        intervalIntegral.integral_congr (fun x _ => by rw [hslice x, zero_mul, zero_mul])
      rw [h1, intervalIntegral.integral_zero]
    rw [Work.FTS.PhiStar.Series.cmode, hnum, zero_div]
  -- ## a single sup bound for every mode
  set Msup : ℕ → ℝ := fun m => (K0 + C) / ((m : ℝ) + 1) ^ 4 with hMsupdef
  have hMsup0 : ∀ m, 0 ≤ Msup m := by
    intro m
    rw [hMsupdef]
    positivity
  have hcmb : ∀ m t, |Work.FTS.PhiStar.Series.cmode m G t| ≤ Msup m := by
    intro m t
    rw [hMsupdef]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have h1 : K0 ≤ K0 + C := by linarith
      simpa using le_trans (hK0b t) h1
    · have h := hCb m hm t
      rw [Work.Spaces.DzIter_zero] at h
      have h2 : C / ((m : ℝ) + 1) ^ 4 ≤ (K0 + C) / ((m : ℝ) + 1) ^ 4 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      exact le_trans h h2
  -- ## the `L²` mass of the source of the radial equation
  have hmass : ∀ m : ℕ,
      MeasureTheory.IntegrableOn
          (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m G t ^ 2) (Set.Ioi 0) ∧
        (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m G t) ^ 2) ≤ (Msup m) ^ 2 * b := by
    intro m
    refine Work.FTS.PhiStar.Honesty.CmodeMass.cmode_sq_mass_le
      (c := fun t => Work.FTS.PhiStar.Series.cmode m G t) hb0 (hMsup0 m)
      (Work.EllipticEst.ModalSolution.aesm_cmode hG.smoothOpen m) ?_ (fun t => hcmb m t)
    intro t ht
    exact hcmzero m t (fun hmem => absurd hmem.2 (not_le.mpr ht))
  -- ## the `L²` mass and its square root
  set B : ℕ → ℝ := fun m => Real.sqrt (∫ t in Set.Ioi 0, Work.FTS.PhiStar.Series.cmode m G t ^ 2)
    with hBdef
  have hBle : ∀ m, B m ≤ Msup m * Real.sqrt b := by
    intro m
    have h := (hmass m).2
    have h2 : Real.sqrt (∫ t in Set.Ioi 0, Work.FTS.PhiStar.Series.cmode m G t ^ 2)
        ≤ Real.sqrt ((Msup m) ^ 2 * b) := Real.sqrt_le_sqrt h
    rw [Real.sqrt_mul (sq_nonneg (Msup m)), Real.sqrt_sq (hMsup0 m)] at h2
    simpa only [hBdef] using h2
  -- ## the per-mode bound (with the uniform constant `2`)
  have hac : ∀ m z, 0 < z →
      |Work.FTS.PhiStar.Series.acoeff α m G z| ≤
        2 * Work.FTS.EllExist.rgK α m * B m * z ^ (-(1 / 2) : ℝ) := by
    intro m z hz
    have h := Work.FTS.PhiStar.Honesty.RadGreenAll.radGreen_abs_le_all
      (hα := hα) (hα1 := hα1) m (hmass m).1 hz
    rw [Work.FTS.PhiStar.Series.acoeff]
    simpa only [hBdef] using h
  -- ## each summand tends to `0`
  have hlim : ∀ m : ℕ, Filter.Tendsto
      (fun z : ℝ => Work.FTS.PhiStar.Series.acoeff α m G z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) Filter.atTop (nhds 0) := by
    intro m
    have hz : Filter.Tendsto (fun z : ℝ => z ^ (-(1 / 2) : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have hC' : Filter.Tendsto (fun z : ℝ =>
        (2 * Work.FTS.EllExist.rgK α m * B m
          * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|) * z ^ (-(1 / 2) : ℝ))
        Filter.atTop (nhds 0) := by
      have h0 := hz.const_mul
        (2 * Work.FTS.EllExist.rgK α m * B m * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|)
      simpa using h0
    refine squeeze_zero_norm' ?_ hC'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz0
    rw [Real.norm_eq_abs, abs_mul]
    calc |Work.FTS.PhiStar.Series.acoeff α m G z|
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ (2 * Work.FTS.EllExist.rgK α m * B m * z ^ (-(1 / 2) : ℝ))
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| :=
          mul_le_mul_of_nonneg_right (hac m z hz0) (abs_nonneg _)
      _ = (2 * Work.FTS.EllExist.rgK α m * B m
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|) * z ^ (-(1 / 2) : ℝ) := by ring
  -- ## the summable majorant
  set bound : ℕ → ℝ := fun m =>
    6 * (Work.FTS.EllExist.rgK α m * ((m : ℝ) + 1)) * Msup m * Real.sqrt b with hbounddef
  have hbound0 : ∀ m, 0 ≤ bound m := by
    intro m
    rw [hbounddef]
    have hrk : 0 < Work.FTS.EllExist.rgK α m := Work.FTS.EllExist.rgK_pos hα m
    positivity
  have hbound_le : ∀ m : ℕ,
      bound m ≤ (3 * Real.sqrt b * (K0 + C) / (2 * α)) / ((m : ℝ) + 1) ^ 4 := by
    intro m
    rw [hbounddef]
    exact bound_le_aux (b := b) (K := K0) (C := C) hα hK00 hC0 m
  have hsum : Summable bound := by
    have hbase : Summable (fun m : ℕ => (3 * Real.sqrt b * (K0 + C) / (2 * α))
        / ((m : ℝ) + 1) ^ 4) := by
      have h0 : Summable (fun m : ℕ => (3 * Real.sqrt b * (K0 + C) / (2 * α))
          * ((1 : ℝ) / ((m : ℝ) + 1) ^ 4)) :=
        summable_one_div_add_one_pow_four.mul_left _
      exact h0.congr (fun m => (div_eq_mul_one_div _ _).symm)
    exact Summable.of_nonneg_of_le hbound0 hbound_le hbase
  -- ## the domination
  have hdom : ∀ᶠ z in Filter.atTop, ∀ m : ℕ,
      ‖Work.FTS.PhiStar.Series.acoeff α m G z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ ≤ bound m := by
    refine eventually_atTop.mpr ⟨1, fun z hz1 => ?_⟩
    intro m
    have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
    have hzp : z ^ (-(1 / 2) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hz1 (by norm_num)
    have hE : |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ 3 * ((m : ℝ) + 1) :=
      le_trans (Work.FTS.PhiStar.Series.abs_eFam_le_sqrt_Npsi m hθ)
        (Work.FTS.PhiStar.Series.sqrt_Npsi_le_three m)
    have hAc : 0 ≤ 2 * Work.FTS.EllExist.rgK α m * B m * z ^ (-(1 / 2) : ℝ) := by
      have hrk : 0 < Work.FTS.EllExist.rgK α m := Work.FTS.EllExist.rgK_pos hα m
      positivity
    have hmid : 2 * Work.FTS.EllExist.rgK α m * B m * z ^ (-(1 / 2) : ℝ)
        ≤ 2 * Work.FTS.EllExist.rgK α m * Msup m * Real.sqrt b := by
      have h1 : B m * z ^ (-(1 / 2) : ℝ) ≤ Msup m * Real.sqrt b :=
        calc B m * z ^ (-(1 / 2) : ℝ) ≤ (Msup m * Real.sqrt b) * z ^ (-(1 / 2) : ℝ) :=
              mul_le_mul_of_nonneg_right (hBle m) (Real.rpow_nonneg hz0.le _)
          _ ≤ (Msup m * Real.sqrt b) * 1 :=
              mul_le_mul_of_nonneg_left hzp (mul_nonneg (hMsup0 m) (Real.sqrt_nonneg b))
          _ = Msup m * Real.sqrt b := mul_one _
      have hrk2 : 0 ≤ 2 * Work.FTS.EllExist.rgK α m := by
        have hrk : 0 < Work.FTS.EllExist.rgK α m := Work.FTS.EllExist.rgK_pos hα m
        linarith
      calc 2 * Work.FTS.EllExist.rgK α m * B m * z ^ (-(1 / 2) : ℝ)
          = 2 * Work.FTS.EllExist.rgK α m * (B m * z ^ (-(1 / 2) : ℝ)) := by ring
        _ ≤ 2 * Work.FTS.EllExist.rgK α m * (Msup m * Real.sqrt b) :=
            mul_le_mul_of_nonneg_left h1 hrk2
        _ = 2 * Work.FTS.EllExist.rgK α m * Msup m * Real.sqrt b := by ring
    rw [Real.norm_eq_abs, abs_mul]
    calc |Work.FTS.PhiStar.Series.acoeff α m G z|
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ (2 * Work.FTS.EllExist.rgK α m * B m * z ^ (-(1 / 2) : ℝ))
            * (3 * ((m : ℝ) + 1)) := mul_le_mul (hac m z hz0) hE (abs_nonneg _) hAc
      _ ≤ (2 * Work.FTS.EllExist.rgK α m * Msup m * Real.sqrt b)
            * (3 * ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hmid (by positivity)
      _ = bound m := by rw [hbounddef]; ring
  -- ## Tannery
  have hmain := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
    (f := fun z m => Work.FTS.PhiStar.Series.acoeff α m G z
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
    (g := fun _ : ℕ => (0 : ℝ)) (bound := bound) hsum hlim hdom
  simpa only [tsum_zero, Work.FTS.PhiStar.Series.psiSeries] using hmain

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_integrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter
open scoped Topology

/-- **`c² ∈ L¹(1,∞)` ⟹ `|c| t^{-2m/α-1} ∈ L¹(1,∞)`.**

This is the hypothesis `hinf` of `Work.FTS.EllExist.Honesty.radGreen_l2_near_zero` (and of the
`radGreen` differentiability lemmas), derived here from the far-field `L²`-hypothesis by AM–GM. -/
private theorem hinf_of_hfar {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hα : 0 < α) (hm : 1 ≤ m)
    (hc : ContinuousOn c (Set.Ioi 0))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1) := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp : (-1 / 2 : ℝ) < 2 * (m : ℝ) / α := by
    have h2 : (0 : ℝ) < 2 * (m : ℝ) / α := div_pos (by linarith) hα
    linarith
  exact integrableOn_abs_mul_rpow_of_sq hp
    (hc.mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))) hfar

/-- **The near half**: `∫_0^1 radGreen² w² < ∞`.

On `(0,1)` we have `w z² = (1+z)⁴/z⁴ ≤ 16/z⁴`, so it suffices to know
`∫_0^1 radGreen²/z⁴ < ∞` — the near-zero honesty
`Work.FTS.EllExist.Honesty.radGreen_l2_near_zero` — whose far-field side condition follows from
`hfar` (`hinf_of_hfar`). -/
private theorem radGreen_sq_w_sq_integrableOn_Ioo {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioo 0 1) := by
  have hinf := hinf_of_hfar hα hm hc hfar
  have hz4 := Work.FTS.EllExist.Honesty.radGreen_l2_near_zero α hα hα4 m hm hc hnear hinf
  have hw : ∀ z : ℝ, (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
    intro z
    rw [Work.Spaces.w, div_pow]
    rw [show ((1 + z) ^ 2) ^ 2 = (1 + z) ^ 4 by ring, show (z ^ 2) ^ 2 = z ^ 4 by ring]
  have hbdd : ∀ᵐ z ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      ‖(fun z : ℝ => (1 + z) ^ 4) z‖ ≤ 16 := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine ae_of_all _ fun z hz => ?_
    have h1 : (0 : ℝ) ≤ 1 + z := by linarith [hz.1]
    have h2 : 1 + z ≤ 2 := by linarith [hz.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (1 + z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h1 h2 4
      _ = 16 := by norm_num
  have hmeas : AEStronglyMeasurable (fun z : ℝ => (1 + z) ^ 4)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    ((continuous_const.add continuous_id).pow 4).continuousOn.aestronglyMeasurable
      measurableSet_Ioo
  have h := Integrable.bdd_mul hz4 hmeas hbdd
  refine IntegrableOn.congr_fun h ?_ measurableSet_Ioo
  intro z _
  show (1 + z) ^ 4 * (Work.FTS.PhiStar.Radial.radGreen α m c z ^ 2 / z ^ 4)
      = Work.FTS.PhiStar.Radial.radGreen α m c z ^ 2 * (Work.Spaces.w z) ^ 2
  rw [hw z]
  ring

/-- **The assembly**: if the two far-field halves `∫_1^∞ G_i² w² < ∞` are known, then
`∫_0^∞ radGreen² w² < ∞`.

The far-field integrand is split with `(G1+G2)² ≤ 2G1² + 2G2²` and `radGreen = K(G1+G2)`; the
continuity of `G1` and `G2` on `(1,∞)` (measurability of the target integrand) comes from the
differentiability lemmas `G1_hasDerivAt_of_intervalIntegrable` / `G2_hasDerivAt` of
`Work.FTS.EllExist.Honesty`, and the two halves are glued by `IntegrableOn.union`. -/
private theorem radGreen_sq_w_sq_integrableOn_of_far {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1))
    (hG1 : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.EllExist.Honesty.G1 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 1))
    (hG2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0) := by
  have hnear' := radGreen_sq_w_sq_integrableOn_Ioo hα hα4 hm hc hnear hfar
  -- measurability of the far-field integrand: `radGreen` is a constant times `G1 + G2`
  have haesmG1 : AEStronglyMeasurable (fun z : ℝ => Work.FTS.EllExist.Honesty.G1 α m c z)
      (volume.restrict (Set.Ioi 1)) :=
    Work.FTS.EllExist.Honesty.G1_far_measurable α hα m hc
  have hinf := hinf_of_hfar hα hm hc hfar
  have hG2deriv := Work.FTS.EllExist.Honesty.G2_hasDerivAt hα hα4 m hm hc hinf
  have haesmG2 : AEStronglyMeasurable (fun z : ℝ => Work.FTS.EllExist.Honesty.G2 α m c z)
      (volume.restrict (Set.Ioi 1)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro z hz
    exact ((hG2deriv z hz).continuousAt).continuousWithinAt
  have haesmSum : AEStronglyMeasurable
      (fun z : ℝ => 1 / (α * (4 * (m : ℝ) + 5))
        * (Work.FTS.EllExist.Honesty.G1 α m c z + Work.FTS.EllExist.Honesty.G2 α m c z))
      (volume.restrict (Set.Ioi 1)) :=
    (haesmG1.add haesmG2).const_mul _
  have hfun : (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z)
      = fun z : ℝ => 1 / (α * (4 * (m : ℝ) + 5))
        * (Work.FTS.EllExist.Honesty.G1 α m c z + Work.FTS.EllExist.Honesty.G2 α m c z) := by
    funext z
    exact Work.FTS.EllExist.Honesty.radGreen_eq_G1_add_G2 α m c z
  have haesmRad : AEStronglyMeasurable (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z)
      (volume.restrict (Set.Ioi 1)) := by
    rw [hfun]
    exact haesmSum
  have haesmW : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (volume.restrict (Set.Ioi 1)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (ContinuousOn.div ?_ ?_ ?_).pow 2
    · exact ((continuous_const.add continuous_id).pow 2).continuousOn
    · exact (continuous_id.pow 2).continuousOn
    · intro z hz
      exact pow_ne_zero 2 (ne_of_gt (lt_trans one_pos (Set.mem_Ioi.mp hz)))
  have haesm : AEStronglyMeasurable
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (volume.restrict (Set.Ioi 1)) := (haesmRad.pow 2).mul haesmW
  -- the dominating integrable function on `(1,∞)`
  have hsum : Integrable
      (fun z : ℝ => 2 * (1 / (α * (4 * (m : ℝ) + 5))) ^ 2
        * ((Work.FTS.EllExist.Honesty.G1 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2
          + (Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2))
      (volume.restrict (Set.Ioi 1)) :=
    (hG1.add hG2).const_mul _
  have hfarint : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 1) := by
    refine Integrable.mono' hsum haesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hK2 : 0 ≤ (1 / (α * (4 * (m : ℝ) + 5))) ^ 2 := sq_nonneg _
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hsq : (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2
        = (1 / (α * (4 * (m : ℝ) + 5))) ^ 2
          * (Work.FTS.EllExist.Honesty.G1 α m c z
              + Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2 := by
      rw [Work.FTS.EllExist.Honesty.radGreen_eq_G1_add_G2 α m c z]
      ring
    have hab : (Work.FTS.EllExist.Honesty.G1 α m c z
        + Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2
        ≤ 2 * (Work.FTS.EllExist.Honesty.G1 α m c z) ^ 2
          + 2 * (Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2 := by
      nlinarith [sq_nonneg (Work.FTS.EllExist.Honesty.G1 α m c z
        - Work.FTS.EllExist.Honesty.G2 α m c z)]
    have hfnn : 0 ≤ (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg (sq_nonneg _) hw2
    rw [Real.norm_of_nonneg hfnn]
    calc (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (1 / (α * (4 * (m : ℝ) + 5))) ^ 2
            * ((Work.FTS.EllExist.Honesty.G1 α m c z
                + Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
          rw [hsq]; ring
      _ ≤ (1 / (α * (4 * (m : ℝ) + 5))) ^ 2
            * ((2 * (Work.FTS.EllExist.Honesty.G1 α m c z) ^ 2
                + 2 * (Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2)
              * (Work.Spaces.w z) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hab hw2) hK2
      _ = 2 * (1 / (α * (4 * (m : ℝ) + 5))) ^ 2
            * ((Work.FTS.EllExist.Honesty.G1 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2
              + (Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
          ring
  -- glue `(0,1)` and `(1,∞)`
  have hA : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    hnear'.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc).symm
  have hB : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ici (1 : ℝ)) :=
    hfarint.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici).symm
  have hU := hA.union hB
  have hset : Set.Icc (0 : ℝ) 1 ∪ Set.Ici (1 : ℝ) = Set.Ici 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro (⟨h1, _⟩ | h3) <;> linarith
    · intro h
      rcases le_or_gt x 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'.le
  rw [hset] at hU
  exact hU.mono_set Set.Ioi_subset_Ici_self

theorem radGreen_sq_w_sq_integrableOn {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0) :=
  radGreen_sq_w_sq_integrableOn_of_far hα hα4 hm hc hnear hfar
    (G1_sq_w_sq_integrableOn_far hα hα4 hm hc hnear hfar)
    (G2_sq_w_sq_integrableOn_far hα hα4 hm hc hfar)

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E2_norm_O =====
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

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- `√(X+Y) ≤ √X + √Y` for nonnegative `X`, `Y`. -/
private theorem sqrt_add_le_sqrt_add_sqrt {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Real.sqrt (X + Y) ≤ Real.sqrt X + Real.sqrt Y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX
  have h2 : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY
  have hexp : (Real.sqrt X + Real.sqrt Y) ^ 2
      = X + 2 * (Real.sqrt X * Real.sqrt Y) + Y := by
    rw [add_sq, h1, h2]; ring
  nlinarith [hexp, mul_nonneg (Real.sqrt_nonneg X) (Real.sqrt_nonneg Y)]

/-- The uniform `α`- and `n`-independent bound for the projector zero mode
`L₁₂(Transport f)(0)`, in the open class. -/
private theorem C0_bound_O :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 5 f →
      Work.Construction.L12 f 0 = 0 →
      (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
        ≤ K * Work.Spaces.HkSq α n (Work.Spaces.Dth f) := by
  refine ⟨16, by norm_num, ?_⟩
  intro α hα hα1 n hn f hO hmem5 hl12
  have hmemdn : Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := n) (by linarith : -(1 / 10 : ℝ) ≤ α) hO
      (Work.FTS.OpenPkg.HkMem_mono_open hO (n + 1) (by omega) hmem5)
  have hmemd0 : Work.Spaces.HkMem α 0 (Work.Spaces.Dth f) :=
    Work.FTS.OpenPkg.HkMem_mono_open hO.Dth 0 (by omega) hmemdn
  have h := E2O.C0_sq_le_HkSq0_O (α := α) hO hmemd0
  have hmono : Work.Spaces.HkSq α 0 (Work.Spaces.Dth f)
      ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.zero_le n) hmemdn
  have h16 : (16 : ℝ) * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f)
      ≤ 16 * Work.Spaces.HkSq α n (Work.Spaces.Dth f) :=
    mul_le_mul_of_nonneg_left hmono (by norm_num)
  have h' : (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
      ≤ 16 * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := h
  linarith

theorem E2_norm_O :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f →
        Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
          ≤ κ * (Work.Spaces.HkNorm α n f
              + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := by
  -- ## the constants
  obtain ⟨Cr, hCrpos, hradS⟩ := E2O.radS_slotSum_le_O C0_bound_O
  obtain ⟨Cg, hCgnn, hgamred⟩ := Work.FTS.CoercivityFix.Transfer.E2norm.gam_rad_integral_le
  obtain ⟨C0c, hC0pos, hE0⟩ := E2hat_HkSq_le_uniform_O 0
  obtain ⟨C1c, hC1pos, hE1⟩ := E2hat_HkSq_le_uniform_O 1
  obtain ⟨C2c, hC2pos, hE2⟩ := E2hat_HkSq_le_uniform_O 2
  obtain ⟨C3c, hC3pos, hE3⟩ := E2hat_HkSq_le_uniform_O 3
  let Cmax : ℝ := max (max C0c C1c) (max C2c C3c)
  have hCmaxdef : Cmax = max (max C0c C1c) (max C2c C3c) := rfl
  have hCmaxnn : 0 ≤ Cmax := by
    rw [hCmaxdef]
    have h : C0c ≤ max (max C0c C1c) (max C2c C3c) :=
      le_trans (le_max_left C0c C1c) (le_max_left _ _)
    linarith [hC0pos]
  refine ⟨Real.sqrt (2 * Cmax + 2 * (Cg * Cr)), Real.sqrt_nonneg _, ?_⟩
  intro α hα hα1 n hn f hf
  -- ## the data of the class
  have hO : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  have hmem5 : Work.Spaces.HkMem α 5 f := hf.1.2.1
  have hl12 : Work.Construction.L12 f 0 = 0 := hf.2.2.2
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 4 (by norm_num) hmem5
  have hmemn : Work.Spaces.HkMem α n f :=
    Work.FTS.OpenPkg.HkMem_mono_open hO n (by omega) hmem5
  have hmemdn : Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := n) (by linarith : -(1 / 10 : ℝ) ≤ α) hO
      (Work.FTS.OpenPkg.HkMem_mono_open hO (n + 1) (by omega) hmem5)
  -- ## the `E₂`-defect is the sum of its two blocks
  have hE2eq : Work.FTS.CoercivityFix.Transfer.E2 α f
      = Work.FTS.CoercivityFix.E2hat f
        + (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) := rfl
  -- ## the radial slot bound and the `Γ·radS` package
  have hslot := hradS α hα hα1 n hn f hO hmem5 hl12
  have hA : ContDiffOn ℝ 4 (Work.Coercivity.L12f f) (Set.Ioi 0) :=
    E2O.contDiffOn_four_L12f α hα hα1 hO hmem5
  have hgam := E2O.gam_rad_package_O α hα hα1 hn hA hslot.1
  have hmemGR : Work.Spaces.HkMem α n
      (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) := hgam.2
  have hcdGR : ContDiffOn ℝ n (Function.uncurry (fun z θ => Work.Spaces.Gam α θ
      * Work.FTS.CoercivityFix.Transfer.radS α f z)) Work.FTS.CoercivityFix.Transfer.E2pkg.Qd :=
    hgam.1
  have hE2hat := E2O.E2hat_mem_contDiff_O α hα (by omega : n ≤ 4) hO hmemn hmemdn
  have hmemE2hat : Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.E2hat f) := hE2hat.1
  have hcdE2hat : ContDiffOn ℝ n (Function.uncurry (Work.FTS.CoercivityFix.E2hat f))
      Work.FTS.CoercivityFix.Transfer.E2pkg.Qd := hE2hat.2
  -- ## the split of the `ℋⁿ`-energy
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.Transfer.E2 α f) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ
          + 2 * Work.Spaces.HkIntegrand α n
              (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) z θ := by
    intro z hz θ hθ
    have h := Work.FTS.CoercivityFix.Transfer.E2pkg.hkIntegrand_add_le_of_contDiffOn α n
      hcdE2hat hcdGR z hz θ hθ
    rwa [hE2eq]
  have hsplit : Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
      ≤ 2 * Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
        + 2 * Work.Spaces.HkSq α n
            (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) := by
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
    have hinner : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.Transfer.E2 α f) z θ)
          ≤ 2 * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ)
            + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n
                (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
                z θ) := by
      intro z hz
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α n (Work.FTS.CoercivityFix.Transfer.E2 α f) z θ)
        (((hmemE2hat.1 z hz).const_mul 2).add ((hmemGR.1 z hz).const_mul 2))
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => hpt z hz θ hθ))
      have hEq : (∫ a in Work.Spaces.Iθ,
            ((fun x => 2 * Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z x)
              + fun x => 2 * Work.Spaces.HkIntegrand α n
                  (fun z θ => Work.Spaces.Gam α θ
                    * Work.FTS.CoercivityFix.Transfer.radS α f z) z x) a)
          = 2 * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ)
            + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n
                (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
                z θ) := by
        simp only [Pi.add_apply]
        rw [MeasureTheory.integral_add ((hmemE2hat.1 z hz).const_mul 2)
            ((hmemGR.1 z hz).const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      exact le_trans hmono (le_of_eq hEq)
    have hmain := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α n (Work.FTS.CoercivityFix.Transfer.E2 α f) z θ)
      (((hmemE2hat.2).const_mul 2).add ((hmemGR.2).const_mul 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hinner)
    simp only [Pi.add_apply] at hmain
    rw [MeasureTheory.integral_add ((hmemE2hat.2).const_mul 2) ((hmemGR.2).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmain
    exact hmain
  -- ## the two blocks
  have hE2hatLe : Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
      ≤ Cmax * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have hZnn : 0 ≤ Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f) := by
      have h1 := Work.Spaces.HkSq_nonneg α n f
      have h2 := Work.Spaces.HkSq_nonneg α n (Work.Spaces.Dth f)
      linarith
    have hreg : Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f :=
      regQo_mono (by omega) hf.1
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with hn0 | hn1 | hn2 | hn3
    · subst hn0
      refine le_trans (hE0 α hα f hreg) ?_
      rw [hCmaxdef]
      exact mul_le_mul_of_nonneg_right (le_trans (le_max_left C0c C1c) (le_max_left _ _)) hZnn
    · subst hn1
      refine le_trans (hE1 α hα f hreg) ?_
      rw [hCmaxdef]
      exact mul_le_mul_of_nonneg_right (le_trans (le_max_right C0c C1c) (le_max_left _ _)) hZnn
    · subst hn2
      refine le_trans (hE2 α hα f hreg) ?_
      rw [hCmaxdef]
      exact mul_le_mul_of_nonneg_right (le_trans (le_max_left C2c C3c) (le_max_right _ _)) hZnn
    · subst hn3
      refine le_trans (hE3 α hα f hreg) ?_
      rw [hCmaxdef]
      exact mul_le_mul_of_nonneg_right (le_trans (le_max_right C2c C3c) (le_max_right _ _)) hZnn
  have hgamLe : Work.Spaces.HkSq α n
        (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
      ≤ (Cg * Cr) * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have h1 : Work.Spaces.HkSq α n
          (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
        ≤ Cg * (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := by
      rw [Work.Spaces.HkSq]
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
          Work.Spaces.HkIntegrand_nonneg α n
            (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) z θ)
        (hslot.1.const_mul Cg)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz =>
          hgamred α hα hα1 n hn (Work.FTS.CoercivityFix.Transfer.radS α f) z hz))
      rw [MeasureTheory.integral_const_mul] at hmono
      exact hmono
    have h2 : Cg * (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ Cg * (Cr * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
      mul_le_mul_of_nonneg_left hslot.2 hCgnn
    calc Work.Spaces.HkSq α n
          (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
        ≤ Cg * (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := h1
      _ ≤ Cg * (Cr * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) := h2
      _ = (Cg * Cr) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
  -- ## assembly and the square root
  have htotal : Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
      ≤ (2 * Cmax + 2 * (Cg * Cr))
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have h1 : 2 * Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ 2 * (Cmax * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
      mul_le_mul_of_nonneg_left hE2hatLe (by norm_num)
    have h2 : 2 * Work.Spaces.HkSq α n
          (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
        ≤ 2 * ((Cg * Cr) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
      mul_le_mul_of_nonneg_left hgamLe (by norm_num)
    calc Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
        ≤ 2 * Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
          + 2 * Work.Spaces.HkSq α n
              (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) := hsplit
      _ ≤ 2 * (Cmax * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)))
          + 2 * ((Cg * Cr) * (Work.Spaces.HkSq α n f
              + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) := by linarith
      _ = (2 * Cmax + 2 * (Cg * Cr))
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
  have hKnn : 0 ≤ 2 * Cmax + 2 * (Cg * Cr) := by
    have : 0 ≤ 2 * (Cg * Cr) := by
      have := mul_nonneg hCgnn hCrpos.le
      linarith
    linarith
  rw [Work.Spaces.HkNorm]
  calc Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f))
      ≤ Real.sqrt ((2 * Cmax + 2 * (Cg * Cr))
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
        Real.sqrt_le_sqrt htotal
    _ = Real.sqrt (2 * Cmax + 2 * (Cg * Cr))
        * Real.sqrt (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) :=
        Real.sqrt_mul hKnn _
    _ ≤ Real.sqrt (2 * Cmax + 2 * (Cg * Cr))
        * (Real.sqrt (Work.Spaces.HkSq α n f)
            + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
        mul_le_mul_of_nonneg_left
          (sqrt_add_le_sqrt_add_sqrt (Work.Spaces.HkSq_nonneg α n f)
            (Work.Spaces.HkSq_nonneg α n (Work.Spaces.Dth f)))
          (Real.sqrt_nonneg _)
    _ = Real.sqrt (2 * Cmax + 2 * (Cg * Cr))
        * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := by
        rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.HkMem_E2_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `HkMem_E2_O` — the `D_z`-defect `E₂ α f` is honest in `ℋⁿ` (`n ≤ 3`) on the open class

`E₂ α f = Ê₂ f + Γ(θ)·radS α f z` splits into a part that is controlled by the *closed*-class
argument of `Transfer/E2_pkg.lean` (namely `Ê₂`) and a separated part `Γ(θ)·radS α f z`, whose
`ℋⁿ`-membership for `n ≤ 3` is the open-class package `E2O.gam_rad_package_O` fed by

* `E2O.contDiffOn_four_L12f` — `L₁₂ f ∈ C⁴` on `(0,∞)`;
* `E2O.radS_slotSum_le_O` — integrability of the radial slot sum `∑_{j≤n}(D_z^j radS)²w²`, whose
  only external input is the projector zero-mode bound `(C₀ f)² ≤ 16 |D_θ f|²_{ℋ⁰}`
  (`E2O.C0_sq_le_HkSq0_O`, the Cauchy–Schwarz estimate of `Transfer/E2norm`).

Assembling with the finite-order additivity `E2pkg.hkMem_add_of_contDiffOn` gives the claim.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 1000000

/-- The uniform, `α`- and `n`-independent bound for the projector zero mode
`L₁₂(Transport f)(0)` in the open class (a local copy of the private `E2_norm_O.C0_bound_O`):
`(L₁₂(Transport f)(0))² ≤ 16 |D_θ f|²_{ℋⁿ}`. -/
private theorem C0_bound_O_local :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 5 f →
      Work.Construction.L12 f 0 = 0 →
      (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
        ≤ K * Work.Spaces.HkSq α n (Work.Spaces.Dth f) := by
  refine ⟨16, by norm_num, ?_⟩
  intro α hα hα1 n hn f hO hmem5 hl12
  have hmemdn : Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := n) (by linarith : -(1 / 10 : ℝ) ≤ α) hO
      (Work.FTS.OpenPkg.HkMem_mono_open hO (n + 1) (by omega) hmem5)
  have hmemd0 : Work.Spaces.HkMem α 0 (Work.Spaces.Dth f) :=
    Work.FTS.OpenPkg.HkMem_mono_open hO.Dth 0 (by omega) hmemdn
  have h := Work.FTS.StrongEps.EpsE4Thr.E2O.C0_sq_le_HkSq0_O (α := α) hO hmemd0
  have hmono : Work.Spaces.HkSq α 0 (Work.Spaces.Dth f)
      ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.zero_le n) hmemdn
  have h16 : (16 : ℝ) * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f)
      ≤ 16 * Work.Spaces.HkSq α n (Work.Spaces.Dth f) :=
    mul_le_mul_of_nonneg_left hmono (by norm_num)
  have h' : (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
      ≤ 16 * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := h
  linarith

/-- **The radial slot sum of `radS α f` is integrable on `Iz`**, for `CoerAdmO`-type data and
`n ≤ 3`. -/
private theorem radS_slot_integrable_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn} (n : ℕ)
    (hn : n ≤ 3) (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem5 : Work.Spaces.HkMem α 5 f)
    (hl12 : Work.Construction.L12 f 0 = 0) :
    MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
  obtain ⟨_C, _hCpos, hradS⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.E2O.radS_slotSum_le_O C0_bound_O_local
  exact (hradS α hα hα1 n hn f hO hmem5 hl12).1

theorem HkMem_E2_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f) (n : ℕ) (hn : n ≤ 3) :
    Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.Transfer.E2 α f) := by
  have hO : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  have hmem5 : Work.Spaces.HkMem α 5 f := hf.1.2.1
  have hl12 : Work.Construction.L12 f 0 = 0 := hf.2.2.2
  have hmemn : Work.Spaces.HkMem α n f :=
    Work.FTS.OpenPkg.HkMem_mono_open hO n (by omega) hmem5
  have hmemdn : Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := n) (by linarith : -(1 / 10 : ℝ) ≤ α) hO
      (Work.FTS.OpenPkg.HkMem_mono_open hO (n + 1) (by omega) hmem5)
  -- the `C^∞`-on-the-open-quadrant data of the two blocks
  have hslot : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    radS_slot_integrable_O α hα hα1 n hn hO hmem5 hl12
  have hA : ContDiffOn ℝ 4 (Work.Coercivity.L12f f) (Set.Ioi 0) :=
    Work.FTS.StrongEps.EpsE4Thr.E2O.contDiffOn_four_L12f α hα hα1 hO hmem5
  have hgam := Work.FTS.StrongEps.EpsE4Thr.E2O.gam_rad_package_O α hα hα1 hn hA hslot
  have hE2hat := Work.FTS.StrongEps.EpsE4Thr.E2O.E2hat_mem_contDiff_O α hα (by omega : n ≤ 4)
    hO hmemn hmemdn
  -- the split `E₂ α f = Ê₂ f + Γ·radS α f` and the finite-order additivity
  have hsplit : Work.FTS.CoercivityFix.Transfer.E2 α f
      = Work.FTS.CoercivityFix.E2hat f
        + (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) := by
    funext z θ
    rfl
  rw [hsplit]
  exact Work.FTS.CoercivityFix.Transfer.E2pkg.hkMem_add_of_contDiffOn α n
    hE2hat.2 hgam.1 hE2hat.1 hgam.2

end Work.FTS.StrongEps.EpsE4Thr.TransO
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsSliceLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

theorem EpsSliceLe :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : ℝ → ℝ → ℝ, ∀ z : ℝ, 0 < z →
      ContDiffOn ℝ 1 (fun θ => f z θ) (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto (fun θ => f z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn
        (fun θ => (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        ≤ C / (Work.Spaces.gam α - 1) ^ 2 *
          (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
  -- The slice Hardy inequality `∫ sin(2θ)^{-c} u² ≤ C/(c-1)² ∫ sin(2θ)^{2-c}(u')²` for
  -- `1 < c ≤ 3/2`, applied at `c = γ = 1 + α/10` and `u = (f z ·)`.
  obtain ⟨CH, hCHpos, hCH⟩ := Work.FTS.StrongEps.EpsSqTools.hardySinGam_weak
  refine ⟨CH, hCHpos, ?_⟩
  intro α hα f z hz hcd ht1 ht2 hslot
  obtain ⟨hα0, hα1⟩ := hα
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα0
  have hγ32 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  -- the Hardy hypothesis on the derivative side, converted from the `(0,1)`-slot
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2)
      Work.Spaces.Iθ :=
    Work.FTS.StrongEps.EpsSqTools.pth_slice_integrable (α := α) (z := z) (f := f)
      hα0 hα1 hz hslot
  obtain ⟨hL1, hL2⟩ := hCH (Work.Spaces.gam α) (fun θ => f z θ) hγ1 hγ32 hcd ht1 ht2 hint
  have hcomm : (∫ θ in Work.Spaces.Iθ,
        (f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (f z θ) ^ 2) :=
    MeasureTheory.setIntegral_congr_fun
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) (fun θ _ => by ring)
  have hbound : (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
      ≤ CH / (Work.Spaces.gam α - 1) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    calc (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          Work.FTS.StrongEps.EpsSqTools.epsSq_slice_eq α z f
      _ = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (f z θ) ^ 2 := by rw [hcomm]
      _ ≤ (Work.Spaces.w z) ^ 2 * (CH / (Work.Spaces.gam α - 1) ^ 2 *
            ∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hL2 (sq_nonneg _)
      _ = CH / (Work.Spaces.gam α - 1) ^ 2 * ((Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2) := by
          ring
      _ = CH / (Work.Spaces.gam α - 1) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
          rw [Work.FTS.StrongEps.EpsSqTools.slot_slice_eq (α := α) (z := z) hα0 hα1 f]
  refine ⟨?_, hbound⟩
  -- integrability of the `EpsSq`-slice, transported from the Hardy conclusion
  refine (hL1.const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) fun θ hθ => ?_
  have h1 : (Work.FTS.StrongEps.epsW α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    Work.FTS.StrongEps.EpsSqTools.epsW_sq_eq hθ
  simp only []
  rw [mul_pow, h1]
  ring

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.SliceTracePth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The angular trace of a slice, in the `pth`/`mixed`/`Wt` vocabulary

`SliceTracePth` is the version of the `C¹`-slice trace lemma `SliceTraceO` (same directory) in
which the weighted angular energy is written with the plain angular derivative `∂_θ f = pth f`,
and in which the integrability hypothesis is given in the `(0,1)`-slot form used by the
`ε`-scheme, `(D_θ f · W)²` with `D_θ f = mixed 0 1 f` and `W = Wt α z ·`.

The two integrands are related by

  `(mixed 0 1 f z θ · Wt α z θ)² = (w z)² · sin(2θ)^{2-γ} · (pth f z θ)²`

(`mixed 0 1 f = D_θ f = sin(2θ)·∂_θ f` and `Wt = w·sin(2θ)^{-γ/2}`), so the slot hypothesis is,
up to the nonzero constant `(w z)²`, integrability of the weighted energy
`sin(2θ)^{2-γ} (∂_θ f)²`; this conversion is the lemma
`Work.FTS.StrongEps.EpsSqTools.pth_slice_integrable`.  The slice `θ ↦ f z θ` is `C¹` on
`(0,π/2)` because `f` is `C^∞` on the open quadrant (`SmoothOpen.curry_θ`).  With these two
inputs the trace and its weighted Hardy rate are exactly `SliceTraceO`. -/

/-- The integrand of `SliceTraceO` for the slice `θ ↦ f z θ`, with `pth` unfolded and the two
factors exchanged; the two sides are equal pointwise. -/
private lemma pthSq_sin_eq (f : ℝ → ℝ → ℝ) (z α : ℝ) :
    (fun θ : ℝ => (deriv (fun θ' : ℝ => f z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth f z θ) ^ 2 := by
  funext θ
  rw [Work.Spaces.pth]
  ring

theorem SliceTracePth {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hslot : MeasureTheory.Integrable
      (fun θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)^2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    ∃ mu : ℝ, Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds mu) ∧
      ∀ θ ∈ Set.Ioo 0 (π/4),
        (f z θ - mu)^2 ≤ 100/(Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
          * (∫ σ in Work.Spaces.Iθ,
              (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- the integrability of the weighted angular energy of the slice, from the slot hypothesis
  have hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth f z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.StrongEps.EpsSqTools.pth_slice_integrable hα0 hα1 hz hslot
  -- the same integrand in the shape consumed by `SliceTraceO`
  have hint' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun θ' : ℝ => f z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    rw [pthSq_sin_eq f z α]
    exact hint
  -- the slice is `C¹` on `(0,π/2)`, being the `θ`-slice of a `C^∞` datum on the open quadrant
  have hsm : ContDiffOn ℝ 1 (fun θ : ℝ => f z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hso.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  obtain ⟨mu, hmu, hbd⟩ := SliceTraceO (α := α) (u := fun θ : ℝ => f z θ) hα hsm hint'
  refine ⟨mu, hmu, fun θ hθ => ?_⟩
  have hInt : (∫ σ in Work.Spaces.Iθ,
        (deriv (fun θ' : ℝ => f z θ') σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      = ∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) fun σ _ => ?_
    rw [Work.Spaces.pth]
    ring
  have h := hbd θ hθ
  rw [hInt] at h
  simpa using h

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.Slot01LeHkSq1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

/-- The `(0,1)`-slot of the `ℋ¹`-integrand: `(D_θ f · W)²` is one of the summands of
`HkIntegrand α 1 f` (namely the mixed term `i = 1`, `j = 0`), so the `θ`-integral of the
slot is bounded by the `θ`-integral of the integrand, and hence by `HkSq α 1 f`. -/
theorem Slot01LeHkSq1 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 1 f) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ Work.Spaces.HkSq α 1 f := by
  have hprod : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed 0 1 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed hso hm 0 1
      (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · simpa only [Function.uncurry, MeasureTheory.IntegrableOn]
      using hprod.integral_prod_left
  · rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
      hm.2 ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hm.1 z hz) ?_
    filter_upwards with θ
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 1 f z θ 1 0 (by norm_num) (by norm_num)

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfileSlotCompare =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **A mixed slot of the `ℋ^k`-integrand is dominated by `HkSq α k`.**  For `f` which is `C^∞`
on the open quadrant and honestly in `ℋ^k`, and for a slot `(j,i)` of the mixed block
(`1 ≤ i`, `i + j ≤ k`), the `θ`-integral of the slot is `z`-integrable and

  `∫_z ∫_θ (D_z^j D_θ^i f · W)² ≤ HkSq α k f`. -/
theorem slot_mixed_le_HkSq {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α k f)
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ Work.Spaces.HkSq α k f := by
  have hprod : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed hso hm j i hi hij
  refine ⟨?_, ?_⟩
  · simpa only [Function.uncurry, MeasureTheory.IntegrableOn]
      using hprod.integral_prod_left
  · rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
      hm.2 ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hm.1 z hz) ?_
    filter_upwards with θ
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij

end Work.FTS.StrongEps.EpsRLX
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.KdKFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## Auxiliary facts about the routed kernels `KdK ρ ε a b`

The routed kernels `KdK ρ ε a b = ∂₁^a∂₂^b (Jker ρ ε)` are smooth, compactly supported, and
supported in the closed ball of radius `ε`; this module collects the five facts about them that
the `ε`-square estimates use: the scaling identity in `ε` (with the change of variables
`p ↦ ε⁻¹ • p`), the bound of their mass by the level-`M` mass `Ksm`, their integrability against
functions continuous on the ball, their support bound `|p.1| + |p.2| ≤ 2ε`, and the resulting
exponential-moment estimate. -/

/-- **The change of variables `p ↦ ε⁻¹ • p`** for the rescaled kernel: the mass of `|Jker σ ε|`
equals the mass of `|σ|`.  (`Jker σ ε p = ε⁻¹ ^ 2 · σ (ε⁻¹ • p)` and the substitution has
Jacobian `ε ^ 2` in `ℝ²`.) -/
private lemma integral_abs_Jker (σ : ℝ × ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker σ ε p| = ∫ p : ℝ × ℝ, |σ p| := by
  have hpt : ∀ p : ℝ × ℝ,
      |Work.FTS.StrongEps.Jker σ ε p| = ε⁻¹ ^ 2 * |σ (ε⁻¹ • p)| := by
    intro p
    simp only [Work.FTS.StrongEps.Jker, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε⁻¹ ^ 2)]
  calc ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker σ ε p|
      = ∫ p : ℝ × ℝ, ε⁻¹ ^ 2 * |σ (ε⁻¹ • p)| :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = ε⁻¹ ^ 2 * ∫ p : ℝ × ℝ, |σ (ε⁻¹ • p)| := by
        rw [MeasureTheory.integral_const_mul]
    _ = ε⁻¹ ^ 2 * (ε ^ 2 * ∫ p : ℝ × ℝ, |σ p|) := by
        rw [Work.FTS.StrongEps.integral_comp_inv_smul_two (fun p => |σ p|) hε]
    _ = ∫ p : ℝ × ℝ, |σ p| := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, one_mul]

/-- **The routed scaling identity, integrated**: the mass of the routed derivative `∂₁^a∂₂^b`
of `Jker ρ ε` is `ε⁻¹^{a+b}` times the mass of the corresponding derivative of `ρ`. -/
private lemma integral_abs_KdK_eq (ρ : ℝ × ℝ → ℝ)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (a b : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
      = ε⁻¹ ^ (a + b)
          * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b p| := by
  have hpt : ∀ p : ℝ × ℝ,
      |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
        = ε⁻¹ ^ (a + b)
            * |Work.FTS.StrongEps.Jker (Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b) ε p| := by
    intro p
    show |Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) a b p|
        = ε⁻¹ ^ (a + b)
            * |Work.FTS.StrongEps.Jker (Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b) ε p|
    rw [congrFun (Work.FTS.StrongEps.EpsE4Thr.Kd_Jker_scale_fn hρ ε a b) p, abs_mul,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hε.le) _)]
  calc ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
      = ∫ p : ℝ × ℝ,
          ε⁻¹ ^ (a + b)
            * |Work.FTS.StrongEps.Jker (Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b) ε p| :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = ε⁻¹ ^ (a + b)
          * ∫ p : ℝ × ℝ,
              |Work.FTS.StrongEps.Jker (Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b) ε p| := by
        rw [MeasureTheory.integral_const_mul]
    _ = ε⁻¹ ^ (a + b)
          * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b p| := by
        rw [integral_abs_Jker (Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b) hε]

/-- **The scaling identity of the routed mass** in the exact form used by the `ε`-square
estimates: `∫ |KdK ρ ε a b| = ε⁻¹^{a+b} ∫ |KdK ρ 1 a b|`. -/
private lemma integral_abs_KdK_scale (ρ : ℝ × ℝ → ℝ)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (a b : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
      = ε⁻¹ ^ (a + b)
          * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p| := by
  rw [integral_abs_KdK_eq ρ hρ a b hε]
  congr 1
  rw [integral_abs_KdK_eq ρ hρ a b one_pos]
  simp

/-- **The mass of a routed kernel is at most the level-`M` mass** `Ksm ρ 1 M` (immediate from the
definition of `Ksm` as the sum over all slots of order `≤ M`). -/
private lemma integral_abs_KdK_le_Ksm (ρ : ℝ × ℝ → ℝ) {M a b : ℕ} (ha : a ≤ M) (hb : b ≤ M) :
    ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p|
      ≤ Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M := by
  simp only [Work.FTS.StrongEps.EpsE4Thr.Ksm]
  calc ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p|
      ≤ ∑ a' ∈ Finset.range (M + 1),
          ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b p| :=
        Finset.single_le_sum (f := fun a' => ∫ p : ℝ × ℝ,
            |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b p|)
          (fun _ _ => integral_nonneg fun p => abs_nonneg _)
          (Finset.mem_range.mpr (by omega))
    _ ≤ ∑ a' ∈ Finset.range (M + 1), ∑ b' ∈ Finset.range (M + 1),
          ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b' p| :=
        Finset.sum_le_sum fun a' _ => Finset.single_le_sum
          (f := fun b' => ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b' p|)
          (fun _ _ => integral_nonneg fun p => abs_nonneg _)
          (Finset.mem_range.mpr (by omega))

/-- **The routed kernels are supported in the closed ball of radius `ε`.** -/
private lemma tsupport_KdK_subset_closedBall {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ) :
    tsupport (Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b)
      ⊆ Metric.closedBall (0 : ℝ × ℝ) ε := by
  have hS : ∀ {F : ℝ × ℝ → ℝ}, tsupport F ⊆ Metric.closedBall (0 : ℝ × ℝ) ε →
      tsupport (Work.FTS.StrongEps.partSnd F) ⊆ Metric.closedBall (0 : ℝ × ℝ) ε := by
    intro F hF
    refine closure_minimal (fun q hq => ?_) Metric.isClosed_closedBall
    exact hF (Work.FTS.StrongEps.EpsE4Thr.mem_tsupport_of_partSnd_ne_zero
      (Function.mem_support.mp hq))
  have hP : ∀ {F : ℝ × ℝ → ℝ}, tsupport F ⊆ Metric.closedBall (0 : ℝ × ℝ) ε →
      tsupport (Work.FTS.StrongEps.partFst F) ⊆ Metric.closedBall (0 : ℝ × ℝ) ε := by
    intro F hF
    refine closure_minimal (fun q hq => ?_) Metric.isClosed_closedBall
    exact hF (Work.FTS.StrongEps.EpsE4Thr.mem_tsupport_of_partFst_ne_zero
      (Function.mem_support.mp hq))
  have hbase : tsupport (Work.FTS.StrongEps.Jker ρ ε) ⊆ Metric.closedBall (0 : ℝ × ℝ) ε := by
    refine closure_minimal (fun q hq => ?_) Metric.isClosed_closedBall
    have h := Work.FTS.StrongEps.Jker_ne_zero_support hρ.moll hε (Function.mem_support.mp hq)
    have h1 : q.1 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg q.2]
    have h2 : q.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg q.1]
    have ha : |q.1| ≤ ε := by rw [sq_le_sq] at h1; rwa [abs_of_nonneg hε.le] at h1
    have hb : |q.2| ≤ ε := by rw [sq_le_sq] at h2; rwa [abs_of_nonneg hε.le] at h2
    rw [Metric.mem_closedBall, dist_zero_right]
    exact max_le ha hb
  induction a with
  | zero =>
    induction b with
    | zero =>
      simpa only [Work.FTS.StrongEps.EpsE4Thr.KdK, Work.FTS.StrongEps.Kd_zero_eq,
        Function.iterate_zero_apply] using hbase
    | succ b ih =>
      simpa only [Work.FTS.StrongEps.EpsE4Thr.KdK, Work.FTS.StrongEps.Kd_zero_succ] using hS ih
  | succ a ih =>
    simpa only [Work.FTS.StrongEps.EpsE4Thr.KdK, Work.FTS.StrongEps.Kd_succ_eq] using hP ih

/-- A routed kernel vanishes off the closed ball of radius `ε`. -/
private lemma KdK_eq_zero_of_notMem_closedBall {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ) {p : ℝ × ℝ}
    (hp : p ∉ Metric.closedBall (0 : ℝ × ℝ) ε) :
    Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p = 0 := by
  by_contra hne
  refine hp (tsupport_KdK_subset_closedBall hρ hε a b ?_)
  exact subset_tsupport _ (Function.mem_support.mpr hne)

/-- **The sharp support bound**: a point where a routed kernel does not vanish satisfies
`|p.1| + |p.2| ≤ 2ε`. -/
private lemma abs_KdK_sum_le_two_mul {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ) {p : ℝ × ℝ}
    (hp : Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p ≠ 0) : |p.1| + |p.2| ≤ 2 * ε := by
  have hmem : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε :=
    tsupport_KdK_subset_closedBall hρ hε a b (subset_tsupport _ (Function.mem_support.mpr hp))
  have h : max |p.1| |p.2| ≤ ε := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using hmem
  have h1 : |p.1| ≤ ε := le_trans (le_max_left _ _) h
  have h2 : |p.2| ≤ ε := le_trans (le_max_right _ _) h
  linarith

/-- **Integrability of a routed kernel against a function continuous on its support**: the product
is supported in the compact ball of radius `ε`, where it is continuous. -/
private lemma integrable_abs_KdK_mul {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ)
    {B : ℝ × ℝ → ℝ} (hB : ContinuousOn B (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    Integrable (fun p : ℝ × ℝ => |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p| * B p) := by
  have hon : IntegrableOn (fun p : ℝ × ℝ => |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p| * B p)
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    (((Work.FTS.StrongEps.EpsE4Thr.KdK_continuous hρ ε a b).abs.continuousOn).mul hB)
      |>.integrableOn_compact (isCompact_closedBall (0 : ℝ × ℝ) ε)
  refine hon.integrable_of_forall_notMem_eq_zero (fun p hp => ?_)
  rw [KdK_eq_zero_of_notMem_closedBall hρ hε a b hp, abs_zero, zero_mul]

/-- **The exponential moment of a routed kernel**: since the support has `|p.1| + |p.2| ≤ 2ε ≤ 2`,
the exponential weight is bounded by `e^{2(2c+δ)}` on it. -/
private lemma lintegral_abs_KdK_mul_exp_le {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε c δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : 0 ≤ c) (hδ : 0 ≤ δ) (a b : ℕ) :
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
        * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
      ≤ ENNReal.ofReal (Real.exp (2 * (2 * c + δ))
          * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|) := by
  have hcd : 0 ≤ 2 * c + δ := by linarith
  have hmono : ∀ p : ℝ × ℝ,
      ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
          * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
        ≤ ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
            * Real.exp (2 * (2 * c + δ))) := by
    intro p
    refine ENNReal.ofReal_le_ofReal ?_
    rcases eq_or_ne (Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p) 0 with h | h
    · rw [h, abs_zero, zero_mul, zero_mul]
    · have hsum := abs_KdK_sum_le_two_mul hρ hε a b h
      have h2 : |p.1| + |p.2| ≤ 2 := by linarith
      have hexp : Real.exp ((2 * c + δ) * (|p.1| + |p.2|)) ≤ Real.exp (2 * (2 * c + δ)) := by
        rw [Real.exp_le_exp]
        nlinarith [hcd, abs_nonneg p.1, abs_nonneg p.2]
      exact mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
  refine (lintegral_mono hmono).trans_eq ?_
  have hEq : ∀ p : ℝ × ℝ,
      ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
          * Real.exp (2 * (2 * c + δ)))
        = ENNReal.ofReal (Real.exp (2 * (2 * c + δ)))
            * ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|) := by
    intro p
    rw [ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
  have hint : Integrable (fun p : ℝ × ℝ =>
      |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|) := by
    have h := integrable_abs_KdK_mul hρ hε a b (B := fun _ : ℝ × ℝ => (1 : ℝ))
      continuousOn_const
    simpa only [mul_one] using h
  rw [lintegral_congr hEq,
    MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun p => abs_nonneg _)]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]

theorem KdKFacts (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    (∀ {ε : ℝ}, 0 < ε → ∀ a b : ℕ,
        ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
          = ε⁻¹ ^ (a + b) * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p|)
    ∧ (∀ {a b : ℕ}, a ≤ 3 → b ≤ 3 →
        ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p|
          ≤ Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3)
    ∧ (∀ {ε : ℝ}, 0 < ε → ∀ a b : ℕ, ∀ {B : ℝ × ℝ → ℝ},
        ContinuousOn B (Metric.closedBall (0 : ℝ × ℝ) ε) →
        MeasureTheory.Integrable (fun p : ℝ × ℝ => |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p| * B p))
    ∧ (∀ {ε : ℝ}, 0 < ε → ∀ a b : ℕ, ∀ {p : ℝ × ℝ},
        Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε)
    ∧ (∀ {ε c δ : ℝ}, 0 < ε → ε ≤ 1 → 0 ≤ c → 0 ≤ δ → ∀ a b : ℕ,
        ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
            * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
          ≤ ENNReal.ofReal (Real.exp (2 * (2 * c + δ))
              * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ε hε a b
    exact integral_abs_KdK_scale ρ hρ a b hε
  · intro a b ha hb
    exact integral_abs_KdK_le_Ksm ρ ha hb
  · intro ε hε a b B hB
    exact integrable_abs_KdK_mul hρ hε a b hB
  · intro ε hε a b p hp
    exact abs_KdK_sum_le_two_mul hρ hε a b hp
  · intro ε c δ hε hε1 hc hδ a b
    exact lintegral_abs_KdK_mul_exp_le hρ hε hε1 hc hδ a b

end Work.FTS.StrongEps.EpsSqTools
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.L12_zero_le_EpsSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Pointwise facts on the open quadrant

The weight `epsW α z θ = w z / sin(2θ)^{γ/2}` of the `ε`-scheme dominates both `1` and the
closed-quadrant weight `w z` on the open quadrant, where `w z ≥ 1` and `0 < sin(2θ) ≤ 1`. -/

theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, one_le_div (by positivity)]
  nlinarith

theorem w_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Work.Spaces.w z ≠ 0 := by
  rw [Work.Spaces.w]
  exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 hz.ne')

theorem div_sq_eq_w (r : ℝ) : ((1 + r) / r) ^ 2 = Work.Spaces.w r := by
  rw [Work.Spaces.w, div_pow]

theorem sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem gam_half_pos {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α / 2 := by
  rw [Work.Spaces.gam]; linarith

theorem one_le_epsW {α z θ : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 1 ≤ epsW α z θ := by
  have hs := sin_two_pos_of_mem hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hs _
  have hsle : Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) ≤ 1 :=
    Real.rpow_le_one hs.le hs1 (gam_half_pos hα).le
  rw [epsW, one_le_div hspos]
  exact le_trans hsle (one_le_w_of_pos hz)

theorem epsW_ne_zero {α z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    epsW α z θ ≠ 0 := by
  have hs := sin_two_pos_of_mem hθ
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hs _
  exact div_ne_zero (w_ne_zero_of_pos hz) hspos.ne'

theorem w_le_epsW_sq {α z θ : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Work.Spaces.w z ≤ (epsW α z θ) ^ 2 := by
  have h1 := one_le_epsW hα hz hθ
  have hs := sin_two_pos_of_mem hθ
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hs _
  have hsle : Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) ≤ 1 :=
    Real.rpow_le_one hs.le (Real.sin_le_one _) (gam_half_pos hα).le
  have hw0 : 0 ≤ Work.Spaces.w z := le_trans zero_le_one (one_le_w_of_pos hz)
  have hwe : Work.Spaces.w z ≤ epsW α z θ := by
    rw [epsW, le_div_iff₀ hspos]
    calc Work.Spaces.w z * Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2)
        ≤ Work.Spaces.w z * 1 := mul_le_mul_of_nonneg_left hsle hw0
      _ = Work.Spaces.w z := mul_one _
  calc Work.Spaces.w z ≤ epsW α z θ := hwe
    _ ≤ (epsW α z θ) ^ 2 := by nlinarith

theorem mul_w_le_sq_epsW {α z θ : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (x : ℝ) :
    x ^ 2 * Work.Spaces.w z ≤ (x * epsW α z θ) ^ 2 := by
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left (w_le_epsW_sq hα hz hθ) (sq_nonneg x)

/-- On the open quadrant the two weights are exchanged by the bounded factor `q`. -/
theorem epsW_sq_mul_inv {α z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (x : ℝ) :
    (x * epsW α z θ) ^ 2
        * ((Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2)) ^ 2 / Work.Spaces.w z)
      = x ^ 2 * Work.Spaces.w z := by
  have hs := sin_two_pos_of_mem hθ
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hs _
  have hw : Work.Spaces.w z ≠ 0 := w_ne_zero_of_pos hz
  rw [epsW]
  field_simp

/-- The angular interval is a.e. the open interval. -/
theorem theta_restrict_Ioo :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm

/-! ## The zero-mode bound of `L₁₂` in the `ε`-space -/

/- **The `L₁₂(0)` bound in the weighted space `X` of the `ε`-scheme.**  There is an
`α`-independent constant `C` (namely `3`) with
`|L₁₂(h)(0)| ≤ C √(EpsSq α h)` for every `α ∈ (0,1]` and every `h : Fn` with honest weighted
`L²`-membership `EpsMem α h`. -/
theorem L12_zero_le_EpsSq : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ h : Work.FTS.Galerkin.Fn, Work.FTS.StrongEps.EpsMem α h →
      |Work.Construction.L12 h 0| ≤ C * Real.sqrt (Work.FTS.StrongEps.EpsSq α h) := by
  refine ⟨3, by norm_num, ?_⟩
  intro α hαI h hf
  have hα : 0 < α := hαI.1
  -- the product measure on `Iz ×ˢ Iθ` is the product of the two restricted measures
  have hM : (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, ← MeasureTheory.Measure.prod_restrict]
  have hQuad : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict Work.FTS.StrongEps.Quad :=
    hM.symm.trans restrict_prod_eq_restrict_quad
  -- the `epsSq`-weighted square is integrable on the product
  have hG : Integrable (fun p : ℝ × ℝ => (h p.1 p.2 * epsW α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [← hM]
    exact hf
  -- the auxiliary factor relating the two weights
  set q : ℝ × ℝ → ℝ :=
    fun p => (Real.sin (2 * p.2) ^ (Work.Spaces.gam α / 2)) ^ 2 / Work.Spaces.w p.1 with hq
  have hq_meas : Measurable q := by
    rw [hq]
    unfold Work.Spaces.w
    fun_prop
  have hq_aesm : AEStronglyMeasurable q
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hq_meas.aestronglyMeasurable
  have hq_bdd : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), ‖q p‖ ≤ 1 := by
    rw [hQuad]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_quad (fun p hp => ?_)
    obtain ⟨hz, hθ⟩ := Work.FTS.StrongEps.mem_Quad.mp hp
    have hs := sin_two_pos_of_mem hθ
    have hs1 : Real.sin (2 * p.2) ≤ 1 := Real.sin_le_one _
    have hspos : 0 < Real.sin (2 * p.2) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hs _
    have hsle : Real.sin (2 * p.2) ^ (Work.Spaces.gam α / 2) ≤ 1 :=
      Real.rpow_le_one hs.le hs1 (gam_half_pos hα).le
    have hs2 : (Real.sin (2 * p.2) ^ (Work.Spaces.gam α / 2)) ^ 2 ≤ 1 := by
      nlinarith [hspos.le, hsle]
    have hw1 : 1 ≤ Work.Spaces.w p.1 := one_le_w_of_pos hz
    have hq0 : 0 ≤ (Real.sin (2 * p.2) ^ (Work.Spaces.gam α / 2)) ^ 2 / Work.Spaces.w p.1 :=
      div_nonneg (sq_nonneg _) (le_trans zero_le_one hw1)
    have hq1 : (Real.sin (2 * p.2) ^ (Work.Spaces.gam α / 2)) ^ 2 / Work.Spaces.w p.1 ≤ 1 := by
      rw [div_le_one (lt_of_lt_of_le zero_lt_one hw1)]
      exact le_trans hs2 hw1
    rw [hq, Real.norm_of_nonneg hq0]
    exact hq1
  -- integrability of the closed-quadrant weight times `h²`
  have hΞ : Integrable (fun p : ℝ × ℝ => (h p.1 p.2) ^ 2 * Work.Spaces.w p.1)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have h1 : Integrable (fun p : ℝ × ℝ => (h p.1 p.2 * epsW α p.1 p.2) ^ 2 * q p)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      hG.mul_bdd hq_aesm hq_bdd
    refine h1.congr ?_
    rw [hQuad]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_quad (fun p hp => ?_)
    obtain ⟨hz, hθ⟩ := Work.FTS.StrongEps.mem_Quad.mp hp
    rw [hq]
    exact epsW_sq_mul_inv hz hθ (h p.1 p.2)
  -- a.e. slice integrability of `h²`
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    have hmem : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Work.Spaces.Iz :=
      MeasureTheory.ae_restrict_mem measurableSet_Ici
    have hne : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      have hset : {z : ℝ | ¬z ≠ 0} = ({0} : Set ℝ) := by
        ext z; simp
      rw [hset]
      rw [MeasureTheory.Measure.restrict_apply (measurableSet_singleton 0)]
      have hI : ({0} : Set ℝ) ∩ Work.Spaces.Iz = ({0} : Set ℝ) := by
        rw [Work.Spaces.Iz]
        ext z
        simp
      rw [hI]
      exact MeasureTheory.measure_singleton 0
    filter_upwards [hmem, hne] with z hz hz0
    exact lt_of_le_of_ne hz (Ne.symm hz0)
  have hslz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Integrable (fun θ => (h z θ) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hΞ.prod_right_ae, hzpos] with z h1 hz
    have hw : Work.Spaces.w z ≠ 0 := w_ne_zero_of_pos hz
    have h2 : Integrable
        (fun θ => (Work.Spaces.w z)⁻¹ * ((h z θ) ^ 2 * Work.Spaces.w z))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := h1.const_mul _
    refine h2.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show (Work.Spaces.w z)⁻¹ * ((h z θ) ^ 2 * Work.Spaces.w z) = (h z θ) ^ 2
    rw [mul_comm ((h z θ) ^ 2) (Work.Spaces.w z), inv_mul_cancel_left₀ hw]
  have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      IntegrableOn (fun θ => (h r θ) ^ 2) Work.Spaces.Iθ :=
    MeasureTheory.ae_mono
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self) hslz
  -- integrability of the weighted angular energy
  have hXint : Integrable
      (fun r => (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * Work.Spaces.w r)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h1 : Integrable
        (fun z => ∫ θ, (h z θ) ^ 2 * Work.Spaces.w z
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := hΞ.integral_prod_left
    refine h1.congr (Filter.Eventually.of_forall (fun r => ?_))
    show (∫ θ, (h r θ) ^ 2 * Work.Spaces.w r
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * Work.Spaces.w r
    rw [MeasureTheory.integral_mul_const]
  have hXfin : IntegrableOn
      (fun r => (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * Work.Spaces.w r)
      (Set.Ioi (0 : ℝ)) :=
    hXint.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self)
  -- a.e. strong measurability of the weighted angular energy
  have hmeas : AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : AEStronglyMeasurable
        (fun r => (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * Work.Spaces.w r)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hXfin.aestronglyMeasurable
    refine h1.congr (Filter.Eventually.of_forall (fun r => ?_))
    show (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * Work.Spaces.w r
      = (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * ((1 + r) / r) ^ 2
    rw [div_sq_eq_w r]
  -- integrability of the `epsSq`-weighted angular energy
  have hΦ : IntegrableOn (fun r => ∫ θ in Work.Spaces.Iθ, (h r θ * epsW α r θ) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    (hG.integral_prod_left).mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self)
  -- the a.e. comparison of the two angular energies
  have h1ae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Integrable (fun θ => (h r θ) ^ 2 * Work.Spaces.w r)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_mono
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self)
      hΞ.prod_right_ae
  have h2ae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Integrable (fun θ => (h r θ * epsW α r θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_mono
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self)
      hG.prod_right_ae
  have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * ((1 + r) / r) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, (h r θ * epsW α r θ) ^ 2 := by
    filter_upwards [h1ae, h2ae, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r h1r h2r hr
    have hr0 : 0 < r := hr
    have hpt : (fun θ => (h r θ) ^ 2 * Work.Spaces.w r)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ => (h r θ * epsW α r θ) ^ 2) := by
      rw [theta_restrict_Ioo]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => mul_w_le_sq_epsW hα hr0 hθ (h r θ))
    have hmono := MeasureTheory.integral_mono_ae h1r h2r hpt
    rw [MeasureTheory.integral_mul_const] at hmono
    rwa [div_sq_eq_w r]
  have hmain := Work.FTS.OpenPkg.l12zero_of_weight_bound (f := h)
    (Φ := fun r => ∫ θ in Work.Spaces.Iθ, (h r θ * epsW α r θ) ^ 2) hsl hmeas hΦ hbd
  have hEps : (∫ r in Set.Ioi (0 : ℝ),
        ∫ θ in Work.Spaces.Iθ, (h r θ * epsW α r θ) ^ 2) = EpsSq α h := by
    rw [EpsSq, Work.Spaces.Iz]
    exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici
  calc |Work.Construction.L12 h 0|
      ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          ∫ θ in Work.Spaces.Iθ, (h r θ * epsW α r θ) ^ 2) := hmain
    _ = 3 * Real.sqrt (EpsSq α h) := by rw [hEps]

end

end Work.FTS.StrongEps.EpsSqTools
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6Gam.b1gOuter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
/-! ## Radial integrability of the slice integral -/

theorem b1gOuter : ∀ (α : ℝ) (A f : ℝ → ℝ → ℝ) (M : ℝ), α ∈ Set.Ioc 0 1 →
    Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.FTS.Nonlin.Xn α f ≤ M →
    MeasureTheory.Integrable
      (fun z => ∫ θ, |b1gF α A f (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  intro α A f M hα hA hf h6A h6f hXnM
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXnM
  have hMXint : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2
      * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX_apply] using
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xProdIntLe α A hα0 hα1 hA h6A).1
  have hQint : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2
      * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz_apply] using
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.zProdIntLe α f hα0 hα1 hf h6f).1
  have hMajAbs_int : MeasureTheory.Integrable (fun z => Real.sqrt 3 * M
      * (((Work.Spaces.w z) ^ 2 * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z
          + (Work.Spaces.w z) ^ 2
            * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z) / 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((hMXint.add hQint).div_const 2).const_mul _
  have hcontF : ContinuousOn (fun p : ℝ × ℝ => b1gF α A f p) Work.FTS.EllipticEst.Q0 := by
    simp only [b1gF_apply]
    exact (((Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.contOn_leafGam α).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn
        (hA.mixed 5 0))).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hf.mixed 1 1))).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hf.mixed 5 1))
  have hIaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => |b1gF α A f p|)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcontF.abs
  refine MeasureTheory.Integrable.mono' hMajAbs_int hIaesm.integral_prod_right' ?_
  filter_upwards [b1gInner α A f M hα hA hf h6A h6f hXnM] with z hz
  have hA_nn : 0 ≤ ∫ θ, |b1gF α A f (z, θ)|
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.integral_nonneg (fun θ => abs_nonneg _)
  rw [Real.norm_of_nonneg hA_nn]
  refine le_trans hz ?_
  have hAMall : (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
      * (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))
      ≤ ((Work.Spaces.w z) ^ 2 * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z
          + (Work.Spaces.w z) ^ 2
            * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z) / 2 := by
    have hMXnn : 0 ≤ Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z := by
      rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX_apply]
      refine add_nonneg (mul_nonneg (by positivity)
          (MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)))
        (mul_nonneg (div_nonneg (by norm_num) (by
            rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.hgam_const]; linarith))
          (MeasureTheory.setIntegral_nonneg measurableSet_Icc
            (fun θ hθ => mul_nonneg
              (Real.rpow_nonneg
                (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_nonneg_of_Iθ' hθ) _)
              (sq_nonneg _))))
    have hQznn : 0 ≤ Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z := by
      rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz_apply]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg
          (Real.rpow_nonneg
            (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_nonneg_of_Iθ' hθ) _)
          (sq_nonneg _))
    have ha : (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)) ^ 2
        = (Work.Spaces.w z) ^ 2
          * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z := by
      rw [mul_pow, Real.sq_sqrt hMXnn]
    have hb : (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)) ^ 2
        = (Work.Spaces.w z) ^ 2
          * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z := by
      rw [mul_pow, Real.sq_sqrt hQznn]
    nlinarith [sq_nonneg (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
      - Work.Spaces.w z * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))]
  exact mul_le_mul_of_nonneg_left hAMall (mul_nonneg (Real.sqrt_nonneg 3) hMnn)
end

end Work.FTS.StrongPersist.H6Row6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.ScalarRows =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/



/-- **Four-factor product monotonicity**: `a·p·s ≤ b·t·q·s` when `a ≤ b`, `p ≤ q`, `1 ≤ t` and
everything is nonnegative. -/
theorem mul_four_le {a b p q s t : ℝ} (hab : a ≤ b) (hpq : p ≤ q) (ht : 1 ≤ t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    a * p * s ≤ b * t * q * s := by
  have h1 : a * p * s ≤ b * p * s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab hp) hs
  have h2 : b * p * s ≤ b * q * s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpq hb) hs
  have h3 : b * q * s ≤ b * (t * q) * s := by
    have h : q ≤ t * q := le_mul_of_one_le_left hq ht
    calc b * q * s = b * (q * s) := by ring
      _ ≤ b * ((t * q) * s) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h hs) hb
      _ = b * (t * q) * s := by ring
  have h4 : b * (t * q) * s = b * t * q * s := by ring
  linarith [h1, h2, h3, le_of_eq h4]

/-- `α^{-1}·α^{-9} = α^{-10}`. -/
theorem rpow_neg_one_mul_nine {α : ℝ} (hα : 0 < α) :
    α ^ (-(1 : ℝ)) * α ^ (-(9 : ℝ)) = α ^ (-(10 : ℝ)) := by
  have h := Real.rpow_add hα (-(1 : ℝ)) (-(9 : ℝ))
  rw [show -(1 : ℝ) + -(9 : ℝ) = -(10 : ℝ) by norm_num] at h
  exact h.symm

/-- `α^{-10}·α = α^{-9}`. -/
theorem rpow_neg_ten_mul {α : ℝ} (hα : 0 < α) :
    α ^ (-(10 : ℝ)) * α = α ^ (-(9 : ℝ)) := by
  have h := Real.rpow_add hα (-(9 : ℝ)) (-(1 : ℝ))
  rw [show -(9 : ℝ) + -(1 : ℝ) = -(10 : ℝ) by norm_num] at h
  rw [Real.rpow_neg_one] at h
  have hαne : α ≠ 0 := ne_of_gt hα
  calc α ^ (-(10 : ℝ)) * α = (α ^ (-(9 : ℝ)) * α⁻¹) * α := by rw [h]
    _ = α ^ (-(9 : ℝ)) := by field_simp

/-- `α^{-9} ≤ α^{-10}` for `0 < α ≤ 1`. -/
theorem rpow_neg_nine_le {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(9 : ℝ)) ≤ α ^ (-(10 : ℝ)) := by
  have hQ0 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  rw [← rpow_neg_ten_mul hα0]
  calc α ^ (-(10 : ℝ)) * α ≤ α ^ (-(10 : ℝ)) * 1 := mul_le_mul_of_nonneg_left hα1 hQ0
    _ = α ^ (-(10 : ℝ)) := by ring

/-- `1 ≤ α^{-q}` for `0 < α ≤ 1` and `q ≥ 0`. -/
theorem one_le_rpow_neg_of {α q : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hq : 0 ≤ q) :
    (1 : ℝ) ≤ α ^ (-q) := by
  have h1 : α ^ q ≤ 1 := Real.rpow_le_one hα0.le hα1 hq
  have h2 : 0 < α ^ q := Real.rpow_pos_of_pos hα0 q
  rw [Real.rpow_neg hα0.le q]
  exact (one_le_inv₀ h2).mpr h1

/-- `M ≤ (1+M)⁴` for `M ≥ 0`. -/
theorem self_le_one_add_pow_four {M : ℝ} (hM0 : 0 ≤ M) : M ≤ (1 + M) ^ 4 := by
  nlinarith [hM0, sq_nonneg M, sq_nonneg (M + 1)]

/-- `(1/(2α))·(C·α^{-9}) = (C/2)·α^{-10}`. -/
theorem half_inv_mul_rpow {α C : ℝ} (hα : 0 < α) :
    (1 / (2 * α)) * (C * α ^ (-(9 : ℝ))) = (C / 2) * α ^ (-(10 : ℝ)) := by
  rw [show (1 : ℝ) / (2 * α) = (1 / 2) * α ^ (-(1 : ℝ)) by
      rw [Real.rpow_neg_one]; ring,
    show (1 / 2 : ℝ) * α ^ (-(1 : ℝ)) * (C * α ^ (-(9 : ℝ)))
        = (C / 2) * (α ^ (-(1 : ℝ)) * α ^ (-(9 : ℝ))) by ring,
    rpow_neg_one_mul_nine hα]

/-! ## The `α`-arithmetic of the modulation bound -/

/-- **The `α`-arithmetic of the modulation bound.**  With `S = (1+M)⁴`, `T = (1+|Ce|+|Cs|)⁴`,
`K := 3(K₀+K_Z+C_T+1)`,

`(1/(2α))(K₀·α^{-9}S + K_Z·T·α^{-9}S + C_T·M) ≤ K·T·α^{-10}·S`.

The three summands are absorbed by `α^{-9} ≥ 1`, `T ≥ 1`, `M ≤ S`; the only `rpow` input is
`α^{-1}·α^{-9} = α^{-10}`. -/
theorem scalar_arith {α K0 KZ CT M Ce Cs : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hM0 : 0 ≤ M) (hK0 : 0 ≤ K0) (hKZ : 0 ≤ KZ) (hCT : 0 ≤ CT) :
    (1 / (2 * α)) * (K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
        + KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 + CT * M)
      ≤ (3 * (K0 + KZ + CT + 1)) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
          * (1 + M) ^ 4 := by
  have hP0 : 0 ≤ α ^ (-(9 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hP1 : 1 ≤ α ^ (-(9 : ℝ)) := one_le_rpow_neg_of hα0 hα1 (by norm_num)
  have hS0 : 0 ≤ (1 + M) ^ 4 := by positivity
  have hMle : M ≤ (1 + M) ^ 4 := self_le_one_add_pow_four hM0
  have hT1 : 1 ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    one_le_pow₀ (by have h1 := abs_nonneg Ce; have h2 := abs_nonneg Cs; linarith)
  have hT0 : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := le_trans zero_le_one hT1
  have hPS0 : 0 ≤ α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := mul_nonneg hP0 hS0
  have hK'0 : 0 ≤ K0 + KZ + CT + 1 := by linarith
  have hTQ0 : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 := by positivity
  -- the three summands, each bounded by the common `K'·T·(P·S)`
  have h1 : K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
      ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by
    calc K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 = K0 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by ring
      _ ≤ (K0 + KZ + CT + 1) * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) :=
          mul_le_mul_of_nonneg_right (by linarith) hPS0
      _ ≤ (K0 + KZ + CT + 1) * ((1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hPS0 hT1) hK'0
      _ = (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by ring
  have h2 : KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
      ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by
    have hkt : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by positivity
    calc KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
        = KZ * ((1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)) := by ring
      _ ≤ (K0 + KZ + CT + 1) * ((1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)) :=
          mul_le_mul_of_nonneg_right (by linarith) hkt
      _ = (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by ring
  have h3 : CT * M
      ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by
    have h1 : CT * M ≤ CT * (1 + M) ^ 4 := mul_le_mul_of_nonneg_left hMle hCT
    have h2 : CT * (1 + M) ^ 4
        ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 := by
      calc CT * (1 + M) ^ 4 ≤ (K0 + KZ + CT + 1) * (1 + M) ^ 4 :=
            mul_le_mul_of_nonneg_right (by linarith) hS0
        _ ≤ (K0 + KZ + CT + 1) * ((1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hS0 hT1) hK'0
        _ = (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 := by ring
    have h3 : (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
        ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by
      calc (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          = (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (1 * (1 + M) ^ 4) := by ring
        _ ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4
              * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hP1 hS0) (by positivity)
    linarith [h1, h2, h3]
  have hZ : K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
        + KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 + CT * M
      ≤ 3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4
          * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)) := by
    have e : 3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4
          * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4))
        = (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)
          + (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)
          + (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by
      ring
    rw [e]
    linarith [h1, h2, h3]
  -- the factor `1/(2α)`
  have hfac : 0 ≤ (1 : ℝ) / (2 * α) := by positivity
  have hstep : (1 / (2 * α)) * (K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
        + KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 + CT * M)
      ≤ (1 / (2 * α)) * (3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4
          * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4))) :=
    mul_le_mul_of_nonneg_left hZ hfac
  have hhalf : (1 / (2 * α)) * (3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4
        * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)))
      = (3 * (K0 + KZ + CT + 1) / 2) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
          * (1 + M) ^ 4 := by
    have h := half_inv_mul_rpow (α := α) (C := (1 : ℝ)) hα0
    rw [one_mul] at h
    calc (1 / (2 * α)) * (3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4
          * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)))
        = (3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4))
            * ((1 / (2 * α)) * α ^ (-(9 : ℝ))) := by ring
      _ = (3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4))
            * ((1 / 2) * α ^ (-(10 : ℝ))) := by rw [h]
      _ = (3 * (K0 + KZ + CT + 1) / 2) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
            * (1 + M) ^ 4 := by ring
  have hfin : (3 * (K0 + KZ + CT + 1) / 2) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
        * (1 + M) ^ 4
      ≤ (3 * (K0 + KZ + CT + 1)) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
          * (1 + M) ^ 4 := by
    have hk : 3 * (K0 + KZ + CT + 1) / 2 ≤ 3 * (K0 + KZ + CT + 1) := by linarith
    calc (3 * (K0 + KZ + CT + 1) / 2) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
          * (1 + M) ^ 4
        = (3 * (K0 + KZ + CT + 1) / 2) * ((1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
            * (1 + M) ^ 4) := by ring
      _ ≤ (3 * (K0 + KZ + CT + 1)) * ((1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
            * (1 + M) ^ 4) := mul_le_mul_of_nonneg_right hk hTQ0
      _ = (3 * (K0 + KZ + CT + 1)) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
            * (1 + M) ^ 4 := by ring
  linarith [hstep, le_of_eq hhalf, hfin]

/-- **The two scalars from the zero-mode bounds.**  With `K := 3(K₀+K_Z+C_T+1)`, the `N₀`- and
transport zero modes are the *proved* lemmas, the `N`-zero mode is the hypothesis `hZ` (the
delegated `H6Rows.NZzero6`). -/
theorem muBdd_of_zeroModes {Ce : ℝ}
    (hZ : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (f Ψ Φs : Fn) (M Cs : ℝ) (E : Fn → Fn),
        H6Adm α f → Work.Spaces.HkMem α 7 f → Work.FTS.Nonlin.Xn α f ≤ M →
        Ell6Ctx α Ce Cs E Φs f Ψ →
        |Work.Construction.L12 (Work.Construction.N α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ) 0|
          ≤ K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4) :
    ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Fam) (τ M Cs : ℝ) (E : Fn → Fn) (Φs : Fn), 0 ≤ τ →
        L6Ctx (IP6 1 1 1 1 1 1 1 1 1 1) α M Ce Cs E Φs g Φ τ →
        |Work.FTS.Galerkin.muDyn α Φ g τ|
            ≤ K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 ∧
        |Work.Construction.mubar
            (Work.Construction.N0 α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice g τ))
            (Work.Construction.N α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice Φ τ))|
          ≤ K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 := by
  obtain ⟨KZ, αZ, hKZ, hαZ, hαZle, hZb⟩ := hZ
  obtain ⟨K0, α0, hK0, hα0, hQb⟩ := H6Pair6Aux.h6pair_N0_zero
  obtain ⟨CT, hCT, hCTb⟩ := H6Pair6Aux.transport_zero_le'
  refine ⟨3 * (K0 + KZ + CT + 1), min (min α0 αZ) 1, by linarith,
    lt_min (lt_min hα0 hαZ) one_pos, min_le_right _ _, ?_⟩
  intro α hα g Φ τ M Cs E Φs hτ hctx
  have hαpos : 0 < α := hα.1
  have hαmin : α ≤ min α0 αZ := le_trans hα.2 (min_le_left _ _)
  have hαone : α ≤ 1 := le_trans hα.2 (min_le_right _ _)
  have hα0' : α ∈ Set.Ioc 0 α0 := ⟨hαpos, le_trans hαmin (min_le_left _ _)⟩
  have hαZ' : α ∈ Set.Ioc 0 αZ := ⟨hαpos, le_trans hαmin (min_le_right _ _)⟩
  set f : Fn := Work.FTS.Galerkin.slice g τ with hf
  set Ψ : Fn := Work.FTS.Galerkin.slice Φ τ with hΨ
  set F : Fn := Work.Construction.Ftau α g τ with hF
  have hreg : H6Adm α f := hctx.hreg
  have h7 : Work.Spaces.HkMem α 7 f := hctx.h7
  have hbdM : Work.FTS.Nonlin.Xn α f ≤ M := hctx.hbdd
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hreg.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 f := hreg.reg.2
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.IPGen.HkMem_mono_le hso 4 (by norm_num) hmem6
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hbdM
  have h0 : |Work.Construction.L12 (Work.Construction.N0 α F f) 0|
      ≤ K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := hQb α hα0' f M hreg h7 hbdM
  have hZb' : |Work.Construction.L12 (Work.Construction.N α F Ψ) 0|
      ≤ KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 :=
    hZb α hαZ' f Ψ Φs M Cs E hreg h7 hbdM hctx.hell
  have hTb : |Work.Construction.L12 (Work.Coercivity.Transport f) 0| ≤ CT * M := by
    have h := hCTb α f hαpos hαone hmem4
    calc |Work.Construction.L12 (Work.Coercivity.Transport f) 0|
        ≤ CT * Work.FTS.Nonlin.Xn α f := h
      _ ≤ CT * M := mul_le_mul_of_nonneg_left hbdM hCT.le
  have hmudyn : Work.FTS.Galerkin.muDyn α Φ g τ
      = (1 / (2 * α)) * (Work.Construction.mubar (Work.Construction.N0 α F f)
          (Work.Construction.N α F Ψ)
          + Work.Construction.L12 (Work.Coercivity.Transport f) 0) := by
    have htwo := Work.Construction.two_mul_mufunS α (Work.Construction.N0 α F f)
      (Work.Construction.N α F Ψ) f (ne_of_gt hαpos)
    rw [Work.FTS.Galerkin.muDyn_eq, ← hF, ← hf, ← hΨ, ← htwo]
    have hne : (2 : ℝ) * α ≠ 0 := by positivity
    field_simp
  have hmubar_eq : Work.Construction.mubar (Work.Construction.N0 α F f)
      (Work.Construction.N α F Ψ)
      = Work.Construction.L12 (Work.Construction.N0 α F f) 0
        + Work.Construction.L12 (Work.Construction.N α F Ψ) 0 := rfl
  have hQ0 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hαpos.le _
  have hP0 : 0 ≤ α ^ (-(9 : ℝ)) := Real.rpow_nonneg hαpos.le _
  have hS0 : 0 ≤ (1 + M) ^ 4 := by positivity
  have hT0 : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
  have hPQ : α ^ (-(9 : ℝ)) ≤ α ^ (-(10 : ℝ)) := rpow_neg_nine_le hαpos hαone
  have hT1' : 1 ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    one_le_pow₀ (by have h1 := abs_nonneg Ce; have h2 := abs_nonneg Cs; linarith)
  refine ⟨?_, ?_⟩
  · rw [hmudyn, hmubar_eq, abs_mul]
    have hc0 : 0 ≤ (1 / (2 * α)) := by positivity
    rw [abs_of_nonneg hc0]
    have htri : |Work.Construction.L12 (Work.Construction.N0 α F f) 0
          + Work.Construction.L12 (Work.Construction.N α F Ψ) 0
          + Work.Construction.L12 (Work.Coercivity.Transport f) 0|
        ≤ K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
          + KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 + CT * M := by
      linarith [abs_add_le (Work.Construction.L12 (Work.Construction.N0 α F f) 0
          + Work.Construction.L12 (Work.Construction.N α F Ψ) 0)
          (Work.Construction.L12 (Work.Coercivity.Transport f) 0),
        abs_add_le (Work.Construction.L12 (Work.Construction.N0 α F f) 0)
          (Work.Construction.L12 (Work.Construction.N α F Ψ) 0), h0, hZb', hTb]
    exact le_trans (mul_le_mul_of_nonneg_left htri hc0)
      (scalar_arith hαpos hαone hM0 hK0.le hKZ.le hCT.le)
  · rw [hmubar_eq]
    have htri : |Work.Construction.L12 (Work.Construction.N0 α F f) 0
          + Work.Construction.L12 (Work.Construction.N α F Ψ) 0|
        ≤ K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
          + KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := by
      linarith [abs_add_le (Work.Construction.L12 (Work.Construction.N0 α F f) 0)
        (Work.Construction.L12 (Work.Construction.N α F Ψ) 0), h0, hZb']
    have hK0le : K0 ≤ K0 + KZ + CT + 1 := by linarith
    have hKZle : KZ ≤ K0 + KZ + CT + 1 := by linarith
    have hK'0 : 0 ≤ K0 + KZ + CT + 1 := by linarith
    have hTX0 : 0 ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 := mul_nonneg hK'0 hT0
    have hR0 : 0 ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
        * (1 + M) ^ 4 := mul_nonneg (mul_nonneg hTX0 hQ0) hS0
    have h1 : K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
        ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
            * (1 + M) ^ 4 :=
      mul_four_le hK0le hPQ hT1' hK0.le hK'0 hP0 hQ0 hS0
    have h2 : KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
        ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
            * (1 + M) ^ 4 := by
      have h := mul_four_le (a := KZ * (1 + |Ce| + |Cs|) ^ 4)
        (b := (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4)
        (p := α ^ (-(9 : ℝ))) (q := α ^ (-(10 : ℝ))) (s := (1 + M) ^ 4) (t := 1)
        (by exact mul_le_mul_of_nonneg_right hKZle hT0) hPQ le_rfl
        (by positivity) (mul_nonneg hK'0 hT0) hP0 hQ0 hS0
      simpa only [mul_one, one_mul] using h
    have hgoal : |Work.Construction.L12 (Work.Construction.N0 α F f) 0
          + Work.Construction.L12 (Work.Construction.N α F Ψ) 0|
        ≤ (3 * (K0 + KZ + CT + 1)) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
            * (1 + M) ^ 4 := by
      calc |Work.Construction.L12 (Work.Construction.N0 α F f) 0
            + Work.Construction.L12 (Work.Construction.N α F Ψ) 0|
          ≤ K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
              + KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := htri
        _ ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4
              + ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
                  * (1 + M) ^ 4) := add_le_add h1 h2
        _ ≤ 3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
              * (1 + M) ^ 4) := by linarith [hR0]
        _ = (3 * (K0 + KZ + CT + 1)) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
              * (1 + M) ^ 4 := by ring
    exact hgoal

end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.EH6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/StrongPersist/SP6/FieldEH` — the order-six flat bound of the `EH`-field

`Work.FTS.PhiStar.EH α Y = 2Y + 2α sin²θ·(Y/(z+1) + z∂_zY) + sin(2θ)·∂_θY` is the
`((z+1)/z)·ℛ(Φ̃_*)`-field (the `Rop`-row of the star package), expressed in terms of
`Ŷ = Ycheck α Φs`.

The task `FieldEH` asks for

`FlatW 6 (EH α Y) (C·(α+1)·(K + KY + KD))`

from `SmoothOpen Y`, `FlatW 7 Y K`, `Fb 6 KY Y` and `F0 6 KD (Yblk Y)`, with a *universal*
constant `C` (it may not depend on `Y`, and it carries the factor `(α+1)`, which is needed:
`EH` grows linearly in `α` when `∂_zY ≠ 0`).

## Route

`FlatW 6 f M` is, by `SP6.flatW6_of_F0`, the pair `F0 6 M f` and `F0 5 M (∂_θ f)`; so it
suffices to bound the flat class of `EH α Y` at order `6` and that of `∂_θ(EH α Y)` at
order `5`.

The two expressions are the *canonical forms* of `FbEHDefs.lean`,

* `EhC α Y = 2Y + ((2α)·(sin²θ · X) + sin 2θ · ∂_θY)`,  `X = Y/(z+1) + z∂_zY`
  (with `eh_EH_eq_EhC : EH α Y = EhC α Y` pointwise, no quadrant hypothesis), and
* `EhD α Y = 2∂_θY + ((2α)·(∂_θ(sin²θ)·X + sin²θ·∂_θX)
    + (∂_θ(sin 2θ)·∂_θY + D_θ(∂_θY)))`
  (with `eh_pth_EhC_eq : ∂_θ(EhC α Y) = EhD α Y` on the open quadrant).

Both are sums of *products of a coefficient function with one block*, so they are bounded by
the bilinear flat calculus `F0_mul`/`F0_add`/`F0_zpz`/`F0_Dth`/`F0_const_mul`, which is
*linear* in the block constants; the coefficient constants come from the single bundle
`CoefBundle6`.

The blocks and their constants are

| block | constant |
|---|---|
| `Y`, `∂_θY`, `z∂_zY`, `D_θ(∂_θY)` | `S = K + KY + KD` (`FlatW 7`, `Fb 6`, `F0 6`) |
| `z∂_z(∂_θY)` | `6S` (`F0_zpz` at level `5` applied to `F0 6 K (∂_θY)`) |

and every coefficient constant is `≤ M := A + 6 ≥ 6` where `A` is the `CoefBundle6`
constant.  Since each product of the calculus multiplies the constant of a *coefficient*
(which carries no `S`) by the constant of a *block* (linear in `S`), the accumulated
constants are linear in `S`, and the final bookkeeping (`ehC_const_le`, `ehD_const_le`)
dominates them by `8 · (2^45·M^40·(α+1)·S) ≤ (2^48·M^40 + 8)·(α+1)·S`, using the absorption
lemmas `mono_le_unit`, `mono_le_unit_alpha`, `eight_unit_le` of `StarPkg6Fields.lean`.

Everything here is `sorry`-free (see `declare_proven` / the axiom record).
-/

namespace Work.FTS.StrongPersist.SP6

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.PhiStar
open Work.FTS.PhiStar.CoreAux

set_option maxHeartbeats 1000000

/-- The smoothness class of the open quadrant, as a local abbreviation. -/
private abbrev Sm (f : ℝ → ℝ → ℝ) : Prop := Work.FTS.EllipticEst.SmoothOpen f

/-! ## The arithmetic of the constant

The accumulated constant of the order-`6` half is an explicit polynomial in `M`, `S`, `α`;
the next two lemmas dominate it by `(2^48·M^40 + 8)·(α+1)·S`, splitting it into at most four
"units" `2^j·u·v·w·M^c·(α or 1)·S` with `u,v,w ≤ M`, each of which is an instance of
`mono_le_unit` / `mono_le_unit_alpha`. -/

private lemma eh_unit_nonneg {M S α : ℝ} (hM : 1 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α) :
    0 ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S := by
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
  have h2 : (0 : ℝ) ≤ 2 ^ 45 := by norm_num
  have hM40 : (0 : ℝ) ≤ M ^ 40 := pow_nonneg hM0 40
  have hα1 : (0 : ℝ) ≤ α + 1 := by linarith
  exact mul_nonneg (mul_nonneg (mul_nonneg h2 hM40) hα1) hS

/-- The accumulated constant of the `EhC`-half is dominated by the final constant. -/
private lemma ehC_const_le {M S α : ℝ} (hM : 1 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α) :
    2 * S + (2 * α * (2 ^ 6 * M * (2 ^ 6 * S * M + S)) + 2 ^ 6 * M * S)
      ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S := by
  have h1 : (2 : ℝ) ^ 1 * 1 * 1 * 1 * M ^ 0 * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit (M := M) (S := S) (α := α) hM hS hα (j := 1) (c := 0)
      (u := 1) (v := 1) (w := 1)
      (by norm_num) (by norm_num) (by norm_num) hM (by norm_num) hM (by norm_num) hM
  have h2 : (2 : ℝ) ^ 13 * M * M * 1 * M ^ 0 * α * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit_alpha (M := M) (S := S) (α := α) hM hS hα (j := 13) (c := 0)
      (u := M) (v := M) (w := 1)
      (by norm_num) (by norm_num) (le_trans zero_le_one hM) le_rfl
      (le_trans zero_le_one hM) le_rfl (by norm_num) hM
  have h3 : (2 : ℝ) ^ 7 * M * 1 * 1 * M ^ 0 * α * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit_alpha (M := M) (S := S) (α := α) hM hS hα (j := 7) (c := 0)
      (u := M) (v := 1) (w := 1)
      (by norm_num) (by norm_num) (le_trans zero_le_one hM) le_rfl (by norm_num) hM
      (by norm_num) hM
  have h4 : (2 : ℝ) ^ 6 * M * 1 * 1 * M ^ 0 * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit (M := M) (S := S) (α := α) hM hS hα (j := 6) (c := 0)
      (u := M) (v := 1) (w := 1)
      (by norm_num) (by norm_num) (le_trans zero_le_one hM) le_rfl (by norm_num) hM
      (by norm_num) hM
  have hexp : 2 * S + (2 * α * (2 ^ 6 * M * (2 ^ 6 * S * M + S)) + 2 ^ 6 * M * S)
      = (2 : ℝ) ^ 1 * 1 * 1 * 1 * M ^ 0 * S
        + ((2 : ℝ) ^ 13 * M * M * 1 * M ^ 0 * α * S
            + (2 : ℝ) ^ 7 * M * 1 * 1 * M ^ 0 * α * S)
        + (2 : ℝ) ^ 6 * M * 1 * 1 * M ^ 0 * S := by ring
  have hunit := eh_unit_nonneg (M := M) (S := S) (α := α) hM hS hα
  have h8 := eight_unit_le (M := M) (S := S) (α := α) hM hS hα
  rw [hexp]
  linarith

/-- The accumulated constant of the `EhD`-half is dominated by the final constant. -/
private lemma ehD_const_le {M S α : ℝ} (hM : 1 ≤ M) (hM7 : 7 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α) :
    2 * S + (2 * α * (2 ^ 5 * M * (2 ^ 5 * S * M + S) + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S))
        + (2 ^ 5 * M * S + S))
      ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S := by
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
  have h1 : (2 : ℝ) ^ 0 * 3 * 1 * 1 * M ^ 0 * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit (M := M) (S := S) (α := α) hM hS hα (j := 0) (c := 0)
      (u := 3) (v := 1) (w := 1)
      (by norm_num) (by norm_num) (by norm_num) (by linarith) (by norm_num) hM (by norm_num) hM
  have h2 : (2 : ℝ) ^ 12 * M * M * 1 * M ^ 0 * α * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit_alpha (M := M) (S := S) (α := α) hM hS hα (j := 12) (c := 0)
      (u := M) (v := M) (w := 1)
      (by norm_num) (by norm_num) hM0 le_rfl hM0 le_rfl (by norm_num) hM
  have h3 : (2 : ℝ) ^ 6 * 7 * M * 1 * M ^ 0 * α * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit_alpha (M := M) (S := S) (α := α) hM hS hα (j := 6) (c := 0)
      (u := 7) (v := M) (w := 1)
      (by norm_num) (by norm_num) (by norm_num) hM7 hM0 le_rfl (by norm_num) hM
  have h4 : (2 : ℝ) ^ 5 * M * 1 * 1 * M ^ 0 * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit (M := M) (S := S) (α := α) hM hS hα (j := 5) (c := 0)
      (u := M) (v := 1) (w := 1)
      (by norm_num) (by norm_num) hM0 le_rfl (by norm_num) hM (by norm_num) hM
  have hexp : 2 * S + (2 * α * (2 ^ 5 * M * (2 ^ 5 * S * M + S) + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S))
        + (2 ^ 5 * M * S + S))
      = (2 : ℝ) ^ 0 * 3 * 1 * 1 * M ^ 0 * S + (2 : ℝ) ^ 5 * M * 1 * 1 * M ^ 0 * S
        + ((2 : ℝ) ^ 12 * M * M * 1 * M ^ 0 * α * S
            + (2 : ℝ) ^ 6 * 7 * M * 1 * M ^ 0 * α * S) := by ring
  have hunit := eh_unit_nonneg (M := M) (S := S) (α := α) hM hS hα
  have h8 := eight_unit_le (M := M) (S := S) (α := α) hM hS hα
  rw [hexp]
  linarith

/-! ## The field estimate -/

/-- **The order-six flat bound of the `EH`-star-field.**

Prove `FlatW 6 (EH α Y) M` with `M := C·(α+1)·(K+KY+KD)` from `SmoothOpen Y`,
`FlatW 7 Y K` (which yields `F0 6 K (∂_θY)`), `Fb 6 KY Y` and `F0 6 KD (Yblk Y)`; the
constant must stay **linear** in `K + KY + KD` (do not use `Fb_basic`, which squares).

Ingredients (import `Submission.Work.FTS.StrongPersist.SP6.Flat6Defs`, module
`Submission.Work.FTS.StrongPersist.SP6.Flat6Defs`): `CoefBundle6s`; `atomData`; the
reassociated field `EHR`/`EHD` with `ehEHR_eq`; `flatW6_of_F0`; `FlatW_mono6`;
`mono_const`. The sibling `Submission/Work/FTS/PhiStar/CoreAux/Fb_EH_bound.lean` is the same
statement at order **four** with the constant `C·A⁴(K+1)(α+1)` from `Fb 6 (A(K+1)) Y` — it
contains the `∂_θ`-identity machinery (`EhC`, `EhD`, `eh_pth_EhC_eq`) and can be adapted. -/
theorem EH6 : ∃ C : ℝ, 0 < C ∧ ∀ (α K KY KD : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 0 ≤ KY → 0 ≤ KD → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.VocabO2.FlatW 7 Y K → Work.FTS.PhiStar.Fb 6 KY Y → Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) →
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EH α Y) (C * (α + 1) * (K + KY + KD)) := by
  obtain ⟨A, hA1, hsin_sq, _hcos_sq, hsin_two, hcos_two,
    _hdsq1, _hdsq2, hdsq3, _hdsq4, _hrho, hrinv⟩ := CoefBundle6
  set M : ℝ := A + 6 with hMdef
  have hM1 : 1 ≤ M := by rw [hMdef]; linarith
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM1
  have hAM : A ≤ M := by rw [hMdef]; linarith
  have hM7 : 7 ≤ M := by rw [hMdef]; linarith
  refine ⟨2 ^ 48 * M ^ 40 + 8, ?_, ?_⟩
  · have h : (0 : ℝ) ≤ 2 ^ 48 * M ^ 40 := mul_nonneg (by norm_num) (pow_nonneg hM0 40)
    linarith
  · intro α K KY KD Y hα hK hKY hKD hsm hY7 hFb hD
    set S : ℝ := K + KY + KD with hSdef
    have hS0 : 0 ≤ S := by rw [hSdef]; linarith
    have hKS : K ≤ S := by rw [hSdef]; linarith
    have hKYS : KY ≤ S := by rw [hSdef]; linarith
    have hKDS : KD ≤ S := by rw [hSdef]; linarith
    -- ### the coefficient bundle at the master constant `M`
    have hPhi1_6 : F0 6 M EhPhi1 := hsin_sq.mono le_rfl hAM
    have hSin2_6 : F0 6 M EhSin2 := hsin_two.mono le_rfl hAM
    have hCos2_6 : F0 6 M EhCos2 := hcos_two.mono le_rfl hAM
    have hRhoInv6 : F0 6 M EhRhoInv := hrinv.mono le_rfl hAM
    have hPhi1_5 : F0 5 M EhPhi1 := hPhi1_6.mono (by norm_num) le_rfl
    have hSin2_5 : F0 5 M EhSin2 := hSin2_6.mono (by norm_num) le_rfl
    have hRhoInv5 : F0 5 M EhRhoInv := hRhoInv6.mono (by norm_num) le_rfl
    -- ### the blocks
    have hP6 : F0 6 K (Work.Spaces.pth Y) := F0_six_pth_of_FlatW hY7
    have bY6 : F0 6 S Y := hFb.f0.mono le_rfl hKYS
    have bP6 : F0 6 S (Work.Spaces.pth Y) := hP6.mono le_rfl hKS
    have bB6 : F0 6 S (Yblk Y) := hD.mono le_rfl hKDS
    have bY5 : F0 5 S Y := bY6.mono (by norm_num) le_rfl
    have bP5 : F0 5 S (Work.Spaces.pth Y) := bP6.mono (by norm_num) le_rfl
    have bB5 : F0 5 S (Yblk Y) := bB6.mono (by norm_num) le_rfl
    -- ### the smoothness of the pieces
    have smYr : Sm (fun z θ => Y z θ * EhRhoInv z θ) := Fbq_smoothOpen_mul hsm eh_smooth_rhoinv
    have smYblk : Sm (Yblk Y) := eh_smooth_yblk hsm
    have smX : Sm (EhX Y) := eh_smooth_EhX hsm
    have smPthYr : Sm (fun z θ => Work.Spaces.pth Y z θ * EhRhoInv z θ) :=
      Fbq_smoothOpen_mul hsm.pth eh_smooth_rhoinv
    have smPthYblk : Sm (Yblk (Work.Spaces.pth Y)) := eh_smooth_yblk hsm.pth
    have smDX : Sm (EhDX Y) := eh_smooth_EhDX hsm
    have smDSinSq : Sm EhDSinSq := eh_smooth_dsinsq
    have smDSin2 : Sm EhDSin2 := eh_smooth_dsin2
    have smPhi1 : Sm EhPhi1 := eh_smooth_ph1
    have smSin2 : Sm EhSin2 := eh_smooth_sin2
    have sm2Y : Sm (fun z θ => 2 * Y z θ) := smoothOpen_const_mul 2 hsm
    have sm2Pth : Sm (fun z θ => 2 * Work.Spaces.pth Y z θ) := smoothOpen_const_mul 2 hsm.pth
    have sm2aPhi1X : Sm (fun z θ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)) :=
      smoothOpen_const_mul (2 * α) (Fbq_smoothOpen_mul smPhi1 smX)
    have smSin2P : Sm (fun z θ => EhSin2 z θ * Work.Spaces.pth Y z θ) :=
      Fbq_smoothOpen_mul smSin2 hsm.pth
    have smDSinSqX : Sm (fun z θ => EhDSinSq z θ * EhX Y z θ) := Fbq_smoothOpen_mul smDSinSq smX
    have smPhi1DX : Sm (fun z θ => EhPhi1 z θ * EhDX Y z θ) := Fbq_smoothOpen_mul smPhi1 smDX
    have smDSin2P : Sm (fun z θ => EhDSin2 z θ * Work.Spaces.pth Y z θ) :=
      Fbq_smoothOpen_mul smDSin2 hsm.pth
    have smDthP : Sm (Work.Spaces.Dth (Work.Spaces.pth Y)) := hsm.pth.Dth
    -- ### level `6`: the canonical form `EhC` of `EH`
    have hX6nn : (0 : ℝ) ≤ 2 ^ 6 * S * M + S := by nlinarith [hS0, hM0]
    have hYr6 : F0 6 (2 ^ 6 * S * M) (fun z θ => Y z θ * EhRhoInv z θ) :=
      F0_mul hS0 hM0 hsm eh_smooth_rhoinv bY6 hRhoInv6
    have hX6 : F0 6 (2 ^ 6 * S * M + S) (EhX Y) :=
      F0_congr (fun z θ _ _ _ => rfl)
        (F0_add smYr smYblk hYr6 bB6)
    have hPhi1X6 : F0 6 (2 ^ 6 * M * (2 ^ 6 * S * M + S))
        (fun z θ => EhPhi1 z θ * EhX Y z θ) :=
      F0_mul hM0 hX6nn smPhi1 smX hPhi1_6 hX6
    have h2aPhi1X6 : F0 6 (2 * α * (2 ^ 6 * M * (2 ^ 6 * S * M + S)))
        (fun z θ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)) := by
      have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 * α) hPhi1X6
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * α)] at h
      exact h
    have hSin2P6 : F0 6 (2 ^ 6 * M * S) (fun z θ => EhSin2 z θ * Work.Spaces.pth Y z θ) :=
      F0_mul hM0 hS0 smSin2 hsm.pth hSin2_6 bP6
    have hInner6 : F0 6 (2 * α * (2 ^ 6 * M * (2 ^ 6 * S * M + S)) + 2 ^ 6 * M * S)
        (fun z θ => (2 * α) * (EhPhi1 z θ * EhX Y z θ) + EhSin2 z θ * Work.Spaces.pth Y z θ) :=
      F0_add sm2aPhi1X smSin2P h2aPhi1X6 hSin2P6
    have h2Y6 : F0 6 (2 * S) (fun z θ => 2 * Y z θ) := by
      have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 : ℝ) bY6
      simpa using h
    have hEhC6 : F0 6 (2 * S + (2 * α * (2 ^ 6 * M * (2 ^ 6 * S * M + S)) + 2 ^ 6 * M * S))
        (EhC α Y) :=
      F0_congr (fun z θ _ _ _ => rfl)
        (F0_add sm2Y (smoothOpen_add sm2aPhi1X smSin2P) h2Y6 hInner6)
    have hEHf0 : F0 6 (2 * S + (2 * α * (2 ^ 6 * M * (2 ^ 6 * S * M + S)) + 2 ^ 6 * M * S))
        (Work.FTS.PhiStar.EH α Y) :=
      F0_congr (fun z θ _ _ _ => eh_EH_eq_EhC z θ) hEhC6
    -- ### level `5`: the canonical form `EhD` of `∂_θ(EH)`
    have hBP5 : F0 5 (6 * S) (Yblk (Work.Spaces.pth Y)) := by
      have h := F0_zpz (n := 5) (K := K) hK hsm.pth hP6
      have h6 : ((↑(5 : ℕ) : ℝ) + 1) * K = 6 * K := by norm_num
      rw [h6] at h
      exact h.mono le_rfl (by linarith)
    have hDthP5 : F0 5 S (Work.Spaces.Dth (Work.Spaces.pth Y)) :=
      (F0_Dth (n := 5) hP6).mono le_rfl hKS
    have hX5nn : (0 : ℝ) ≤ 2 ^ 5 * S * M + S := by nlinarith [hS0, hM0]
    have hDX5nn : (0 : ℝ) ≤ 2 ^ 5 * S * M + 6 * S := by nlinarith [hS0, hM0]
    have hYr5 : F0 5 (2 ^ 5 * S * M) (fun z θ => Y z θ * EhRhoInv z θ) :=
      F0_mul hS0 hM0 hsm eh_smooth_rhoinv bY5 hRhoInv5
    have hX5 : F0 5 (2 ^ 5 * S * M + S) (EhX Y) :=
      F0_congr (fun z θ _ _ _ => rfl) (F0_add smYr smYblk hYr5 bB5)
    have hDSinSq5 : F0 5 M EhDSinSq := eh_F0_dsinsq hSin2_5
    have hDSinSqX5 : F0 5 (2 ^ 5 * M * (2 ^ 5 * S * M + S))
        (fun z θ => EhDSinSq z θ * EhX Y z θ) :=
      F0_mul hM0 hX5nn smDSinSq smX hDSinSq5 hX5
    have hPthYr5 : F0 5 (2 ^ 5 * S * M) (fun z θ => Work.Spaces.pth Y z θ * EhRhoInv z θ) :=
      F0_mul hS0 hM0 hsm.pth eh_smooth_rhoinv bP5 hRhoInv5
    have hDX5 : F0 5 (2 ^ 5 * S * M + 6 * S) (EhDX Y) :=
      F0_congr (fun z θ _ _ _ => rfl) (F0_add smPthYr smPthYblk hPthYr5 hBP5)
    have hPhi1DX5 : F0 5 (2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S))
        (fun z θ => EhPhi1 z θ * EhDX Y z θ) :=
      F0_mul hM0 hDX5nn smPhi1 smDX hPhi1_5 hDX5
    have hSum5 : F0 5 (2 ^ 5 * M * (2 ^ 5 * S * M + S) + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S))
        (fun z θ => EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ) :=
      F0_add smDSinSqX smPhi1DX hDSinSqX5 hPhi1DX5
    have h2aSum5 : F0 5 (2 * α * (2 ^ 5 * M * (2 ^ 5 * S * M + S)
          + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S)))
        (fun z θ => (2 * α) * (EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ)) := by
      have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 * α) hSum5
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * α)] at h
      exact h
    have hDSin2_5 : F0 5 M EhDSin2 := by
      have hb : F0 5 A (fun _ θ : ℝ => deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ) :=
        hdsq3.mono (by norm_num) le_rfl
      refine F0_congr (f := EhDSin2)
        (g := fun _ θ : ℝ => deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ) ?_
        (hb.mono le_rfl hAM)
      intro z θ _ _ _
      show 2 * Real.cos (2 * θ) = deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ
      rw [deriv_sin_two]
    have hDSin2P5 : F0 5 (2 ^ 5 * M * S) (fun z θ => EhDSin2 z θ * Work.Spaces.pth Y z θ) :=
      F0_mul hM0 hS0 smDSin2 hsm.pth hDSin2_5 bP5
    have hTail5 : F0 5 (2 ^ 5 * M * S + S)
        (fun z θ => EhDSin2 z θ * Work.Spaces.pth Y z θ
          + Work.Spaces.Dth (Work.Spaces.pth Y) z θ) :=
      F0_add smDSin2P smDthP hDSin2P5 hDthP5
    have hInner5 : F0 5 (2 * α * (2 ^ 5 * M * (2 ^ 5 * S * M + S)
          + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S)) + (2 ^ 5 * M * S + S))
        (fun z θ => (2 * α) * (EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ)
          + (EhDSin2 z θ * Work.Spaces.pth Y z θ + Work.Spaces.Dth (Work.Spaces.pth Y) z θ)) :=
      F0_add (smoothOpen_const_mul (2 * α) (smoothOpen_add smDSinSqX smPhi1DX))
        (smoothOpen_add smDSin2P smDthP) h2aSum5 hTail5
    have h2P5 : F0 5 (2 * S) (fun z θ => 2 * Work.Spaces.pth Y z θ) := by
      have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 : ℝ) bP5
      simpa using h
    have hEhD5 : F0 5 (2 * S + (2 * α * (2 ^ 5 * M * (2 ^ 5 * S * M + S)
          + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S)) + (2 ^ 5 * M * S + S)))
        (EhD α Y) :=
      F0_congr (fun z θ _ _ _ => rfl)
        (F0_add sm2Pth
          (smoothOpen_add (smoothOpen_const_mul (2 * α) (smoothOpen_add smDSinSqX smPhi1DX))
            (smoothOpen_add smDSin2P smDthP)) h2P5 hInner5)
    have hEHfd : F0 5 (2 * S + (2 * α * (2 ^ 5 * M * (2 ^ 5 * S * M + S)
          + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S)) + (2 ^ 5 * M * S + S)))
        (Work.Spaces.pth (Work.FTS.PhiStar.EH α Y)) :=
      F0_congr (fun z θ hz hθ hθ' => by
        rw [pth_congr_Q0 (f := Work.FTS.PhiStar.EH α Y) (g := EhC α Y)
          (fun z θ _ _ _ => eh_EH_eq_EhC z θ) z θ hz hθ hθ']
        exact eh_pth_EhC_eq hsm z θ hz hθ hθ') hEhD5
    -- ### conclusion
    have hC1 : 2 * S + (2 * α * (2 ^ 6 * M * (2 ^ 6 * S * M + S)) + 2 ^ 6 * M * S)
        ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S :=
      ehC_const_le (M := M) (S := S) (α := α) hM1 hS0 hα
    have hEHf0' : F0 6 ((2 ^ 48 * M ^ 40 + 8) * (α + 1) * S) (Work.FTS.PhiStar.EH α Y) :=
      hEHf0.mono le_rfl hC1
    have hC2 : 2 * S + (2 * α * (2 ^ 5 * M * (2 ^ 5 * S * M + S)
          + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S)) + (2 ^ 5 * M * S + S))
        ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S :=
      ehD_const_le (M := M) (S := S) (α := α) hM1 hM7 hS0 hα
    have hEHfd' : F0 5 ((2 ^ 48 * M ^ 40 + 8) * (α + 1) * S)
        (Work.Spaces.pth (Work.FTS.PhiStar.EH α Y)) :=
      hEHfd.mono le_rfl hC2
    exact flatW6_of_F0 hEHf0' hEHfd'

end Work.FTS.StrongPersist.SP6
end
