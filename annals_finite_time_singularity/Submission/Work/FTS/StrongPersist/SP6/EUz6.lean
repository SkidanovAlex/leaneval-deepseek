import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.Honesty.continuousOn_cmode_of_hkMem_one
import Submission.Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_meas_engine
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sigmaDivisibility
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ip4UnfoldSix
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAsmA
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.StrongPersist.hasDerivAt_wip_family
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.PkgJets.cosWeightTail_le
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_MuLipC.RowN.PvAesmOpen
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.ClassCHon.Hcoef.cmode_slice_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Local-in-`z` bound for the mode coefficients `cmode m F ·`

For `F` which is `C^∞` on the open quadrant, whose level-`0` `ℋ`-integrand is honest
(`HkMem α 0 F`) and whose radial derivative `z ∂_z F` is honest as well, the mode coefficients
`cmode m F t` are `O(1/√(eNorm m))` **uniformly on every compact `z`-interval**: for each `z > 0`
there is `L ≥ 0` with

  `|cmode m F t| ≤ L / √(eNorm m)`   for all `m : ℕ`, `t ∈ [z/2, 2z]`.

**Proof.** The sharp per-mode Bessel bound
`eNorm m * (cmode m F t)² ≤ ∫_θ (F t θ)² sin(2θ)^{-η}` (the sibling
`eNorm_mul_cmode_sq_le_sliceMass`) reduces everything to controlling the angular slice mass

  `mFun t := ∫_θ (F t θ)² · sEta θ`

on the interval `[z/2, 2z]`.  That slice mass is *continuous* on `(0,∞)` by
`sliceMass_continuous` (the honest radial derivative is what makes the `z`-FTC + Cauchy–Schwarz
argument work), and the interval is compact and contained in `(0,∞)` since `z > 0`; so `mFun` is
bounded there by `M := mFun x` at a point `x` where its maximum is attained.  The per-slice
integrability needed to apply the Bessel bound is `integrableOn_sq_sEta_of_HkMem`, available for
every `t > 0`.  Taking `L := √M` (nonnegative because `M` is an integral of a nonnegative
integrand) gives the claim after `√(M / eNorm m) = √M / √(eNorm m)` and `eNorm m > 0`.
-/

open MeasureTheory Set

namespace Work.FTS.ClassCHon.Hcoef

theorem cmode_slice_bound {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF0 : Work.Spaces.HkMem α 0 F)
    (hDz : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz F z θ)) :
    ∀ z : ℝ, 0 < z → ∃ L : ℝ, 0 ≤ L ∧ ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (z / 2) (2 * z) →
      |Work.FTS.PhiStar.Series.cmode m F t|
        ≤ L / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
  intro z hz
  -- the angular slice mass is continuous on `(0,∞)`
  have hcont : ContinuousOn (fun t : ℝ => ∫ θ in Work.Spaces.Iθ,
      (F t θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.ClassCHon.sliceMass_continuous hsm hF0 hDz
  -- the interval `[z/2, 2z]` sits inside `(0,∞)` and is nonempty
  have hsub : Set.Icc (z / 2) (2 * z) ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    simp only [Set.mem_Ioi]
    linarith [ht.1, hz]
  have hne : (Set.Icc (z / 2) (2 * z)).Nonempty :=
    ⟨z, by simp only [Set.mem_Icc]; constructor <;> linarith [hz]⟩
  -- a point where the slice mass is maximal on the interval
  obtain ⟨x, _hxmem, hxmax⟩ := isCompact_Icc.exists_isMaxOn hne (hcont.mono hsub)
  have hxmax' : ∀ y ∈ Set.Icc (z / 2) (2 * z),
      (∫ θ in Work.Spaces.Iθ, (F y θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (F x θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    isMaxOn_iff.mp hxmax
  -- `sEta` is nonnegative on the angular interval
  have hsEta_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.sEta θ := fun θ hθ => by
    simpa only [Work.FTS.EllipticEst.sEta, Work.FTS.EllipticEst.AngSecond.sig]
      using Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
  -- the maximising slice mass is nonnegative
  have hMnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (F x θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    integral_nonneg_of_ae <| by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (hsEta_nn θ hθ)
  refine ⟨Real.sqrt (∫ θ in Work.Spaces.Iθ,
      (F x θ) ^ 2 * Work.FTS.EllipticEst.sEta θ), Real.sqrt_nonneg _, ?_⟩
  intro m t ht
  have htpos : 0 < t := by
    simp only [Set.mem_Icc] at ht
    linarith [ht.1, hz]
  -- per-slice integrability of the `η`-weighted square
  have hint : IntegrableOn
      (fun θ : ℝ => (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem (F := F) hF0 htpos
  -- the sharp per-mode Bessel bound
  have hslice := Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass
    (m := m) (F := F) (z := t) hint
  -- the slice mass at `t` is dominated by the maximal one at `x`
  have hbound : (∫ θ in Work.Spaces.Iθ,
        (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ ∫ θ in Work.Spaces.Iθ, (F x θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    hxmax' t ht
  have hcm2 : (Work.FTS.PhiStar.Series.cmode m F t) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (F x θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        / Work.EllipticEst.ModalSolution.eNorm m := by
    rw [le_div_iff₀ (Work.EllipticEst.ModalSolution.eNorm_pos m), mul_comm]
    exact le_trans hslice hbound
  have habs := Real.abs_le_sqrt hcm2
  rwa [Real.sqrt_div hMnn] at habs

end Work.FTS.ClassCHon.Hcoef
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.cmode_isLittleO_at_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-! ## Two elementary numerical lemmas -/

/-- `(t^{3/2})² = t³`, with the exponent `3` written as a *natural* power on the right. -/
private lemma sq_rpow_three_halves {t : ℝ} (ht : 0 ≤ t) :
    (t ^ ((3 : ℝ) / 2)) ^ 2 = t ^ ((3 : ℕ) : ℝ) := by
  rw [← Real.rpow_mul_natCast ht ((3 : ℝ) / 2) 2]
  norm_num

/-- `1 / w u ^ 2 ≤ t ^ 4` for `0 < u ≤ t`, where `w u = (1+u)²/u²`. -/
private lemma one_div_w_sq_le {u t : ℝ} (hu : 0 < u) (hut : u ≤ t) :
    1 / (Work.Spaces.w u) ^ 2 ≤ t ^ 4 := by
  have hu2 : (0 : ℝ) < u ^ 2 := by positivity
  have hw1 : (1 : ℝ) ≤ (1 + u) ^ 2 := by nlinarith [sq_nonneg u]
  have hwpos : 0 < Work.Spaces.w u := by
    rw [Work.Spaces.w]
    exact div_pos (pow_pos (by linarith) 2) (pow_pos hu 2)
  have hw : 1 / u ^ 2 ≤ Work.Spaces.w u := by
    rw [Work.Spaces.w]
    exact div_le_div_of_nonneg_right hw1 (by positivity)
  have h1 : 1 / Work.Spaces.w u ≤ 1 / (1 / u ^ 2) :=
    one_div_le_one_div_of_le (by positivity) hw
  have h2 : 1 / (1 / u ^ 2) = u ^ 2 := by
    rw [one_div_one_div]
  have h3 : (1 / Work.Spaces.w u) ^ 2 ≤ (u ^ 2) ^ 2 := by
    rw [← h2]
    exact pow_le_pow_left₀ (le_of_lt (one_div_pos.mpr hwpos)) h1 2
  have h4 : (u ^ 2) ^ 2 = u ^ 4 := by ring
  have h5 : u ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ hu.le hut 4
  refine le_trans (le_of_eq ?_) (le_trans h3 (le_trans (le_of_eq h4) h5))
  rw [show (1 : ℝ) / (Work.Spaces.w u) ^ 2 = (1 / Work.Spaces.w u) ^ 2 from by
    rw [div_pow, one_pow]]

/-! ## The main theorem -/

theorem cmode_isLittleO_at_zero {α : ℝ} {F : ℝ → ℝ → ℝ} (m : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF1 : Work.Spaces.HkMem α 1 F) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      |Work.FTS.PhiStar.Series.cmode m F t| ≤ ε * t ^ ((3 : ℝ) / 2) := by
  intro ε hε
  obtain ⟨K, hKpos, hK⟩ := cmode_variation_le m
  -- the mode norm is at least `1`
  have hE1 : 1 ≤ Work.EllipticEst.ModalSolution.eNorm m := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmm : (0 : ℝ) ≤ (m : ℝ) ^ 2 := sq_nonneg _
    rw [Work.EllipticEst.ModalSolution.eNorm, Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m,
      one_le_div (by positivity : (0 : ℝ) < 4 * (m : ℝ) + 5)]
    nlinarith [hm0, hmm]
  have hEpos : 0 < Work.EllipticEst.ModalSolution.eNorm m := lt_of_lt_of_le one_pos hE1
  -- the integrated `ℋ¹`-integrand
  set G : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F z θ with hGdef
  have hHknn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 1 F z θ := by
    intro z θ
    rw [Work.Spaces.HkIntegrand]
    refine add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs with h
      · exact sq_nonneg _
      · exact le_refl 0
  have hGintIz : MeasureTheory.IntegrableOn G Work.Spaces.Iz := by
    rw [hGdef]
    exact hF1.2
  have hGnnIz : ∀ z ∈ Work.Spaces.Iz, 0 ≤ G z := by
    intro z _
    rw [hGdef]
    exact MeasureTheory.integral_nonneg fun θ => hHknn z θ
  -- one-sided continuity of the primitive of `G` at `0`
  have hGintIcc : MeasureTheory.IntegrableOn G (Set.Icc (0 : ℝ) 1) :=
    hGintIz.mono_set (fun z hz => hz.1)
  have hGintU : MeasureTheory.IntegrableOn G (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hGintIcc
  have hΨc : ContinuousOn (fun b : ℝ => ∫ x in (0 : ℝ)..b, G x) (Set.Icc (0 : ℝ) 1) := by
    have h := intervalIntegral.continuousOn_primitive_interval (f := G) (a := (0 : ℝ)) (b := 1)
      hGintU
    rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
  have hΨcw : ContinuousWithinAt (fun b : ℝ => ∫ x in (0 : ℝ)..b, G x) (Set.Icc (0 : ℝ) 1) 0 :=
    hΨc.continuousWithinAt ⟨le_refl 0, by norm_num⟩
  have hΨtend1 : Filter.Tendsto (fun b : ℝ => ∫ x in (0 : ℝ)..b, G x)
      (𝓝[Set.Icc (0 : ℝ) 1] 0) (𝓝 0) := by
    have h := hΨcw
    rw [ContinuousWithinAt] at h
    simpa using h
  have hle : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝[Set.Icc (0 : ℝ) 1] 0 := by
    rw [nhdsWithin_le_iff, mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Ioo (-1) 1, Ioo_mem_nhds (by norm_num) (by norm_num),
      fun y hy => ⟨hy.2.le, hy.1.2.le⟩⟩
  have hΨtend : Filter.Tendsto (fun b : ℝ => ∫ x in (0 : ℝ)..b, G x)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    hΨtend1.mono_left hle
  -- choose the radius
  have hδev : ∀ᶠ b in 𝓝[Set.Ioi (0 : ℝ)] 0,
      ∫ x in (0 : ℝ)..b, G x < (ε / (K + 2)) ^ 2 :=
    hΨtend.eventually (Iio_mem_nhds (show (0 : ℝ) < (ε / (K + 2)) ^ 2 by positivity))
  have hδmem : {b : ℝ | ∫ x in (0 : ℝ)..b, G x < (ε / (K + 2)) ^ 2}
      ∈ 𝓝[Set.Ioi (0 : ℝ)] 0 := hδev
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hδmem
  obtain ⟨U, hUnhds, hUsub⟩ := hδmem
  obtain ⟨r, hrpos, hr⟩ := Metric.mem_nhds_iff.mp hUnhds
  set δ : ℝ := min (r / 2) 1 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) one_pos
  have hδU : δ ∈ U := by
    refine hr ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδpos, hδdef]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδc : ∫ x in (0 : ℝ)..δ, G x < (ε / (K + 2)) ^ 2 := hUsub ⟨hδU, hδpos⟩
  have hδnn : 0 ≤ ∫ x in (0 : ℝ)..δ, G x :=
    intervalIntegral.integral_nonneg hδpos.le (fun s hs => hGnnIz s hs.1)
  have hK2pos : 0 < K + 2 := by linarith
  have hδsqrt : Real.sqrt (∫ x in (0 : ℝ)..δ, G x) < ε / (K + 2) := by
    rw [Real.sqrt_lt' (by positivity : (0 : ℝ) < ε / (K + 2))]
    exact hδc
  refine ⟨δ, hδpos, ?_⟩
  intro t ht htd
  -- interval integrability of `G` on the two windows
  have hGintU0t : MeasureTheory.IntegrableOn G (Set.uIcc (0 : ℝ) t) := by
    refine hGintIz.mono_set ?_
    intro z hz
    rw [Set.uIcc_of_le ht.le] at hz
    exact hz.1
  have hGintU0δ : MeasureTheory.IntegrableOn G (Set.uIcc (0 : ℝ) δ) := by
    refine hGintIz.mono_set ?_
    intro z hz
    rw [Set.uIcc_of_le hδpos.le] at hz
    exact hz.1
  have hGintt : IntervalIntegrable G MeasureTheory.volume (0 : ℝ) t :=
    hGintU0t.intervalIntegrable
  have hGintδ : IntervalIntegrable G MeasureTheory.volume (0 : ℝ) δ :=
    hGintU0δ.intervalIntegrable
  have hGaet : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)] G :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      (fun s hs => hGnnIz s hs.1.le)
  have hGaeδ : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) δ)] G :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      (fun s hs => hGnnIz s hs.1.le)
  have hBw_nn : 0 ≤ ∫ s in (t / 2)..t, G s :=
    intervalIntegral.integral_nonneg (by linarith)
      (fun s hs => hGnnIz s (Set.mem_Ici.mpr (le_trans (by linarith : (0 : ℝ) ≤ t / 2) hs.1)))
  have hΨmono : ∫ x in (0 : ℝ)..t, G x ≤ ∫ x in (0 : ℝ)..δ, G x :=
    intervalIntegral.integral_mono_interval (c := (0 : ℝ)) (d := δ) (a := (0 : ℝ)) (b := t)
      (le_refl 0) ht.le htd hGaeδ hGintδ
  have hBw_le : ∫ s in (t / 2)..t, G s ≤ ∫ x in (0 : ℝ)..t, G x :=
    intervalIntegral.integral_mono_interval (c := (0 : ℝ)) (d := t) (a := t / 2) (b := t)
      (by linarith) (by linarith) (le_refl t) hGaet hGintt
  -- the point of the window where `G` is small
  obtain ⟨u, huIcc, huG⟩ := exists_lt_average_witness ht hGintIz hGnnIz
  have hupos : 0 < u := lt_of_lt_of_le (by linarith : (0 : ℝ) < t / 2) huIcc.1
  have hut : u ≤ t := huIcc.2
  -- the slice-mass bound at `u`
  obtain ⟨hAint, hAle, -, -⟩ := cmode_slice_mass_le hsm hF1 hupos
  have hEcm : Work.EllipticEst.ModalSolution.eNorm m * (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, (F u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    eNorm_mul_cmode_sq_le_sliceMass (m := m) (F := F) (z := u) hAint
  have hwupos : 0 < Work.Spaces.w u := by
    rw [Work.Spaces.w]
    exact div_pos (pow_pos (by linarith) 2) (pow_pos hupos 2)
  have hGu_nn : 0 ≤ G u := hGnnIz u (Set.mem_Ici.mpr hupos.le)
  have hEprod : 0 < Work.EllipticEst.ModalSolution.eNorm m * (Work.Spaces.w u) ^ 2 :=
    mul_pos hEpos (pow_pos hwupos 2)
  have h1 : Work.EllipticEst.ModalSolution.eNorm m * (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
        * (Work.Spaces.w u) ^ 2 ≤ G u :=
    le_trans (mul_le_mul_of_nonneg_right hEcm (sq_nonneg _)) hAle
  have hcu2 : (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
      ≤ t ^ 4 * G u / Work.EllipticEst.ModalSolution.eNorm m := by
    have h2 : (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
        ≤ G u / (Work.EllipticEst.ModalSolution.eNorm m * (Work.Spaces.w u) ^ 2) := by
      rw [le_div_iff₀ hEprod]
      rw [show (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
            * (Work.EllipticEst.ModalSolution.eNorm m * (Work.Spaces.w u) ^ 2)
          = Work.EllipticEst.ModalSolution.eNorm m
            * (Work.FTS.PhiStar.Series.cmode m F u) ^ 2 * (Work.Spaces.w u) ^ 2 from by ring]
      exact h1
    have h3 : 1 / (Work.Spaces.w u) ^ 2 ≤ t ^ 4 := one_div_w_sq_le hupos hut
    have h4 : G u / (Work.EllipticEst.ModalSolution.eNorm m * (Work.Spaces.w u) ^ 2)
        = (G u / Work.EllipticEst.ModalSolution.eNorm m) * (1 / (Work.Spaces.w u) ^ 2) := by
      field_simp
    have h5 : t ^ 4 * G u / Work.EllipticEst.ModalSolution.eNorm m
        = (G u / Work.EllipticEst.ModalSolution.eNorm m) * t ^ 4 := by ring
    calc (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
        ≤ G u / (Work.EllipticEst.ModalSolution.eNorm m * (Work.Spaces.w u) ^ 2) := h2
      _ = (G u / Work.EllipticEst.ModalSolution.eNorm m) * (1 / (Work.Spaces.w u) ^ 2) := h4
      _ ≤ (G u / Work.EllipticEst.ModalSolution.eNorm m) * t ^ 4 :=
          mul_le_mul_of_nonneg_left h3 (div_nonneg hGu_nn hEpos.le)
      _ = t ^ 4 * G u / Work.EllipticEst.ModalSolution.eNorm m := h5.symm
  have hGu_le : G u ≤ 4 * (∫ s in (t / 2)..t, G s) / t := by
    rw [le_div_iff₀ ht]
    exact huG
  have hcu4 : (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
      ≤ 4 * t ^ 3 * (∫ s in (t / 2)..t, G s) / Work.EllipticEst.ModalSolution.eNorm m := by
    refine le_trans hcu2 ?_
    refine le_trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hGu_le (by positivity : (0 : ℝ) ≤ t ^ 4)) hEpos.le) ?_
    rw [show t ^ 4 * (4 * (∫ s in (t / 2)..t, G s) / t) / Work.EllipticEst.ModalSolution.eNorm m
          = 4 * t ^ 3 * (∫ s in (t / 2)..t, G s) / Work.EllipticEst.ModalSolution.eNorm m from by
        field_simp]
  have hpow : (2 * t ^ ((3 : ℝ) / 2)) ^ 2 * (∫ s in (t / 2)..t, G s)
      = 4 * t ^ 3 * (∫ s in (t / 2)..t, G s) := by
    rw [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, ← Real.rpow_natCast t 3,
      ← sq_rpow_three_halves ht.le]
  have hcu4' : (Work.FTS.PhiStar.Series.cmode m F u) ^ 2
      ≤ (2 * t ^ ((3 : ℝ) / 2)) ^ 2 * (∫ s in (t / 2)..t, G s) := by
    rw [hpow]
    refine le_trans hcu4 ?_
    rw [div_le_iff₀ hEpos]
    exact le_mul_of_one_le_right (by positivity) hE1
  have hcu_le : |Work.FTS.PhiStar.Series.cmode m F u|
      ≤ 2 * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..t, G x) := by
    have h2 : Real.sqrt ((2 * t ^ ((3 : ℝ) / 2)) ^ 2 * (∫ s in (t / 2)..t, G s))
        = 2 * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ s in (t / 2)..t, G s) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    calc |Work.FTS.PhiStar.Series.cmode m F u|
        = Real.sqrt ((Work.FTS.PhiStar.Series.cmode m F u) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((2 * t ^ ((3 : ℝ) / 2)) ^ 2 * (∫ s in (t / 2)..t, G s)) :=
          Real.sqrt_le_sqrt hcu4'
      _ = 2 * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ s in (t / 2)..t, G s) := h2
      _ ≤ 2 * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..t, G x) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hBw_le) (by positivity)
  -- the variation bound
  have hmono_u : ∫ s in u..t, G s ≤ ∫ x in (0 : ℝ)..t, G x :=
    intervalIntegral.integral_mono_interval (c := (0 : ℝ)) (d := t) (a := u) (b := t)
      hupos.le hut (le_refl t) hGaet hGintt
  have hvar : |Work.FTS.PhiStar.Series.cmode m F t - Work.FTS.PhiStar.Series.cmode m F u|
      ≤ K * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..t, G x) := by
    refine le_trans (hK α F hsm hF1 hupos hut) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Real.sqrt_le_sqrt hmono_u
  -- assembly
  calc |Work.FTS.PhiStar.Series.cmode m F t|
      ≤ |Work.FTS.PhiStar.Series.cmode m F t - Work.FTS.PhiStar.Series.cmode m F u|
          + |Work.FTS.PhiStar.Series.cmode m F u| := by
        have h := abs_sub_abs_le_abs_sub (Work.FTS.PhiStar.Series.cmode m F t)
          (Work.FTS.PhiStar.Series.cmode m F u)
        linarith
    _ ≤ K * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..t, G x)
          + 2 * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..t, G x) := by
        linarith [hvar, hcu_le]
    _ = (K + 2) * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..t, G x) := by ring
    _ ≤ (K + 2) * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..δ, G x) := by
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hΨmono)
          (le_of_lt (mul_pos hK2pos (Real.rpow_pos_of_pos ht _)))
    _ ≤ ε * t ^ ((3 : ℝ) / 2) := by
        have h2 : (K + 2) * t ^ ((3 : ℝ) / 2) * Real.sqrt (∫ x in (0 : ℝ)..δ, G x)
            < (K + 2) * t ^ ((3 : ℝ) / 2) * (ε / (K + 2)) :=
          mul_lt_mul_of_pos_left hδsqrt
            (mul_pos hK2pos (Real.rpow_pos_of_pos ht _))
        have h3 : (K + 2) * t ^ ((3 : ℝ) / 2) * (ε / (K + 2))
            = ε * t ^ ((3 : ℝ) / 2) := by
          field_simp
        rw [h3] at h2
        exact le_of_lt h2

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.cmode_modeEnergy_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.FTS.PhiStar.Honesty

/-- At `k = 0` the `H^k`-integrand collapses to a single square: the `D_z`-sum has the one term
`i = 0` and the mixed double sum is empty. -/
private theorem HkIntegrand_zero_eq_prv (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- **The slice mass is `Iθ`-integrable at every `z > 0`.**  This is the hypothesis `hint`
required by the per-mode slice bounds; it follows from `HkMem α 0 F` because at level `k = 0`
the `H^k`-integrand is `w z²` times the slice mass, and `w z ≠ 0` for `z > 0`. -/
private theorem sliceMass_integrableOn_Iθ {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α 0 F) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := by
  have hz' : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hwt : Work.FTS.EllipticEst.AngSecond.w2 z ≠ 0 := by
    rw [Work.FTS.EllipticEst.AngSecond.w2]
    exact pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 (by linarith : (1 : ℝ) + z ≠ 0))
      (pow_ne_zero 2 (ne_of_gt hz)))
  have h1 : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 F z θ)
      Work.Spaces.Iθ := hF.1 z hz'
  have h2 : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.w2 z
      * ((F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) Work.Spaces.Iθ :=
    h1.congr_fun (fun θ hθ => by
      dsimp only
      rw [HkIntegrand_zero_eq_prv α F z θ, Work.FTS.EllipticEst.AngSecond.sq_mul_W F hθ]
      simp only [Work.FTS.EllipticEst.AngSecond.sig]
      ring) measurableSet_Icc
  have h3 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.FTS.EllipticEst.AngSecond.w2 z)⁻¹ * (Work.FTS.EllipticEst.AngSecond.w2 z
        * ((F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))) Work.Spaces.Iθ :=
    h2.const_mul _
  exact h3.congr_fun (fun θ hθ => by field_simp) measurableSet_Icc

/-- The squared mode coefficient is a.e. strongly measurable on the open half-line `(0,∞)`. -/
private theorem aeStronglyMeasurable_cmode_sq {F : ℝ → ℝ → ℝ} (m : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  (Work.EllipticEst.ModalSolution.aesm_cmode hsm m).pow 2

theorem cmode_modeEnergy_integrable {α : ℝ} {F : ℝ → ℝ → ℝ} (m : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 0 F) :
    MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 / t ^ 4) (Set.Ioo 0 1) ∧
      MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) (Set.Ioi 1) := by
  -- the slice mass and the per-mode bound with a `z`-independent constant
  set M : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hM
  have hEpos : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
    Work.EllipticEst.ModalSolution.eNorm_pos m
  have hbound : ∀ z : ℝ, 0 < z →
      (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        ≤ (Work.EllipticEst.ModalSolution.eNorm m)⁻¹ * M z := by
    intro z hz
    have h := Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass (m := m) (F := F) (z := z)
      (sliceMass_integrableOn_Iθ hF hz)
    rw [hM]
    have hdiv : (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ,
            (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          / Work.EllipticEst.ModalSolution.eNorm m := by
      rw [le_div_iff₀ hEpos]
      calc (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * Work.EllipticEst.ModalSolution.eNorm m
          = Work.EllipticEst.ModalSolution.eNorm m
              * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 := by ring
        _ ≤ ∫ θ in Work.Spaces.Iθ,
              (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := h
    calc (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ,
            (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          / Work.EllipticEst.ModalSolution.eNorm m := hdiv
      _ = (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
            * (∫ θ in Work.Spaces.Iθ,
                (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
          rw [div_eq_inv_mul]
  constructor
  · -- near `0`: `(cmode m F z)²/z⁴` is dominated by `M z / z⁴`, integrable by `HkMem α 0 F`
    have hMint : MeasureTheory.IntegrableOn (fun z : ℝ => M z / z ^ 4) (Set.Ioo 0 1) := by
      rw [hM]
      exact Work.FTS.PhiStar.Honesty.integrableOn_sliceMass_div_z4_of_HkMem hF
    have hdom : MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.EllipticEst.ModalSolution.eNorm m)⁻¹ * (M z / z ^ 4))
        (Set.Ioo 0 1) := hMint.const_mul _
    refine hdom.mono' ?_ ?_
    · -- a.e. strong measurability on `(0,1)`
      have h1 : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
        (aeStronglyMeasurable_cmode_sq (F := F) m hsm).mono_measure
          (Measure.restrict_mono (fun z hz => hz.1) le_rfl)
      have h2 : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => (z ^ 4)⁻¹)
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
        ((measurable_inv.comp (Measurable.pow_const measurable_id 4)).aemeasurable).aestronglyMeasurable
      exact h1.mul h2
    · -- the pointwise domination
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo ?_
      intro z hz
      have hz4 : (0 : ℝ) < z ^ 4 := pow_pos hz.1 4
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hz4))]
      calc (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 / z ^ 4
          ≤ ((Work.EllipticEst.ModalSolution.eNorm m)⁻¹ * M z) / z ^ 4 :=
            div_le_div_of_nonneg_right (hbound z hz.1) (le_of_lt hz4)
        _ = (Work.EllipticEst.ModalSolution.eNorm m)⁻¹ * (M z / z ^ 4) := by ring
  · -- far `∞`: `(cmode m F z)²` is dominated by `M z`, integrable by `HkMem α 0 F`
    have hMint : MeasureTheory.IntegrableOn M (Set.Ioi 1) := by
      rw [hM]
      exact Work.FTS.PhiStar.Honesty.integrableOn_sliceMass_Ioi_one_of_HkMem hF
    have hdom : MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.EllipticEst.ModalSolution.eNorm m)⁻¹ * M z) (Set.Ioi 1) :=
      hMint.const_mul _
    refine hdom.mono' ?_ ?_
    · have h1 : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
          (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
        (aeStronglyMeasurable_cmode_sq (F := F) m hsm).mono_measure
          (Measure.restrict_mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)) le_rfl)
      simpa only using h1
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro z hz
      have hz1 : 0 < z := by linarith [Set.mem_Ioi.mp hz]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound z hz1

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.integrableOn_acoeff_sq_w_sq_meas =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter

-- `hsm` is part of the (fixed) statement but is not needed by the proof: the only regularity
-- of `F` that the argument consumes is `HkMem α 0 F` (measurability of the clamped `cmode`
-- is a hypothesis).
set_option linter.unusedVariables false


/-! ## The Green's function only sees `c` on `(0,∞)` -/

/-- For `z > 0` the value `radGreen α m c z` depends only on the values of `c` on the open
half-line `(0,∞)`: both integrals in `radGreen` are taken over subsets of `(0,∞)`
(namely `(0,z]` and `(z,∞)`). -/
private lemma radGreen_congr_of_eqOn_Ioi {α : ℝ} {m : ℕ} {c₁ c₂ : ℝ → ℝ}
    (h : ∀ t : ℝ, 0 < t → c₁ t = c₂ t) {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Radial.radGreen α m c₁ z
      = Work.FTS.PhiStar.Radial.radGreen α m c₂ z := by
  have h1 : (∫ t in (0 : ℝ)..z, c₁ t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      = ∫ t in (0 : ℝ)..z, c₂ t * t ^ ((2 * (m : ℝ) + 5) / α - 1) := by
    rw [intervalIntegral.integral_of_le hz.le, intervalIntegral.integral_of_le hz.le]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (fun t ht => by rw [h t ht.1])
  have h2 : (∫ t in Set.Ioi z, c₁ t * t ^ (-(2 * (m : ℝ) / α) - 1))
      = ∫ t in Set.Ioi z, c₂ t * t ^ (-(2 * (m : ℝ) / α) - 1) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => by rw [h t (lt_trans hz ht)])
  rw [Work.FTS.PhiStar.Radial.radGreen, Work.FTS.PhiStar.Radial.radGreen, h1, h2]

/-! ## The target -/

theorem integrableOn_acoeff_sq_w_sq_meas {α : ℝ} {m : ℕ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 0 F)
    (hc : AEMeasurable (fun z : ℝ => if 0 < z then Work.FTS.PhiStar.Series.cmode m F z else 0)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := by
  classical
  set cl : ℝ → ℝ := fun z => if 0 < z then Work.FTS.PhiStar.Series.cmode m F z else 0 with hcl
  have hcl_eq : ∀ t : ℝ, 0 < t → cl t = Work.FTS.PhiStar.Series.cmode m F t := by
    intro t ht
    simp [hcl, ht]
  have hENpos : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
    Work.EllipticEst.ModalSolution.eNorm_pos m
  -- the slice mass uniformly dominates the squared mode coefficient
  have hbnd : ∀ z : ℝ, 0 < z → (cl z) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        / Work.EllipticEst.ModalSolution.eNorm m := by
    intro z hz
    have h := eNorm_mul_cmode_sq_le_sliceMass (m := m) (F := F) (z := z)
      (integrableOn_sq_sEta_of_HkMem hF hz)
    have h' : (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        * Work.EllipticEst.ModalSolution.eNorm m
        ≤ ∫ θ in Work.Spaces.Iθ,
            (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [mul_comm]; exact h
    rw [hcl_eq z hz]
    exact (le_div_iff₀ hENpos).mpr h'
  -- near `0`: `∫_0^1 c²/t⁴ < ∞`
  have hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (cl t) ^ 2 / t ^ 4) (Set.Ioo 0 1) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
          * ((∫ θ in Work.Spaces.Iθ,
              (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) / t ^ 4))
        (Set.Ioo 0 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_sliceMass_div_z4_of_HkMem hF) _
    refine MeasureTheory.Integrable.mono' (MeasureTheory.IntegrableOn.integrable hdom) ?_ ?_
    · exact (AEMeasurable.div
        ((hc.mono_measure MeasureTheory.Measure.restrict_le_self).pow_const 2)
        ((measurable_id.pow_const 4).aemeasurable)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := ht.1
      have hb := hbnd t ht0
      rw [Real.norm_of_nonneg (by positivity)]
      calc (cl t) ^ 2 / t ^ 4
          ≤ ((∫ θ in Work.Spaces.Iθ,
                (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              / Work.EllipticEst.ModalSolution.eNorm m) / t ^ 4 :=
            div_le_div_of_nonneg_right hb (by positivity)
        _ = (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
              * ((∫ θ in Work.Spaces.Iθ,
                  (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) / t ^ 4) := by
            ring_nf
  -- far `∞`: `∫_1^∞ c² < ∞`
  have hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (cl t) ^ 2) (Set.Ioi 1) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
          * (∫ θ in Work.Spaces.Iθ,
              (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        (Set.Ioi 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_sliceMass_Ioi_one_of_HkMem hF) _
    refine MeasureTheory.Integrable.mono' (MeasureTheory.IntegrableOn.integrable hdom) ?_ ?_
    · exact ((hc.mono_measure MeasureTheory.Measure.restrict_le_self).pow_const 2).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans one_pos ht
      have hb := hbnd t ht0
      rw [Real.norm_of_nonneg (by positivity)]
      calc (cl t) ^ 2
          ≤ ((∫ θ in Work.Spaces.Iθ,
                (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              / Work.EllipticEst.ModalSolution.eNorm m) := hb
        _ = (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
              * (∫ θ in Work.Spaces.Iθ,
                  (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            rw [div_eq_inv_mul]
  -- the radial Green's-function estimate
  have hE : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m cl z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0) :=
    radGreen_sq_w_sq_meas_engine hα hα4 hm hc hnear hfar
  -- replace the clamped coefficient by `cmode m F` (they agree on `(0,∞)`)
  have hEq : Set.EqOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m cl z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m
        (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m F t) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0) := by
    intro z hz
    show (Work.FTS.PhiStar.Radial.radGreen α m cl z) ^ 2 * (Work.Spaces.w z) ^ 2
      = (Work.FTS.PhiStar.Radial.radGreen α m
          (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m F t) z) ^ 2 * (Work.Spaces.w z) ^ 2
    rw [radGreen_congr_of_eqOn_Ioi (fun t ht => hcl_eq t ht) hz]
  have hE' := MeasureTheory.IntegrableOn.congr_fun hE hEq measurableSet_Ioi
  have hE'' := MeasureTheory.IntegrableOn.congr_set_ae hE'
    (MeasureTheory.Ioi_ae_eq_Ici).symm
  simpa only [Work.FTS.PhiStar.Series.acoeff, Work.Spaces.Iz] using hE''

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.StarPkgo2OfCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- `Fb n K f` gives the `FlatW n K f` consumed by `wlInf_of_zeroOff`. -/
private theorem Fb_to_FlatW {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (h : Fb n K f) :
    Work.FTS.VocabO2.FlatW n f K := by
  intro z θ hz hθ hθ2
  refine ⟨fun k _ => ?_, fun k i hki => ?_⟩
  · simpa using h.f0 k 0 (by omega) z θ hz hθ hθ2
  · exact h.fd k i (by omega) z θ hz hθ hθ2

/-- `Fb` transfers along pointwise equality on the open quadrant. -/
private theorem Fb_congr_p {n : ℕ} {K : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    (hg : Fb n K g) : Fb n K f := by
  refine ⟨Work.FTS.PhiStar.CoreAux.F0_congr h hg.f0, Work.FTS.PhiStar.CoreAux.F0_congr ?_ hg.fd⟩
  intro z θ hz hθ hθ'
  have hev : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun θ' => g z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (Real.pi / 2) from ⟨hθ, hθ'⟩)]
      with θ' hθ''
    exact h z θ' hz hθ''.1 hθ''.2
  exact hev.deriv_eq

theorem StarPkgo2OfCore : ∃ C : ℝ, 0 < C ∧ ∀ (α Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn),
    0 < α → α ≤ 1 / 4 → 0 < Cs → Work.FTS.VocabO2.StarCore α Cs Φs → Work.FTS.VocabO2.StarPkgo2 α (C * Cs) Φs := by
  obtain ⟨A0, hA0ge, hth1₀, hth2₀, hth3₀, hth4₀, hz1₀, hz2₀⟩ := StarPkgo2Aux.CoeffF0
  obtain ⟨C1, hC1pos, hFbFlat⟩ := Work.FTS.PhiStar.CoreAux.Fb_of_FlatW
  obtain ⟨Ce, hCepos, hEHb⟩ := StarPkgo2Aux.FbEH
  obtain ⟨Cv, hCvpos, hEVb⟩ := StarPkgo2Aux.FbEV
  obtain ⟨Cu, hCupos, hEUb⟩ := StarPkgo2Aux.FbEU
  obtain ⟨Cp, hCppos, hEPUb⟩ := StarPkgo2Aux.F0EPU
  obtain ⟨Cwd, hCwdpos, hWDp4⟩ := Work.FTS.PhiStar.CoreAux.F0_to_WDp 4
  obtain ⟨Cwd5, hCwd5pos, hWDp5⟩ := Work.FTS.PhiStar.CoreAux.F0_to_WDp 5
  obtain ⟨Cct, hCctpos, hCoeffTh⟩ := Work.FTS.PhiStar.CoreAux.F0_to_CoefTh 3
  obtain ⟨Cwl, hCwlpos, hWlInf⟩ := wlInf_of_zeroOff
  generalize hAdef : A0 + C1 + Ce + Cv + Cu + Cp + Cwd + Cwd5 + Cct + Cwl + 2 = A
  have hA1 : 1 ≤ A := by
    rw [← hAdef]; linarith [hA0ge, le_of_lt hC1pos, le_of_lt hCepos, le_of_lt hCvpos,
      le_of_lt hCupos, le_of_lt hCppos, le_of_lt hCwdpos, le_of_lt hCwd5pos,
      le_of_lt hCctpos, le_of_lt hCwlpos]
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA1
  have hA0A : A0 ≤ A := by rw [← hAdef]; linarith
  have hAC1 : C1 ≤ A := by rw [← hAdef]; linarith
  have hAe : Ce ≤ A := by rw [← hAdef]; linarith
  have hAv : Cv ≤ A := by rw [← hAdef]; linarith
  have hAu : Cu ≤ A := by rw [← hAdef]; linarith
  have hAp : Cp ≤ A := by rw [← hAdef]; linarith
  have hAwd : Cwd ≤ A := by rw [← hAdef]; linarith
  have hAwd5 : Cwd5 ≤ A := by rw [← hAdef]; linarith
  have hAct : Cct ≤ A := by rw [← hAdef]; linarith
  have hAwl : Cwl ≤ A := by rw [← hAdef]; linarith
  refine ⟨2 * A ^ 6 + 1, by positivity, ?_⟩
  intro α Cs Φs hα hα4 hCs hs
  have hα1 : α ≤ 1 := by linarith
  have hα2 : α + 1 ≤ 2 := by linarith
  have hS0 : 0 ≤ Cs * α := by positivity
  let Ψ : ℝ → ℝ → ℝ := Work.FTS.VocabO2.PhiTs α Φs
  let Y : ℝ → ℝ → ℝ := Work.FTS.VocabO2.Ycheck α Φs
  let fRW : ℝ → ℝ → ℝ :=
    fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
  let fV : ℝ → ℝ → ℝ := Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)
  let fVz : ℝ → ℝ → ℝ :=
    fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
  let fUs : ℝ → ℝ → ℝ :=
    fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ
  let fUsz : ℝ → ℝ → ℝ :=
    fun z θ => (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      / Work.Construction.s2 θ)
  let fDU : ℝ → ℝ → ℝ := Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs))
  have hsmΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    (Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs hα hα1 hs.smooth).1
  have hsmY : Work.FTS.EllipticEst.SmoothOpen Y :=
    (Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs hα hα1 hs.smooth).2.2
  have hFbY : Fb 6 (A * (Cs * α)) Y := by
    refine Fb.mono le_rfl ?_ (hFbFlat (Cs * α) Y (by positivity) hsmY hs.core)
    nlinarith [hAC1, hS0]
  have hsq : F0 6 A (fun _ θ => Real.sin θ ^ 2) := F0.mono le_rfl hA0A hth1₀
  have hccs : F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) :=
    F0.mono le_rfl hA0A hth2₀
  have hc2 : F0 6 A (fun _ θ => Real.cos (2 * θ)) := F0.mono le_rfl hA0A hth3₀
  have hsi : F0 6 A (fun _ θ => Real.sin (2 * θ)) := F0.mono le_rfl hA0A hth4₀
  have hcz : F0 6 A (fun z _ => z / (1 + z)) := F0.mono le_rfl hA0A hz1₀
  have hci : F0 6 A (fun z _ => (1 + z)⁻¹) := F0.mono le_rfl hA0A hz2₀
  have hident := StarPkgo2Aux.FieldIdents α Ψ Y hsmΨ (fun z θ _ => rfl)
  have hreg := StarPkgo2Aux.FieldRegularity α Ψ hsmΨ
  have hzer := StarPkgo2Aux.ZeroOffFields α Ψ hs.zeroOff
  -- ## the flat bounds of the clean expressions
  have hFbEH := hEHb α (Cs * α) A Y (le_of_lt hα) hS0 hA1 hsmY hsq hccs hc2 hsi hcz hci hFbY
  have hFbEV := hEVb α (Cs * α) A Y (le_of_lt hα) hS0 hA1 hsmY hsq hccs hc2 hsi hcz hci hFbY
  have hFbEU := hEUb α (Cs * α) A Y (le_of_lt hα) hS0 hA1 hsmY hsq hccs hc2 hsi hcz hci hFbY
  have hF0EPU := hEPUb α (Cs * α) A Y (le_of_lt hα) hS0 hA1 hsmY hsq hccs hc2 hsi hcz hci hFbY
  -- ## transfer to the actual fields
  have hFbRW : Fb 4 (Ce * A ^ 4 * (Cs * α) * (α + 1)) fRW :=
    Fb_congr_p (fun z θ hz hθ hθ2 => ((hident z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)).1).symm) hFbEH
  have hFbV : Fb 4 (Cv * A ^ 4 * (Cs * α) * (α + 1)) fV :=
    Fb_congr_p (fun z θ hz hθ hθ2 => ((hident z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)).2.1).symm) hFbEV.2
  have hFbVz : Fb 4 (Cv * A ^ 4 * (Cs * α) * (α + 1)) fVz :=
    Fb_congr_p (fun z θ hz hθ hθ2 => ((hident z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)).2.2.1).symm) hFbEV.1
  have hFbUs : Fb 4 (Cu * A ^ 4 * (Cs * α) * (α + 1)) fUs :=
    Fb_congr_p (fun z θ hz hθ hθ2 => ((hident z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)).2.2.2.1).symm) hFbEU.2
  have hFbUsz : Fb 4 (Cu * A ^ 4 * (Cs * α) * (α + 1)) fUsz :=
    Fb_congr_p (fun z θ hz hθ hθ2 => ((hident z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)).2.2.2.2.1).symm) hFbEU.1
  have hF0DU : F0 5 (Cp * A ^ 4 * (Cs * α) * (α + 1)) fDU :=
    Work.FTS.PhiStar.CoreAux.F0_congr
      (fun z θ hz hθ hθ2 => ((hident z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)).2.2.2.2.2).symm) hF0EPU
  -- ## the `𝒲`-bounds
  have hWlRW := hWlInf α fRW (Ce * A ^ 4 * (Cs * α) * (α + 1)) hα hα1
    hzer.1 hreg.1 (Fb_to_FlatW hFbRW)
  have hWlV := hWlInf α fV (Cv * A ^ 4 * (Cs * α) * (α + 1)) hα hα1
    hzer.2.1 hreg.2.1 (Fb_to_FlatW hFbV)
  have hWlVz := hWlInf α fVz (Cv * A ^ 4 * (Cs * α) * (α + 1)) hα hα1
    hzer.2.2.1 hreg.2.2.1 (Fb_to_FlatW hFbVz)
  have hWlUs := hWlInf α fUs (Cu * A ^ 4 * (Cs * α) * (α + 1)) hα hα1
    hzer.2.2.2.1 hreg.2.2.2.1 (Fb_to_FlatW hFbUs)
  have hWlUsz := hWlInf α fUsz (Cu * A ^ 4 * (Cs * α) * (α + 1)) hα hα1
    hzer.2.2.2.2 hreg.2.2.2.2.1 (Fb_to_FlatW hFbUsz)
  -- ## the old fields
  have hWDRW := hWDp4 (Ce * A ^ 4 * (Cs * α) * (α + 1)) fRW (by positivity) hreg.1 hFbRW.1
  have hWDV := hWDp4 (Cv * A ^ 4 * (Cs * α) * (α + 1)) fV (by positivity) hreg.2.1 hFbV.1
  have hWDDU := hWDp5 (Cp * A ^ 4 * (Cs * α) * (α + 1)) fDU (by positivity)
    hreg.2.2.2.2.2 hF0DU
  have hCfV := hCoeffTh (Cv * A ^ 4 * (Cs * α) * (α + 1)) fV (by positivity) hreg.2.1
    (F0.mono (by norm_num : 3 ≤ 4) le_rfl hFbV.2)
  -- ## the constant comparisons
  have hbig : ∀ x y : ℝ, 0 ≤ x → x ≤ A → 0 ≤ y → y ≤ A →
      x * (y * A ^ 4 * (Cs * α) * (α + 1)) ≤ ((2 * A ^ 6 + 1) * Cs) * α := by
    intro x y hx0 hxA hy0 hyA
    have hxy : x * y ≤ A * A := mul_le_mul hxA hyA hy0 (by linarith)
    have hA4 : 0 ≤ A ^ 4 := by positivity
    have h1 : A ^ 4 * (Cs * α) * (α + 1) ≤ A ^ 4 * (Cs * α) * 2 :=
      mul_le_mul_of_nonneg_left hα2 (by positivity)
    have h2 : x * (y * A ^ 4 * (Cs * α) * (α + 1)) ≤ (A * A) * (A ^ 4 * (Cs * α) * 2) := by
      rw [show x * (y * A ^ 4 * (Cs * α) * (α + 1))
        = (x * y) * (A ^ 4 * (Cs * α) * (α + 1)) from by ring]
      exact mul_le_mul hxy h1 (by positivity) (by positivity)
    have h3 : (A * A) * (A ^ 4 * (Cs * α) * 2) = 2 * A ^ 6 * (Cs * α) := by ring
    rw [h3] at h2
    have h4 : 2 * A ^ 6 * (Cs * α) ≤ ((2 * A ^ 6 + 1) * Cs) * α := by
      have h5 : 2 * A ^ 6 * (Cs * α) = (2 * A ^ 6) * (Cs * α) := by ring
      rw [h5]
      have h6 : 2 * A ^ 6 ≤ 2 * A ^ 6 + 1 := by linarith
      calc (2 * A ^ 6) * (Cs * α) ≤ (2 * A ^ 6 + 1) * (Cs * α) :=
            mul_le_mul_of_nonneg_right h6 hS0
        _ = ((2 * A ^ 6 + 1) * Cs) * α := by ring
    linarith
  -- ## `vanishU`
  have hvanish : Work.Spaces.VanishTheta (Work.Construction.Uop α Ψ) := by
    have hz0 : ∀ z : ℝ, (z, (0 : ℝ)) ∉ Work.FTS.EllipticEst.Q0 := by
      intro z hmem
      exact absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.1 (lt_irrefl 0)
    have hzπ : ∀ z : ℝ, (z, Real.pi / 2) ∉ Work.FTS.EllipticEst.Q0 := by
      intro z hmem
      exact absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.2 (lt_irrefl _)
    refine ⟨fun z => ?_, fun z => ?_⟩
    · show Work.Construction.Uop α Ψ z 0 = 0
      have h1 : Ψ z 0 = 0 := hs.zeroOff z 0 (hz0 z)
      have hsl : (fun z' : ℝ => Ψ z' 0) = fun _ => (0 : ℝ) :=
        funext (fun z' => hs.zeroOff z' 0 (hz0 z'))
      have h2 : Work.Spaces.pz Ψ z 0 = 0 := by
        simp only [Work.Spaces.pz]
        rw [hsl]
        simp
      simp only [Work.Construction.Uop, h1, h2]
      ring
    · show Work.Construction.Uop α Ψ z (Real.pi / 2) = 0
      have h1 : Ψ z (Real.pi / 2) = 0 := hs.zeroOff z (Real.pi / 2) (hzπ z)
      have hsl : (fun z' : ℝ => Ψ z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
        funext (fun z' => hs.zeroOff z' (Real.pi / 2) (hzπ z'))
      have h2 : Work.Spaces.pz Ψ z (Real.pi / 2) = 0 := by
        simp only [Work.Spaces.pz]
        rw [hsl]
        simp
      simp only [Work.Construction.Uop, h1, h2]
      ring
  exact
    { toStarPkgo :=
        { sol := hs.sol
          smooth := hs.smooth
          R := ⟨hWDRW.1, le_trans hWDRW.2 (hbig Cwd Ce (by positivity) hAwd (by positivity) hAe)⟩
          dU := ⟨hWDDU.1, le_trans hWDDU.2 (hbig Cwd5 Cp (by positivity) hAwd5 (by positivity) hAp)⟩
          V := ⟨hWDV.1, le_trans hWDV.2 (hbig Cwd Cv (by positivity) hAwd (by positivity) hAv)⟩
          vanishU := hvanish
          Vth := ⟨hCfV.1, le_trans hCfV.2 (hbig Cct Cv (by positivity) hAct (by positivity) hAv)⟩ }
      RW := ⟨hWlRW.1, le_trans hWlRW.2 (hbig Cwl Ce (by positivity) hAwl (by positivity) hAe)⟩
      VW := ⟨hWlV.1, le_trans hWlV.2 (hbig Cwl Cv (by positivity) hAwl (by positivity) hAv)⟩
      VzW := ⟨hWlVz.1, le_trans hWlVz.2 (hbig Cwl Cv (by positivity) hAwl (by positivity) hAv)⟩
      UsW := ⟨hWlUs.1, le_trans hWlUs.2 (hbig Cwl Cu (by positivity) hAwl (by positivity) hAu)⟩
      UszW := ⟨hWlUsz.1, le_trans hWlUsz.2 (hbig Cwl Cu (by positivity) hAwl (by positivity) hAu)⟩ }

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.SliceWrap =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false



end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.slotCrossLeGen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **General cross-slot Cauchy–Schwarz with a constant.**  Let `W` be any nonnegative weight
on the quadrant, and suppose that (on the open quadrant) the `W`-weighted squares of two
functions `X`, `Y` are pointwise dominated by the `ℋ^p`- resp. `ℋ^n`-integrands of a common
`f`.  If `P` is pointwise dominated by `C · W · |X| · |Y|`, then

  `|∫∫ P| ≤ C · |f|_{ℋ^p} · |f|_{ℋ^n}`.

This is the two-level Cauchy–Schwarz argument (`slotCrossLe` / `cs_slotInt_abs_le`): at each
radial slice the pointwise AM–GM estimate `W|X||Y| ≤ √(W X²)·√(W Y²)` turns `|P|` into a
multiple of the product of the two square roots, and Cauchy–Schwarz integrates the product of
the square roots first in `θ` and then in `z`. -/
theorem slotCrossLeGen {α : ℝ} {f X Y W P : ℝ → ℝ → ℝ} {p n : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hp : Work.Spaces.HkMem α p f) (hn : Work.Spaces.HkMem α n f)
    (hXc : ContinuousOn (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    (hYc : ContinuousOn (Function.uncurry Y) Work.FTS.EllipticEst.Q0)
    (hWc : ContinuousOn (Function.uncurry W) Work.FTS.EllipticEst.Q0)
    (hWnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 ≤ W z θ)
    (hdomX : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      W z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α p f z θ)
    (hdomY : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      W z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α n f z θ)
    (hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |P z θ| ≤ C * (W z θ * |X z θ| * |Y z θ|)) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, P z θ|
      ≤ C * Work.Spaces.HkNorm α p f * Work.Spaces.HkNorm α n f := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hAnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α p f z θ := fun z θ =>
    Work.Spaces.HkIntegrand_nonneg α p f z θ
  have hBnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α n f z θ := fun z θ =>
    Work.Spaces.HkIntegrand_nonneg α n f z θ
  -- ## the angular slice estimate
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, P z θ|
        ≤ C * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α p f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) := by
    intro z hz
    have hAslice : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α p f z θ)
        Work.Spaces.Iθ := hp.1 z hz
    have hBslice : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α n f z θ)
        Work.Spaces.Iθ := hn.1 z hz
    have hAmeas : AEStronglyMeasurable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α p f z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hAslice.aestronglyMeasurable
    have hBmeas : AEStronglyMeasurable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hBslice.aestronglyMeasurable
    have hAsq : Integrable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α p f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      hAslice.congr (Eventually.of_forall (fun θ => (Real.sq_sqrt (hAnn z θ)).symm))
    have hBsq : Integrable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      hBslice.congr (Eventually.of_forall (fun θ => (Real.sq_sqrt (hBnn z θ)).symm))
    have hAlp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α p f z θ)) 2
        (volume.restrict Work.Spaces.Iθ) :=
      (memLp_two_iff_integrable_sq hAmeas).mpr hAsq
    have hBlp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)) 2
        (volume.restrict Work.Spaces.Iθ) :=
      (memLp_two_iff_integrable_sq hBmeas).mpr hBsq
    have hprodθ : Integrable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α p f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      memLp_one_iff_integrable.mp (hAlp.mul hBlp)
    have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        |P z θ| ≤ C * (Real.sqrt (Work.Spaces.HkIntegrand α p f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)) := by
      filter_upwards [Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ] with θ hθ
      have hgm : W z θ * |X z θ| * |Y z θ|
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α p f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ) :=
        Work.FTS.StrongPersist.H6Pair6Aux.leaf_prod_sqrt_le (hWnn z hz θ hθ)
          (hdomX z hz θ hθ) (hdomY z hz θ hθ)
      exact le_trans (hP z hz θ hθ) (mul_le_mul_of_nonneg_left hgm hC)
    have hmain : (∫ θ in Work.Spaces.Iθ, |P z θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, C * (Real.sqrt (Work.Spaces.HkIntegrand α p f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)) :=
      integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _)
        (hprodθ.const_mul C) hpt
    calc |∫ θ in Work.Spaces.Iθ, P z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |P z θ| := abs_integral_le_integral_abs
      _ ≤ ∫ θ in Work.Spaces.Iθ, C * (Real.sqrt (Work.Spaces.HkIntegrand α p f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)) := hmain
      _ = C * ∫ θ in Work.Spaces.Iθ, (Real.sqrt (Work.Spaces.HkIntegrand α p f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)) := integral_const_mul C _
      _ ≤ C * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α p f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) :=
          mul_le_mul_of_nonneg_left
            (Work.FTS.StrongPersist.H6Pair6Aux.cs_sqrt_le_fts hAslice hBslice
              (fun θ => hAnn z θ) (fun θ => hBnn z θ)) hC
  -- ## the radial Cauchy–Schwarz
  have hFint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α p f z θ) Work.Spaces.Iz := hp.2
  have hGint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α n f z θ) Work.Spaces.Iz := hn.2
  have hFnn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α p f z θ :=
    fun z => integral_nonneg fun θ => hAnn z θ
  have hGnn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ :=
    fun z => integral_nonneg fun θ => hBnn z θ
  have houter : IntegrableOn (fun z =>
      Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α p f z θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ))
      Work.Spaces.Iz := by
    have h1meas : AEStronglyMeasurable
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α p f z θ))
        (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hFint.aestronglyMeasurable
    have h2meas : AEStronglyMeasurable
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ))
        (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hGint.aestronglyMeasurable
    have h1sq : Integrable
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α p f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) :=
      hFint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hFnn z)).symm))
    have h2sq : Integrable
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) :=
      hGint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hGnn z)).symm))
    have h1lp : MemLp
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α p f z θ)) 2
        (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq h1meas).mpr h1sq
    have h2lp : MemLp
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) 2
        (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq h2meas).mpr h2sq
    exact memLp_one_iff_integrable.mp (h1lp.mul h2lp)
  have hstep1o : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, P z θ|
      ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, P z θ| :=
    abs_integral_le_integral_abs
  have hstep2o : (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, P z θ|)
      ≤ ∫ z in Work.Spaces.Iz, C * (Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α p f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _)
      (houter.const_mul C) (ae_restrict_of_forall_mem hIzm hslice)
  have hstep3o : (∫ z in Work.Spaces.Iz, C * (Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α p f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)))
      = C * ∫ z in Work.Spaces.Iz, (Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α p f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) :=
    integral_const_mul C _
  have hCS : (∫ z in Work.Spaces.Iz, (Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α p f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)))
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α p f z θ)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α n f z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.cs_sqrt_le_fts hFint hGint hFnn hGnn
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, P z θ|
      ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, P z θ| := hstep1o
    _ ≤ ∫ z in Work.Spaces.Iz, C * (Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α p f z θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) := hstep2o
    _ = C * ∫ z in Work.Spaces.Iz, (Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α p f z θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) := hstep3o
    _ ≤ C * (Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α p f z θ)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α n f z θ)) := mul_le_mul_of_nonneg_left hCS hC
    _ = C * Work.Spaces.HkNorm α p f * Work.Spaces.HkNorm α n f := by
        simp only [Work.Spaces.HkNorm, Work.Spaces.HkSq]
        ring

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.coefData_pert =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open scoped Real Topology

set_option autoImplicit false




end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6Gam.b1gDefs =====
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
/-! ## Definitions of the `b1fiveGamRowDz` integrand and slice functionals -/

/-- The `z`-slice functional of the `γ`-weighted slot `D_zD_θf`. -/
noncomputable def b1gPz (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
    * (Work.Spaces.mixed 1 1 f z θ) ^ 2

/-- The integrand of `b1fiveGamRowDz`. -/
noncomputable def b1gF (α : ℝ) (A f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun p =>
  Work.FTS.TransportS.leafGam α p.1 p.2
    * Work.Spaces.mixed 5 0 A p.1 p.2
    * Work.Spaces.mixed 1 1 f p.1 p.2
    * Work.Spaces.mixed 5 1 f p.1 p.2

theorem b1gF_apply (α : ℝ) (A f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    b1gF α A f p = Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed 5 0 A p.1 p.2
      * Work.Spaces.mixed 1 1 f p.1 p.2
      * Work.Spaces.mixed 5 1 f p.1 p.2 := rfl

theorem b1gPz_apply (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    b1gPz α f z = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed 1 1 f z θ) ^ 2 := rfl

/-- Continuity of `σ^{-γ}·|mixed 1 1 f|·|mixed 5 1 f|` on the open quadrant. -/
theorem contOn_sig_abs11 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ =>
        (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed 1 1 f p.1 p.2| * |Work.Spaces.mixed 5 1 f p.1 p.2|))
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => |Work.Spaces.mixed 1 1 f p.1 p.2|)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (h.mixed 1 1)).abs
  have h2 : ContinuousOn (fun p : ℝ × ℝ => |Work.Spaces.mixed 5 1 f p.1 p.2|)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (h.mixed 5 1)).abs
  have hs : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))
      Work.FTS.EllipticEst.Q0 := by
    have h3 : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    refine h3.rpow_const (fun p hp => Or.inl ?_)
    exact ne_of_gt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_pos_of_Ioo
      ⟨(Work.FTS.EllipticEst.mem_Q0.mp hp).2.1, (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2⟩)
  exact hs.mul (h1.mul h2)

/-! ## Slice integrability of the `b1gF` integrand -/

theorem b1gSliceInt : ∀ (α : ℝ) (A f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f →
    ∀ z : ℝ, 0 < z →
      MeasureTheory.Integrable (fun θ => |b1gF α A f (z, θ)|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  intro α A f hα0 hα1 hA hf h6A h6f z hz
  have hWint := Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.integrableOn_gamMixed_slice
    (b := 1) (a := 1) hα0 hf h6f le_rfl (by norm_num) hz
  have hZint := Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.integrableOn_gamMixed_slice
    (b := 5) (a := 1) hα0 hf h6f le_rfl (by norm_num) hz
  have hg : MeasureTheory.Integrable (fun θ => (Work.Spaces.w z) ^ 2
      * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
      * (((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 1 1 f z θ) ^ 2
          + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (((hWint.add hZint)).div_const 2).const_mul _
  refine MeasureTheory.Integrable.mono' hg ?_ ?_
  · refine Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => |b1gF α A f p|) ?_ hz
    simp only [b1gF_apply]
    exact ((((Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.contOn_leafGam α).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hA.mixed 5 0))).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hf.mixed 1 1))).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn
        (hf.mixed 5 1))).abs
  · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
    have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Real.rpow_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_nonneg_of_Iθ' hθ) _
    have hcoefnn : 0 ≤ Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z := by
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
    have hX2 : |Work.Spaces.DzIter 5 A z θ|
        ≤ Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z) := by
      rw [← Real.sqrt_sq_eq_abs]
      refine Real.sqrt_le_sqrt ?_
      rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX_apply]
      exact Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xSliceAgmon5 α A hα0 hα1 hA h6A
        z θ hz hθ0 hθ1
    have habsF : |b1gF α A f (z, θ)| = (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.DzIter 5 A z θ|
          * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|) := by
      simp only [b1gF_apply, Work.FTS.TransportS.leafGam, Work.Spaces.mixed_zero_right]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) hσnn)]
      ring
    rw [Real.norm_of_nonneg (abs_nonneg _), habsF]
    have hAM : |Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|
        ≤ ((Work.Spaces.mixed 1 1 f z θ) ^ 2 + (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|Work.Spaces.mixed 1 1 f z θ| - |Work.Spaces.mixed 5 1 f z θ|),
        sq_abs (Work.Spaces.mixed 1 1 f z θ), sq_abs (Work.Spaces.mixed 5 1 f z θ)]
    calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.DzIter 5 A z θ|
          * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.DzIter 5 A z θ|
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
            * (((Work.Spaces.mixed 1 1 f z θ) ^ 2 + (Work.Spaces.mixed 5 1 f z θ) ^ 2)
              / 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg _) hσnn)
            exact mul_le_mul hX2 hAM (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              (Real.sqrt_nonneg _)
      _ = (Work.Spaces.w z) ^ 2
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
          * (((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 1 1 f z θ) ^ 2
            + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2) := by
            ring
end

end Work.FTS.StrongPersist.H6Row6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.ResidPtOfGo =====
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

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkNorm)

set_option autoImplicit false
set_option linter.unusedVariables false


end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.EU6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/StrongPersist/SP6/EU6.lean` — the order-six flat bound of the `EU`-star-field

`Work.FTS.PhiStar.EU α Y = -(z/(z+1))·Wone α Y` with
`Wone α Y = 3Y + α(Y/(z+1) + z ∂_zY)`, and `EUz α Y = -Wone α Y`.  This file proves the
order-six flat bound

`FlatW 6 (EU α Y) (C·(α+1)·(K + KY + KD))`

from `SmoothOpen Y`, `FlatW 7 Y K`, `Fb 6 KY Y` and `F0 6 KD (Yblk Y)`, with a constant which
is **linear** in `K + KY + KD`.

## The route

`EU α Y = -(z/(z+1))·EUz α Y` and `FlatW 6` is the pair (`F0 6`, `F0 5 ∘ ∂_θ`) — this is
`flatW6_of_F0`.  So it suffices to prove the strong pair

* `F0 6 (EUR α Y)` — the reassociated field `(z/(z+1))·EUzR α Y`,
* `F0 5 (pth (EUR α Y))`, identified with `F0 5 (EUD α Y)` through the pointwise identity
  `∂_θ(EUR α Y) = EUD α Y` on the open quadrant (the radial factor `z/(1+z)` is `θ`-free and
  `∂_θ(EUzR α Y) = EUzD α Y`, which is the product rule plus
  `∂_θ(D_zY) = D_z(∂_θY)`, i.e. `Fb_zpz.pth_zpz_smoothOpen`).

Both halves are then pure flat calculus (`F0_mul`, `F0_add`, `F0_const_mul`, `F0_congr`) against
the block bounds of `Flat6Defs.atomData` and the coefficient bounds of `Flat6Defs.CoefBundle6s`
(the two radial factors `z/(1+z)`, `(1+z)⁻¹`).  The auxiliary definition `EUzB` is the
*un-negated* body `3Y + α((1+z)⁻¹Y + D_zY)`; both `EUzR α Y = -EUzB α Y` and
`EUzD α Y = -EUzB α (∂_θY)` hold by `rfl`, which makes the negation bookkeeping trivial.

The order-four analogue of this statement is `PhiStar/CoreAux/Fb_EU_bound.lean`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.SP6

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The un-negated `EUz`-body -/

/-- The un-negated body of `EUz`: `EUzB α Y = 3Y + α(Y/(z+1) + D_zY)`.  The two identities
`EUzR α Y = -EUzB α Y` and `EUzD α Y = -EUzB α (∂_θY)` hold definitionally. -/
def EUzB (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ) + α * Work.FTS.PhiStar.Yblk Y z θ



/-! ## Elementary flat-calculus helpers -/

/-- `∂_θ` of a multiple by a factor depending on `z` alone. -/
theorem pth_zM (g : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => g z * f z θ) = fun z θ => g z * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  exact deriv_const_mul_field (g z)

/-- `Yblk Y = z ∂_zY` is smooth on the open quadrant when `Y` is. -/
theorem sYblk {Y : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.PhiStar.Yblk Y) := h.Dz

/-- Negation preserves smoothness on the open quadrant. -/
theorem smoothOpen_neg_S {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => -f z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ : ℝ => -f z θ)
      = fun p : ℝ × ℝ => -(Function.uncurry f p) := rfl
  rw [h]
  exact hf.neg


/-! ## Smoothness of the two `EUz`-bodies -/

theorem smoothOpen_EUzB (α : ℝ) (Y : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (EUzB α Y) := by
  have s1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 3 * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts 3 hsm
  have s2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α
      (Work.FTS.PhiStar.CoreAux.smoothOpen_mul_fts
        Work.FTS.PhiStar.CoreAux.smoothOpen_inv_one_plus_z_fts hsm)
  have s3 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * Work.FTS.PhiStar.Yblk Y z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α (sYblk hsm)
  exact Work.FTS.PhiStar.CoreAux.smoothOpen_add_fts
    (Work.FTS.PhiStar.CoreAux.smoothOpen_add_fts s1 s2) s3

theorem smoothOpen_EUzR (α : ℝ) (Y : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (EUzR α Y) := by
  change Work.FTS.EllipticEst.SmoothOpen (fun z θ => -EUzB α Y z θ)
  exact smoothOpen_neg_S (smoothOpen_EUzB α Y hsm)

theorem smoothOpen_EUzD (α : ℝ) (Y : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (EUzD α Y) := by
  change Work.FTS.EllipticEst.SmoothOpen (fun z θ => -EUzB α (Work.Spaces.pth Y) z θ)
  exact smoothOpen_neg_S (smoothOpen_EUzB α (Work.Spaces.pth Y) hsm.pth)

/-! ## The pointwise `θ`-derivative identities -/

/-- `∂_θ(EUzB α Y) = EUzB α (∂_θY)` on the open quadrant. -/
theorem pth_EUzB (α : ℝ) (Y : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EUzB α Y) z θ = EUzB α (Work.Spaces.pth Y) z θ := by
  intro z θ hz hθ hθ'
  have s1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 3 * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts 3 hsm
  have s2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α
      (Work.FTS.PhiStar.CoreAux.smoothOpen_mul_fts
        Work.FTS.PhiStar.CoreAux.smoothOpen_inv_one_plus_z_fts hsm)
  have s3 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * Work.FTS.PhiStar.Yblk Y z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α (sYblk hsm)
  have hW1 : Work.Spaces.pth (fun z θ : ℝ => 3 * Y z θ) z θ = 3 * Work.Spaces.pth Y z θ :=
    congrFun (congrFun (Work.FTS.PhiStar.CoreAux.pth_const_mul 3 Y) z) θ
  have hW2 : Work.Spaces.pth (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ)) z θ
      = α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ) := by
    rw [congrFun (congrFun (Work.FTS.PhiStar.CoreAux.pth_const_mul α
      (fun z θ : ℝ => (1 + z)⁻¹ * Y z θ)) z) θ]
    rw [congrFun (congrFun (pth_zM (fun z => (1 + z)⁻¹) Y) z) θ]
  have hW3 : Work.Spaces.pth (fun z θ : ℝ => α * Work.FTS.PhiStar.Yblk Y z θ) z θ
      = α * Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y) z θ := by
    rw [congrFun (congrFun (Work.FTS.PhiStar.CoreAux.pth_const_mul α
      (Work.FTS.PhiStar.Yblk Y)) z) θ]
    show α * Work.Spaces.pth (fun z θ => z * Work.Spaces.pz Y z θ) z θ
      = α * Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y) z θ
    rw [Work.FTS.PhiStar.CoreAux.pth_zpz_smoothOpen (f := Y) hsm z θ hz hθ hθ']
    rfl
  have h12 : Work.Spaces.pth (fun z θ : ℝ => 3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ)) z θ
      = 3 * Work.Spaces.pth Y z θ + α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ) := by
    rw [Work.FTS.PhiStar.CoreAux.pth_add_Q0 s1 s2 z θ hz hθ hθ', hW1, hW2]
  have h123 : Work.Spaces.pth (fun z θ : ℝ =>
      (3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ)) + α * Work.FTS.PhiStar.Yblk Y z θ) z θ
      = (3 * Work.Spaces.pth Y z θ + α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ))
        + α * Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y) z θ := by
    rw [Work.FTS.PhiStar.CoreAux.pth_add_Q0
      (Work.FTS.PhiStar.CoreAux.smoothOpen_add_fts s1 s2) s3 z θ hz hθ hθ', h12, hW3]
  exact h123

/-- `∂_θ(EUzR α Y) = EUzD α Y` on the open quadrant. -/
theorem pth_EUzR (α : ℝ) (Y : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EUzR α Y) z θ = EUzD α Y z θ := by
  intro z θ hz hθ hθ'
  have h1 : Work.Spaces.pth (EUzR α Y) z θ = -(Work.Spaces.pth (EUzB α Y) z θ) := by
    change Work.Spaces.pth (-EUzB α Y) z θ = -(Work.Spaces.pth (EUzB α Y) z θ)
    exact congrFun (congrFun (Work.FTS.EllipticEst.pth_neg (EUzB α Y)) z) θ
  rw [h1, pth_EUzB α Y hsm z θ hz hθ hθ']
  rfl

/-- `∂_θ(EUR α Y) = EUD α Y` on the open quadrant (`z/(1+z)` is `θ`-free). -/
theorem pth_EUR (α : ℝ) (Y : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EUR α Y) z θ = EUD α Y z θ := by
  intro z θ hz hθ hθ'
  have h1 : Work.Spaces.pth (EUR α Y) z θ
      = (z / (1 + z)) * Work.Spaces.pth (EUzR α Y) z θ := by
    change Work.Spaces.pth (fun z θ => (z / (1 + z)) * EUzR α Y z θ) z θ
      = (z / (1 + z)) * Work.Spaces.pth (EUzR α Y) z θ
    exact congrFun (congrFun (pth_zM (fun z => z / (1 + z)) (EUzR α Y)) z) θ
  rw [h1, pth_EUzR α Y hsm z θ hz hθ hθ']
  rfl

/-! ## The `F0`-bounds of the two `EUz`-bodies -/

/-- **`F0 6` of `EUzR`.**  The bound is `3KY + α(2⁶AKY) + αKD`, linear in `KY`, `KD`. -/
theorem F0_EUzR (α K KY KD A : ℝ) (Y : ℝ → ℝ → ℝ)
    (hα : 0 ≤ α) (hA0 : 0 ≤ A) (hKY : 0 ≤ KY) (hKD : 0 ≤ KD)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Y)
    (hY : Work.FTS.PhiStar.F0 6 KY Y) (hD : Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y))
    (hrhoinv : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => (1 + z)⁻¹))
    (srhoinv : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 + z)⁻¹)) :
    Work.FTS.PhiStar.F0 6 (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD)) (EUzR α Y) := by
  have hW1 : Work.FTS.PhiStar.F0 6 (3 * KY) (fun z θ : ℝ => 3 * Y z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (3 : ℝ) hY
    simpa using h
  have hInv : Work.FTS.PhiStar.F0 6 (2 ^ 6 * A * KY) (fun z θ : ℝ => (1 + z)⁻¹ * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul hA0 hKY srhoinv hsm hrhoinv hY
  have hW2 : Work.FTS.PhiStar.F0 6 (α * (2 ^ 6 * A * KY))
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ)) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul α hInv
    rwa [abs_of_nonneg hα] at h
  have hW3 : Work.FTS.PhiStar.F0 6 (α * KD)
      (fun z θ : ℝ => α * Work.FTS.PhiStar.Yblk Y z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul α hD
    rwa [abs_of_nonneg hα] at h
  have s1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 3 * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts 3 hsm
  have s2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α
      (Work.FTS.PhiStar.CoreAux.smoothOpen_mul_fts srhoinv hsm)
  have s3 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * Work.FTS.PhiStar.Yblk Y z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α (sYblk hsm)
  have h12 := Work.FTS.PhiStar.CoreAux.F0_add s1 s2 hW1 hW2
  have h123 := Work.FTS.PhiStar.CoreAux.F0_add
    (Work.FTS.PhiStar.CoreAux.smoothOpen_add_fts s1 s2) s3 h12 hW3
  have hneg : Work.FTS.PhiStar.F0 6 (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
      (fun z θ : ℝ => -EUzB α Y z θ) := by
    have h := h123
    have hc : (3 * KY + α * (2 ^ 6 * A * KY)) + α * KD
        = 3 * KY + (α * (2 ^ 6 * A * KY) + α * KD) := by ring
    rw [hc] at h
    have h2 := Work.FTS.PhiStar.CoreAux.F0_const_mul (-1 : ℝ) h
    have h3 : (|(-1 : ℝ)| * (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD)))
        = (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD)) := by
      rw [abs_neg, abs_one, one_mul]
    rw [h3] at h2
    refine Work.FTS.PhiStar.CoreAux.F0_congr
      (g := fun z θ : ℝ => (-1 : ℝ) * ((3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ))
        + α * Work.FTS.PhiStar.Yblk Y z θ)) (fun z θ _ _ _ => ?_) h2
    simp only [EUzB]
    ring
  refine Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => ?_) hneg
  simp only [EUzR]
  rfl

/-- **`F0 5` of `EUzD`.**  The bound is `3(K+KY) + α(2⁵A(K+KY)) + α·6(K+KY)`, linear in the
blocks. -/
theorem F0_EUzD (α K KY KD A : ℝ) (Y : ℝ → ℝ → ℝ)
    (hα : 0 ≤ α) (hA0 : 0 ≤ A) (hKY : 0 ≤ KY) (hKPY : 0 ≤ K + KY)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Y)
    (hP : Work.FTS.PhiStar.F0 6 (K + KY) (Work.Spaces.pth Y))
    (hZp : Work.FTS.PhiStar.F0 5 (6 * (K + KY)) (Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y)))
    (hrhoinv : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => (1 + z)⁻¹))
    (srhoinv : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 + z)⁻¹)) :
    Work.FTS.PhiStar.F0 5
      (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))) (EUzD α Y) := by
  have hP5 : Work.FTS.PhiStar.F0 5 (K + KY) (Work.Spaces.pth Y) := hP.mono (by norm_num) le_rfl
  have hW1 : Work.FTS.PhiStar.F0 5 (3 * (K + KY))
      (fun z θ : ℝ => 3 * Work.Spaces.pth Y z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (3 : ℝ) hP5
    simpa using h
  have hInv : Work.FTS.PhiStar.F0 5 (2 ^ 5 * A * (K + KY))
      (fun z θ : ℝ => (1 + z)⁻¹ * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul hA0 hKPY srhoinv hsm.pth
      (hrhoinv.mono (by norm_num) le_rfl) hP5
  have hW2 : Work.FTS.PhiStar.F0 5 (α * (2 ^ 5 * A * (K + KY)))
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ)) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul α hInv
    rwa [abs_of_nonneg hα] at h
  have hW3 : Work.FTS.PhiStar.F0 5 (α * (6 * (K + KY)))
      (fun z θ : ℝ => α * Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y) z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul α hZp
    rwa [abs_of_nonneg hα] at h
  have s1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 3 * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts 3 hsm.pth
  have s2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α
      (Work.FTS.PhiStar.CoreAux.smoothOpen_mul_fts srhoinv hsm.pth)
  have s3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => α * Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y) z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α (sYblk hsm.pth)
  have h12 := Work.FTS.PhiStar.CoreAux.F0_add s1 s2 hW1 hW2
  have h123 := Work.FTS.PhiStar.CoreAux.F0_add
    (Work.FTS.PhiStar.CoreAux.smoothOpen_add_fts s1 s2) s3 h12 hW3
  have hneg : Work.FTS.PhiStar.F0 5
      (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))))
      (fun z θ : ℝ => -EUzB α (Work.Spaces.pth Y) z θ) := by
    have h := h123
    have hc : (3 * (K + KY) + α * (2 ^ 5 * A * (K + KY))) + α * (6 * (K + KY))
        = 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))) := by ring
    rw [hc] at h
    have h2 := Work.FTS.PhiStar.CoreAux.F0_const_mul (-1 : ℝ) h
    have h3 : (|(-1 : ℝ)| * (3 * (K + KY)
          + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))))
        = (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))) := by
      rw [abs_neg, abs_one, one_mul]
    rw [h3] at h2
    refine Work.FTS.PhiStar.CoreAux.F0_congr
      (g := fun z θ : ℝ => (-1 : ℝ) * ((3 * Work.Spaces.pth Y z θ
        + α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ))
        + α * Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y) z θ)) (fun z θ _ _ _ => ?_) h2
    simp only [EUzB]
    ring
  refine Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => ?_) hneg
  simp only [EUzD]
  rfl

/-! ## The radial multiplications -/

theorem F0_EUR (α A BU : ℝ) (Y : ℝ → ℝ → ℝ) (hA0 : 0 ≤ A) (hBU : 0 ≤ BU)
    (srho : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)))
    (sEUzR : Work.FTS.EllipticEst.SmoothOpen (EUzR α Y))
    (hrho : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => z / (1 + z)))
    (hEUzR : Work.FTS.PhiStar.F0 6 BU (EUzR α Y)) :
    Work.FTS.PhiStar.F0 6 (2 ^ 6 * A * BU) (EUR α Y) := by
  have h := Work.FTS.PhiStar.CoreAux.F0_mul hA0 hBU srho sEUzR hrho hEUzR
  exact h

theorem F0_EUD (α A BE : ℝ) (Y : ℝ → ℝ → ℝ) (hA0 : 0 ≤ A) (hBE : 0 ≤ BE)
    (srho : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)))
    (sEUzD : Work.FTS.EllipticEst.SmoothOpen (EUzD α Y))
    (hrho : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => z / (1 + z)))
    (hEUzD : Work.FTS.PhiStar.F0 5 BE (EUzD α Y)) :
    Work.FTS.PhiStar.F0 5 (2 ^ 5 * A * BE) (EUD α Y) := by
  have h := Work.FTS.PhiStar.CoreAux.F0_mul hA0 hBE srho sEUzD
    (hrho.mono (by norm_num) le_rfl) hEUzD
  exact h

/-! ## The elementary absorption `αᵐ Aʲ x ≤ (A+1)²(α+1)S` -/

/-- `A·x ≤ (A+1)²(α+1)S` for `0 ≤ x ≤ S`, `1 ≤ A`, `0 ≤ α`. -/
theorem leM1 {A α S x : ℝ} (hA : 1 ≤ A) (hα : 0 ≤ α) (hx : 0 ≤ x) (hxS : x ≤ S) :
    A * x ≤ (A + 1) ^ 2 * (α + 1) * S := by
  have hA1 : (0 : ℝ) < A + 1 := by linarith
  have hS : 0 ≤ S := le_trans hx hxS
  have h1 : A * x ≤ (A + 1) * S := by
    calc A * x ≤ (A + 1) * x := mul_le_mul_of_nonneg_right (by linarith) hx
      _ ≤ (A + 1) * S := mul_le_mul_of_nonneg_left hxS hA1.le
  have h2 : (A + 1) * S ≤ (A + 1) ^ 2 * (α + 1) * S :=
    mul_le_mul_of_nonneg_right (by nlinarith : A + 1 ≤ (A + 1) ^ 2 * (α + 1)) hS
  linarith

/-- `α·A·x ≤ (A+1)²(α+1)S` for `0 ≤ x ≤ S`, `1 ≤ A`, `0 ≤ α`. -/
theorem leM2 {A α S x : ℝ} (hA : 1 ≤ A) (hα : 0 ≤ α) (hx : 0 ≤ x) (hxS : x ≤ S) :
    α * A * x ≤ (A + 1) ^ 2 * (α + 1) * S := by
  have hA0 : 0 ≤ A := by linarith
  have hS : 0 ≤ S := le_trans hx hxS
  have h1 : α * A * x ≤ (α + 1) * (A + 1) * S := by
    have hbc : A * x ≤ (A + 1) * S := by
      calc A * x ≤ (A + 1) * x := mul_le_mul_of_nonneg_right (by linarith) hx
        _ ≤ (A + 1) * S := mul_le_mul_of_nonneg_left hxS (by linarith)
    calc α * A * x = α * (A * x) := by ring
      _ ≤ (α + 1) * ((A + 1) * S) :=
          mul_le_mul (by linarith) hbc (mul_nonneg hA0 hx) (by linarith)
      _ = (α + 1) * (A + 1) * S := by ring
  have h2 : (α + 1) * (A + 1) * S ≤ (A + 1) ^ 2 * (α + 1) * S := by
    have hc : A + 1 ≤ (A + 1) ^ 2 := by nlinarith
    calc (α + 1) * (A + 1) * S = (α + 1) * ((A + 1) * S) := by ring
      _ ≤ (α + 1) * ((A + 1) ^ 2 * S) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hS) (by linarith)
      _ = (A + 1) ^ 2 * (α + 1) * S := by ring
  linarith

/-- `α·A²·x ≤ (A+1)²(α+1)S` for `0 ≤ x ≤ S`, `1 ≤ A`, `0 ≤ α`. -/
theorem leM3 {A α S x : ℝ} (hA : 1 ≤ A) (hα : 0 ≤ α) (hx : 0 ≤ x) (hxS : x ≤ S) :
    α * A ^ 2 * x ≤ (A + 1) ^ 2 * (α + 1) * S := by
  have hA0 : 0 ≤ A := by linarith
  have hA10 : 0 ≤ A + 1 := by linarith
  have hA2 : A ^ 2 ≤ (A + 1) ^ 2 := pow_le_pow_left₀ hA0 (by linarith) 2
  calc α * A ^ 2 * x = α * (A ^ 2 * x) := by ring
    _ ≤ (α + 1) * ((A + 1) ^ 2 * S) :=
        mul_le_mul (by linarith) (mul_le_mul hA2 hxS hx (pow_nonneg hA10 2))
          (mul_nonneg (pow_nonneg hA0 2) hx) (by linarith)
    _ = (A + 1) ^ 2 * (α + 1) * S := by ring

/-! ## The target -/

/-- **The order-six flat bound of the `EU`-star-field**, `EU α Y = -(z/(z+1))·Wone α Y`.

Prove `FlatW 6 (EU α Y) M` with `M := C·(α+1)·(K+KY+KD)` from `SmoothOpen Y`, `FlatW 7 Y K`,
`Fb 6 KY Y`, `F0 6 KD (Yblk Y)`; the constant must stay **linear** in `K + KY + KD`.

Import `Submission.Work.FTS.StrongPersist.SP6.Flat6Defs`: `CoefBundle6s`, `atomData`,
`EUzR`/`EUzD`, `EUR`/`EUD` and `euEUR_eq`, `flatW6_of_F0`, `FlatW_mono6`, `mono_const`,
`pth_thetaOnly`. Recommended route: prove the strong pair `F0 6 (EUR α Y)` and
`F0 5 (pth (EUR α Y)) = F0 5 (EUD α Y)` (`z/(z+1)` is `θ`-free), where the `EUz`-parts are the
same estimates as in the `EUz`-task; then `F0_congr` + `flatW6_of_F0`. The sibling
`Submission/Work/FTS/PhiStar/CoreAux/Fb_EU_bound.lean` proves the order-**four** version of the
joint statement for `EUz` and `EU`. -/
theorem EU6 : ∃ C : ℝ, 0 < C ∧ ∀ (α K KY KD : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 0 ≤ KY → 0 ≤ KD → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.VocabO2.FlatW 7 Y K → Work.FTS.PhiStar.Fb 6 KY Y →
    Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) →
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EU α Y) (C * (α + 1) * (K + KY + KD)) := by
  obtain ⟨A, hA1, hcoef⟩ := CoefBundle6s
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hrF : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => z / (1 + z)) :=
    (hcoef (fun z _ : ℝ => z / (1 + z)) (by simp [coefFun])).1
  have srF : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) :=
    (hcoef (fun z _ : ℝ => z / (1 + z)) (by simp [coefFun])).2
  have hiF : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => (1 + z)⁻¹) :=
    (hcoef (fun z _ : ℝ => (1 + z)⁻¹) (by simp [coefFun])).1
  have siF : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 + z)⁻¹) :=
    (hcoef (fun z _ : ℝ => (1 + z)⁻¹) (by simp [coefFun])).2
  refine ⟨5000 * (A + 1) ^ 2, by positivity, ?_⟩
  intro α K KY KD Y hα hK hKY hKD hsm hW hFb hD
  obtain ⟨hY6, hP6, hD6, hZp5, _hDthP5⟩ := atomData hK hKY hKD hsm hW hFb hD
  have hKPY : 0 ≤ K + KY := by linarith
  have hEUzR6 := F0_EUzR α K KY KD A Y hα hA0 hKY hKD hsm hY6 hD6 hiF siF
  have hEUzD5 := F0_EUzD α K KY KD A Y hα hA0 hKY hKPY hsm hP6 hZp5 hiF siF
  have sEUzR := smoothOpen_EUzR α Y hsm
  have sEUzD := smoothOpen_EUzD α Y hsm
  have BU6nn : 0 ≤ 3 * KY + (α * (2 ^ 6 * A * KY) + α * KD) := by
    have h1 : 0 ≤ α * (2 ^ 6 * A * KY) :=
      mul_nonneg hα (mul_nonneg (mul_nonneg (by positivity) hA0) hKY)
    have h2 : 0 ≤ α * KD := mul_nonneg hα hKD
    have h3 : 0 ≤ 3 * KY := by linarith
    linarith
  have BE5nn : 0 ≤ 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))) := by
    have h1 : 0 ≤ α * (2 ^ 5 * A * (K + KY)) :=
      mul_nonneg hα (mul_nonneg (mul_nonneg (by positivity) hA0) hKPY)
    have h2 : 0 ≤ α * (6 * (K + KY)) := mul_nonneg hα (by linarith)
    have h3 : 0 ≤ 3 * (K + KY) := by linarith
    linarith
  have hEUR6 := F0_EUR α A (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD)) Y
    hA0 BU6nn srF sEUzR hrF hEUzR6
  have hEUD5 := F0_EUD α A
    (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))) Y
    hA0 BE5nn srF sEUzD hrF hEUzD5
  have hEURp5 : Work.FTS.PhiStar.F0 5
      (2 ^ 5 * A * (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))))
      (Work.Spaces.pth (EUR α Y)) :=
    Work.FTS.PhiStar.CoreAux.F0_congr (pth_EUR α Y hsm) hEUD5
  -- the arithmetic: both constants are dominated by `5000(A+1)²(α+1)(K+KY+KD)`
  set S : ℝ := K + KY + KD with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; linarith
  have hKYle : KY ≤ S := by rw [hSdef]; linarith
  have hKPYle : K + KY ≤ S := by rw [hSdef]; linarith
  have hKDle : KD ≤ S := by rw [hSdef]; linarith
  have hM0 : 0 ≤ (A + 1) ^ 2 * (α + 1) * S :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith)) hS0
  have hle6 : 2 ^ 6 * A * (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
      ≤ 5000 * (A + 1) ^ 2 * (α + 1) * S := by
    have h1 := leM1 (A := A) (α := α) (S := S) (x := KY) hA1 hα hKY hKYle
    have h2 := leM2 (A := A) (α := α) (S := S) (x := KD) hA1 hα hKD hKDle
    have h3 := leM3 (A := A) (α := α) (S := S) (x := KY) hA1 hα hKY hKYle
    have hexp : 2 ^ 6 * A * (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
        = 192 * (A * KY) + 4096 * (α * A ^ 2 * KY) + 64 * (α * A * KD) := by ring
    rw [hexp]
    calc 192 * (A * KY) + 4096 * (α * A ^ 2 * KY) + 64 * (α * A * KD)
        ≤ 5000 * ((A + 1) ^ 2 * (α + 1) * S) := by linarith
      _ = 5000 * (A + 1) ^ 2 * (α + 1) * S := by ring
  have hle5 : 2 ^ 5 * A * (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))))
      ≤ 5000 * (A + 1) ^ 2 * (α + 1) * S := by
    have h1 := leM1 (A := A) (α := α) (S := S) (x := K + KY) hA1 hα hKPY hKPYle
    have h2 := leM2 (A := A) (α := α) (S := S) (x := K + KY) hA1 hα hKPY hKPYle
    have h3 := leM3 (A := A) (α := α) (S := S) (x := K + KY) hA1 hα hKPY hKPYle
    have hexp : 2 ^ 5 * A * (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))))
        = 96 * (A * (K + KY)) + 1024 * (α * A ^ 2 * (K + KY)) + 192 * (α * A * (K + KY)) := by
      ring
    rw [hexp]
    calc 96 * (A * (K + KY)) + 1024 * (α * A ^ 2 * (K + KY)) + 192 * (α * A * (K + KY))
        ≤ 5000 * ((A + 1) ^ 2 * (α + 1) * S) := by linarith
      _ = 5000 * (A + 1) ^ 2 * (α + 1) * S := by ring
  have hF1 : Work.FTS.PhiStar.F0 6 (5000 * (A + 1) ^ 2 * (α + 1) * S) (EUR α Y) :=
    hEUR6.mono le_rfl hle6
  have hF2 : Work.FTS.PhiStar.F0 5 (5000 * (A + 1) ^ 2 * (α + 1) * S)
      (Work.Spaces.pth (EUR α Y)) := hEURp5.mono le_rfl hle5
  -- transfer the two halves to `EU α Y = EUR α Y` (`euEUR_eq`) and assemble
  have heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.PhiStar.EU α Y z θ = EUR α Y z θ := fun z θ _ _ _ => euEUR_eq α Y z θ
  have hF1' : Work.FTS.PhiStar.F0 6 (5000 * (A + 1) ^ 2 * (α + 1) * S)
      (Work.FTS.PhiStar.EU α Y) :=
    Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ hz hθ hθ' => heq z θ hz hθ hθ') hF1
  have hF2' : Work.FTS.PhiStar.F0 5 (5000 * (A + 1) ^ 2 * (α + 1) * S)
      (Work.Spaces.pth (Work.FTS.PhiStar.EU α Y)) :=
    Work.FTS.PhiStar.CoreAux.F0_congr
      (fun z θ hz hθ hθ' => pth_congr6 heq z θ hz hθ hθ') hF2
  exact flatW6_of_F0 hF1' hF2'

end Work.FTS.StrongPersist.SP6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.EUz6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.PhiStar
open Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The angular derivative of the reassociated `EUz` field -/

/-- **The `∂_θ`-identity of the `EUz`-field**, in the reassociated form used by the flat
calculus: on the open quadrant,

`∂_θ (EUzR α Y) = EUzD α Y`

for a datum smooth on the quadrant.  The three inputs are the `θ`-derivative of the two `α`
terms (`EUzD` is exactly the sum of their derivatives) and the structural identity
`∂_θ (Yblk Y) = Yblk (∂_θ Y)` (`pth_zpz_smoothOpen`), the radial factor `(1+z)⁻¹` being
`θ`-free (`deriv_const_mul_field`). -/
theorem pth_EUzR_eq {α : ℝ} {Y : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EUzR α Y) z θ = EUzD α Y z θ := by
  intro z θ hz hθ hθ'
  have hsmr : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => (1 + z)⁻¹ * Y z θ) :=
    Fbq_smoothOpen_mul eh_smooth_rhoinv hsm
  have hsmb : Work.FTS.EllipticEst.SmoothOpen (Yblk Y) := eh_smooth_yblk hsm
  have hInv : Work.Spaces.pth (fun z θ : ℝ => (1 + z)⁻¹ * Y z θ) z θ
      = (1 + z)⁻¹ * Work.Spaces.pth Y z θ := by
    show deriv (fun θ' : ℝ => (1 + z)⁻¹ * Y z θ') θ
      = (1 + z)⁻¹ * deriv (fun θ' : ℝ => Y z θ') θ
    rw [deriv_const_mul_field]
  have hBlk : Work.Spaces.pth (Yblk Y) z θ = Yblk (Work.Spaces.pth Y) z θ :=
    pth_zpz_smoothOpen hsm z θ hz hθ hθ'
  have hG1 : Work.Spaces.pth (fun z θ : ℝ => 3 * Y z θ) z θ = 3 * Work.Spaces.pth Y z θ := by
    show deriv (fun θ' : ℝ => 3 * Y z θ') θ = 3 * deriv (fun θ' : ℝ => Y z θ') θ
    rw [deriv_const_mul_field]
  have hEuzR : Work.Spaces.pth (EUzR α Y) z θ
      = Work.Spaces.pth (fun z θ : ℝ => -(3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ)
          + α * Yblk Y z θ)) z θ :=
    pth_congr_Q0 (fun z θ _ _ _ => by simp only [EUzR]) z θ hz hθ hθ'
  have hOuter : Work.Spaces.pth (fun z θ : ℝ => 3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ)
        + α * Yblk Y z θ) z θ
      = 3 * Work.Spaces.pth Y z θ + α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ)
        + α * Yblk (Work.Spaces.pth Y) z θ := by
    rw [pth_add_Q0 (f := fun z θ : ℝ => 3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ))
        (g := fun z θ : ℝ => α * Yblk Y z θ)
        (SmoothOpen.add (SmoothOpen.const_mul hsm 3) (SmoothOpen.const_mul hsmr α))
        (SmoothOpen.const_mul hsmb α) z θ hz hθ hθ']
    rw [pth_add_Q0 (f := fun z θ : ℝ => 3 * Y z θ)
        (g := fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ))
        (SmoothOpen.const_mul hsm 3) (SmoothOpen.const_mul hsmr α) z θ hz hθ hθ']
    rw [hG1, pth_const_mul α (fun z θ : ℝ => (1 + z)⁻¹ * Y z θ)]
    simp only []
    rw [hInv, pth_const_mul α (Yblk Y)]
    simp only []
    rw [hBlk]
  have hNeg : Work.Spaces.pth (fun z θ : ℝ => -(3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ)
        + α * Yblk Y z θ)) z θ
      = - Work.Spaces.pth (fun z θ : ℝ => 3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ)
        + α * Yblk Y z θ) z θ := by
    show deriv (fun θ' : ℝ => -(3 * Y z θ' + α * ((1 + z)⁻¹ * Y z θ')
        + α * Yblk Y z θ')) θ
      = - deriv (fun θ' : ℝ => 3 * Y z θ' + α * ((1 + z)⁻¹ * Y z θ') + α * Yblk Y z θ') θ
    exact deriv.neg
  rw [hEuzR, hNeg, hOuter]
  simp only [EUzD]

/-- **The order-six flat bound of the `EUz`-star-field**,
`EUz α Y = -(3Y + α(Y/(z+1) + z∂_zY)) = -Wone α Y`.

Prove `FlatW 6 (EUz α Y) M` with `M := C·(α+1)·(K+KY+KD)` from `SmoothOpen Y`, `FlatW 7 Y K`,
`Fb 6 KY Y`, `F0 6 KD (Yblk Y)`; the constant must stay **linear** in `K + KY + KD` (note the
factor `α` in front of the two `αY`-terms — this is where the `(α+1)` is genuinely needed, cf.
the refutation in `Submission/Work/FTS/StrongPersist/SP6/FlatW6Fields.lean` for the variant
without `(α+1)`).

Import `Submission.Work.FTS.StrongPersist.SP6.Flat6Defs`: `CoefBundle6s`, `atomData`,
`EUzR`/`EUzD` and `euzEUzR_eq`, `flatW6_of_F0`, `FlatW_mono6`, `mono_const`, `pth_thetaOnly`.
Natural route: `F0 6 (EUzR α Y)` and `F0 5 (pth (EUzR α Y)) = F0 5 (EUzD α Y)` (`pth (Yblk Y) =
Yblk (pth Y)` on `Q0` via `pth_zpz_smoothOpen`; `atomData` supplies every block bound), then
`F0_congr` + `flatW6_of_F0`. The sibling
`Submission/Work/FTS/PhiStar/CoreAux/Fb_EU_bound.lean` proves the order-**four** version of the
joint statement for `EUz` and `EU`. -/
theorem EUz6 : ∃ C : ℝ, 0 < C ∧ ∀ (α K KY KD : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 0 ≤ KY → 0 ≤ KD → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.VocabO2.FlatW 7 Y K → Work.FTS.PhiStar.Fb 6 KY Y →
    Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) →
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EUz α Y) (C * (α + 1) * (K + KY + KD)) := by
  obtain ⟨A, hA1, hcoef⟩ := CoefBundle6s
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  refine ⟨65 * A, by linarith, ?_⟩
  intro α K KY KD Y hα hK hKY hKD hsm hW hFb hD
  obtain ⟨hY6, hP6, hD6, hPblk5, hDthP5⟩ := atomData hK hKY hKD hsm hW hFb hD
  -- ### the coefficient `(1+z)⁻¹` and the smoothness of the pieces
  have hRhoInv := hcoef (fun z _ : ℝ => (1 + z)⁻¹) (by simp [coefFun])
  have hRhoInv6 : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => (1 + z)⁻¹) := hRhoInv.1
  have hRhoInvS : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 + z)⁻¹) := hRhoInv.2
  have hsmr : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => (1 + z)⁻¹ * Y z θ) :=
    Fbq_smoothOpen_mul hRhoInvS hsm
  have hsmb : Work.FTS.EllipticEst.SmoothOpen (Yblk Y) := eh_smooth_yblk hsm
  have hSm3Y : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 3 * Y z θ) :=
    SmoothOpen.const_mul hsm 3
  have hSmαr : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ)) :=
    SmoothOpen.const_mul hsmr α
  have hSmαb : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * Yblk Y z θ) :=
    SmoothOpen.const_mul hsmb α
  -- ### level `6`: the flat class of `EUzR`
  have hInvY6 : Work.FTS.PhiStar.F0 6 (2 ^ 6 * A * KY) (fun z θ : ℝ => (1 + z)⁻¹ * Y z θ) :=
    F0_mul hA0 hKY hRhoInvS hsm hRhoInv6 hY6
  have hαInvY6 : Work.FTS.PhiStar.F0 6 (α * (2 ^ 6 * A * KY))
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ)) := by
    have h := F0_const_mul (n := 6) (K := 2 ^ 6 * A * KY) α hInvY6
    rwa [abs_of_nonneg hα] at h
  have hαYblk6 : Work.FTS.PhiStar.F0 6 (α * KD) (fun z θ : ℝ => α * Yblk Y z θ) := by
    have h := F0_const_mul (n := 6) (K := KD) α hD6
    rwa [abs_of_nonneg hα] at h
  have hSum6 : Work.FTS.PhiStar.F0 6 (α * (2 ^ 6 * A * KY) + α * KD)
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ) + α * Yblk Y z θ) :=
    F0_add hSmαr hSmαb hαInvY6 hαYblk6
  have h3Y6 : Work.FTS.PhiStar.F0 6 (3 * KY) (fun z θ : ℝ => 3 * Y z θ) := by
    have h := F0_const_mul (n := 6) (K := KY) (3 : ℝ) hY6
    rwa [show |(3 : ℝ)| = 3 by norm_num] at h
  have hBig6 : Work.FTS.PhiStar.F0 6 (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
      (fun z θ : ℝ => 3 * Y z θ + (α * ((1 + z)⁻¹ * Y z θ) + α * Yblk Y z θ)) :=
    F0_add hSm3Y (SmoothOpen.add hSmαr hSmαb) h3Y6 hSum6
  have hAssoc6 : Work.FTS.PhiStar.F0 6 (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
      (fun z θ : ℝ => 3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ) + α * Yblk Y z θ) :=
    F0_congr (fun z θ _ _ _ => by ring) hBig6
  have hEUzR6 : Work.FTS.PhiStar.F0 6 (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
      (EUzR α Y) := by
    have h := F0_const_mul (n := 6) (K := 3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
      (-1 : ℝ) hAssoc6
    rw [show |(-1 : ℝ)| * (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
        = 3 * KY + (α * (2 ^ 6 * A * KY) + α * KD) by norm_num] at h
    refine F0_congr (fun z θ _ _ _ => ?_) h
    simp only [EUzR, Yblk]
    ring
  -- ### level `5`: the flat class of `EUzD`
  have hP5 : Work.FTS.PhiStar.F0 5 (K + KY) (Work.Spaces.pth Y) :=
    hP6.mono (by norm_num) le_rfl
  have hRhoInv5 : Work.FTS.PhiStar.F0 5 A (fun z _ : ℝ => (1 + z)⁻¹) :=
    hRhoInv6.mono (by norm_num) le_rfl
  have hKN : 0 ≤ K + KY := by linarith
  have hInvP5 : Work.FTS.PhiStar.F0 5 (2 ^ 5 * A * (K + KY))
      (fun z θ : ℝ => (1 + z)⁻¹ * Work.Spaces.pth Y z θ) :=
    F0_mul hA0 hKN hRhoInvS hsm.pth hRhoInv5 hP5
  have hαInvP5 : Work.FTS.PhiStar.F0 5 (α * (2 ^ 5 * A * (K + KY)))
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ)) := by
    have h := F0_const_mul (n := 5) (K := 2 ^ 5 * A * (K + KY)) α hInvP5
    rwa [abs_of_nonneg hα] at h
  have hαPblk5 : Work.FTS.PhiStar.F0 5 (α * (6 * (K + KY)))
      (fun z θ : ℝ => α * Yblk (Work.Spaces.pth Y) z θ) := by
    have h := F0_const_mul (n := 5) (K := 6 * (K + KY)) α hPblk5
    rwa [abs_of_nonneg hα] at h
  have hsmrP : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => (1 + z)⁻¹ * Work.Spaces.pth Y z θ) :=
    Fbq_smoothOpen_mul hRhoInvS hsm.pth
  have hsmbP : Work.FTS.EllipticEst.SmoothOpen (Yblk (Work.Spaces.pth Y)) :=
    eh_smooth_yblk hsm.pth
  have hSmαrP : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ)) :=
    SmoothOpen.const_mul hsmrP α
  have hSmαbP : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => α * Yblk (Work.Spaces.pth Y) z θ) :=
    SmoothOpen.const_mul hsmbP α
  have hSm3P : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 3 * Work.Spaces.pth Y z θ) :=
    SmoothOpen.const_mul hsm.pth 3
  have hSum5 : Work.FTS.PhiStar.F0 5 (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ)
        + α * Yblk (Work.Spaces.pth Y) z θ) :=
    F0_add hSmαrP hSmαbP hαInvP5 hαPblk5
  have h3P5 : Work.FTS.PhiStar.F0 5 (3 * (K + KY))
      (fun z θ : ℝ => 3 * Work.Spaces.pth Y z θ) := by
    have h := F0_const_mul (n := 5) (K := K + KY) (3 : ℝ) hP5
    rwa [show |(3 : ℝ)| = 3 by norm_num] at h
  have hBig5 : Work.FTS.PhiStar.F0 5
      (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))))
      (fun z θ : ℝ => 3 * Work.Spaces.pth Y z θ
        + (α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ) + α * Yblk (Work.Spaces.pth Y) z θ)) :=
    F0_add hSm3P (SmoothOpen.add hSmαrP hSmαbP) h3P5 hSum5
  have hAssoc5 : Work.FTS.PhiStar.F0 5
      (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))))
      (fun z θ : ℝ => 3 * Work.Spaces.pth Y z θ
        + α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ) + α * Yblk (Work.Spaces.pth Y) z θ) :=
    F0_congr (fun z θ _ _ _ => by ring) hBig5
  have hEUzD5 : Work.FTS.PhiStar.F0 5
      (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))) (EUzD α Y) := by
    have h := F0_const_mul (n := 5)
      (K := 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))))
      (-1 : ℝ) hAssoc5
    rw [show |(-1 : ℝ)| * (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))))
        = 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))) by norm_num] at h
    refine F0_congr (fun z θ _ _ _ => ?_) h
    simp only [EUzD, Yblk]
    ring
  -- ### the arithmetic of the two constants
  have hS0 : (0 : ℝ) ≤ K + KY + KD := by linarith
  have hc6 : 3 * KY + (α * (2 ^ 6 * A * KY) + α * KD) ≤ 65 * A * (α + 1) * (K + KY + KD) := by
    have hKYle : KY ≤ K + KY + KD := by linarith
    have hKDle : KD ≤ K + KY + KD := by linarith
    have h1 : 3 * KY ≤ 3 * (K + KY + KD) := by linarith
    have h2 : α * (2 ^ 6 * A * KY) ≤ α * (2 ^ 6 * A * (K + KY + KD)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKYle (by norm_num; linarith)) hα
    have h3 : α * KD ≤ α * (K + KY + KD) := mul_le_mul_of_nonneg_left hKDle hα
    have h4 : 3 * (K + KY + KD) + (α * (2 ^ 6 * A * (K + KY + KD)) + α * (K + KY + KD))
        ≤ (K + KY + KD) * (65 * A * (α + 1)) := by
      rw [show 3 * (K + KY + KD) + (α * (2 ^ 6 * A * (K + KY + KD)) + α * (K + KY + KD))
          = (K + KY + KD) * (3 + (2 ^ 6 * A * α + α)) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hS0
      have hA65 : (65 : ℝ) ≤ 65 * A := by linarith
      have hAα : α ≤ A * α := by nlinarith [hα, hA1]
      nlinarith
    calc 3 * KY + (α * (2 ^ 6 * A * KY) + α * KD)
        ≤ 3 * (K + KY + KD) + (α * (2 ^ 6 * A * (K + KY + KD)) + α * (K + KY + KD)) := by
          linarith
      _ ≤ (K + KY + KD) * (65 * A * (α + 1)) := h4
      _ = 65 * A * (α + 1) * (K + KY + KD) := by ring
  have hc5 : 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))
      ≤ 65 * A * (α + 1) * (K + KY + KD) := by
    have hKNle : K + KY ≤ K + KY + KD := by linarith
    have h5 : 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))
        ≤ (K + KY) * (65 * A * (α + 1)) := by
      rw [show 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))
          = (K + KY) * (3 + (2 ^ 5 * A * α + 6 * α)) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hKN
      have hA65 : (65 : ℝ) ≤ 65 * A := by linarith
      have hAα : α ≤ A * α := by nlinarith [hα, hA1]
      nlinarith
    calc 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))
        ≤ (K + KY) * (65 * A * (α + 1)) := h5
      _ ≤ (K + KY + KD) * (65 * A * (α + 1)) :=
          mul_le_mul_of_nonneg_right hKNle (by positivity)
      _ = 65 * A * (α + 1) * (K + KY + KD) := by ring
  -- ### conclusion
  have hEUz : Work.FTS.PhiStar.F0 6 (65 * A * (α + 1) * (K + KY + KD))
      (Work.FTS.PhiStar.EUz α Y) :=
    (F0_congr (fun z θ _ _ _ => euzEUzR_eq α Y z θ) hEUzR6).mono le_rfl hc6
  have hpth : Work.FTS.PhiStar.F0 5 (65 * A * (α + 1) * (K + KY + KD))
      (Work.Spaces.pth (Work.FTS.PhiStar.EUz α Y)) :=
    (F0_congr (fun z θ hz hθ hθ' =>
      (pth_congr_Q0 (fun z θ _ _ _ => euzEUzR_eq α Y z θ) z θ hz hθ hθ').trans
        (pth_EUzR_eq hsm z θ hz hθ hθ')) hEUzD5).mono le_rfl hc5
  exact flatW6_of_F0 hEUz hpth

end Work.FTS.StrongPersist.SP6
end
