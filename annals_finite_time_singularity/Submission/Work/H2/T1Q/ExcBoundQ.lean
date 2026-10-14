import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.N4Fields.AngSmoothIntHelpers
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_pth_poincare_unif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option maxHeartbeats 800000

/-- The `θ`-derivative of the `θ`-slice of a function smooth on the open quadrant. -/
private lemma hasDerivAt_slice_pth_unif {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun θ' : ℝ => F z θ') (Work.Spaces.pth F z θ) θ := by
  have hd : DifferentiableAt ℝ (fun θ' : ℝ => F z θ') θ :=
    ((hF.curry_θ hz).differentiableOn
      (by rw [Work.Stability.smoothOrder]; simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  exact hd.hasDerivAt

theorem slice_pth_poincare_unif (G : ℝ → ℝ → ℝ)
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 0 < w →
      (∫ s in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G w s) ^ 2)
        ≤ C * (∫ s in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2) := by
  -- the uniform angular Poincaré inequality supplies the constant once and for all
  obtain ⟨C, hC, hCbound⟩ := thetaPoincare_unif
  have hTcopy : Work.FTS.EllSol.EllPkgAux.TraceClass G := hT
  obtain ⟨hsm, h0, hpi, -, -, -, -, -⟩ := hT
  refine ⟨C, hC, ?_⟩
  intro w hw
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  -- ## The angular derivatives of the two slices
  have hd1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' : ℝ => G w θ') (Work.Spaces.pth G w θ) θ :=
    fun θ hθ => hasDerivAt_slice_pth_unif hsm hw hθ
  have hd2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' : ℝ => Work.Spaces.pth G w θ')
        (Work.Spaces.pth (Work.Spaces.pth G) w θ) θ :=
    fun θ hθ => hasDerivAt_slice_pth_unif hsm.pth hw hθ
  -- ## Integrability of `∂_θG(w,·)` on `Iθ`
  have hint : IntervalIntegrable (fun s : ℝ => Work.Spaces.pth G w s) volume 0 (Real.pi / 2) :=
    intervalIntegrable_pth_slice G hTcopy hw
  have hfint : IntegrableOn (fun s : ℝ => Work.Spaces.pth G w s) Work.Spaces.Iθ := by
    have h1 : IntegrableOn (fun s : ℝ => Work.Spaces.pth G w s) (Set.Ioc 0 (Real.pi / 2)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hint
    exact h1.congr_set_ae (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm
  -- ## Vanishing mean of `∂_θG(w,·)` (FTC on the slice, whose endpoint values both vanish)
  have hmeanz : (∫ s in (0 : ℝ)..(Real.pi / 2), Work.Spaces.pth G w s) = 0 := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0 : ℝ))
      (b := Real.pi / 2) hle (slice_continuousOn G hTcopy hw) hd1 hint
    rw [hftc, hpi w, h0 w, sub_zero]
  have hmean : (∫ s in Work.Spaces.Iθ, Work.Spaces.pth G w s) = 0 := by
    show (∫ s in Set.Icc (0 : ℝ) (Real.pi / 2), Work.Spaces.pth G w s) = 0
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    exact hmeanz
  -- ## Integrability of the squared second angular derivative on `Iθ`
  have hwint : IntegrableOn
      (fun s : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2
        * Work.FTS.EllipticEst.thEta s) Work.Spaces.Iθ :=
    slice_deriv2_weighted_integrableOn (G := G) hTcopy (w := w) hw
  have haesm : AEStronglyMeasurable
      (fun s : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    have hc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        Work.FTS.EllipticEst.Q0 := (hsm.pth.pth).continuousOn
    have h := Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2) hc hw
    convert h.mul h using 1
    ext s
    rw [Pi.mul_apply, pow_two]
  have hf'int : IntegrableOn
      (fun s : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2) Work.Spaces.Iθ := by
    refine Integrable.mono' hwint haesm ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (one_le_thEta_of_mem_Ioo hs)
  -- ## The *uniform* angular Poincaré estimate applied to `f = ∂_θG(w,·)`
  exact hCbound hd2 hf'int hfint hmean

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.ceAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false



end Work.FTS.EllipticEst.Dispatch
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smoothInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.N4Fields

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The unit-profile pointwise `ℋ^k`-bound with open-interval smoothness

This is `Work.FTS.EllipticEst.Blocks.HkIntegrand_ang_mul_unit_le` (in
`Submission/Work/FTS/Nonlinear/N4Fields/angmul_field_smooth.lean`) with its analyticity
hypothesis `∀ θ : ℝ, ContDiffAt ℝ ⊤ a θ` replaced by
`ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2) Q0`.  The proof is a verbatim
copy of the reference proof: the only two uses of the analyticity hypothesis are the smoothness
of the product `(z,θ) ↦ a θ · f z θ` (now `smoothOpen_angMul_On`) and the Leibniz expansion
`D_θ^i (a · D_z^j f)` (now `DthIter_angular_mul_expand_On`, whose hypothesis on `a` is the
open-interval one supplied by `contDiffOn_ang_of_Q0`). -/
theorem HkIntegrand_ang_mul_unit_le_Int (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ → ℝ), (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |a θ| ≤ 1) →
      ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
        Work.FTS.EllipticEst.Q0 →
      (∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ 2) →
      ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
        Work.FTS.EllipticEst.SmoothOpen f →
        ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) z θ
            ≤ C * Work.Spaces.HkIntegrand α k f z θ := by
  set K : ℕ → ℝ := fun _ => 1 with hKdef
  have hK : ∀ m : ℕ, 0 ≤ K m := fun m => by rw [hKdef]; exact zero_le_one
  set KB : ℝ := ∑ m ∈ Finset.range (k + 1), (K m + 1) with hKBdef
  have hKBpos : 0 < KB := by
    rw [hKBdef]
    exact Finset.sum_pos (fun m _ => by linarith [hK m])
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
  set CB : ℝ := ((2 : ℝ) ^ k) ^ 2 with hCBdef
  have hCBnonneg : 0 ≤ CB := by rw [hCBdef]; positivity
  set Cpair : ℝ := ((k : ℝ) + 1) * CB * KB with hCpairdef
  have hCpairnonneg : 0 ≤ Cpair := by rw [hCpairdef]; positivity
  set C1 : ℝ := ((k : ℝ) + 1) ^ 2 * Cpair with hC1def
  refine ⟨((k : ℝ) + 1) + C1, by positivity, ?_⟩
  intro a ha1 hha hKb0 α f hα hα1 hf z θ hz hθ0 hθ1
  have hKb : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 ≤ K m * (Real.sin (2 * θ)) ^ 2 := by
    intro m hm1 hmk θ hθ
    rw [hKdef]
    simpa using hKb0 m hm1 hmk θ hθ
  have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hHe : 0 ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZi : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [Work.FTS.EllipticEst.Blocks.DzIter_angular_mul i a f]
      have ha2 : (a θ) ^ 2 ≤ 1 := by
        have h := pow_le_pow_left₀ (abs_nonneg (a θ)) (ha1 θ hθIoo) 2
        rwa [sq_abs, one_pow] at h
      calc (a θ * Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (a θ) ^ 2 * (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
        _ ≤ 1 * (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
            mul_le_mul_of_nonneg_right ha2 (sq_nonneg _)
        _ = (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := one_mul _
        _ ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.sq_le_HkIntegrand_z α k f z θ i hik
    calc (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (k + 1), Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hMi : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ C1 * Work.Spaces.HkIntegrand α k f z θ := by
    have hpair : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
        (1 ≤ i ∧ i + j ≤ k) →
        (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Cpair * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi j hj hc
      obtain ⟨hi1, hij⟩ := hc
      have hik : i ≤ k := by omega
      have hjk : j ≤ k := by omega
      have hexp : Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ
          = ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ := by
        have hag : Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * f z θ) :=
          smoothOpen_angMul_On hha hf
        rw [← Work.FTS.EllipticEst.SmoothOpen.DthIter_DzIter_eq_mixed hag j i hz hθIoo]
        rw [Work.FTS.EllipticEst.Blocks.DzIter_angular_mul j a f]
        rw [DthIter_angular_mul_expand_On (contDiffOn_ang_of_Q0 hha) hf i j hz hθIoo]
        exact Finset.sum_congr rfl fun m _ => by
          rw [Work.FTS.EllipticEst.SmoothOpen.DthIter_DzIter_eq_mixed hf j (i - m) hz hθIoo]
      rw [hexp]
      have hstep : (∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ) * Work.Spaces.Wt α z θ
          = ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) := by
        rw [Finset.sum_mul]
      rw [hstep]
      have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
        (f := fun m => (i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
          * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ)
      have hbound : ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ)
            * Work.FTS.EllipticEst.LopIter m a θ
            * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ CB * KB * Work.Spaces.HkIntegrand α k f z θ := by
        have hchoose : ∀ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 ≤ CB := by
          intro m hm
          have h1 : (i.choose m : ℝ) ≤ (2 : ℝ) ^ k := by
            have h2 : i.choose m ≤ 2 ^ k := le_trans (Nat.choose_le_two_pow i m)
              (Nat.pow_le_pow_right (by norm_num) hik)
            exact_mod_cast h2
          calc (i.choose m : ℝ) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
            _ = CB := by rw [hCBdef]
        have hsumKB : ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1)
            ≤ CB * KB := by
          have hstep1 : ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1)
              ≤ ∑ m ∈ Finset.range (i + 1), CB * (K m + 1) := by
            refine Finset.sum_le_sum fun m hm => ?_
            exact mul_le_mul_of_nonneg_right (hchoose m hm) (by linarith [hK m])
          have hstep2 : ∑ m ∈ Finset.range (i + 1), CB * (K m + 1)
              = CB * ∑ m ∈ Finset.range (i + 1), (K m + 1) := by
            rw [Finset.mul_sum]
          have hstep3 : ∑ m ∈ Finset.range (i + 1), (K m + 1) ≤ KB := by
            rw [hKBdef]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro m hm
              simp only [Finset.mem_range] at hm ⊢
              omega
            · intro m _ _
              linarith [hK m]
          calc _ ≤ ∑ m ∈ Finset.range (i + 1), CB * (K m + 1) := hstep1
            _ = CB * ∑ m ∈ Finset.range (i + 1), (K m + 1) := hstep2
            _ ≤ CB * KB := mul_le_mul_of_nonneg_left hstep3 hCBnonneg
        calc ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1)
                * Work.Spaces.HkIntegrand α k f z θ := by
              refine Finset.sum_le_sum fun m hm => ?_
              have hmi : m ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
              exact Work.FTS.EllipticEst.Blocks.angular_summand_sq_le_le_unit k a K ha1 hK hKb
                α f i j m hα1 hi1 hij hmi z θ hθ0 hθ1
          _ = Work.Spaces.HkIntegrand α k f z θ
                * ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun m _ => by ring
          _ ≤ Work.Spaces.HkIntegrand α k f z θ * (CB * KB) :=
              mul_le_mul_of_nonneg_left hsumKB hHe
          _ = CB * KB * Work.Spaces.HkIntegrand α k f z θ := by ring
      have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
        rw [Finset.card_range]
        push_cast
        ring
      calc (∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) * ∑ m ∈ Finset.range (i + 1),
              ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
                * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2 := hcs
        _ ≤ (((i : ℝ) + 1)) * (CB * KB * Work.Spaces.HkIntegrand α k f z θ) := by
            rw [hcard]
            exact mul_le_mul_of_nonneg_left hbound (by positivity)
        _ ≤ ((k : ℝ) + 1) * (CB * KB * Work.Spaces.HkIntegrand α k f z θ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have : (i : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hik
            linarith
        _ = Cpair * Work.Spaces.HkIntegrand α k f z θ := by
            rw [hCpairdef]
            ring
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
            Cpair * Work.Spaces.HkIntegrand α k f z θ := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc]
            exact hpair i hi j hj hc
          · rw [if_neg hc]
            exact mul_nonneg hCpairnonneg hHe
      _ = C1 * Work.Spaces.HkIntegrand α k f z θ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [hC1def]
          push_cast
          ring
  rw [Work.Spaces.HkIntegrand]
  refine le_trans (add_le_add hZi hMi) (le_of_eq ?_)
  ring

/-! ## The interface field -/


end Work.FTS.Nonlinear.N4Fields
end
end
-- ===== merged: Submission.Work.FTS.TransportS.HardDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

set_option autoImplicit false

/-!
# The slot decomposition of the `D_z`-transport hard part

This module collects the *definitions* (and the immediate product-measure facts and
elementary identities) used by the proof of `Work.FTS.TransportS.T2Hard`, the bound on the
five order-five terms `Work.FTS.H2.Hhard α f g` of the `D_z`-transport pairing.

`Hhard α f g z θ = f z θ · z · ∑_{k : Fin 5} pz (Thard g k) z θ · Thard g k z θ · w² · sghard α k θ`
(`Work.FTS.H2.T2Defs`), and `z · pz (Thard g k) z θ = Work.Spaces.Dz (Thard g k) z θ`
(`Dz_Thard` below).  Each of the five summands is thus the product `f · X_k · Y_k` of the
coefficient `f` with the two weighted derivatives

* `Xz α g k` — the order-`4` factor: `D_z^4 g · w/sin(2θ)^{η/2}` for `k = 0`, and
  `D_z^{4-k}D_θ^k g · W` for `k ≥ 1`,
* `Yz α g k` — the order-`5` factor: `D_z^5 g · w/sin(2θ)^{η/2}` for `k = 0`, and
  `D_z^{5-k}D_θ^k g · W` for `k ≥ 1`,

whose *squares* are single summands of `HkIntegrand α 4 g` resp. `HkIntegrand α 5 g`.  The
pointwise AM–GM inequality `|X Y| ≤ (X² + Y²)/2` therefore makes `Hhard` dominated by
`5 Mf · HkIntegrand α 5 g`, which is product-integrable for `g ∈ ℋ⁵`; this is the
integrability input of the Fubini argument behind `T2Hard`.
-/

/-- The weighted order-`4` factor of the `k`-th hard slot.  Its square is the corresponding
summand of `Work.Spaces.HkIntegrand α 4 g`: the `D_z^4 g`-slot (weight `w/sin(2θ)^{η/2}`) for
`k = 0` and the mixed slot `D_z^{4-k}D_θ^k g` (weight `W`) for `k ≥ 1`. -/
def Xz (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) : ℝ → ℝ → ℝ :=
  if k.val = 0 then fun z θ => Work.Spaces.DzIter 4 g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
  else fun z θ => Work.Spaces.mixed (4 - k.val) k.val g z θ * Work.Spaces.Wt α z θ

/-- The weighted order-`5` factor of the `k`-th hard slot: the same construction with
`D_z(D_z^4 g) = D_z^5 g` resp. `D_z(D_z^{4-k}D_θ^k g) = D_z^{5-k}D_θ^k g`. -/
def Yz (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) : ℝ → ℝ → ℝ :=
  if k.val = 0 then fun z θ => Work.Spaces.DzIter 5 g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
  else fun z θ => Work.Spaces.mixed (5 - k.val) k.val g z θ * Work.Spaces.Wt α z θ

/-- The `k`-th summand of `Hhard`, in the exact shape in which it occurs in the sum (with the
plain `∂_z` of the slot). -/
def gK (α : ℝ) (f g : ℝ → ℝ → ℝ) (k : Fin 5) : ℝ → ℝ → ℝ :=
  fun z θ => f z θ * z * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ
    * Work.FTS.H2.Thard g k z θ * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.sghard α k θ

/-- The `k`-th summand of `Hhard` with the `z ∂_z` written as `D_z`; it is equal to `gK`
(`gK_eq_hK`). -/
def hK (α : ℝ) (f g : ℝ → ℝ → ℝ) (k : Fin 5) : ℝ → ℝ → ℝ :=
  fun z θ => f z θ * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.sghard α k θ
    * Work.FTS.H2.Thard g k z θ * Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ

/-- The `z`-slice integrand obtained by integrating by parts the `k`-th summand of `Hhard`
(one half of `∂_z (f z θ · z w²) · (Thard g k z θ)²`). -/
def gK' (α : ℝ) (f g : ℝ → ℝ → ℝ) (k : Fin 5) : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
      + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))))
    * (Work.FTS.H2.Thard g k z θ) ^ 2

/-! ## The elementary identities -/

/-- `D_z` of the `k`-th order-`4` slot is the order-`5` slot with the same angular part. -/
theorem Dz_Thard (g : ℝ → ℝ → ℝ) (k : Fin 5) :
    Work.Spaces.Dz (Work.FTS.H2.Thard g k)
      = fun z θ => Work.Spaces.mixed (5 - k.val) k.val g z θ := by
  rw [Work.FTS.H2.Thard_eq_mixed g k]
  funext z θ
  fin_cases k <;> rfl



/-! ## The elementary weight algebra

The weight of the `k`-th order-`4` (resp. order-`5`) factor is `w z / sin(2θ)^{η/2}` for
`k = 0` and `W = w z · sin(2θ)^{-γ/2}` for `k ≥ 1`; in both cases the *square* of the weight is
`w(z)² · sin(2θ)^{-c}` (`c = η` resp. `c = γ`), which is the weight of the corresponding
summand of `Work.Spaces.HkIntegrand`.  The `rpow` identities behind this are collected here;
everything is pointwise and holds trivially when `sin(2θ) = 0` (`0 ^ c = 0` for `c ≠ 0` and
`0 ^ 0 = 1`). -/

/-- `(w / s^{c/2}) · (w / s^{c/2}) = w² · s^{-c}` for `s ≥ 0`. -/
theorem mul_self_div_rpow {w s : ℝ} (hs : 0 ≤ s) (c : ℝ) :
    (w / s ^ (c / 2)) * (w / s ^ (c / 2)) = w ^ 2 * s ^ (-c) := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    rw [show (0 : ℝ) / 2 = 0 by norm_num, show -(0 : ℝ) = 0 by norm_num,
      Real.rpow_zero, div_one, mul_one]
    ring
  · rcases eq_or_lt_of_le hs with h | h
    · subst h
      have h1 : (c / 2 : ℝ) ≠ 0 := fun hh => hc (by linarith)
      rw [Real.zero_rpow h1, div_zero, mul_zero,
        Real.zero_rpow (by simpa using neg_ne_zero.mpr hc), mul_zero]
    · have hpos : 0 < s := h
      have h2 : s ^ (c / 2) * s ^ (c / 2) = s ^ c := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring
      rw [div_mul_div_comm, h2, div_eq_mul_inv, ← Real.rpow_neg hpos.le]
      ring

/-- `(w / s^{c/2})² = w² · s^{-c}` for `s ≥ 0`. -/
theorem sq_div_rpow {w s : ℝ} (hs : 0 ≤ s) (c : ℝ) :
    (w / s ^ (c / 2)) ^ 2 = w ^ 2 * s ^ (-c) := by
  rw [pow_two]
  exact mul_self_div_rpow hs c

/-- `(s^{-c/2})² = s^{-c}` for `s ≥ 0`. -/
theorem sq_rpow_neg_half {s : ℝ} (hs : 0 ≤ s) (c : ℝ) :
    (s ^ (-(c / 2))) ^ 2 = s ^ (-c) := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    rw [show -((0 : ℝ) / 2) = 0 by norm_num, show -(0 : ℝ) = 0 by norm_num, Real.rpow_zero]
    norm_num
  · rcases eq_or_lt_of_le hs with h | h
    · subst h
      have h1 : (-(c / 2) : ℝ) ≠ 0 := fun hh => hc (by linarith)
      rw [Real.zero_rpow h1, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        Real.zero_rpow (by simpa using neg_ne_zero.mpr hc)]
    · have hpos : 0 < s := h
      have h2 : (s ^ (-(c / 2))) * (s ^ (-(c / 2))) = s ^ (-c) := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring
      rw [pow_two]; exact h2

/-- `(w · s^{-c/2})² = w² · s^{-c}` for `s ≥ 0`. -/
theorem sq_mul_rpow_neg_half {w s : ℝ} (hs : 0 ≤ s) (c : ℝ) :
    (w * s ^ (-(c / 2))) ^ 2 = w ^ 2 * s ^ (-c) := by
  rw [mul_pow, sq_rpow_neg_half hs c]

/-! ## Pointwise forms of the slot data -/

/-- The order-`4` weighted factor of the `k`-th slot, for `k = 0`. -/
theorem Xz_apply_zero (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Xz α g 0 z θ = Work.Spaces.DzIter 4 g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
  simp only [Xz]
  rw [if_pos (show ((0 : Fin 5).val = 0) from rfl)]

/-- The order-`5` weighted factor of the `k`-th slot, for `k = 0`. -/
theorem Yz_apply_zero (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Yz α g 0 z θ = Work.Spaces.DzIter 5 g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
  simp only [Yz]
  rw [if_pos (show ((0 : Fin 5).val = 0) from rfl)]

theorem Xz_apply_ne {α : ℝ} {g : ℝ → ℝ → ℝ} {k : Fin 5} (hk : k.val ≠ 0) (z θ : ℝ) :
    Xz α g k z θ = Work.Spaces.mixed (4 - k.val) k.val g z θ * Work.Spaces.Wt α z θ := by
  simp only [Xz]
  rw [if_neg hk]

theorem Yz_apply_ne {α : ℝ} {g : ℝ → ℝ → ℝ} {k : Fin 5} (hk : k.val ≠ 0) (z θ : ℝ) :
    Yz α g k z θ = Work.Spaces.mixed (5 - k.val) k.val g z θ * Work.Spaces.Wt α z θ := by
  simp only [Yz]
  rw [if_neg hk]

/-- The order-`4` slot, for `k = 0`. -/
theorem Thard_apply_zero (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.H2.Thard g 0 z θ = Work.Spaces.DzIter 4 g z θ := by
  rw [Work.FTS.H2.Thard_eq_mixed]
  rfl


/-- The order-`4` slot, for `k ≠ 0`. -/
theorem Thard_apply_ne {g : ℝ → ℝ → ℝ} {k : Fin 5} (hk : k.val ≠ 0) (z θ : ℝ) :
    Work.FTS.H2.Thard g k z θ = Work.Spaces.mixed (4 - k.val) k.val g z θ := by
  rw [Work.FTS.H2.Thard_eq_mixed]

/-- `D_z` of the order-`4` slot is the order-`5` slot. -/
theorem Dz_Thard_apply (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) :
    Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ
      = Work.Spaces.mixed (5 - k.val) k.val g z θ := by
  rw [Dz_Thard g k]

/-- The square of the `k`-th order-`4` weighted factor is `w² · sin(2θ)^{-η_k}` times the
square of the slot `Thard g k`. -/
theorem Xz_sq {α : ℝ} (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Xz α g k z θ) ^ 2
      = (Work.FTS.H2.Thard g k z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.H2.sghard α k θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    rw [Xz_apply_zero, Thard_apply_zero, Work.FTS.H2.sghard_apply_zero, mul_pow,
      sq_div_rpow hs Work.Spaces.eta]
    ring
  · have hW : Work.Spaces.Wt α z θ ^ 2
        = (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
      show (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2 = _
      exact sq_mul_rpow_neg_half hs (Work.Spaces.gam α)
    rw [Xz_apply_ne hk, Thard_apply_ne hk, Work.FTS.H2.sghard_apply_ne α k hk θ, mul_pow, hW]
    ring


/-- The product of the two weighted factors of a slot is `Thard g k · D_z(Thard g k) · w² σ_k`. -/
theorem Xz_mul_Yz {α : ℝ} (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    Xz α g k z θ * Yz α g k z θ
      = Work.FTS.H2.Thard g k z θ * Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ
        * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.sghard α k θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    have hd : Work.Spaces.Dz (Work.FTS.H2.Thard g 0) z θ = Work.Spaces.DzIter 5 g z θ := by
      rw [Dz_Thard_apply g 0 z θ]
      rfl
    have ht := mul_self_div_rpow (s := Real.sin (2 * θ)) (w := Work.Spaces.w z) hs
      Work.Spaces.eta
    rw [Xz_apply_zero, Yz_apply_zero, Thard_apply_zero, hd, Work.FTS.H2.sghard_apply_zero]
    rw [show (Work.Spaces.DzIter 4 g z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))
          * (Work.Spaces.DzIter 5 g z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))
        = Work.Spaces.DzIter 4 g z θ * Work.Spaces.DzIter 5 g z θ
          * ((Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) from by ring,
      ht]
    ring
  · have hW : Work.Spaces.Wt α z θ * Work.Spaces.Wt α z θ
        = (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
      show (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))
          * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) = _
      rw [← pow_two]
      exact sq_mul_rpow_neg_half hs (Work.Spaces.gam α)
    rw [Xz_apply_ne hk, Yz_apply_ne hk, Thard_apply_ne hk, Dz_Thard_apply,
      Work.FTS.H2.sghard_apply_ne α k hk θ]
    rw [show (Work.Spaces.mixed (4 - k.val) k.val g z θ * Work.Spaces.Wt α z θ)
          * (Work.Spaces.mixed (5 - k.val) k.val g z θ * Work.Spaces.Wt α z θ)
        = Work.Spaces.mixed (4 - k.val) k.val g z θ
          * Work.Spaces.mixed (5 - k.val) k.val g z θ
          * (Work.Spaces.Wt α z θ * Work.Spaces.Wt α z θ) from by ring,
      hW]
    ring


/-- A single order-`4` weighted factor is a summand of `HkIntegrand α 5 g`. -/
theorem Xz_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) :
    (Xz α g k z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 5 g z θ := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    rw [Xz_apply_zero]
    exact Work.Spaces.sq_le_HkIntegrand_z α 5 g z θ 4 (by norm_num)
  · rw [Xz_apply_ne hk]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 5 g z θ k.val (4 - k.val)
      (Nat.one_le_iff_ne_zero.mpr hk) (by omega)

/-- The same with the order-`4` integrand (used for the final numerical bound). -/
theorem Xz_sq_le_HkIntegrand4 (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) :
    (Xz α g k z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    rw [Xz_apply_zero]
    exact Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 4 le_rfl
  · rw [Xz_apply_ne hk]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ k.val (4 - k.val)
      (Nat.one_le_iff_ne_zero.mpr hk) (by omega)

/-- A single order-`5` weighted factor is a summand of `HkIntegrand α 5 g`. -/
theorem Yz_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) :
    (Yz α g k z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 5 g z θ := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    rw [Yz_apply_zero]
    exact Work.Spaces.sq_le_HkIntegrand_z α 5 g z θ 5 le_rfl
  · rw [Yz_apply_ne hk]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 5 g z θ k.val (5 - k.val)
      (Nat.one_le_iff_ne_zero.mpr hk) (by omega)

/-! ## The pointwise bounds

`Hhard α f g` is the sum of the five summands `gK α f g k`, each of which is `f · X_k · Y_k`
with the two weighted factors of `HardDefs`; the AM–GM inequality `|X Y| ≤ (X² + Y²)/2`
turns these into a bound by `Mf · HkIntegrand α 5 g`.  The corresponding bound for the
integration-by-parts integrand `gK'` uses `|∂_z (f · z w²)| ≤ 4 Mf w²` and
`sin(2θ)^{η_k} ≤ 1` (`1 ≤ sghard α k θ`). -/



/-- Each summand of `Hhard` is `f` times the product of the two weighted slot factors. -/
theorem gK_eq_mul (α : ℝ) (f g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    gK α f g k z θ = f z θ * (Xz α g k z θ * Yz α g k z θ) := by
  have hDz : Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ
      = Work.Spaces.mixed (5 - k.val) k.val g z θ := Dz_Thard_apply g k z θ
  have hpz : z * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ
      = Work.Spaces.mixed (5 - k.val) k.val g z θ := by
    rw [← hDz]
    rfl
  rw [gK, Xz_mul_Yz g k z θ hθ, hDz,
    show f z θ * z * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ
        * Work.FTS.H2.Thard g k z θ * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.sghard α k θ
      = f z θ * (z * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ)
        * Work.FTS.H2.Thard g k z θ * (Work.Spaces.w z) ^ 2
        * Work.FTS.H2.sghard α k θ from by ring,
    hpz]
  ring

/-- The pointwise bound on a single summand of `Hhard`. -/
theorem abs_gK_le {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (hMf : 0 ≤ Mf)
    (hf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (k : Fin 5) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |gK α f g k z θ| ≤ Mf * Work.Spaces.HkIntegrand α 5 g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hAM : |Xz α g k z θ| * |Yz α g k z θ|
      ≤ ((Xz α g k z θ) ^ 2 + (Yz α g k z θ) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|Xz α g k z θ| - |Yz α g k z θ|), sq_abs (Xz α g k z θ),
      sq_abs (Yz α g k z θ)]
  have hX := Xz_sq_le_HkIntegrand α g k z θ
  have hY := Yz_sq_le_HkIntegrand α g k z θ
  rw [gK_eq_mul α f g k z θ hθI, abs_mul, abs_mul]
  calc |f z θ| * (|Xz α g k z θ| * |Yz α g k z θ|)
      ≤ Mf * (((Xz α g k z θ) ^ 2 + (Yz α g k z θ) ^ 2) / 2) :=
        mul_le_mul (hf z θ hz hθ.1 hθ.2) hAM (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hMf
    _ ≤ Mf * ((Work.Spaces.HkIntegrand α 5 g z θ + Work.Spaces.HkIntegrand α 5 g z θ) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hMf
    _ = Mf * Work.Spaces.HkIntegrand α 5 g z θ := by ring



/-! ## The one-dimensional integration by parts on the half line -/

/-- A function with a limit along `𝓝[>] a` (whose value at `a` is that limit) is continuous
within `Ici a` at `a`.  (The `Ioi`-filter is finer than the `Ici`-filter, so the implication
needs the explicit value; we prove it through the basis `Ico a u` of `𝓝[Ici a] a`.) -/
theorem tendsto_Ici_of_tendsto_Ioi {F : ℝ → ℝ} {a b : ℝ}
    (h : Filter.Tendsto F (nhdsWithin a (Set.Ioi a)) (nhds b)) (hb : F a = b) :
    Filter.Tendsto F (nhdsWithin a (Set.Ici a)) (nhds b) := by
  intro t ht
  obtain ⟨u, hau, hu⟩ := (nhdsGT_basis a).mem_iff.mp (h ht)
  refine (nhdsGE_basis_Ico a).mem_iff.mpr ⟨u, hau, ?_⟩
  rintro x ⟨hax, hxu⟩
  rcases eq_or_lt_of_le hax with rfl | hlt
  · simp only [Set.mem_preimage]
    rw [hb]
    exact mem_of_mem_nhds ht
  · exact hu ⟨hlt, hxu⟩

/-- **Integration by parts on `(0,∞)`.**  If `φ` and `V` are differentiable on `(0,∞)` with
derivatives `φ'` resp. `V'`, the products `φ V V'` and `φ' V²` are integrable on `(0,∞)`,
`|φ z| ≤ Mf · z w(z)²` and `z (V w)² → 0` at `0⁺` and at `+∞`, then
`∫_{0}^{∞} φ V V' = -(1/2) ∫_{0}^{∞} φ' V²`. -/
theorem zibp_Ioi {Mf : ℝ} (hMf : 0 ≤ Mf) {φ φ' V V' : ℝ → ℝ}
    (hderivφ : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt φ (φ' z) z)
    (hderivV : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt V (V' z) z)
    (hint1 : MeasureTheory.IntegrableOn (fun z => φ z * V z * V' z) (Set.Ioi (0 : ℝ)))
    (hint2 : MeasureTheory.IntegrableOn (fun z => φ' z * V z ^ 2) (Set.Ioi (0 : ℝ)))
    (hφbnd : ∀ z ∈ Set.Ici (0 : ℝ), |φ z| ≤ Mf * (z * (Work.Spaces.w z) ^ 2))
    (hlim0 : Filter.Tendsto (fun z => z * (V z * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hlimTop : Filter.Tendsto (fun z => z * (V z * Work.Spaces.w z) ^ 2) atTop (nhds 0)) :
    ∫ z in Set.Ioi (0 : ℝ), φ z * V z * V' z
      = -(1 / 2) * ∫ z in Set.Ioi (0 : ℝ), φ' z * V z ^ 2 := by
  -- `φ 0 = 0` (the bound at `z = 0` is `|φ 0| ≤ Mf · 0 = 0`)
  have hφ0 : φ 0 = 0 := by
    have h := hφbnd 0 (Set.mem_Ici.mpr le_rfl)
    have hw : (0 : ℝ) * (Work.Spaces.w 0) ^ 2 = 0 := by ring
    rw [hw, mul_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  set F : ℝ → ℝ := fun z => (1 / 2) * (φ z * V z ^ 2) with hF
  set F' : ℝ → ℝ := fun z => (1 / 2) * φ' z * V z ^ 2 + φ z * V z * V' z with hF'
  -- the derivative of `F`
  have hderivF : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt F (F' z) z := by
    intro z hz
    have h1 := ((hderivφ z hz).mul ((hderivV z hz).pow 2))
    have h2 := h1.const_mul (1 / 2)
    convert h2 using 1
    rw [hF']
    simp only [Pi.pow_apply]
    ring_nf
  have hintF : MeasureTheory.IntegrableOn F' (Set.Ioi (0 : ℝ)) := by
    have h3 : MeasureTheory.IntegrableOn (fun z => (1 / 2) * φ' z * V z ^ 2) (Set.Ioi (0 : ℝ)) :=
      (hint2.const_mul (1 / 2)).congr (Filter.Eventually.of_forall fun z => by ring)
    have h4 : MeasureTheory.IntegrableOn (fun z => φ z * V z * V' z) (Set.Ioi (0 : ℝ)) := hint1
    refine (h3.add h4).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply, hF']
  -- the two limits of `F`
  have hFbound : ∀ z ∈ Set.Ici (0 : ℝ), |F z| ≤ (1 / 2) * Mf * (z * (V z * Work.Spaces.w z) ^ 2) := by
    intro z hz
    have hzw : 0 ≤ z * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg hz (sq_nonneg _)
    have h := hφbnd z hz
    rw [hF]
    calc |(1 / 2) * (φ z * V z ^ 2)|
        = (1 / 2) * (|φ z| * V z ^ 2) := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2), abs_mul,
            abs_of_nonneg (sq_nonneg (V z))]
      _ ≤ (1 / 2) * ((Mf * (z * (Work.Spaces.w z) ^ 2)) * V z ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h (sq_nonneg _)) (by norm_num)
      _ = (1 / 2) * Mf * (z * (V z * Work.Spaces.w z) ^ 2) := by ring
  have hF0eq : F 0 = 0 := by
    rw [hF]; simp [hφ0]
  have hFtop : Filter.Tendsto F atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun z => (1 / 2) * Mf * (z * (V z * Work.Spaces.w z) ^ 2))
      (Filter.Eventually.of_forall fun z => norm_nonneg _) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with z hz
      rw [Real.norm_eq_abs]
      exact hFbound z hz
    · have h3 := hlimTop.const_mul ((1 / 2) * Mf)
      simpa only [mul_zero] using h3
  have hF0 : Filter.Tendsto F (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun z => (1 / 2) * Mf * (z * (V z * Work.Spaces.w z) ^ 2))
      (Filter.Eventually.of_forall fun z => norm_nonneg _) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with z hz
      rw [Real.norm_eq_abs]
      exact hFbound z (Set.mem_Ici.mpr (le_of_lt hz))
    · have h3 := hlim0.const_mul ((1 / 2) * Mf)
      simpa only [mul_zero] using h3
  have hcont : ContinuousWithinAt F (Set.Ici 0) 0 := by
    rw [ContinuousWithinAt]
    have hlim : Filter.Tendsto F (nhdsWithin (0:ℝ) (Set.Ici 0)) (nhds 0) :=
      tendsto_Ici_of_tendsto_Ioi hF0 hF0eq
    rw [hF0eq]
    exact hlim
  -- the fundamental theorem of calculus
  have hFTC : (∫ z in Set.Ioi (0 : ℝ), F' z) = 0 := by
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderivF hintF hFtop, hF0eq,
      sub_zero]
  -- split the integral and conclude
  have hsplit : (∫ z in Set.Ioi (0 : ℝ), F' z)
      = (1 / 2) * (∫ z in Set.Ioi (0 : ℝ), φ' z * V z ^ 2)
        + ∫ z in Set.Ioi (0 : ℝ), φ z * V z * V' z := by
    have h3 : MeasureTheory.IntegrableOn (fun z => (1 / 2) * φ' z * V z ^ 2)
        (Set.Ioi (0 : ℝ)) :=
      (hint2.const_mul (1 / 2)).congr (Filter.Eventually.of_forall fun z => by ring)
    have h4 : MeasureTheory.IntegrableOn (fun z => φ z * V z * V' z) (Set.Ioi (0 : ℝ)) := hint1
    rw [show (∫ z in Set.Ioi (0 : ℝ), F' z)
        = ∫ z in Set.Ioi (0 : ℝ),
            ((1 / 2) * φ' z * V z ^ 2 + φ z * V z * V' z) from by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      rw [hF']]
    have h5 : (∫ z in Set.Ioi (0:ℝ), (1 / 2) * φ' z * V z ^ 2)
        = (1 / 2) * ∫ z in Set.Ioi (0:ℝ), φ' z * V z ^ 2 := by
      rw [show (fun z => (1 / 2) * φ' z * V z ^ 2)
          = fun z => (1 / 2) * (φ' z * V z ^ 2) from by funext z; ring,
        MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_add h3 h4, h5]
  linarith [hFTC, hsplit]

/-! ## Continuity of the blocks on the open quadrant -/

theorem continuousOn_w_Qd :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.LocData.Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
  rw [hfun]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (Set.mem_prod.mp hp).1))

theorem continuousOn_w_sq_Qd :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) Work.FTS.LocData.Qd :=
  continuousOn_w_Qd.pow 2

theorem continuousOn_sinpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.LocData.Qd := by
  have hsinpos : ∀ p ∈ Work.FTS.LocData.Qd, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Set.mem_prod.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

theorem continuousOn_wdivsin_Qd :
    ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Work.FTS.LocData.Qd := by
  have hsinpos : ∀ p ∈ Work.FTS.LocData.Qd, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Set.mem_prod.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact continuousOn_w_Qd.div (continuousOn_sinpow_Qd _)
    (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))


theorem continuousOn_Wt_Qd (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.LocData.Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact continuousOn_w_Qd.mul (continuousOn_sinpow_Qd _)

theorem continuousOn_mixed_Qd {g : ℝ → ℝ → ℝ} (hsg : Work.FTS.LocData.SmoothQuad g) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2) Work.FTS.LocData.Qd := by
  refine ((Work.FTS.LocData.contDiffOn_mixed (V := Work.Spaces.quadU) Work.Spaces.isOpen_quadU hsg
    j i).continuousOn).mono ?_
  intro p hp
  obtain ⟨h1, h2⟩ := Set.mem_prod.mp hp
  have h1' : (0 : ℝ) < p.1 := h1
  exact Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr (by linarith), h2⟩









/-! ## The product measure, and a.e. statements on the open quadrant -/

/-- The product of the two restricted Lebesgue measures is the restriction of the planar
Lebesgue measure to `Iz ×ˢ Iθ`. -/
theorem prod_restrict_eq :
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      = (volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]

/-- A statement true on the whole open quadrant holds a.e. for the product of the two
restricted Lebesgue measures. -/
theorem ae_of_forall_Qd {P : ℝ × ℝ → Prop}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → P (z, θ)) :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)), P p := by
  have hz : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[(volume : MeasureTheory.Measure (ℝ × ℝ))] (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [prod_restrict_eq, MeasureTheory.Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_of_forall_mem (isOpen_Ioi.prod isOpen_Ioo).measurableSet
    fun p hp => h p.1 p.2 hp.1 hp.2.1 hp.2.2

/-- The open quadrant has full measure for the product of the two restricted Lebesgue
measures. -/
theorem ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hθ]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- A.e. membership in the open quadrant for the product measure. -/
theorem ae_mem_Qd : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod
    (volume.restrict Work.Spaces.Iθ)), 0 < p.1 ∧ 0 < p.2 ∧ p.2 < π / 2 :=
  ae_of_forall_Qd fun z θ hz hθ hθ' => ⟨hz, hθ, hθ'⟩

/-- The θ-marginal of a product-integrable function is a.e. integrable on `Iz`. -/
theorem ae_integrableOn_slice {H : ℝ × ℝ → ℝ}
    (hH : MeasureTheory.Integrable H
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => H (z, θ)) Work.Spaces.Iz := by
  have h := MeasureTheory.Integrable.prod_left_ae hH
  simpa only [MeasureTheory.IntegrableOn, Function.uncurry_apply_pair] using h

/-! ## The per-angle integration by parts identity -/


/-! ## Product-measure facts for the `ℋ^k`-integrand -/

/-- The uncurried `HkIntegrand α k g` is a.e. strongly measurable for the product of the
restricted Lebesgue measures, for `g` smooth on the open quadrant. -/
theorem aesm_HkIntegrand_prod {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.LocData.SmoothQuad g) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α k g hg)

/-- The `ℋ^k`-integrand of `g` is product-integrable with respect to the product of the two
restricted Lebesgue measures, and its product integral is `HkSq α k g`. -/
theorem integrable_HkIntegrand_prod {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α k g) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
      ∧ (∫ p, Work.Spaces.HkIntegrand α k g p.1 p.2
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        = Work.Spaces.HkSq α k g := by
  have h := Work.Spaces.integrable_prod_of_iterated
    (μ := volume.restrict Work.Spaces.Iz) (ν := volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => Work.Spaces.HkIntegrand α k g z θ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
    (aesm_HkIntegrand_prod hg)
    ((MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iz from
      measurableSet_Ici)).mpr (Filter.Eventually.of_forall fun z hz => hmem.1 z hz))
    hmem.2
  exact ⟨h.1, by rw [h.2]; rfl⟩




/-! ## Product-integrability of the blocks -/





/-! ## Product-measure facts for the `ℋ^k`-integrand -/
end Work.FTS.TransportS
end
end
-- ===== merged: Submission.Work.H2.T1Q.ExcBoundQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

open Work.Spaces

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Two elementary facts on the angular interval -/

/-- A point of `Iθ` at which `sin(2θ)` does not vanish is interior. -/
private theorem mem_Ioo_of_mem_Iθ_of_sin_ne {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hne : Real.sin (2 * θ) ≠ 0) : θ ∈ Set.Ioo 0 (π / 2) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le hθ.1 with h | h
    · exact absurd (by rw [← h]; simp) hne
    · exact h
  · rcases eq_or_lt_of_le hθ.2 with h | h
    · exact absurd (by rw [h, show 2 * (π / 2) = π by ring, Real.sin_pi]) hne
    · exact h

/-- `supAbsThO` is nonnegative whenever the slice is bounded. -/
private theorem supAbsThO_nonneg_aux {u : ℝ → ℝ → ℝ} {z : ℝ}
    (hb : BddAbove {y : ℝ | ∃ θ ∈ Set.Ioo 0 (π / 2), y = |u z θ|}) :
    0 ≤ Work.FTS.H2.supAbsThO u z :=
  le_trans (abs_nonneg _) (Work.FTS.H2.abs_le_supAbsThO
    (show (π / 4 : ℝ) ∈ Set.Ioo 0 (π / 2) by
      constructor <;> linarith [Real.pi_pos]) hb)



/-! ## The exceptional summand of `T1Easy` in the interior class -/


end Work.H2.T1Q
end
end
