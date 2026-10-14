import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.H2.HQ.BadsummandQ
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Aux.R.DthIbp
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.HardSlotLemGen
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Rl1.l12densMeasAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.Rl1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Work.FTS.Galerkin (Fn)

/-- The product measure of the `rl1` rows: Lebesgue measure on `(0,∞)` times Lebesgue measure
on `Iθ = [0,π/2]`. -/
abbrev rl1Meas : MeasureTheory.Measure (ℝ × ℝ) :=
  Work.FTS.Nonlinear.Pieces.rl1Tools.bmMeasure

/-! ## Generic tools -/

/-- The `rl1` product measure is the planar Lebesgue measure restricted to the open quadrant. -/
theorem rl1Meas_eq_prodRestrict :
    rl1Meas = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := by
  rw [rl1Meas, Work.FTS.Nonlinear.Pieces.rl1Tools.bmMeasure, MeasureTheory.Measure.prod_restrict]
  exact MeasureTheory.Measure.restrict_congr_set Work.FTS.Nonlinear.Pieces.rl1Tools.ae_prod_eq

/-- Almost every point of the `rl1` product measure has positive first coordinate. -/
theorem ae_fst_pos : ∀ᵐ p ∂rl1Meas, 0 < p.1 := by
  rw [rl1Meas_eq_prodRestrict]
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)]
    with p hp
  exact hp.1

/-- Almost every point of the `rl1` product measure has non-zero first coordinate. -/
theorem ae_fst_ne_zero : ∀ᵐ p ∂rl1Meas, p.1 ≠ 0 :=
  ae_fst_pos.mono fun _ hp => ne_of_gt hp

/-- Almost every point of the `rl1` product measure lies in the open quadrant. -/
theorem ae_mem_Qd : ∀ᵐ p ∂rl1Meas, p ∈ Work.Construction.Qd := by
  rw [rl1Meas_eq_prodRestrict]
  exact MeasureTheory.ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)


/-- The angular integrand `(z,θ) ↦ K(θ)·f(z,θ)/z` is a.e.-measurable as soon as the uncurried
datum is. -/
theorem aem_uncurry_K_mul_div {f : ℝ → ℝ → ℝ}
    (h : AEMeasurable (Function.uncurry f) rl1Meas) :
    AEMeasurable (Function.uncurry (fun z θ => Work.Spaces.K θ * f z θ / z)) rl1Meas := by
  have hK : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) rl1Meas :=
    (Work.Coercivity.K_facts_continuous.measurable.comp measurable_snd).aemeasurable
  have hinv : AEMeasurable (fun p : ℝ × ℝ => (p.1)⁻¹) rl1Meas :=
    (measurable_inv.comp measurable_fst).aemeasurable
  refine ((hK.mul h).mul hinv).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Function.uncurry, Pi.mul_apply, div_eq_mul_inv]

/-- A.e. strong measurability of the `L₁₂`-density from a.e.-measurability of the uncurried
datum, by Fubini measurability of the partial integral. -/
theorem aesm_L12dens_of_aem_uncurry {f : ℝ → ℝ → ℝ}
    (h : AEMeasurable (Function.uncurry f) rl1Meas) :
    AEStronglyMeasurable (fun s => Work.Construction.L12dens f s)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have h1 : AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Spaces.K θ * f z θ / z)) rl1Meas :=
    (aem_uncurry_K_mul_div h).aestronglyMeasurable
  have h2 := h1.integral_prod_right' (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
  refine h2.congr (Filter.Eventually.of_forall fun s => ?_)
  show (∫ (y : ℝ), Function.uncurry (fun z θ => Work.Spaces.K θ * f z θ / z) (s, y)
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) = Work.Construction.L12dens f s
  rfl



/-! ## Transfer of a.e.-measurability along the open quadrant -/





/-- `sin(2θ) ≠ 0` on the open angular interval. -/
theorem s2_ne_zero_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Construction.s2 θ ≠ 0 := by
  have h1 : 0 < 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ < Real.pi := by linarith [hθ.2, Real.pi_pos]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)


/-! ## The derived blocks of the `rl1` rows -/





/-! ## A.e.-measurability of the uncurried pieces of `N` -/






/-! ## A.e. strong measurability of the five group densities -/






end Work.FTS.Nonlinear.Pieces.Rl1
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E2hat_HkSq_le_uniform_O =====
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

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- `Iθ = [0,π/2]` and `(0,π/2)` differ by a null set. -/
private lemma restrict_Iθ_eq_Ioo :
    (volume : Measure ℝ).restrict Work.Spaces.Iθ
      = (volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)) :=
  (MeasureTheory.restrict_Ioo_eq_restrict_Icc (μ := (volume : Measure ℝ)) (a := 0)
    (b := π / 2)).symm

/-- **The `α`-uniform `ℋⁿ`-defect estimate on the open class.**  For every `α > 0` and every
`f ∈ RegQo α (n+1)`,

`HkSq α n (Ê₂ f) ≤ Cn · (HkSq α n f + HkSq α n (D_θ f))`

with a constant `Cn` depending only on `n`.  The angular slices are controlled pointwise by
`E2hatOAux.E2hat_HkIntegrand_le_uniform_pt` on `(0,π/2)` (a null complement of `Iθ`), and the
outer integrals by monotonicity, using `OpenPkg.HkMem_mono_open` for `f` and
`IPGen.HkMem_Dth_le` for `D_θ f`. -/
theorem E2hat_HkSq_le_uniform_O (n : ℕ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ α : ℝ, 0 < α → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f →
        Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
          ≤ Cn * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
  obtain ⟨Cn, hCnpos, hpt⟩ := E2hatOAux.E2hat_HkIntegrand_le_uniform_pt n
  refine ⟨Cn, hCnpos, ?_⟩
  intro α hαpos f hf
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.1
  have hmemf : Work.Spaces.HkMem α (n + 1) f := hf.2.1
  have hmf : Work.Spaces.HkMem α n f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm n (Nat.le_succ n) hmemf
  have hmth : Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := n) (by linarith : -(1 / 10 : ℝ) ≤ α) hsm hmemf
  -- the angular slice inequality, for every `z ∈ Iz`
  have hsl : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ)
        ≤ Cn * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
          + (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)) := by
    intro z hz
    have hzge : 0 ≤ z := hz
    rw [restrict_Iθ_eq_Ioo]
    rcases eq_or_lt_of_le hzge with hz0 | hzpos
    · subst hz0
      simp [Work.FTS.EllipticEst.HkIntegrand_eq_zero_of_z_eq_zero']
    · have h1 : Integrable (fun θ => Work.Spaces.HkIntegrand α n f z θ)
          ((volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) := by
        have h : Integrable (fun θ => Work.Spaces.HkIntegrand α n f z θ)
            ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
          hmf.1 z (Set.mem_Ici.mpr hzpos.le)
        rwa [restrict_Iθ_eq_Ioo] at h
      have h2 : Integrable (fun θ => Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)
          ((volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) := by
        have h : Integrable (fun θ => Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)
            ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
          hmth.1 z (Set.mem_Ici.mpr hzpos.le)
        rwa [restrict_Iθ_eq_Ioo] at h
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (μ := (volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)))
        (f := fun θ => Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ)
        (g := fun θ => Cn * (Work.Spaces.HkIntegrand α n f z θ
            + Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ))
        (Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α n (Work.FTS.CoercivityFix.E2hat f) z θ)
        ((h1.add h2).const_mul Cn)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => hpt α f hαpos hsm z hzpos θ hθ))
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add h1 h2] at hmono
      exact hmono
  -- the outer integral, by monotonicity
  have hint : Integrable (fun z => Cn *
      ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
        + (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)))
      ((volume : Measure ℝ).restrict Work.Spaces.Iz) := (hmf.2.add hmth.2).const_mul Cn
  have hout := MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg
      (fun θ => Work.Spaces.HkIntegrand_nonneg α n (Work.FTS.CoercivityFix.E2hat f) z θ))
    hint (MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)
      (fun z hz => hsl z hz))
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hmf.2 hmth.2] at hout
  simpa only [Work.Spaces.HkSq] using hout

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.C0EfAux.SliceAe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OClass.C0EfAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The angular slice of a `SmoothOpen` datum -/

/-- The angular slice of a `SmoothOpen` datum is a.e. strongly measurable: it is continuous on
the open interval `(0, π/2)`, which is conull in `Iθ`.  (The open-class analogue of
`Work.FTS.CoercivityFix.Coer1T.aesm_slice_theta_Q`.) -/
theorem aesm_slice_theta_O {g : Fn} (hso : Work.FTS.EllipticEst.SmoothOpen g) {s : ℝ}
    (hs : 0 < s) :
    MeasureTheory.AEStronglyMeasurable (fun θ => g s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => g p.1 p.2) hso.continuousOn hs

/-- A.e. in `z`, the angular slice `θ ↦ f z θ` is integrable, for open-class data satisfying the
`IntPkgO` integrability certificate.  (The open-class analogue of
`Work.FTS.CoercivityFix.Coer1T.ae_integrableOn_slice_f`.) -/
theorem ae_integrableOn_slice_f_O (α : ℝ) {f : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => f s θ) Work.Spaces.Iθ := by
  have hP0 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      f p.1 p.2 ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hIP.sqDzEta 0 (by norm_num)
  filter_upwards [hP0.prod_right_ae, Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos]
    with s hs hspos
  have hRho : (fun θ => f s θ ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta s θ)
      = fun θ => Work.Spaces.w s ^ 2
          * (f s θ ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ) := by
    funext θ
    simp only [Work.FTS.CoercivityFix.Coer1.Rho]
    ring
  rw [hRho] at hs
  have hwpos : (0 : ℝ) < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hwne : Work.Spaces.w s ^ 2 ≠ 0 := by positivity
  have hs2 : MeasureTheory.Integrable
      (fun θ => f s θ ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hwne) _).mp hs
  have hs3 : MeasureTheory.Integrable (fun θ => f s θ ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hs2
      ((aesm_slice_theta_O hso hspos).pow 2) ?_
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : 1 ≤ Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ :=
      Work.FTS.CoercivityFix.Coer1.one_le_sig_eta hθ
    nlinarith [sq_nonneg (f s θ)]
  have h4 : MeasureTheory.Integrable (fun θ => (1 : ℝ) / 2 + (1 / 2) * f s θ ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integrable_const _).add (hs3.const_mul (1 / 2))
  refine h4.mono' (aesm_slice_theta_O hso hspos) ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|f s θ| - 1), sq_abs (f s θ)]

/-- A.e. in `z`, the angular slice `θ ↦ D_θ f z θ` is integrable, for open-class data satisfying
the `IntPkgO` integrability certificate.  (The open-class analogue of
`Work.FTS.CoercivityFix.Coer1T.ae_integrableOn_slice_Dth`.) -/
theorem ae_integrableOn_slice_Dth_O (α : ℝ) (hα : 0 < α) {f : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.Dth f s θ) Work.Spaces.Iθ := by
  have hP2 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.Dth f p.1 p.2 ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho
        (Work.Spaces.gam α) p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    refine (hIP.sqMixedGam 1 0 (by norm_num) (by norm_num)).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Ici.prod measurableSet_Icc)] with p hp'
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.mixed, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
  filter_upwards [hP2.prod_right_ae, Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos]
    with s hs hspos
  have hRho : (fun θ => Work.Spaces.Dth f s θ ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) s θ)
      = fun θ => Work.Spaces.w s ^ 2
          * (Work.Spaces.Dth f s θ ^ 2 * Work.FTS.CoercivityFix.Coer1.sig
              (Work.Spaces.gam α) θ) := by
    funext θ
    simp only [Work.FTS.CoercivityFix.Coer1.Rho]
    ring
  rw [hRho] at hs
  have hwpos : (0 : ℝ) < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hwne : Work.Spaces.w s ^ 2 ≠ 0 := by positivity
  have hs2 : MeasureTheory.Integrable
      (fun θ => Work.Spaces.Dth f s θ ^ 2 * Work.FTS.CoercivityFix.Coer1.sig
        (Work.Spaces.gam α) θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hwne) _).mp hs
  have hs3 : MeasureTheory.Integrable (fun θ => Work.Spaces.Dth f s θ ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hs2
      ((aesm_slice_theta_O hso.Dth hspos).pow 2) ?_
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hγ : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; positivity
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hsin0 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hs1 : 1 ≤ Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ := by
      have h1 := Real.rpow_le_rpow_of_exponent_ge hsin0 hsin1
        (show -(Work.Spaces.gam α) ≤ -(0 : ℝ) by linarith [hγ])
      rw [neg_zero, Real.rpow_zero] at h1
      simpa only [Work.FTS.CoercivityFix.Coer1.sig] using h1
    nlinarith [sq_nonneg (Work.Spaces.Dth f s θ)]
  have h4 : MeasureTheory.Integrable
      (fun θ => (1 : ℝ) / 2 + (1 / 2) * Work.Spaces.Dth f s θ ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integrable_const _).add (hs3.const_mul (1 / 2))
  refine h4.mono' (aesm_slice_theta_O hso.Dth hspos) ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|Work.Spaces.Dth f s θ| - 1), sq_abs (Work.Spaces.Dth f s θ)]

end Work.FTS.StrongEps.EpsE4Thr.OClass.C0EfAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.Zrest_pairing_ge_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OClass

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The two bounds on the nonlocal deflection `Z₃ + Z₄ + Z₇` of `D_z𝓛_Γ^T`, open class.**

This is the `SmoothOpen`/`IntPkgO` port of `Work.FTS.CoercivityFix.Coer1T.Zrest_pairing_ge_Q`.
The two pointwise inputs `Coer1T.Zrest_sq_pt` and `Coer1T.continuousOn_Zrest_Q` are class-free
(they only use `HardyHyp`), so the whole proof transcribes verbatim once the interior bundle
`Coer1.IntPkg_Q α hα hf2` is replaced by the hypothesis `hIP : IntPkgO α f` and the closed-class
continuity `Coer1.continuousOn_DzIter_Q hsq 1` by its open twin
`IntPkgOAux.continuousOn_DzIter_O hso 1`. -/
theorem Zrest_pairing_ge_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) {f : Work.FTS.Galerkin.Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hf2 : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f)
    (hfH : Work.Coercivity.HardyHyp f)
    (hC0 : (Work.Coercivity.C0 f) ^ 2 ≤ 64 * Work.Coercivity.Ef f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    ∧ Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
        (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
          + Work.Coercivity.Z7 α f z θ)
        (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
          + Work.Coercivity.Z7 α f z θ) ≤ 10 ^ 9 * Work.Coercivity.Ef f
    ∧ MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ) * Work.Spaces.Dz f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    ∧ -((1 / 40) * Work.Coercivity.EDz f + 10 ^ 10 * Work.Coercivity.Ef f)
        ≤ Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
            (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
              + Work.Coercivity.Z7 α f z θ) (Work.Spaces.Dz f) := by
  have hα1' : α ≤ 1 := by linarith
  have hp := hIP
  have hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      0 ≤ Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ :=
    fun z θ hθ => Work.FTS.CoercivityFix.Coer1.Rho_nonneg Work.Spaces.eta z θ hθ
  have hEf0 : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
  -- ## integral data for the `θ`-factor
  have hsig_int : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ) Work.Spaces.Iθ :=
    (Work.Coercivity.integral_sin_two_neg_rpow_le Work.Spaces.eta
      (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)).1
  have hsig_le : ∫ θ in Work.Spaces.Iθ,
      Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ ≤ 400 := by
    have h := (Work.Coercivity.integral_sin_two_neg_rpow_le Work.Spaces.eta
      (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)).2
    rw [show (4 : ℝ) / (1 - Work.Spaces.eta) = 400 by rw [Work.Spaces.eta]; norm_num] at h
    exact h
  -- ## integral data for the three `z`-factors
  have hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Work.Spaces.w z) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hp.sqDzOne 0 (by norm_num)).congr_fun ?_ (measurableSet_Ici.prod measurableSet_Icc)
    rintro ⟨z, θ⟩ _
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
    ring
  have hsl := Work.Coercivity.EL12z_ae_slice f hfw
  have hDens := Work.Coercivity.EL12z_Kd f hfH hsl
  have hDens_le : ∫ z in Set.Ioi (0 : ℝ),
      (Work.FM.L12dens Work.Spaces.K f z) ^ 2 ≤ 3 * Work.Coercivity.Ef f := by
    have h2 := Work.Coercivity.EL12z_weight f hfw hsl
    linarith [hDens.2, h2]
  have hLz_int : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Coercivity.L12f f z / z) ^ 2) (Set.Ioi 0) := by
    refine (hfH.intA 1 (by norm_num)).congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Nat.cast_one, mul_one, Real.rpow_two, div_pow]
  have hLz_le : ∫ z in Set.Ioi (0 : ℝ), (Work.Coercivity.L12f f z / z) ^ 2
      ≤ 16 * Work.Coercivity.Ef f := by
    have h := Work.Coercivity.EL12z_le f hfH hfw
    rw [Work.Coercivity.EL12z, Work.Coercivity.L2Sqz] at h
    rwa [Work.FTS.CoercivityFix.Coer1T.setIntegral_Iz_eq_Ioi] at h
  have hInv_int : MeasureTheory.IntegrableOn (fun z : ℝ => (1 + z) ^ (-2 : ℝ)) (Set.Ioi 0) := by
    refine (integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := (0 : ℝ)) (m := (1 : ℝ))
      (by norm_num) (by norm_num)).congr (Filter.Eventually.of_forall (fun z => ?_))
    show (z + 1) ^ (-2 : ℝ) = (1 + z) ^ (-2 : ℝ)
    rw [show z + 1 = 1 + z by ring]
  have hInv_val : ∫ z in Set.Ioi (0 : ℝ), (1 + z) ^ (-2 : ℝ) = 1 := by
    have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun z : ℝ => -((1 + z)⁻¹)) ((1 + x) ^ (-2 : ℝ)) x := by
      intro x hx
      have hx0 : (0 : ℝ) < 1 + x := by
        have hx' : (0 : ℝ) < x := hx
        linarith
      have h1 : HasDerivAt (fun z : ℝ => 1 + z) (1 : ℝ) x := (hasDerivAt_id x).const_add 1
      have h2 : HasDerivAt (fun z : ℝ => (1 + z)⁻¹) (-((1 + x) ^ 2)⁻¹) x := by
        have h := h1.inv (ne_of_gt hx0)
        convert h using 1
        ring
      have h3 : HasDerivAt (fun z : ℝ => -((1 + z)⁻¹)) (-(-((1 + x) ^ 2)⁻¹)) x := h2.neg
      refine h3.congr_deriv ?_
      rw [neg_neg, show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg (x := 1 + x) (le_of_lt hx0) 2, Real.rpow_two]
    have hcont : ContinuousWithinAt (fun z : ℝ => -((1 + z)⁻¹)) (Set.Ici 0) 0 := by
      refine ContinuousAt.neg ?_ |>.continuousWithinAt
      exact ContinuousAt.inv₀ (continuousAt_const.add continuousAt_id) (by norm_num)
    have htend : Filter.Tendsto (fun z : ℝ => -((1 + z)⁻¹)) Filter.atTop (𝓝 (0 : ℝ)) := by
      have h : Filter.Tendsto (fun z : ℝ => (1 + z)⁻¹) Filter.atTop (𝓝 0) :=
        Filter.Tendsto.comp tendsto_inv_atTop_zero
          (tendsto_atTop_add_const_left atTop 1 tendsto_id)
      simpa using h.neg
    have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
      (f := fun z : ℝ => -((1 + z)⁻¹)) (f' := fun z : ℝ => (1 + z) ^ (-2 : ℝ)) (m := 0)
      hcont hderiv hInv_int htend
    simpa using h
  -- ## the three summands of the bracket, over `(0,∞)` and over `Iz`
  have hb1 : MeasureTheory.IntegrableOn (fun z : ℝ =>
      4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2) (Set.Ioi 0) :=
    (hDens.1.const_mul 4).congr (Filter.Eventually.of_forall (fun z => by ring))
  have hb2 : MeasureTheory.IntegrableOn (fun z : ℝ =>
      4 * (Work.Coercivity.L12f f z / z) ^ 2) (Set.Ioi 0) :=
    (hLz_int.const_mul 4).congr (Filter.Eventually.of_forall (fun z => by ring))
  have hb3 : MeasureTheory.IntegrableOn (fun z : ℝ =>
      16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2) (Set.Ioi 0) := by
    refine ((hInv_int.const_mul (16 * (Work.Coercivity.C0 f) ^ 2))).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hz0 : (0 : ℝ) < 1 + z := by
      have hz' : (0 : ℝ) < z := hz
      linarith
    rw [Real.rpow_neg (x := 1 + z) (le_of_lt hz0) 2, Real.rpow_two]
    field_simp
  have hb3val : ∫ z in Set.Ioi (0 : ℝ),
      16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2 = 16 * (Work.Coercivity.C0 f) ^ 2 := by
    rw [show (∫ z in Set.Ioi (0 : ℝ), 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ),
            (16 * (Work.Coercivity.C0 f) ^ 2) * ((1 + z) ^ (-2 : ℝ)) from by
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
      filter_upwards with z hz
      have hz' : (0 : ℝ) < z := hz
      have hz0 : (0 : ℝ) < 1 + z := by linarith
      rw [Real.rpow_neg (x := 1 + z) (le_of_lt hz0) 2, Real.rpow_two]
      field_simp]
    rw [MeasureTheory.integral_const_mul, hInv_val, mul_one]
  -- ## the bracket: integrability and integral bound
  have hbr_int : MeasureTheory.IntegrableOn
      (Work.FTS.CoercivityFix.Coer1T.ZrestBracket f) Work.Spaces.Iz :=
    (Work.FTS.CoercivityFix.Coer1T.integrableOn_Iz_iff_Ioi _).mpr (by
      refine ((hb1.add hb2).add hb3).congr (Filter.Eventually.of_forall (fun z => ?_))
      simp only [Work.FTS.CoercivityFix.Coer1T.ZrestBracket, Pi.add_apply])
  have hbr_le : ∫ z in Work.Spaces.Iz, Work.FTS.CoercivityFix.Coer1T.ZrestBracket f z
      ≤ 1100 * Work.Coercivity.Ef f := by
    have hIz : ∫ z in Work.Spaces.Iz, Work.FTS.CoercivityFix.Coer1T.ZrestBracket f z
        = ∫ z in Set.Ioi (0 : ℝ), Work.FTS.CoercivityFix.Coer1T.ZrestBracket f z :=
      Work.FTS.CoercivityFix.Coer1T.setIntegral_Iz_eq_Ioi _
    rw [hIz]
    have hsplit : ∫ z in Set.Ioi (0 : ℝ), Work.FTS.CoercivityFix.Coer1T.ZrestBracket f z
        = (∫ z in Set.Ioi (0 : ℝ), 4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2)
          + (∫ z in Set.Ioi (0 : ℝ), 4 * (Work.Coercivity.L12f f z / z) ^ 2)
          + (∫ z in Set.Ioi (0 : ℝ), 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2) := by
      simp only [Work.FTS.CoercivityFix.Coer1T.ZrestBracket]
      have hAB : MeasureTheory.IntegrableOn (fun z : ℝ =>
          4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
            + 4 * (Work.Coercivity.L12f f z / z) ^ 2) (Set.Ioi 0) :=
        (hb1.add hb2).congr (Filter.Eventually.of_forall (fun z => by
          simp only [Pi.add_apply]))
      rw [MeasureTheory.integral_add
          (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
          (f := fun z : ℝ => 4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
            + 4 * (Work.Coercivity.L12f f z / z) ^ 2)
          (g := fun z : ℝ => 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2)
          hAB hb3,
        MeasureTheory.integral_add
          (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
          (f := fun z : ℝ => 4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2)
          (g := fun z : ℝ => 4 * (Work.Coercivity.L12f f z / z) ^ 2)
          hb1 hb2]
    rw [hsplit, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hb3val]
    nlinarith [hDens_le, hLz_le, hC0, hEf0]
  -- ## integrability of the majorant and domination of `S²ρ`
  have hmaj_int : MeasureTheory.IntegrableOn
      (Function.uncurry (Work.FTS.CoercivityFix.Coer1T.ZrestMaj f))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have hθ : MeasureTheory.Integrable
        (fun θ : ℝ => 300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hsig_int.const_mul 300
    have hz : MeasureTheory.Integrable (Work.FTS.CoercivityFix.Coer1T.ZrestBracket f)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := hbr_int
    have h := hz.mul_prod hθ
    rw [MeasureTheory.IntegrableOn, ← Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.FTS.CoercivityFix.Coer1T.ZrestMaj]
    ring
  have hS2_cont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
        + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
    ((Work.FTS.CoercivityFix.Coer1T.continuousOn_Zrest_Q α hα hα1' hfH).pow 2).mul
      (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho Work.Spaces.eta)
  have hS2_int : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine Work.FTS.CoercivityFix.Coer1.integrableOn_of_le_Q hS2_cont hmaj_int ?_
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos,
      Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo] with p hp1 hp2
    have hθmem : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
    have h := Work.FTS.CoercivityFix.Coer1T.Zrest_sq_pt (f := f) α hα hα1' hp1 hθmem
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hρnn p.1 p.2 hθmem))]
    simp only [Work.FTS.CoercivityFix.Coer1T.ZrestMaj,
      Work.FTS.CoercivityFix.Coer1T.ZrestBracket]
    exact h
  -- ## the product-measure forms and the bound on `wip ρ S S`
  have hS2_prod : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
        + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hS2_int
  have hmaj_prod : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.Coer1T.ZrestMaj f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hmaj_int
  have hS2_wip : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ)
      (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ)
      = ∫ p : ℝ × ℝ, ((Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
          + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.Coercivity.wip]
    rw [MeasureTheory.integral_prod]
    · refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [Work.FTS.CoercivityFix.Coer1.Rho]
      ring
    · exact hS2_prod
  have hS_bound : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ)
      (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ) ≤ 10 ^ 9 * Work.Coercivity.Ef f := by
    have hprod : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
        (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
          + Work.Coercivity.Z7 α f z θ)
        (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
          + Work.Coercivity.Z7 α f z θ)
        = ∫ p : ℝ × ℝ, ((Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
            + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
            * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hS2_wip
    rw [hprod]
    have hmono : (∫ p : ℝ × ℝ, ((Work.Coercivity.Z3 α f p.1 p.2
            + Work.Coercivity.Z4 α f p.1 p.2 + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
            * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ ∫ p : ℝ × ℝ, Work.FTS.CoercivityFix.Coer1T.ZrestMaj f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      refine MeasureTheory.integral_mono_ae hS2_prod hmaj_prod ?_
      filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos,
        Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo] with p hp1 hp2
      have hθmem : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
      have h := Work.FTS.CoercivityFix.Coer1T.Zrest_sq_pt (f := f) α hα hα1' hp1 hθmem
      simp only [Work.FTS.CoercivityFix.Coer1T.ZrestMaj,
        Work.FTS.CoercivityFix.Coer1T.ZrestBracket]
      exact h
    have hmaj_val : (∫ p : ℝ × ℝ, Work.FTS.CoercivityFix.Coer1T.ZrestMaj f p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ≤ 10 ^ 9 * Work.Coercivity.Ef f := by
      rw [show (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.Coer1T.ZrestMaj f p.1 p.2)
          = fun p : ℝ × ℝ => Work.FTS.CoercivityFix.Coer1T.ZrestBracket f p.1
              * (300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta p.2) from by
        funext p
        simp only [Work.FTS.CoercivityFix.Coer1T.ZrestMaj]
        ring]
      rw [MeasureTheory.integral_prod_mul
        (f := Work.FTS.CoercivityFix.Coer1T.ZrestBracket f)
        (g := fun θ : ℝ => 300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ)]
      have h1 : ∫ θ in Work.Spaces.Iθ,
          300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ ≤ 120000 := by
        rw [MeasureTheory.integral_const_mul]
        have h2 : (300 : ℝ) * ∫ θ in Work.Spaces.Iθ,
            Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ ≤ 120000 := by
          have h2' := mul_le_mul_of_nonneg_left hsig_le (show (0 : ℝ) ≤ 300 by norm_num)
          norm_num at h2'
          exact h2'
        exact h2
      have h3 : 0 ≤ ∫ θ in Work.Spaces.Iθ,
          300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ := by
        rw [MeasureTheory.integral_const_mul]
        refine mul_nonneg (by norm_num) ?_
        refine integral_nonneg_of_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact Real.rpow_nonneg (Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ) _
      have h4 : (0 : ℝ) ≤ 1100 * Work.Coercivity.Ef f := mul_nonneg (by norm_num) hEf0
      exact le_trans (mul_le_mul hbr_le h1 h3 h4) (by nlinarith [hEf0])
    linarith [hmono, hmaj_val]
  -- ## the pairing with `D_z f`
  have hDz2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dz f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hp.sqDzEta 1 (by norm_num)).congr_fun ?_
      (measurableSet_Ici.prod measurableSet_Icc)
    rintro ⟨z, θ⟩ _
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  have hDz2_prod : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.Dz f p.1 p.2) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho
        Work.Spaces.eta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hDz2
  have hpair_cont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
        + Work.Coercivity.Z7 α f p.1 p.2) * Work.Spaces.Dz f p.1 p.2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
    ((Work.FTS.CoercivityFix.Coer1T.continuousOn_Zrest_Q α hα hα1' hfH).mul
      (Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.continuousOn_DzIter_O hso 1)).mul
      (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho Work.Spaces.eta)
  have hpair_maj : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (1 / 40) * ((Work.Spaces.Dz f z θ) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)
        + 10 * ((Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
            + Work.Coercivity.Z7 α f z θ) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    (hDz2.const_mul (1 / 40)).add (hS2_int.const_mul 10)
  have hpair_pt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
          + Work.Coercivity.Z7 α f z θ) * Work.Spaces.Dz f z θ
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ|
        ≤ (1 / 40) * ((Work.Spaces.Dz f z θ) ^ 2
            * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)
          + 10 * ((Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
              + Work.Coercivity.Z7 α f z θ) ^ 2
            * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ) := by
    intro z hz θ hθ
    have hρp : 0 ≤ Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ := hρnn z θ hθ
    have hkey : 0 ≤ Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
        * (|Work.Spaces.Dz f z θ| - 20 * |(Work.Coercivity.Z3 α f z θ
            + Work.Coercivity.Z4 α f z θ + Work.Coercivity.Z7 α f z θ)|) ^ 2 :=
      mul_nonneg hρp (sq_nonneg _)
    have hDzsq : |Work.Spaces.Dz f z θ| ^ 2 = (Work.Spaces.Dz f z θ) ^ 2 := sq_abs _
    have hSsq : |(Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ)| ^ 2
        = (Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
            + Work.Coercivity.Z7 α f z θ) ^ 2 := sq_abs _
    rw [abs_mul, abs_mul, abs_of_nonneg hρp]
    nlinarith [hkey, hDzsq, hSsq]
  have hpair_int : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ) * Work.Spaces.Dz f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine Work.FTS.CoercivityFix.Coer1.integrableOn_of_le_Q hpair_cont hpair_maj ?_
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos,
      Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo] with p hp1 hp2
    exact hpair_pt p.1 (le_of_lt hp1) p.2 ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
  refine ⟨hS2_int, hS_bound, hpair_int, ?_⟩
  -- ## the lower bound for the pairing
  have hprod' : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ) (Work.Spaces.Dz f)
      = ∫ p : ℝ × ℝ, ((Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
          + Work.Coercivity.Z7 α f p.1 p.2) * Work.Spaces.Dz f p.1 p.2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Coercivity.wip_eq_integral_prod _ _ _ hpair_int
  rw [hprod']
  have hpair_prod : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
        + Work.Coercivity.Z7 α f p.1 p.2) * Work.Spaces.Dz f p.1 p.2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hpair_int
  have hpair_maj_prod : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (1 / 40) * ((Work.Spaces.Dz f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
        + 10 * ((Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
            + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hpair_maj
  have hmono2 : (∫ p : ℝ × ℝ, -((1 / 40) * ((Work.Spaces.Dz f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
        + 10 * ((Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
            + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2))
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ ∫ p : ℝ × ℝ, ((Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
          + Work.Coercivity.Z7 α f p.1 p.2) * Work.Spaces.Dz f p.1 p.2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine MeasureTheory.integral_mono_ae hpair_maj_prod.neg hpair_prod ?_
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos,
      Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo] with p hp1 hp2
    have h := hpair_pt p.1 (le_of_lt hp1) p.2 ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
    linarith [neg_le_of_abs_le h]
  have hval : (∫ p : ℝ × ℝ, -((1 / 40) * ((Work.Spaces.Dz f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
        + 10 * ((Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
            + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2))
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = -((1 / 40) * Work.Coercivity.EDz f + 10 * Work.Coercivity.wip
          (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
            + Work.Coercivity.Z7 α f z θ)
          (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
            + Work.Coercivity.Z7 α f z θ)) := by
    rw [MeasureTheory.integral_neg, MeasureTheory.integral_add
      (hDz2_prod.const_mul (1 / 40)) (hS2_prod.const_mul 10),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hA : (∫ p : ℝ × ℝ, (Work.Spaces.Dz f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        = Work.Coercivity.EDz f := by
      rw [Work.Coercivity.EDz_eq_wip]
      rw [Work.Coercivity.wip_eq_integral_prod
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (Work.Spaces.Dz f) (Work.Spaces.Dz f) ?_]
      · refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        rcases p with ⟨z, θ⟩
        simp only [Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]
        rw [show (2 : ℝ) * θ = θ * 2 by ring]
        ring
      · refine hDz2.congr_fun ?_ (measurableSet_Ici.prod measurableSet_Icc)
        rintro ⟨z, θ⟩ _
        simp only [Function.uncurry_apply_pair, Work.FTS.CoercivityFix.Coer1.Rho,
          Work.FTS.CoercivityFix.Coer1.sig]
        rw [show (2 : ℝ) * θ = θ * 2 by ring]
        ring
    rw [hA, ← hS2_wip]
  linarith [hmono2, hval, hS_bound]

end Work.FTS.StrongEps.EpsE4Thr.OClass
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.R.SlotsBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux.R

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000
/-- The angular weight `ρ_β = w²·sin(2θ)^{-β}` (the paper's `w²sin^{-β}`). -/
abbrev Rhoq (β : ℝ) : Fn := Work.FTS.CoercivityFix.Coer1.Rho β

/-- The open quadrant of `SmoothOpen`. -/
abbrev Q0 : Set (ℝ × ℝ) := Work.FTS.EllipticEst.Q0

/-- The product measure on the quadrant is the restriction of the planar measure. -/
theorem pm_eq_restrict :
    (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = MeasureTheory.volume.restrict ((Work.Spaces.Iz : Set ℝ) ×ˢ (Work.Spaces.Iθ : Set ℝ)) := by
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]

/-- Almost every angle of the quadrant is interior. -/
theorem ae_angle_Ioo :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Set.Ioo 0 (Real.pi / 2) :=
  Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo

/-- Almost every point of the quadrant has positive radius. -/
theorem ae_radius_pos : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 < p.1 :=
  Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos

/-! ## Elementary `wip` manipulations -/



/-- `wip ρ u u` is the iterated integral of `u²ρ`. -/
theorem wip_self_eq (ρ u : Fn) :
    Work.Coercivity.wip ρ u u
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, u z θ ^ 2 * ρ z θ := by
  simp only [Work.Coercivity.wip]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with z
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
  intro θ _; ring



/-! ## The `ℋ²`-integrand is integrable -/

/-- `HkIntegrand α k h` is jointly integrable on the quadrant when `h ∈ ℋᵏ` and is smooth
on the open quadrant. -/
theorem int_HkIntegrand (α : ℝ) (k : ℕ) {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h)
    (hm : Work.Spaces.HkMem α k h) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α k h z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hsm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α k h z θ)) ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (hs.continuousOn_HkIntegrand α k)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α k h z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hm.1
  have hmain := (Work.Spaces.integrable_prod_of_iterated
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k h z θ) hsm hslice hm.2).1
  rw [MeasureTheory.IntegrableOn, ← pm_eq_restrict]
  exact hmain

/-- `HkSq α k h` as a product-measure integral of `HkIntegrand α k h`. -/
theorem HkSq_eq_prod (α : ℝ) (k : ℕ) {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h)
    (hm : Work.Spaces.HkMem α k h) :
    Work.Spaces.HkSq α k h
      = ∫ p : ℝ × ℝ, Work.Spaces.HkIntegrand α k h p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hsm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α k h z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (hs.continuousOn_HkIntegrand α k)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α k h z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hm.1
  exact (Work.Spaces.integrable_prod_of_iterated
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k h z θ) hsm hslice hm.2).2.symm

/-- **A self-pairing dominated by a multiple of the `ℋ^k`-integrand** is bounded by `C·HkSq`. -/
theorem wip_self_le_mul_HkSq (α : ℝ) (k : ℕ) {h u : Fn} {ρ : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α k h) {C : ℝ}
    (hC : 0 ≤ C)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hb : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        u p.1 p.2 * u p.1 p.2 * ρ p.1 p.2
          ≤ C * Work.Spaces.HkIntegrand α k h p.1 p.2) :
    Work.Coercivity.wip ρ u u ≤ C * Work.Spaces.HkSq α k h := by
  rw [Work.Coercivity.wip_eq_integral_prod ρ u u hint, HkSq_eq_prod α k hs hm]
  have hint' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => u p.1 p.2 * u p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.IntegrableOn] at hint
    rw [← pm_eq_restrict] at hint
    exact hint
  have hbase := int_HkIntegrand α k hs hm
  have hbase' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => C * Work.Spaces.HkIntegrand α k h p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.IntegrableOn] at hbase
    rw [← pm_eq_restrict] at hbase
    exact hbase.const_mul C
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_mono_ae hint' hbase' hb

/-- **A self-pairing dominated pointwise by the `ℋ^k`-integrand is bounded by `HkSq α k h`.** -/
theorem wip_self_le_HkSq (α : ℝ) (k : ℕ) {h u : Fn} {ρ : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α k h)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (u z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hb : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        (u p.1 p.2) ^ 2 * ρ p.1 p.2 ≤ Work.Spaces.HkIntegrand α k h p.1 p.2) :
    Work.Coercivity.wip ρ u u ≤ Work.Spaces.HkSq α k h := by
  have hint' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hint.congr ?_
    filter_upwards with p
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, sq]
  have := wip_self_le_mul_HkSq α k hs hm (C := 1) (by norm_num) hint'
    (hb.mono (fun p hp => by simpa only [sq, one_mul] using hp))
  simpa using this
/-- **A.e. congruence of `wip` in its first argument** (no integrability needed). -/
theorem wip_congr_fst_ae {ρ A B g : Fn}
    (h : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), A p.1 p.2 = B p.1 p.2) :
    Work.Coercivity.wip ρ A g = Work.Coercivity.wip ρ B g := by
  simp only [Work.Coercivity.wip]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.Measure.ae_ae_of_ae_prod h] with z hz
  exact MeasureTheory.integral_congr_ae (hz.mono (fun θ hθ => by
    show A z θ * g z θ * ρ z θ = B z θ * g z θ * ρ z θ
    rw [hθ]))

/-! ## Weight facts -/

theorem ae_snd_mem_Iθ :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ :=
  Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem measurableSet_Icc
    (MeasureTheory.ae_restrict_mem measurableSet_Icc)

theorem Rhoq_eta_le_gam (α : ℝ) (hα : 0 < α) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      Rhoq Work.Spaces.eta p.1 p.2 ≤ Rhoq (Work.Spaces.gam α) p.1 p.2 := by
  filter_upwards [ae_snd_mem_Iθ] with p hp
  exact Work.FTS.CoercivityFix.Coer1.Rho_eta_le_Rho_gam α hα p.1 p.2 hp



/-- `(w / s^{b/2})² = w²·s^{-b}` for `s > 0`. -/
theorem div_half_sq (s w b : ℝ) (hs : 0 < s) :
    (w / s ^ (b / 2)) ^ 2 = w ^ 2 * s ^ (-b) := by
  have h2 : (s ^ (b / 2)) ^ (2 : ℝ) = (s ^ (b / 2)) ^ (2 : ℕ) := Real.rpow_natCast _ 2
  have hsp : s ^ b = (s ^ (b / 2)) ^ (2 : ℝ) := by
    rw [← Real.rpow_mul hs.le (b / 2) 2]
    norm_num
  rw [div_pow, ← h2, ← hsp, div_eq_mul_inv, Real.rpow_neg hs.le b]

/-- `(w·s^{-b/2})² = w²·s^{-b}` for `s > 0`. -/
theorem mul_half_sq (s w b : ℝ) (hs : 0 < s) :
    (w * s ^ (-(b / 2))) ^ 2 = w ^ 2 * s ^ (-b) := by
  have h2 : (s ^ (-(b / 2))) ^ (2 : ℝ) = (s ^ (-(b / 2))) ^ (2 : ℕ) := Real.rpow_natCast _ 2
  have hsp : s ^ (-b) = (s ^ (-(b / 2))) ^ (2 : ℝ) := by
    rw [← Real.rpow_mul hs.le (-(b / 2)) 2]
    norm_num
  rw [mul_pow, ← h2, ← hsp]

/-- **Integrability by domination.**  An integrand continuous on the open quadrant and a.e.
dominated by `C·HkIntegrand α k h` with `h ∈ ℋᵏ` is integrable. -/
theorem integrableOfHkDom (α : ℝ) (k : ℕ) {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h)
    (hm : Work.Spaces.HkMem α k h) {X : Fn} {C : ℝ}
    (hcont : ContinuousOn (Function.uncurry X) Q0)
    (hd : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        |X p.1 p.2| ≤ C * Work.Spaces.HkIntegrand α k h p.1 p.2) :
    MeasureTheory.IntegrableOn (Function.uncurry X) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [MeasureTheory.IntegrableOn, ← pm_eq_restrict]
  have hbase := int_HkIntegrand α k hs hm
  have hmaj : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => C * Work.Spaces.HkIntegrand α k h p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.IntegrableOn] at hbase
    rw [← pm_eq_restrict] at hbase
    exact hbase.const_mul C
  have haesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry X)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  refine hmaj.mono' haesm ?_
  filter_upwards [hd] with p hp
  rcases p with ⟨z, θ⟩
  simpa only [Function.uncurry_apply_pair, Real.norm_eq_abs] using hp

/-- The `u²ρ` integrability form implies the `u·u·ρ` form. -/
theorem integrableOn_sq_to_mul {u ρ : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (u z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine h.congr ?_
  filter_upwards with p
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, sq]

end Work.FTS.StrongPersist.H6Aux.R
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.EasyLeibIntBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1Hon

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## Elementary facts about `EasyLeib`

`EasyLeib` is the Leibniz majorant of the `D_θ`-transport pairing
(`Submission/Work/FTS/StrongPersist/N6Trans/LeibMajor.lean`).  To transfer the honest-class
bound for `Work.FTS.H2.EasyMajor` to it, we need that `EasyLeib` is nonnegative, that it is
continuous on the open quadrant (hence a.e. strongly measurable for `Work.FTS.H2.pm`), and
that `pm` is concentrated on the open quadrant (so that the pointwise comparison
`Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor` holds a.e.). -/

/-- Each summand of `EasyLeib` carries the square `slotW α a`, so `EasyLeib` is nonnegative
everywhere. -/
theorem EasyLeib_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.FTS.StrongPersist.N6Trans.EasyLeib α f g z θ := by
  rw [Work.FTS.StrongPersist.N6Trans.EasyLeib]
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split_ifs with hab
  · refine Finset.sum_nonneg fun a1 _ => Finset.sum_nonneg fun b1 _ => ?_
    split_ifs with h00
    · exact le_rfl
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (Work.FTS.TransportS.slotW_nonneg α a z θ)
          (abs_nonneg _)) (abs_nonneg _)) (abs_nonneg _)
  · exact le_rfl

/-- The slot weight `Work.FTS.TransportS.slotW α a` is continuous on the open quadrant: it is
a square of `Whz` resp. `Wm`, both continuous there. -/
theorem continuousOn_slotW (α : ℝ) (a : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.slotW α a p.1 p.2) Work.FTS.H2.Qd := by
  simp only [Work.FTS.TransportS.slotW, ite_apply]
  split_ifs with h
  · exact (Work.FTS.H2.continuousOn_Whz_Qd.pow 2)
  · exact ((Work.FTS.H2.continuousOn_Wm_Qd α).pow 2)

/-- `EasyLeib` is continuous on the open quadrant, for `f`, `g` of class `C^∞` there: it is a
finite sum of products of the continuous slot weight with absolute values of the mixed
derivatives `Work.Spaces.mixed`. -/
theorem continuousOn_EasyLeib (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.StrongPersist.N6Trans.EasyLeib α f g p.1 p.2)
      Work.FTS.H2.Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.FTS.StrongPersist.N6Trans.EasyLeib α f g p.1 p.2)
      = fun p : ℝ × ℝ => ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5,
          (if a + b ≤ 4 then
            ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
              (if a1 = 0 ∧ b1 = 0 then 0 else
                Work.FTS.TransportS.slotW α a p.1 p.2
                  * |Work.Spaces.mixed b1 a1 f p.1 p.2|
                  * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g p.1 p.2|
                  * |Work.Spaces.mixed b a g p.1 p.2|)
          else 0) := rfl
  rw [hfun]
  refine continuousOn_finsetSum _ (fun a _ => continuousOn_finsetSum _ (fun b _ => ?_))
  by_cases hab : a + b ≤ 4
  · simp only [hab, ite_true]
    refine continuousOn_finsetSum _ (fun a1 _ => continuousOn_finsetSum _ (fun b1 _ => ?_))
    by_cases h00 : a1 = 0 ∧ b1 = 0
    · simp only [h00]
      exact continuousOn_const
    · simp only [h00, ite_false]
      exact (((continuousOn_slotW α a).mul ((hf.mixed b1 a1).continuousOn.abs)).mul
        ((hg.mixed (b - b1) (a - a1 + 1)).continuousOn.abs)).mul
        ((hg.mixed b a).continuousOn.abs)
  · simp only [hab, ite_false]
    exact continuousOn_const

/-- The product measure `pm` of the closed quadrant is concentrated on the open quadrant: the
complement of `Qd` inside `Iz ×ˢ Iθ` is contained in the three null segments
`{0} × Iθ`, `Iz × {0}` and `Iz × {π/2}`. -/
theorem ae_pm_mem_Qd : ∀ᵐ p ∂Work.FTS.H2.pm, p ∈ Work.FTS.H2.Qd := by
  have hz : (Work.Spaces.Iz : Set ℝ) =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : (Work.Spaces.Iθ : Set ℝ) =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprod : ((Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)))
      =ᵐ[(volume : Measure ℝ).prod volume] Work.FTS.H2.Qd :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  have hpm : Work.FTS.H2.pm = ((volume : Measure ℝ).prod volume).restrict Work.FTS.H2.Qd := by
    rw [Work.FTS.H2.pm, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_congr_set hprod
  rw [hpm]
  exact MeasureTheory.ae_restrict_mem ((isOpen_Ioi.prod isOpen_Ioo).measurableSet)

/-- The pointwise comparison of the two Leibniz majorants `EasyLeib ≤ EasyMajor`, a.e. for the
product measure `pm`. -/
theorem ae_EasyLeib_le_EasyMajor (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ᵐ p ∂Work.FTS.H2.pm,
      Work.FTS.StrongPersist.N6Trans.EasyLeib α f g p.1 p.2
        ≤ Work.FTS.H2.EasyMajor α f g p.1 p.2 :=
  ae_pm_mem_Qd.mono fun p hp =>
    Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor hf hg p.1 p.2
      hp.1 hp.2.1 hp.2.2

end

/-- The honest-class bound for the Leibniz majorant `EasyLeib`
(`Submission/Work/FTS/StrongPersist/N6Trans/LeibMajor.lean`), obtained by combining the proved
pointwise comparison `Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor`
(`LeibMajor/EasyLeib_le_EasyMajor.lean`) with the proved honest-class majorant bound
`Work.FTS.StrongPersist.N6Trans.HonestEasyMajorLem`:

  `Integrable (uncurry (EasyLeib α f g)) pm` and
  `∫ EasyLeib α f g ∂pm ≤ C/√(γ-1)·|f|_{ℋ⁴}·HkSq α 4 g`,

where `pm = (volume.restrict Iz).prod (volume.restrict Iθ)` is `Work.FTS.H2.pm`.

Route: `EasyLeib ≤ EasyMajor` pointwise on the open quadrant (a.e. for `pm`, and both sides are
nonnegative there since every summand carries a `slotW`, i.e. a square), `EasyMajor` is integrable
with the stated bound (`HonestEasyMajorLem`), and `EasyLeib` is continuous on the open quadrant
hence a.e. strongly measurable (`Work.FTS.H2.aesm_of_Qd`), so `Integrable.mono'` and
`integral_mono_ae` give both conjuncts. -/
theorem EasyLeibIntBound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    Work.Spaces.DecayAll 4 g →
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => Work.FTS.StrongPersist.N6Trans.EasyLeib α f g p.1 p.2)
        Work.FTS.H2.pm ∧
      ∫ p, Work.FTS.StrongPersist.N6Trans.EasyLeib α f g p.1 p.2 ∂Work.FTS.H2.pm
        ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
            * Work.Spaces.HkSq α 4 g := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongPersist.N6Trans.HonestEasyMajorLem
  refine ⟨C, hCpos, fun α f g hα hα1 hf hmf hg hmg hdecg => ?_⟩
  -- the honest-class bound for the majorant
  obtain ⟨hEM_int, hEM_le⟩ := hC α f g hα hα1 hf hmf hg hmg hdecg
  -- the pointwise comparison, a.e. for `pm`
  have haele := ae_EasyLeib_le_EasyMajor α hf hg
  -- the left-hand side is integrable, dominated by the integrable majorant
  have hL_int : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.StrongPersist.N6Trans.EasyLeib α f g p.1 p.2)
      Work.FTS.H2.pm :=
    MeasureTheory.Integrable.mono' hEM_int
      (Work.FTS.H2.aesm_of_Qd (continuousOn_EasyLeib α hf hg))
      (haele.mono fun p hp => by
        rw [Real.norm_of_nonneg (EasyLeib_nonneg α f g p.1 p.2)]
        exact hp)
  refine ⟨hL_int, ?_⟩
  exact le_trans (MeasureTheory.integral_mono_ae hL_int hEM_int haele) hEM_le

end Work.FTS.StrongPersist.N6Trans.T1Hon
end
