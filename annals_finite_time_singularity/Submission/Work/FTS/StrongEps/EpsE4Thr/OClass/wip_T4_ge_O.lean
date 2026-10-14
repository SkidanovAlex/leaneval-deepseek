import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenCoer.SlotWCommon
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.ZDecay_of_decay_bounds
import Submission.Work.H2W.FstarDzIterFourPsiAe
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.wip_T2_ge_O =====
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

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The open-class integrability of the `γ`-weighted angular square

The frozen `wip_T2_ge_Q_crude` uses `Work.FTS.CoercivityFix.Coer1.sq_MixedGam` (stated for
`SmoothQuad` data) only in the instance `(i,j) = (1,0)`, i.e. for `(D_θ f)² w² sin(2θ)^{-γ}`.
The port below re-proves the whole family `sq_MixedGam` for `SmoothOpen` data: the `ℋ²`-membership
supplies the iterated integrals of the majorant `HkIntegrand`, and the a.e. strong measurability of
each summand comes from continuity on the *open* quadrant, which `SmoothOpen` provides. -/

namespace WipT2O

/-- **The open-class twin of `Work.FTS.CoercivityFix.Coer1.sq_MixedGam`**: the squared mixed
blocks with the `γ`-weight are jointly integrable for `SmoothOpen f` in `ℋ²`. -/
theorem sq_MixedGam_Op (α : ℝ) (hα : 0 < α) {f : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 2) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
    (((hso.mixed j i).continuousOn).mul
      (Work.FTS.StrongEps.EpsE4Thr.continuousOn_Wt_Q0 α)).pow 2
  have h := Work.FTS.CoercivityFix.Coer1.joint_of_le_HkIntegrand α 2 hm hcont
    (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_mixed α 2 f z θ i j hi hij)
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair] at hp ⊢
  rw [mul_pow, Work.FTS.CoercivityFix.Coer1.Wt_sq_self_Iθ α z θ hα hp.2]
  rfl

end WipT2O

/-- The **open-class** twin of `Work.FTS.CoercivityFix.Coer1T.wip_T2_ge_Q_crude`
(`CoercivityFix/Coer1T/slotGam_LGammaT.lean`, proved): the `T₂`-term of `D_θ𝓛_Γ^T`
(`T2 α f = -D_θΓ·(2z/(c(1+z)²))·L₁₂(f)`) is integrable and bounded below by
`-(1/200)·EDth - 3.2·10⁷·α·Ef`, with `RegQ α 2` replaced by `RegQo α 2` (`SmoothOpen` instead of
`SmoothQuad`).  The frozen proof consumes `SmoothQuad` only through the open-quadrant facts
(a.e. strong measurability of `D_θ f · w` and integrability of `(D_θ f)²·w²·sin^{-γ}`), supplied
in the open class by `OClass.C0_sq_le_EDthW_O` / `OpenCoer.SlotWCommon` and `HkMem α 2 f`; the
Hardy comparison `EL12z f ≤ 16 Ef f` is `EDthW_EL12z_open`.

Proof recipe: copy `wip_T2_ge_Q_crude` verbatim, with `hsq` replaced by `hf.1 : SmoothOpen f`,
`aesm_dth_mul_w_Q hsq` by `OClass.aesm_dth_mul_w_O hf.1` (or
`OpenCoer.SlotWCommon.aesm_dth_mul_w_O`), `EL12z_le_Q α hα hsq hm hfH` by
`EpsE4Thr.EDthW_EL12z_open`'s second conjunct (equivalently `Work.Coercivity.EL12z_le f hfH` with
`integrableOn_f_sq_w_sq_open`), and `sin_half_sq`, `gamDth_l2_bound`, `DthGam_sq_le_GamSq`,
`measurable_DthGam`, `integrable_prod_sep`, `sq_integral_mul_le` as they are (all class-free). -/
theorem wip_T2_ge_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f)
    (hfH : Work.Coercivity.HardyHyp f) (hΓ2 : Work.Coercivity.GammaPointwiseBnd α) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Coercivity.T2 α f z θ * Work.Spaces.Dth f z θ
          * Work.Coercivity.thetaW α z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ -((1 / 200) * Work.Coercivity.EDth α f + 32000000 * α * Work.Coercivity.Ef f)
        ≤ Work.Coercivity.wip (Work.Coercivity.thetaW α)
            (Work.Coercivity.T2 α f) (Work.Spaces.Dth f) := by
  obtain ⟨hso, hm, _hb⟩ := hf
  set P : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hP
  have hvol : MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) = P := by
    rw [hP, MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  have hquad : ∀ᵐ p ∂P, p.1 ∈ Work.Spaces.Iz ∧ p.2 ∈ Work.Spaces.Iθ := by
    rw [hP]; exact Work.Coercivity.ae_prod_quadrant
  set g₁ : ℝ × ℝ → ℝ := fun p => Work.Coercivity.T2 α f p.1 p.2 * Work.Spaces.w p.1
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) with hg₁
  set g₂ : ℝ × ℝ → ℝ := fun p => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) with hg₂
  set Az : ℝ → ℝ := fun z => (2 * z / (Work.Spaces.c α * (1 + z) ^ 2))
      * Work.Coercivity.L12f f z with hAz
  set arad : ℝ → ℝ := fun z => Az z ^ 2 * Work.Spaces.w z ^ 2 with harad
  set aθ : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Coercivity.DthGam α 0 θ) ^ 2 with haθ
  -- ## the two energies are nonnegative
  have hEfnn : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hEDnn : 0 ≤ Work.Coercivity.EDth α f := by
    rw [Work.Coercivity.EDth, Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  -- ## the `θ`-factor: integrability and `∫ aθ ≤ 100α`
  have haθ_int : MeasureTheory.Integrable aθ (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hmed : MeasureTheory.Integrable (fun θ : ℝ => 4 * α ^ 2
        * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((Work.Coercivity.Gam_sq_sin_neg_gam α hα hα1).1.const_mul (4 * α ^ 2)).congr
        (Filter.Eventually.of_forall (fun θ => by ring))
    refine Integrable.mono' hmed ?_ ?_
    · rw [haθ]
      exact (((Real.measurable_sin.comp
        (measurable_const.mul measurable_id)).pow_const _).mul
          ((Work.Coercivity.measurable_DthGam α).pow_const (2 : ℕ))).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs0 : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
      have hsγ : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs0 _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hsγ (sq_nonneg _))]
      have hD := Work.Coercivity.DthGam_sq_le_GamSq α hΓ2 θ hθ
      calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Coercivity.DthGam α 0 θ) ^ 2
          ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (4 * α ^ 2 * (Work.Spaces.Gam α θ) ^ 2) := mul_le_mul_of_nonneg_left hD hsγ
        _ = 4 * α ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
  have haθ_val : ∫ θ in Work.Spaces.Iθ, aθ θ ≤ 100 * α := by
    rw [haθ]
    exact Work.Coercivity.gamDth_l2_bound α hα hα1 hΓ2
  -- ## the `z`-factor: integrability and `∫ arad ≤ 6400 Ef`
  have hbase : MeasureTheory.Integrable
      (fun z : ℝ => Work.Coercivity.L12f f z ^ 2 / z ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := hfH.intA 1 (by norm_num)
    have h1 : MeasureTheory.Integrable (fun z : ℝ => Work.Coercivity.L12f f z ^ 2 / z ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
      refine h.congr (Filter.Eventually.of_forall fun z => ?_)
      show Work.Coercivity.L12f f z ^ 2 / z ^ (2 * ((1 : ℕ) : ℝ))
          = Work.Coercivity.L12f f z ^ 2 / z ^ 2
      have hz : (z : ℝ) ^ (2 * ((1 : ℕ) : ℝ)) = z ^ (2 : ℕ) := by
        rw [show (2 * ((1 : ℕ) : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hz]
    rw [Work.Spaces.Iz, ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact h1
  have harad_pt : arad =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z : ℝ => (4 / Work.Spaces.c α ^ 2) * (Work.Coercivity.L12f f z ^ 2 / z ^ 2)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    show ((2 * z / (Work.Spaces.c α * (1 + z) ^ 2)) * Work.Coercivity.L12f f z) ^ 2
          * Work.Spaces.w z ^ 2
        = (4 / Work.Spaces.c α ^ 2) * (Work.Coercivity.L12f f z ^ 2 / z ^ 2)
    rcases eq_or_ne z 0 with hz0 | hz0
    · subst hz0
      rw [Work.Coercivity.w_eq]
      norm_num
    · have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα hα1
      have hz1 : (1 : ℝ) + z ≠ 0 := by linarith [Set.mem_Ici.mp hz]
      rw [Work.Coercivity.w_eq]
      field_simp
      ring
  have harad_int : MeasureTheory.Integrable arad (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((hbase.const_mul (4 / Work.Spaces.c α ^ 2))).congr harad_pt.symm
  have harad_val : ∫ z in Work.Spaces.Iz, arad z ≤ 6400 * Work.Coercivity.Ef f := by
    have hEL : Work.Coercivity.EL12z f ≤ 16 * Work.Coercivity.Ef f :=
      (Work.FTS.StrongEps.EpsE4Thr.EDthW_EL12z_open (α := α) hα hso hm hfH).2
    have hELnn : 0 ≤ Work.Coercivity.EL12z f := by
      rw [Work.Coercivity.EL12z, Work.Coercivity.L2Sqz]
      exact integral_nonneg fun z => sq_nonneg _
    have hc2 : (4 : ℝ) / Work.Spaces.c α ^ 2 ≤ 400 := by
      have hc := (Work.Spaces.c_bounds α hα hα1).1
      have hcp : 0 < Work.Spaces.c α := Work.Coercivity.c_pos hα hα1
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hc, hcp]
    rw [MeasureTheory.integral_congr_ae harad_pt, MeasureTheory.integral_const_mul]
    rw [show (∫ z in Work.Spaces.Iz, Work.Coercivity.L12f f z ^ 2 / z ^ 2)
        = Work.Coercivity.EL12z f from by
      rw [Work.Coercivity.EL12z, Work.Coercivity.L2Sqz]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show Work.Coercivity.L12f f z ^ 2 / z ^ 2 = (Work.Coercivity.L12f f z / z) ^ 2
      rw [div_pow]]
    calc (4 / Work.Spaces.c α ^ 2) * Work.Coercivity.EL12z f
        ≤ 400 * Work.Coercivity.EL12z f := mul_le_mul_of_nonneg_right hc2 hELnn
      _ ≤ 400 * (16 * Work.Coercivity.Ef f) := by linarith
      _ = 6400 * Work.Coercivity.Ef f := by ring
  -- ## the pointwise identifications of the two `L²`-blocks
  have hg₁_pt : (fun p => g₁ p ^ 2) =ᵐ[P] fun p => arad p.1 * aθ p.2 := by
    filter_upwards [hquad] with p hp
    obtain ⟨hz, hθ⟩ := hp
    have hs := Work.FTS.CoercivityFix.Coer1.sin_half_sq (Work.Spaces.gam α) p.2 hθ
    simp only [hg₁, harad, haθ, hAz]
    rw [show Work.Coercivity.T2 α f p.1 p.2 = -(Work.Coercivity.DthGam α p.1 p.2)
        * (2 * p.1 / (Work.Spaces.c α * (1 + p.1) ^ 2))
          * Work.Coercivity.L12f f p.1 from rfl,
      show Work.Coercivity.DthGam α p.1 p.2 = Work.Coercivity.DthGam α 0 p.2 from by
        rw [Work.Coercivity.DthGam_eq, Work.Coercivity.DthGam_eq]]
    rw [mul_pow, mul_pow, mul_pow, hs]
    ring
  have hg₂_pt : (fun p => g₂ p ^ 2) =ᵐ[P] fun p => Work.Spaces.Dth f p.1 p.2 ^ 2
      * (Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))) := by
    filter_upwards [hquad] with p hp
    obtain ⟨hz, hθ⟩ := hp
    have hs := Work.FTS.CoercivityFix.Coer1.sin_half_sq (Work.Spaces.gam α) p.2 hθ
    simp only [hg₂]
    rw [mul_pow, mul_pow, hs]
    ring
  have hg₁g₂_pt : (fun p => g₁ p * g₂ p) =ᵐ[P] fun p => Work.Coercivity.T2 α f p.1 p.2
      * Work.Spaces.Dth f p.1 p.2 * Work.Coercivity.thetaW α p.1 p.2 := by
    filter_upwards [hquad] with p hp
    obtain ⟨hz, hθ⟩ := hp
    have hs := Work.FTS.CoercivityFix.Coer1.sin_half_sq (Work.Spaces.gam α) p.2 hθ
    simp only [hg₁, hg₂, Work.Coercivity.thetaW]
    rw [← hs]
    ring
  -- ## integrability of the three blocks
  have hDth2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2 ^ 2
      * (Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))) P := by
    have h := WipT2O.sq_MixedGam_Op α hα hso hm 1 0 (by norm_num) (by norm_num)
    have h1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.mixed 0 1 f p.1 p.2 ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) p.1 p.2) P := by
      rw [hP]; exact Work.Coercivity.integrableOn_prod h
    refine h1.congr ?_
    filter_upwards with p
    simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
      Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]
    try ring
  have hg₂sq : MeasureTheory.Integrable (fun p => g₂ p ^ 2) P := hDth2.congr hg₂_pt.symm
  have hg₁rad : MeasureTheory.Integrable (fun p : ℝ × ℝ => arad p.1 * aθ p.2) P :=
    harad_int.mul_prod haθ_int
  have hg₁sq : MeasureTheory.Integrable (fun p => g₁ p ^ 2) P := hg₁rad.congr hg₁_pt.symm
  -- ## a.e. strong measurability
  have hL12aem : AEMeasurable (fun z : ℝ => Work.Coercivity.L12f f z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h1 : AEStronglyMeasurable (fun z : ℝ => Work.Coercivity.L12f f z)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (Work.Coercivity.L12f_continuousOn f hfH).aestronglyMeasurable measurableSet_Ioi
    have h2 : MeasureTheory.volume.restrict Work.Spaces.Iz
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
      rw [Work.Spaces.Iz]
      exact (Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
    rw [h2]; exact h1.aemeasurable
  have hsin_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) P :=
    ((Real.measurable_sin.comp (measurable_const.mul measurable_snd)).pow_const _)
      |>.aestronglyMeasurable
  have hg₂_aesm : AEStronglyMeasurable g₂ P := by
    rw [hg₂, hP]
    exact (aesm_dth_mul_w_O hso).mul hsin_aesm
  have hg₁_aesm : AEStronglyMeasurable g₁ P := by
    have hT2 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Coercivity.T2 α f p.1 p.2) P := by
      have hfun : (fun p : ℝ × ℝ => Work.Coercivity.T2 α f p.1 p.2) = fun p =>
          -(Work.Coercivity.DthGam α p.1 p.2)
            * (2 * p.1 / (Work.Spaces.c α * (1 + p.1) ^ 2))
            * Work.Coercivity.L12f f p.1 := rfl
      rw [hfun, hP]
      have hL : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Coercivity.L12f f p.1) P :=
        (AEMeasurable.comp_fst hL12aem).aestronglyMeasurable
      have hrat : AEStronglyMeasurable
          (fun p : ℝ × ℝ => 2 * p.1 / (Work.Spaces.c α * (1 + p.1) ^ 2)) P :=
        ((measurable_const.mul measurable_fst).div
          (measurable_const.mul ((measurable_const.add measurable_fst).pow_const 2)))
          |>.aestronglyMeasurable
      exact (((Work.Coercivity.measurable_DthGam_prod α).neg.aestronglyMeasurable).mul hrat).mul hL
    have hg₁a : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.w p.1) P :=
      ((Work.Coercivity.measurable_w).comp measurable_fst).aestronglyMeasurable
    rw [hg₁]
    exact (hT2.mul hg₁a).mul hsin_aesm
  -- ## Cauchy–Schwarz
  have hg₁g₂_int : MeasureTheory.Integrable (fun p => g₁ p * g₂ p) P :=
    ((MeasureTheory.memLp_two_iff_integrable_sq hg₁_aesm).mpr hg₁sq).integrable_mul
      ((MeasureTheory.memLp_two_iff_integrable_sq hg₂_aesm).mpr hg₂sq)
  have hCS := Work.Coercivity.sq_integral_mul_le P g₁ g₂ hg₁_aesm hg₂_aesm hg₁sq hg₂sq
  have hg₁nn : 0 ≤ ∫ p, g₁ p ^ 2 ∂P := integral_nonneg fun p => sq_nonneg _
  have hg₂_val : ∫ p, g₂ p ^ 2 ∂P = Work.Coercivity.EDth α f := by
    have hOn : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
          * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
      rw [MeasureTheory.IntegrableOn, hvol]
      refine hDth2.congr ?_
      filter_upwards with p
      rcases p with ⟨z, θ⟩
      show Work.Spaces.Dth f z θ ^ 2
            * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          = Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
            * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ring
    rw [MeasureTheory.integral_congr_ae hg₂_pt, Work.Coercivity.EDth_eq_wip α f,
      Work.Coercivity.wip_eq_integral_prod (fun z θ => Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (Work.Spaces.Dth f) (Work.Spaces.Dth f)
        hOn,
      ← hP]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  -- ## the bound `∫ g₁² ≤ 640000 α Ef` (the two one-variable factors separate)
  have haθ_nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, aθ θ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [haθ]
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _) (sq_nonneg _)
  have hg₁_val : ∫ p, g₁ p ^ 2 ∂P ≤ 640000 * α * Work.Coercivity.Ef f := by
    rw [MeasureTheory.integral_congr_ae hg₁_pt,
      Work.Coercivity.integral_prod_sep arad aθ harad_int haθ_int]
    calc (∫ z in Work.Spaces.Iz, arad z) * (∫ θ in Work.Spaces.Iθ, aθ θ)
        ≤ (6400 * Work.Coercivity.Ef f) * (100 * α) :=
          mul_le_mul harad_val haθ_val haθ_nn (mul_nonneg (by norm_num) hEfnn)
      _ = 640000 * α * Work.Coercivity.Ef f := by ring
  -- ## integrability of the pairing (the pointwise identity above)
  have hOn : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.T2 α f z θ * Work.Spaces.Dth f z θ
        * Work.Coercivity.thetaW α z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.IntegrableOn, hvol]
    refine hg₁g₂_int.congr ?_
    filter_upwards [hg₁g₂_pt] with p hp
    rcases p with ⟨z, θ⟩
    show g₁ (z, θ) * g₂ (z, θ)
      = Work.Coercivity.T2 α f z θ * Work.Spaces.Dth f z θ * Work.Coercivity.thetaW α z θ
    exact hp
  -- ## the final bound on the pairing
  have hkey : |Work.Coercivity.wip (Work.Coercivity.thetaW α)
      (Work.Coercivity.T2 α f) (Work.Spaces.Dth f)|
      ≤ 800 * Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f)
        * Real.sqrt (Work.Coercivity.EDth α f) := by
    have hwip : Work.Coercivity.wip (Work.Coercivity.thetaW α)
        (Work.Coercivity.T2 α f) (Work.Spaces.Dth f) = ∫ p, g₁ p * g₂ p ∂P := by
      rw [Work.Coercivity.wip_eq_integral_prod (Work.Coercivity.thetaW α)
        (Work.Coercivity.T2 α f) (Work.Spaces.Dth f) hOn]
      exact MeasureTheory.integral_congr_ae
        (hg₁g₂_pt.mono fun p hp => hp.symm)
    rw [hwip]
    have hsq : (∫ p, g₁ p * g₂ p ∂P) ^ 2
        ≤ (800 * Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f)
            * Real.sqrt (Work.Coercivity.EDth α f)) ^ 2 := by
      have hb : (∫ p, g₁ p ^ 2 ∂P) * (∫ p, g₂ p ^ 2 ∂P)
          ≤ (640000 * α * Work.Coercivity.Ef f) * Work.Coercivity.EDth α f := by
        rw [hg₂_val]
        exact mul_le_mul_of_nonneg_right hg₁_val hEDnn
      have h2 : (800 * Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f)
            * Real.sqrt (Work.Coercivity.EDth α f)) ^ 2
          = (640000 * α * Work.Coercivity.Ef f) * Work.Coercivity.EDth α f := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hα.le, Real.sq_sqrt hEfnn,
          Real.sq_sqrt hEDnn]
        norm_num
      rw [h2]
      exact hCS.trans hb
    calc |∫ p, g₁ p * g₂ p ∂P| = Real.sqrt ((∫ p, g₁ p * g₂ p ∂P) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((800 * Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f)
            * Real.sqrt (Work.Coercivity.EDth α f)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 800 * Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f)
            * Real.sqrt (Work.Coercivity.EDth α f) := Real.sqrt_sq (by positivity)
  -- ## the numerical conclusion
  have hyoung : 800 * Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f)
      * Real.sqrt (Work.Coercivity.EDth α f)
      ≤ (1 / 200) * Work.Coercivity.EDth α f + 32000000 * α * Work.Coercivity.Ef f := by
    have h1 : (Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f)) ^ 2
        = α * Work.Coercivity.Ef f := by
      rw [mul_pow, Real.sq_sqrt hα.le, Real.sq_sqrt hEfnn]
    have h2 : (Real.sqrt (Work.Coercivity.EDth α f)) ^ 2 = Work.Coercivity.EDth α f :=
      Real.sq_sqrt hEDnn
    nlinarith [sq_nonneg (Real.sqrt (Work.Coercivity.EDth α f)
      - 80000 * (Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f))), h1, h2]
  refine ⟨hOn, ?_⟩
  linarith [neg_abs_le (Work.Coercivity.wip (Work.Coercivity.thetaW α)
    (Work.Coercivity.T2 α f) (Work.Spaces.Dth f)), hkey, hyoung]

end Work.FTS.StrongEps.EpsE4Thr.OClass
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.wip_T4_ge_O =====
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

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The two integrability certificates extracted from `IntPkgO`

The frozen `CoercivityFix/Coer1T/wip_T4_ge_Q` derives the integrability of
`(D_θ f)² w² sin(2θ)^{-γ}` and of `(D_θ f)² w²` from `IntPkg_Q` (`IntPkg.sqMixedGam 1 0` resp.
`IntPkg.sqMixedOne 1 0`), composed with `RegQ α 2 f`.  In the open class the bundle `IntPkgO`
carries literally the same two fields, so the two lemmas below are the same proofs with the
`IntPkg_Q`-invocation replaced by the hypothesis `hIP : IntPkgO α f`. -/

/-- `(D_θ f)²·w²·sin(2θ)^{-γ}` is integrable on the quadrant from `IntPkgO α f` (`sqMixedGam`
at `(i,j) = (1,0)`), rewritten through `Dth = mixed 0 1` and `Rho γ = w²·sin(2θ)^{-γ}`. -/
theorem Dth_sq_gam_of_IntPkgO (α : ℝ) {f : Fn}
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := Work.FTS.CoercivityFix.Coer1.to_h1 (β := Work.Spaces.gam α)
    (u := Work.Spaces.Dth f) (hIP.sqMixedGam 1 0 (by norm_num) (by norm_num))
  simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
    Work.Spaces.DthIter_zero, Work.FTS.CoercivityFix.Coer1.sig, pow_two] using h

/-- `(D_θ f)²·w²` is integrable on the quadrant from `IntPkgO α f` (`sqMixedOne` at
`(i,j) = (1,0)`). -/
theorem Dth_sq_w_sq_of_IntPkgO {α : ℝ} {f : Fn}
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.Spaces.w z ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := hIP.sqMixedOne 1 0 (by norm_num) (by norm_num)
  simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
    Work.Spaces.DthIter_zero, pow_two] using h

/-! ## The scalar arithmetic closing the constant `1/200` -/

/-- If `J² ≤ 120/(17α)` with `0 < α ≤ 10⁻⁹`, then `40αJ ≤ 1/200`.  This is the numerical
step converting the angular bound `T4J α ≤ 120/(17α)` into the constant of the target.  (The
numeric content: `40α√(120/(17α)) ≤ 1/200` is equivalent to `7.68·10⁹·α ≤ 17`, and
`7.68·10⁹·10⁻⁹ = 7.68 < 17`.)  This is the class-free `Coer1T.T4Q_arith` re-stated here so
that the open-class file does not depend on the `SmoothQuad` chapter for its arithmetic. -/
theorem T4O_arith (α J : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 9) (hJ : 0 ≤ J)
    (hJle : J ^ 2 ≤ 120 / (17 * α)) : 40 * α * J ≤ 1 / 200 :=
  Work.FTS.CoercivityFix.Coer1T.T4Q_arith α J hα hα1 hJ hJle

/-! ## A.e. strong measurability of the `L²` factors in the open class -/

/-- `T4B α f` is a.e. strongly measurable on the quadrant for `SmoothOpen` data: it is the
measurable factor `sin(2θ)^{-γ/2}` times `D_θ f · w` (the latter being a.e. strongly measurable
by `aesm_dth_mul_w_O`). -/
theorem aesm_T4B_O (α : ℝ) {f : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable (Work.Coercivity.T4B α f) Work.Coercivity.T4P := by
  have hm : Measurable (fun p : ℝ × ℝ => Work.Coercivity.T4h α p.2) :=
    (Work.Coercivity.measurable_T4h α).comp measurable_snd
  have h := hm.aestronglyMeasurable.mul (aesm_dth_mul_w_O hso)
  have h2 : ((fun p : ℝ × ℝ => Work.Coercivity.T4h α p.2)
      * fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1)
      = Work.Coercivity.T4B α f := by
    funext p
    rw [Pi.mul_apply]
    simp only [Work.Coercivity.T4B]
    ring
  rw [← h2]
  exact h

/-- `T4W α f` is a.e. strongly measurable on the quadrant for `SmoothOpen` data: it is a
measurable factor (the angular data `D_θΓ`, the radial factor `T4g`, the weight
`sin(2θ)^{-γ}w²`) times `D_θ f · w`. -/
theorem aesm_T4W_O (α : ℝ) {f : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable (Work.Coercivity.T4W α f) Work.Coercivity.T4P := by
  have h1 : Measurable (fun p : ℝ × ℝ => Work.Coercivity.DthGam α p.1 p.2) :=
    Work.Coercivity.measurable_DthGam_prod α
  have h2 : Measurable (fun p : ℝ × ℝ => Work.Coercivity.T4g p.1) :=
    Work.Coercivity.measurable_T4g.comp measurable_fst
  have h3 : Measurable
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))) :=
    (Real.measurable_sin.comp (measurable_const.mul measurable_snd)).pow_const _
  have h4 : Measurable (fun p : ℝ × ℝ => Work.Spaces.w p.1) :=
    Work.Coercivity.measurable_w.comp measurable_fst
  have hm : Measurable (fun p : ℝ × ℝ => Work.Coercivity.DthGam α p.1 p.2
      * Work.Coercivity.T4g p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
      * Work.Spaces.w p.1) :=
    ((h1.mul h2).mul h3).mul h4
  have h := hm.aestronglyMeasurable.mul (aesm_dth_mul_w_O hso)
  have h2' : ((fun p : ℝ × ℝ => Work.Coercivity.DthGam α p.1 p.2
        * Work.Coercivity.T4g p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * Work.Spaces.w p.1)
        * fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1)
      = Work.Coercivity.T4W α f := by
    funext p
    rw [Pi.mul_apply]
    simp only [Work.Coercivity.T4W]
    ring
  rw [← h2']
  exact h

/-! ## Integrability and the value of the `L²` norm of `T4B` -/

/-- `(T4B α f)²` is integrable on the product measure as soon as the `γ`-weighted square of
`D_θ f` is integrable on the quadrant. -/
theorem integrable_T4B_sq_O (α : ℝ) {f : ℝ → ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Integrable (fun p : ℝ × ℝ => (Work.Coercivity.T4B α f p) ^ 2)
      Work.Coercivity.T4P := by
  have h' := Work.Coercivity.integrableOn_prod
    (g := fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
      * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) h
  refine h'.congr ?_
  filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
  exact (Work.Coercivity.T4B_sq_eq α f hp.2).symm

/-- `∫ (T4B α f)² = EDth α f`. -/
theorem integral_T4B_sq_O (α : ℝ) {f : ℝ → ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    ∫ p : ℝ × ℝ, (Work.Coercivity.T4B α f p) ^ 2 ∂Work.Coercivity.T4P
      = Work.Coercivity.EDth α f := by
  have hIntOn : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine h.congr ?_
    filter_upwards with p
    simp only [Function.uncurry]
    ring
  rw [Work.Coercivity.EDth_eq_wip α f,
    Work.Coercivity.wip_eq_integral_prod
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Work.Spaces.Dth f) (Work.Spaces.Dth f) hIntOn]
  refine integral_congr_ae ?_
  filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
  rw [Work.Coercivity.T4B_sq_eq α f hp.2]
  ring

/-- Integrability of the `T4W`-integrand in the open class: dominated pointwise by
`2α·|T4A·T4B|`, whose integral is finite by Cauchy–Schwarz. -/
theorem integrable_T4W_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hΓ2 : Work.Coercivity.GammaPointwiseBnd α) {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hB2 : Integrable (fun p : ℝ × ℝ => (Work.Coercivity.T4B α f p) ^ 2)
      Work.Coercivity.T4P) :
    Integrable (Work.Coercivity.T4W α f) Work.Coercivity.T4P := by
  have hAB : Integrable (fun p : ℝ × ℝ =>
      Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p) Work.Coercivity.T4P :=
    (Work.Coercivity.integrable_mul_abs_integral_le_sqrt (Work.Coercivity.T4A α)
      (Work.Coercivity.T4B α f) (Work.Coercivity.aesm_T4A α) (aesm_T4B_O α hso)
      (Work.Coercivity.integrable_T4A_sq α hα hα1) hB2).1
  refine (hAB.abs.const_mul (2 * α)).mono' (aesm_T4W_O α hso) ?_
  filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
  rw [Real.norm_eq_abs]
  exact Work.Coercivity.T4W_abs_le α hα hΓ2 f hp.1 hp.2

/-! ## The target -/

/-- The **open-class** twin of `Work.FTS.CoercivityFix.Coer1T.wip_T4_ge_Q`
(`CoercivityFix/Coer1T/wip_T4_ge_Q.lean`, proved): the projector term
`T4 α f = (D_θΓ/c)·(2z²/(1+z)³)·C₀ f` of `D_θ𝓛_Γ^T` is integrable and bounded below by
`-(1/200)·EDth α f`, with `RegQ α 2` replaced by `RegQo α 2` (`SmoothOpen` instead of
`SmoothQuad`).

Frozen proof and its open replacements: `IntPkg_Q` → the hypothesis `hIP : IntPkgO α f` (fields
`sqMixedGam 1 0`, `sqMixedOne 1 0`); `aesm_Dth_smoothQuad hsq` → the open-class a.e. strong
measurability of `D_θ f · w` (`OClass.aesm_dth_mul_w_O hf.1`; factor `T4B = T4h·(w·D_θ f)`, no
division by `w` needed); `C0_sq_le_EDthW_Q hsq hw2i` → `OClass.C0_sq_le_EDthW_O hf.1 hw2i`;
`EDthW_le_EDth_Q α hα hsq hm2` → `EpsE4Thr.EDthW_le_EDth_open α hα hf.1 hf.2.1`.
Everything else (`integrable_T4B_sq`, `integral_T4B_sq`, `integrable_T4W`, `T4W_abs_le`,
`integrable_mul_abs_integral_le_sqrt`, `Gam_sq_sin_neg_gam`, `T4Q_arith`, `c_bounds`) is
class-free and copies verbatim.  (`RegQo` also supplies `BdryTraces α 2 f`, unused here.) -/
theorem wip_T4_ge_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 9) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f)
    (hΓ2 : Work.Coercivity.GammaPointwiseBnd α) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Coercivity.T4 α f z θ * Work.Spaces.Dth f z θ
          * Work.Coercivity.thetaW α z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ -((1 / 200) * Work.Coercivity.EDth α f)
        ≤ Work.Coercivity.wip (Work.Coercivity.thetaW α)
            (Work.Coercivity.T4 α f) (Work.Spaces.Dth f) := by
  obtain ⟨hso, hm2, -⟩ := hf
  have hα1' : α ≤ 1 := by linarith [hα1]
  -- ### the integrability certificates
  have hgam := Dth_sq_gam_of_IntPkgO α hIP
  have hw2i := Dth_sq_w_sq_of_IntPkgO hIP
  have hT4A2 : Integrable (fun p : ℝ × ℝ => (Work.Coercivity.T4A α p) ^ 2)
      Work.Coercivity.T4P := Work.Coercivity.integrable_T4A_sq α hα hα1'
  have hT4B2 : Integrable (fun p : ℝ × ℝ => (Work.Coercivity.T4B α f p) ^ 2)
      Work.Coercivity.T4P := integrable_T4B_sq_O α hgam
  have hB2val : ∫ p : ℝ × ℝ, (Work.Coercivity.T4B α f p) ^ 2 ∂Work.Coercivity.T4P
      = Work.Coercivity.EDth α f := integral_T4B_sq_O α hgam
  have hA2val : ∫ p : ℝ × ℝ, (Work.Coercivity.T4A α p) ^ 2 ∂Work.Coercivity.T4P
      = 4 * Work.Coercivity.T4J α := Work.Coercivity.integral_T4A_sq α hα hα1'
  have haesmB := aesm_T4B_O α hso
  obtain ⟨hABint, hABle⟩ := Work.Coercivity.integrable_mul_abs_integral_le_sqrt
    (Work.Coercivity.T4A α) (Work.Coercivity.T4B α f) (Work.Coercivity.aesm_T4A α)
    haesmB hT4A2 hT4B2
  have hT4Wint : Integrable (Work.Coercivity.T4W α f) Work.Coercivity.T4P :=
    integrable_T4W_O α hα hα1' hΓ2 hso hT4B2
  -- ### the first conjunct
  have hT4intP : Integrable (fun p : ℝ × ℝ =>
      Work.Coercivity.T4 α f p.1 p.2 * Work.Spaces.Dth f p.1 p.2
        * Work.Coercivity.thetaW α p.1 p.2) Work.Coercivity.T4P := by
    refine (hT4Wint.const_mul (Work.Coercivity.C0 f / Work.Spaces.c α)).congr ?_
    filter_upwards with p
    exact (Work.Coercivity.T4_integrand_eq α f p).symm
  have hOn : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.T4 α f z θ * Work.Spaces.Dth f z θ
        * Work.Coercivity.thetaW α z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [IntegrableOn, Work.Coercivity.volume_restrict_prod]
    exact hT4intP
  refine ⟨hOn, ?_⟩
  -- ### nonnegativity of the energy
  have hEDthnn : 0 ≤ Work.Coercivity.EDth α f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDth_eq_En]
    exact Work.FTS.CoercivityFix.Coer1.En_nonneg (Work.Spaces.gam α) (Work.Spaces.Dth f)
  -- ### `wip` as `(C₀/c) ∫ T4W`
  have hwip2 : Work.Coercivity.wip (Work.Coercivity.thetaW α)
        (Work.Coercivity.T4 α f) (Work.Spaces.Dth f)
      = (Work.Coercivity.C0 f / Work.Spaces.c α)
        * ∫ p : ℝ × ℝ, Work.Coercivity.T4W α f p ∂Work.Coercivity.T4P := by
    rw [Work.Coercivity.wip_eq_integral_prod (Work.Coercivity.thetaW α)
      (Work.Coercivity.T4 α f) (Work.Spaces.Dth f) hOn, ← integral_const_mul]
    exact integral_congr_ae
      (Eventually.of_forall fun p => Work.Coercivity.T4_integrand_eq α f p)
  -- ### the bound on `∫ T4W`
  have hWb : |∫ p : ℝ × ℝ, Work.Coercivity.T4W α f p ∂Work.Coercivity.T4P|
      ≤ 2 * α * ∫ p : ℝ × ℝ,
          |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p| ∂Work.Coercivity.T4P := by
    have h1 : |∫ p : ℝ × ℝ, Work.Coercivity.T4W α f p ∂Work.Coercivity.T4P|
        ≤ ∫ p : ℝ × ℝ, |Work.Coercivity.T4W α f p| ∂Work.Coercivity.T4P :=
      abs_integral_le_integral_abs
    have h2 : ∫ p : ℝ × ℝ, |Work.Coercivity.T4W α f p| ∂Work.Coercivity.T4P
        ≤ ∫ p : ℝ × ℝ,
            2 * α * |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p|
              ∂Work.Coercivity.T4P := by
      refine integral_mono_ae hT4Wint.abs (hABint.abs.const_mul (2 * α)) ?_
      filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
      exact Work.Coercivity.T4W_abs_le α hα hΓ2 f hp.1 hp.2
    have h3 : ∫ p : ℝ × ℝ,
          2 * α * |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p|
            ∂Work.Coercivity.T4P
        = 2 * α * ∫ p : ℝ × ℝ,
            |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p|
              ∂Work.Coercivity.T4P :=
      integral_const_mul _ _
    linarith
  have hABb : ∫ p : ℝ × ℝ,
        |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p| ∂Work.Coercivity.T4P
      ≤ Real.sqrt (∫ p : ℝ × ℝ, (Work.Coercivity.T4A α p) ^ 2 ∂Work.Coercivity.T4P)
        * Real.sqrt (∫ p : ℝ × ℝ, (Work.Coercivity.T4B α f p) ^ 2
            ∂Work.Coercivity.T4P) := by
    have hAabs : AEStronglyMeasurable (fun p : ℝ × ℝ => |Work.Coercivity.T4A α p|)
        Work.Coercivity.T4P := (Work.Coercivity.aesm_T4A α).norm
    have hBabs : AEStronglyMeasurable
        (fun p : ℝ × ℝ => |Work.Coercivity.T4B α f p|) Work.Coercivity.T4P := haesmB.norm
    have hAabs2 : Integrable (fun p : ℝ × ℝ => (|Work.Coercivity.T4A α p|) ^ 2)
        Work.Coercivity.T4P :=
      hT4A2.congr (Eventually.of_forall fun p => (sq_abs (Work.Coercivity.T4A α p)).symm)
    have hBabs2 : Integrable (fun p : ℝ × ℝ => (|Work.Coercivity.T4B α f p|) ^ 2)
        Work.Coercivity.T4P :=
      hT4B2.congr (Eventually.of_forall fun p => (sq_abs (Work.Coercivity.T4B α f p)).symm)
    obtain ⟨-, hle⟩ := Work.Coercivity.integrable_mul_abs_integral_le_sqrt
      (fun p => |Work.Coercivity.T4A α p|) (fun p => |Work.Coercivity.T4B α f p|)
      hAabs hBabs hAabs2 hBabs2
    have e1 : ∫ p : ℝ × ℝ, (|Work.Coercivity.T4A α p|) ^ 2 ∂Work.Coercivity.T4P
        = ∫ p : ℝ × ℝ, (Work.Coercivity.T4A α p) ^ 2 ∂Work.Coercivity.T4P :=
      integral_congr_ae (Eventually.of_forall fun p => sq_abs (Work.Coercivity.T4A α p))
    have e2 : ∫ p : ℝ × ℝ, (|Work.Coercivity.T4B α f p|) ^ 2 ∂Work.Coercivity.T4P
        = ∫ p : ℝ × ℝ, (Work.Coercivity.T4B α f p) ^ 2 ∂Work.Coercivity.T4P :=
      integral_congr_ae (Eventually.of_forall fun p => sq_abs (Work.Coercivity.T4B α f p))
    have e3 : ∫ p : ℝ × ℝ,
          |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p| ∂Work.Coercivity.T4P
        = |∫ p : ℝ × ℝ,
            |Work.Coercivity.T4A α p| * |Work.Coercivity.T4B α f p|
              ∂Work.Coercivity.T4P| := by
      rw [abs_of_nonneg (integral_nonneg fun p => mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      exact integral_congr_ae (Eventually.of_forall fun p => abs_mul _ _)
    calc ∫ p : ℝ × ℝ,
          |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p| ∂Work.Coercivity.T4P
        = |∫ p : ℝ × ℝ,
            |Work.Coercivity.T4A α p| * |Work.Coercivity.T4B α f p|
              ∂Work.Coercivity.T4P| := e3
      _ ≤ Real.sqrt (∫ p : ℝ × ℝ, (|Work.Coercivity.T4A α p|) ^ 2 ∂Work.Coercivity.T4P)
            * Real.sqrt (∫ p : ℝ × ℝ, (|Work.Coercivity.T4B α f p|) ^ 2
                ∂Work.Coercivity.T4P) := hle
      _ = Real.sqrt (∫ p : ℝ × ℝ, (Work.Coercivity.T4A α p) ^ 2 ∂Work.Coercivity.T4P)
            * Real.sqrt (∫ p : ℝ × ℝ, (Work.Coercivity.T4B α f p) ^ 2
                ∂Work.Coercivity.T4P) := by rw [e1, e2]
  have hW2 : |∫ p : ℝ × ℝ, Work.Coercivity.T4W α f p ∂Work.Coercivity.T4P|
      ≤ 2 * α * (2 * Real.sqrt (Work.Coercivity.T4J α))
        * Real.sqrt (Work.Coercivity.EDth α f) := by
    have hstep1 : 2 * α * ∫ p : ℝ × ℝ,
          |Work.Coercivity.T4A α p * Work.Coercivity.T4B α f p| ∂Work.Coercivity.T4P
        ≤ 2 * α * (Real.sqrt
              (∫ p : ℝ × ℝ, (Work.Coercivity.T4A α p) ^ 2 ∂Work.Coercivity.T4P)
            * Real.sqrt (∫ p : ℝ × ℝ, (Work.Coercivity.T4B α f p) ^ 2
                ∂Work.Coercivity.T4P)) :=
      mul_le_mul_of_nonneg_left hABb (by positivity)
    have heq : 2 * α * (Real.sqrt
              (∫ p : ℝ × ℝ, (Work.Coercivity.T4A α p) ^ 2 ∂Work.Coercivity.T4P)
            * Real.sqrt (∫ p : ℝ × ℝ, (Work.Coercivity.T4B α f p) ^ 2
                ∂Work.Coercivity.T4P))
        = 2 * α * (2 * Real.sqrt (Work.Coercivity.T4J α))
            * Real.sqrt (Work.Coercivity.EDth α f) := by
      rw [hA2val, hB2val]
      have h4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [show Real.sqrt (4 * Work.Coercivity.T4J α)
          = 2 * Real.sqrt (Work.Coercivity.T4J α) by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) (Work.Coercivity.T4J α), h4]]
      ring
    exact le_trans hWb (le_trans hstep1 (le_of_eq heq))
  -- ### the sharp `C₀` bound: `|C₀ f / c α| ≤ 10 √EDth`
  have hC0 : (Work.Coercivity.C0 f) ^ 2 ≤ Work.Coercivity.EDthW f :=
    C0_sq_le_EDthW_O hso hw2i
  have hC0abs : |Work.Coercivity.C0 f| ≤ Real.sqrt (Work.Coercivity.EDth α f) := by
    have h1 : Real.sqrt ((Work.Coercivity.C0 f) ^ 2)
        ≤ Real.sqrt (Work.Coercivity.EDthW f) := Real.sqrt_le_sqrt hC0
    rw [Real.sqrt_sq_eq_abs] at h1
    exact le_trans h1
      (Real.sqrt_le_sqrt (Work.FTS.StrongEps.EpsE4Thr.EDthW_le_EDth_open (α := α) hα hso hm2))
  have hcinv : |(1 : ℝ) / Work.Spaces.c α| ≤ 10 := by
    have hc := (Work.Spaces.c_bounds α hα hα1').1
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (Work.Coercivity.c_pos hα hα1')]
    linarith
  have hC0c : |Work.Coercivity.C0 f / Work.Spaces.c α|
      ≤ 10 * Real.sqrt (Work.Coercivity.EDth α f) := by
    calc |Work.Coercivity.C0 f / Work.Spaces.c α|
        = |Work.Coercivity.C0 f| * |(1 : ℝ) / Work.Spaces.c α| := by
          rw [div_eq_mul_one_div, abs_mul]
      _ ≤ Real.sqrt (Work.Coercivity.EDth α f) * 10 :=
          mul_le_mul hC0abs hcinv (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = 10 * Real.sqrt (Work.Coercivity.EDth α f) := by ring
  -- ### the angular bound and the arithmetic
  have hJnn : 0 ≤ Work.Coercivity.T4J α := by
    rw [Work.Coercivity.T4J]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _)
  have hJle : Work.Coercivity.T4J α ≤ 120 / (17 * α) :=
    (Work.Coercivity.Gam_sq_sin_neg_gam α hα hα1').2
  have hJsq : (Real.sqrt (Work.Coercivity.T4J α)) ^ 2 ≤ 120 / (17 * α) := by
    rw [Real.sq_sqrt hJnn]
    exact hJle
  have harith : 40 * α * Real.sqrt (Work.Coercivity.T4J α) ≤ 1 / 200 :=
    T4O_arith α (Real.sqrt (Work.Coercivity.T4J α)) hα hα1 (Real.sqrt_nonneg _) hJsq
  have harith' : 40 * (α * Real.sqrt (Work.Coercivity.T4J α)) ≤ 1 / 200 := by
    linarith [harith]
  -- ### the final chain
  have hmain : |Work.Coercivity.wip (Work.Coercivity.thetaW α) (Work.Coercivity.T4 α f)
        (Work.Spaces.Dth f)| ≤ (1 / 200) * Work.Coercivity.EDth α f := by
    rw [hwip2, abs_mul]
    have hstep : |Work.Coercivity.C0 f / Work.Spaces.c α|
          * |∫ p : ℝ × ℝ, Work.Coercivity.T4W α f p ∂Work.Coercivity.T4P|
        ≤ 10 * Real.sqrt (Work.Coercivity.EDth α f)
          * (2 * α * (2 * Real.sqrt (Work.Coercivity.T4J α))
              * Real.sqrt (Work.Coercivity.EDth α f)) :=
      mul_le_mul hC0c hW2 (abs_nonneg _) (by positivity)
    have hshape : 10 * Real.sqrt (Work.Coercivity.EDth α f)
          * (2 * α * (2 * Real.sqrt (Work.Coercivity.T4J α))
              * Real.sqrt (Work.Coercivity.EDth α f))
        = 40 * (α * Real.sqrt (Work.Coercivity.T4J α))
            * (Real.sqrt (Work.Coercivity.EDth α f)) ^ 2 := by ring
    calc |Work.Coercivity.C0 f / Work.Spaces.c α|
          * |∫ p : ℝ × ℝ, Work.Coercivity.T4W α f p ∂Work.Coercivity.T4P|
        ≤ 10 * Real.sqrt (Work.Coercivity.EDth α f)
          * (2 * α * (2 * Real.sqrt (Work.Coercivity.T4J α))
              * Real.sqrt (Work.Coercivity.EDth α f)) := hstep
      _ = 40 * (α * Real.sqrt (Work.Coercivity.T4J α))
            * (Real.sqrt (Work.Coercivity.EDth α f)) ^ 2 := hshape
      _ ≤ (1 / 200) * (Real.sqrt (Work.Coercivity.EDth α f)) ^ 2 :=
          mul_le_mul_of_nonneg_right harith' (sq_nonneg _)
      _ = (1 / 200) * Work.Coercivity.EDth α f := by
          rw [Real.sq_sqrt hEDthnn]
  exact (abs_le.mp hmain).1

end Work.FTS.StrongEps.EpsE4Thr.OClass
end
end
