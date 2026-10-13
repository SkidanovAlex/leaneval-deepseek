import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.EDthW_EL12z_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.C0_sq_le_EDthW_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenCoer.SlotWCommon
import Submission.Work.FTS.CoercivityFix.Coer1T.slotGam_LGammaT

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
