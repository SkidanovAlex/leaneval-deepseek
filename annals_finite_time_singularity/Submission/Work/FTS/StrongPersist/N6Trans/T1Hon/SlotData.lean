import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.EasyLeibIntBound
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_MuLipC.RowN.FaDens
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2W.FstarDzIterFourPsiAe
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.C0_sq_le_Ef_O =====
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
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The bound `(C₀ f)² ≤ 64 Ef f` in the open class -/

theorem C0_sq_le_Ef_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Work.FTS.Galerkin.Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hf2 : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f) :
    (Work.Coercivity.C0 f) ^ 2 ≤ 64 * Work.Coercivity.Ef f := by
  have hbd0 : Work.FTS.Nonlin.BdryTraces α 0 f :=
    fun a b hab => hf2.2.2 a b (le_trans hab (by norm_num))
  -- ## the measure, the two test functions and the auxiliary `H`
  set μ : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Iz).prod
    (volume.restrict Work.Spaces.Iθ) with hμdef
  set J : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ with hJdef
  set A : ℝ × ℝ → ℝ := fun p => f p.1 p.2 * Work.Spaces.w p.1 with hAdef
  set B : ℝ × ℝ → ℝ := fun p =>
    Work.Coercivity.C0g p.2 * (1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1)) with hBdef
  set H : ℝ × ℝ → ℝ := fun p =>
    Work.Coercivity.C0g p.2 * f p.1 p.2 / (p.1 * (1 + p.1)) with hHdef
  have hJmeas : MeasurableSet J := by
    rw [hJdef]; exact measurableSet_Ioi.prod measurableSet_Icc
  have hμJ : μ = (volume.prod volume).restrict J := by
    rw [hμdef, hJdef]
    have h1 : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) :=
      (Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
    rw [h1, Measure.prod_restrict]
  have hmemJ : ∀ᵐ p ∂μ, p ∈ J := by
    rw [hμJ]; exact ae_restrict_mem hJmeas
  -- ## a.e. strong measurability
  have hC0g_cont : Continuous Work.Coercivity.C0g := by
    unfold Work.Coercivity.C0g
    fun_prop
  have hf_aesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2) μ :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hso.continuousOn
  have hw_aesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.w p.1) μ :=
    Work.Spaces.aesm_of_continuousOn_Qd _ Work.Coercivity.continuousOn_w_quad
  have hA_aesm : MeasureTheory.AEStronglyMeasurable A μ := by
    rw [hAdef]; exact hf_aesm.mul hw_aesm
  have hrat_meas : Measurable (fun p : ℝ × ℝ => 1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1)) := by
    unfold Work.Spaces.w
    fun_prop
  have hB_aesm : MeasureTheory.AEStronglyMeasurable B μ := by
    rw [hBdef]
    exact ((hC0g_cont.measurable.comp measurable_snd).mul hrat_meas).aestronglyMeasurable
  have hH_aesm : MeasureTheory.AEStronglyMeasurable H μ := by
    rw [hHdef]
    have h1 : AEMeasurable (fun p : ℝ × ℝ => Work.Coercivity.C0g p.2 * f p.1 p.2) μ :=
      ((hC0g_cont.measurable.comp measurable_snd).aestronglyMeasurable.mul hf_aesm).aemeasurable
    have h2 : AEMeasurable (fun p : ℝ × ℝ => p.1 * (1 + p.1)) μ :=
      (measurable_fst.mul (measurable_const.add measurable_fst)).aemeasurable
    exact (h1.div h2).aestronglyMeasurable
  -- ## integrability of `A²`, `B²` and `H`
  have hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Work.Spaces.w z) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hIP.sqDzOne 0 (by norm_num)).congr_fun ?_ (measurableSet_Ici.prod measurableSet_Icc)
    rintro ⟨z, θ⟩ _
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
    ring
  have hA2int : MeasureTheory.Integrable (fun p : ℝ × ℝ => A p ^ 2) μ := by
    rw [hAdef, hμdef, Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hfw
  have hInvSq : MeasureTheory.IntegrableOn
      (fun s : ℝ => (1 / (s * (1 + s) * Work.Spaces.w s)) ^ 2) Work.Spaces.Iz := by
    refine (Work.Coercivity.integrable_Iz_zsq_div_six).congr
      (Filter.Eventually.of_forall (fun s => ?_))
    rcases eq_or_ne s 0 with rfl | hs
    · norm_num [Work.Spaces.w]
    · unfold Work.Spaces.w
      field_simp
  have hC0g2_int : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Coercivity.C0g θ) ^ 2) Work.Spaces.Iθ :=
    (hC0g_cont.pow 2).continuousOn.integrableOn_Icc
  have hB2int : MeasureTheory.Integrable (fun p : ℝ × ℝ => B p ^ 2) μ := by
    rw [hBdef, hμdef]
    have h1 : (fun p : ℝ × ℝ => (Work.Coercivity.C0g p.2
          * (1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1))) ^ 2)
        = fun p : ℝ × ℝ =>
          (1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1)) ^ 2 * (Work.Coercivity.C0g p.2) ^ 2 := by
      funext p; rw [mul_pow]; ring
    rw [h1]
    exact hInvSq.mul_prod hC0g2_int
  have hHdom : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (1 / 2) * (A p ^ 2 + B p ^ 2)) μ :=
    (hA2int.add hB2int).const_mul (1 / 2)
  have hHint : MeasureTheory.Integrable H μ := by
    refine MeasureTheory.Integrable.mono' hHdom hH_aesm ?_
    filter_upwards [hmemJ] with p hp
    have hp1 : 0 < p.1 := hp.1
    have hwpos : 0 < Work.Spaces.w p.1 := by rw [Work.Spaces.w]; positivity
    have hden : 0 < p.1 * (1 + p.1) := by positivity
    have hAeq : A p ^ 2 = (|f p.1 p.2| * Work.Spaces.w p.1) ^ 2 := by
      rw [hAdef, mul_pow, mul_pow, sq_abs]
    have hBeq : B p ^ 2
        = (|Work.Coercivity.C0g p.2| * (1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1))) ^ 2 := by
      rw [hBdef, mul_pow, mul_pow, sq_abs]
    have hHeq : ‖H p‖ = (|f p.1 p.2| * Work.Spaces.w p.1)
        * (|Work.Coercivity.C0g p.2| * (1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1))) := by
      simp only [hHdef]
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hden]
      have hp1ne : p.1 ≠ 0 := ne_of_gt hp1
      have h1p1 : (0 : ℝ) < 1 + p.1 := by linarith
      have h1p1ne : (1 : ℝ) + p.1 ≠ 0 := ne_of_gt h1p1
      have hwne : Work.Spaces.w p.1 ≠ 0 := ne_of_gt hwpos
      field_simp
    rw [hHeq, hAeq, hBeq]
    nlinarith [two_mul_le_add_sq (|f p.1 p.2| * Work.Spaces.w p.1)
      (|Work.Coercivity.C0g p.2| * (1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1)))]
  -- ## Fubini and the identification with the double integral
  have hH_fub : (∫ s in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, H (s, θ)) = ∫ p, H p ∂μ := by
    have hint := hHint
    rw [hμdef] at hint ⊢
    exact (MeasureTheory.integral_prod H hint).symm
  have hX : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Coercivity.C0g θ * f s θ / (s * (1 + s)))
      = ∫ p, A p * B p ∂μ := by
    have hfill : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Coercivity.C0g θ * f s θ / (s * (1 + s)))
        = ∫ s in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, H (s, θ) := by
      rw [hHdef]
      exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
    rw [hfill, hH_fub]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hmemJ] with p hp
    have hp1 : 0 < p.1 := hp.1
    have hwne : Work.Spaces.w p.1 ≠ 0 := by rw [Work.Spaces.w]; positivity
    have hp1ne : p.1 ≠ 0 := ne_of_gt hp1
    have h1p1 : (0 : ℝ) < 1 + p.1 := by linarith
    have h1p1ne : (1 : ℝ) + p.1 ≠ 0 := ne_of_gt h1p1
    rw [hHdef, hAdef, hBdef]
    field_simp
  -- ## the two `L²` norms
  have hA2eq : ∫ p, A p ^ 2 ∂μ = Work.Coercivity.Ef f := by
    have hint := hA2int
    rw [hAdef] at hint ⊢
    rw [hμdef] at hint ⊢
    rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2) hint]
    rfl
  have hB2eq : ∫ p, B p ^ 2 ∂μ = Work.Coercivity.C0Ih * Work.Coercivity.C0D := by
    have h1 : (fun p : ℝ × ℝ => B p ^ 2)
        = fun p : ℝ × ℝ =>
          (1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1)) ^ 2 * (Work.Coercivity.C0g p.2) ^ 2 := by
      funext p; rw [hBdef, mul_pow]; ring
    rw [h1, hμdef]
    rw [MeasureTheory.integral_prod_mul
      (f := fun s : ℝ => (1 / (s * (1 + s) * Work.Spaces.w s)) ^ 2)
      (g := fun θ : ℝ => (Work.Coercivity.C0g θ) ^ 2)]
    have hC0D' : (∫ s in Work.Spaces.Iz, (1 / (s * (1 + s) * Work.Spaces.w s)) ^ 2)
        = Work.Coercivity.C0D :=
      (MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
    rw [show Work.Coercivity.C0Ih = ∫ θ in Work.Spaces.Iθ, (Work.Coercivity.C0g θ) ^ 2 from rfl,
      hC0D']
    ring
  have hnum : Work.Coercivity.C0Ih * Work.Coercivity.C0D ≤ 64 := by
    have h1 : Work.Coercivity.C0Ih ≤ 729 := Work.Coercivity.C0Ih_le
    have h2 : Work.Coercivity.C0D ≤ 1 / 16 := Work.Coercivity.C0D_le
    have h3 : 0 ≤ Work.Coercivity.C0Ih := by
      rw [Work.Coercivity.C0Ih]; exact integral_nonneg (fun θ => sq_nonneg _)
    have h4 : 0 ≤ Work.Coercivity.C0D := by
      rw [Work.Coercivity.C0D]; exact integral_nonneg (fun s => sq_nonneg _)
    nlinarith [h1, h2, h3, h4]
  have hEf : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
  -- ## the identity `C₀ f = -∫∫ C0g(θ)f/(s(1+s))`
  have hC0 : Work.Coercivity.C0 f
      = -∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Coercivity.C0g θ * f s θ / (s * (1 + s)) := by
    have step1 : Work.Coercivity.C0 f
        = ∫ s in Set.Ioi (0 : ℝ),
            Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport f) s := by
      rw [Work.Coercivity.C0, Work.Coercivity.L12f, Work.FM.L12]
    rw [step1]
    have step2 : (∫ s in Set.Ioi (0 : ℝ),
          Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport f) s)
        = ∫ s in Set.Ioi (0 : ℝ), (1 / (s * (1 + s)))
            * ∫ θ in Work.Spaces.Iθ, Work.Coercivity.C0h θ * Work.Spaces.pth f s θ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs' => ?_)
      have hs'0 : (0 : ℝ) < s := hs'
      have hs0 : s ≠ 0 := ne_of_gt hs'0
      have hs1 : (1 : ℝ) + s ≠ 0 := ne_of_gt (by linarith)
      rw [Work.FM.L12dens]
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [Work.Coercivity.Transport, Work.Spaces.Dth, Work.Coercivity.C0h, Work.Spaces.K]
      field_simp
    rw [step2]
    have step3 : (∫ s in Set.Ioi (0 : ℝ), (1 / (s * (1 + s)))
          * ∫ θ in Work.Spaces.Iθ, Work.Coercivity.C0h θ * Work.Spaces.pth f s θ)
        = -∫ s in Set.Ioi (0 : ℝ), (1 / (s * (1 + s)))
            * ∫ θ in Work.Spaces.Iθ, Work.Coercivity.C0g θ * f s θ := by
      rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
      have hsf : ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          MeasureTheory.IntegrableOn (fun θ => f s θ) Work.Spaces.Iθ :=
        C0EfAux.ae_integrableOn_slice_f_O α hso hIP
      have hsD : ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          MeasureTheory.IntegrableOn (fun θ => Work.Spaces.Dth f s θ) Work.Spaces.Iθ :=
        C0EfAux.ae_integrableOn_slice_Dth_O α hα hso hIP
      have hsf' : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
          MeasureTheory.IntegrableOn (fun θ => f s θ) Work.Spaces.Iθ := by
        rw [Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
        exact hsf
      have hsD' : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
          MeasureTheory.IntegrableOn (fun θ => Work.Spaces.Dth f s θ) Work.Spaces.Iθ := by
        rw [Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
        exact hsD
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hsf' hsD'
      filter_upwards [hsf', hsD'] with s hfs hDs hs'
      rw [C0EfAux.C0thetaIBP_O α hα hso hbd0 hs' (hfs hs') (hDs hs')]
      ring
    rw [step3]
    have step4 : (∫ s in Set.Ioi (0 : ℝ), (1 / (s * (1 + s)))
          * ∫ θ in Work.Spaces.Iθ, Work.Coercivity.C0g θ * f s θ)
        = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
            Work.Coercivity.C0g θ * f s θ / (s * (1 + s)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs' => ?_)
      rw [MeasureTheory.integral_div]
      ring
    rw [step4]
  -- ## Cauchy–Schwarz and the numerical bound
  calc (Work.Coercivity.C0 f) ^ 2
      = (∫ p, A p * B p ∂μ) ^ 2 := by rw [hC0, hX]; ring
    _ ≤ (∫ p, A p ^ 2 ∂μ) * (∫ p, B p ^ 2 ∂μ) :=
        Work.Coercivity.cs_integral_mul
          ((MeasureTheory.memLp_two_iff_integrable_sq hA_aesm).mpr hA2int)
          ((MeasureTheory.memLp_two_iff_integrable_sq hB_aesm).mpr hB2int)
    _ = Work.Coercivity.Ef f
          * (Work.Coercivity.C0Ih * Work.Coercivity.C0D) := by rw [hA2eq, hB2eq]
    _ ≤ Work.Coercivity.Ef f * 64 := by nlinarith [hnum, hEf]
    _ = 64 * Work.Coercivity.Ef f := by ring

end Work.FTS.StrongEps.EpsE4Thr.OClass
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.est_A_O =====
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

set_option maxHeartbeats 1600000

/-- **The coercivity of `𝓛̂` on the `η`-slot `D_z`, in the open class.**
The open-class twin of `Work.FTS.CoercivityFix.Coer1.est_A`, with `RegQ α 2` replaced by
`RegQo α 2` and the integrability bundle `IntPkg` by its open counterpart `IntPkgO`. -/
theorem est_A_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f) :
    (47 / 100) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz f)
      - (Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta f
          + 4 * Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α) (Work.Spaces.Dth f)
          + (1 / 8) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz f))
      ≤ Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f) := by
  have hp := hIP
  obtain ⟨hso, hm, hb⟩ := hf
  -- ## the `𝓛̂`-pairing of `D_z f`
  have hsoDz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz f) := hso.Dz
  have hvan := Work.FTS.CoercivityFix.Coer1.hvan_eta_of_gam α hα
    (fun z hz => ((hb 0 1 (by norm_num)).2 z hz).1)
    (fun z hz => ((hb 0 1 (by norm_num)).2 z hz).2)
  have h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dz f z θ) ^ 2 * Work.Spaces.w z ^ 2
        * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.DzIter 1 f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)
      (hp.sqDzEta 1 (by norm_num)) (fun z θ => by
        simp only [Work.FTS.CoercivityFix.Coer1.Rho, Work.Spaces.DzIter_succ,
          Work.Spaces.DzIter_zero]; ring)
  have h2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.L (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
        * Work.Spaces.w z ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      Work.Coercivity.L (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)
      hp.intL_Dz_eta (fun z θ => by simp only [Work.FTS.CoercivityFix.Coer1.Rho]; ring)
  have h3 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        * Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ / (1 + z))
      hp.hint_Dz_eta (fun z θ => by simp only [Work.FTS.CoercivityFix.Coer1.Rho,
        Work.FTS.CoercivityFix.Coer1.sig]; ring)
  have h4 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        * (Work.Spaces.Dz f z θ) ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q h1 (fun z θ => by
      simp only [Work.FTS.CoercivityFix.Coer1.sig]; ring)
  have h5 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Transport (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      3 * (Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ / (1 + z)))
      (hp.hint_Dz_eta.const_mul 3) (fun z θ => by
        simp only [Work.Coercivity.Transport]; ring)
  have hwc : ∀ A B : Fn, Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta) A B
      = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2
          * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ) A B :=
    fun A B => rfl
  have hwDz : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
        (Work.Spaces.Dz f) (Work.Spaces.Dz f)
      = Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz f) :=
    Work.FTS.CoercivityFix.Coer1.wip_Rho_self Work.Spaces.eta (Work.Spaces.Dz f)
  have hL0 := Work.FTS.CoercivityFix.Coer1SO.wip_L_self_QO (Work.Spaces.Dz f) hp.zibp_Dz
    (Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta) h1 h2
  have hTr := Work.FTS.StrongEps.EpsE4Thr.wip_transport_le_O Work.Spaces.eta (Work.Spaces.Dz f)
    hsoDz hvan.1 hvan.2 h3 h4
  have hTr' : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (Work.Coercivity.Transport (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
      ≤ (3 / 100) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz f) := by
    rw [hwDz] at hTr
    have heta : (3 : ℝ) * |Work.Spaces.eta - 1| ≤ 3 / 100 := by
      rw [Work.Spaces.eta]
      rw [show |(99 : ℝ) / 100 - 1| = 1 / 100 by norm_num]
      norm_num
    have hEn := Work.FTS.CoercivityFix.Coer1.En_nonneg Work.Spaces.eta (Work.Spaces.Dz f)
    have h2' := mul_le_mul_of_nonneg_right heta hEn
    linarith [hTr, h2']
  have hL : (47 / 100) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz f)
      ≤ Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f) := by
    have hsplit : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
        = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
            (Work.Coercivity.L (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
          - Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
              (Work.Coercivity.Transport (Work.Spaces.Dz f)) (Work.Spaces.Dz f) := by
      have h := Work.FTS.CoercivityFix.Coer1.wip_sub_left
        (ρ := Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
        (A := Work.Coercivity.L (Work.Spaces.Dz f))
        (B := Work.Coercivity.Transport (Work.Spaces.Dz f)) (C := Work.Spaces.Dz f)
        hp.intL_Dz_eta h5
      show Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
        (fun z θ => Work.Coercivity.L (Work.Spaces.Dz f) z θ
          - Work.Coercivity.Transport (Work.Spaces.Dz f) z θ) (Work.Spaces.Dz f) = _
      exact h
    rw [hsplit, hwc (Work.Coercivity.L (Work.Spaces.Dz f)) (Work.Spaces.Dz f), hL0,
      ← hwc (Work.Spaces.Dz f) (Work.Spaces.Dz f), hwDz]
    linarith [hTr']
  -- ## the `D_z`-commutator defect
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
          + Work.FTS.CoercivityFix.E2hat f z θ := by
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos] with z hz
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
    exact Work.FTS.StrongPersist.H6Aux.Dz_Lhat_of_open Work.FTS.EllipticEst.isOpen_Q0 hso
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩) hz
  have hsplitE : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f)
      = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
        + Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
            (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f) := by
    rw [Work.Coercivity.wip_congr_ae hae]
    exact Work.Coercivity.wip_add_left (ρ := Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (g := Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
      (h := Work.FTS.CoercivityFix.E2hat f) (k := Work.Spaces.Dz f)
      hp.intLhat_Dz_eta hp.intE2hat_Dz_eta
  have hU0 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.DzIter 0 f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)
      (hp.sqDzEta 0 (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.DzIter_zero])
  have hDη : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.mixed 0 1 f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)
      (hp.sqMixedEta 1 0 (by norm_num) (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
          Work.Spaces.DthIter_succ])
  have hDγ : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.mixed 0 1 f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ)
      (hp.sqMixedGam 1 0 (by norm_num) (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
          Work.Spaces.DthIter_succ])
  have hG : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dz f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.DzIter 1 f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)
      (hp.sqDzEta 1 (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero])
  have hE := Work.FTS.CoercivityFix.Coer1.E2hat_wip_lower α hα hp.intE2hat_Dz_eta hU0 hDγ hG
  rw [hsplitE]
  linarith [hL, hE]

end Work.FTS.StrongEps.EpsE4Thr.OClass
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.est_B_O =====
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
set_option maxHeartbeats 1600000

/-- **The `η`-weighted `L²`-pairing of `𝓛̂` in the open class.**
`⟨𝓛̂f, f⟩_{w² sin^{-η}} ≥ (47/100)·E_η(f)`: `(LW)` gives `⟨𝓛f,f⟩ = ½E_η(f)`, and the transport
pairing costs at most `3|η-1| = 3/100` of `E_η(f)`.

This is `Work.FTS.CoercivityFix.Coer1.est_B` with the interior class `RegQ α 2` replaced by the
open class `RegQo α 2` and the integrability bundle `IntPkg` by `IntPkgO`. -/
theorem est_B_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {f : Fn}
    (hf : RegQo α 2 f) (hp : IntPkgO α f) :
    (47 / 100) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta f
      ≤ Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.FTS.CoercivityFix.Lhat f) f := by
  obtain ⟨hso, hm, hb⟩ := hf
  -- ### the integrability certificates in the `w²σ` shape of the two `wip` identities
  have h0 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho
        Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hp.sqDzEta 0 (by norm_num)).congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
  have h1 := Work.FTS.CoercivityFix.Coer1.to_h1 (β := Work.Spaces.eta) h0
  have h2 := Work.FTS.CoercivityFix.Coer1.to_tr_hint2 (β := Work.Spaces.eta) h0
  have hL2 := Work.FTS.CoercivityFix.Coer1.to_h2 (β := Work.Spaces.eta) hp.intL_f_eta
  have hT2 := Work.FTS.CoercivityFix.Coer1.to_tr_hint (β := Work.Spaces.eta) hp.hint_f_eta
  -- ### the angular vanishing limits at the `η` exponent, from the `γ` ones
  have hvan := Work.FTS.CoercivityFix.Coer1.hvan_eta_of_gam α hα
    (fun z hz => ((hb 0 0 (by norm_num)).2 z hz).1)
    (fun z hz => ((hb 0 0 (by norm_num)).2 z hz).2)
  -- ### the two Euler–Lagrange inputs
  have hL := Work.FTS.CoercivityFix.Coer1SO.wip_L_self_QO f hp.zibp_f
    (Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta) h1 hL2
  have hw : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta) f f
      = Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta f :=
    Work.FTS.CoercivityFix.Coer1.wip_Rho_self Work.Spaces.eta f
  have hTr := wip_transport_le_O Work.Spaces.eta f hso hvan.1 hvan.2 hT2 h2
  have hTr' : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (Work.Coercivity.Transport f) f
      ≤ (3 / 100) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta f := by
    rw [hw] at hTr
    have heta : (3 : ℝ) * |Work.Spaces.eta - 1| ≤ 3 / 100 := by
      rw [Work.Spaces.eta]
      rw [show |(99 : ℝ) / 100 - 1| = 1 / 100 by norm_num]
      norm_num
    have hEn := Work.FTS.CoercivityFix.Coer1.En_nonneg Work.Spaces.eta f
    have h2' := mul_le_mul_of_nonneg_right heta hEn
    linarith [hTr, h2']
  -- ### the split of `𝓛̂ = 𝓛 - Transport`
  have hT : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Transport f z θ * f z θ * Work.FTS.CoercivityFix.Coer1.Rho
        Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.intTransport_of hp.hint_f_eta
  have hsplit : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
        (Work.FTS.CoercivityFix.Lhat f) f
      = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.Coercivity.L f) f
        - Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.Coercivity.Transport f) f := by
    have h := Work.FTS.CoercivityFix.Coer1.wip_sub_left
      (ρ := Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (A := Work.Coercivity.L f) (B := Work.Coercivity.Transport f) (C := f)
      hp.intL_f_eta hT
    show Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (fun z θ => Work.Coercivity.L f z θ - Work.Coercivity.Transport f z θ) f = _
    exact h
  have hwc : ∀ A B : Fn, Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta) A B
      = Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ)
          A B := by
    intro A B
    simp only [Work.Coercivity.wip, Work.FTS.CoercivityFix.Coer1.Rho]
  rw [hsplit, hwc (Work.Coercivity.L f) f, hL, ← hwc f f, hw]
  linarith [hTr']

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.R.Slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongPersist.H6Aux.R.Slots` — the level-one slot infrastructure

Aggregator for the two halves of the infrastructure used by the four slot estimates of the
base case `base_R`: `R.SlotsBasic` (the `wip` manipulation lemmas, the `ℋᵏ`-integrand
integrability, and the integrability-by-domination machinery) and `R.SlotsBlocks` (continuity
of the blocks, the pointwise block bounds against `HkIntegrand`, the `Lhat`-block bounds and
the weighted-square/product integrability workhorses).
-/
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.SlotData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1Hon

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The slot data of the `T1` transport pairing -/

/-- The leaf weight `w²·sin(2θ)^{-q}` of a slot with angular exponent `q`. -/
def t1W (q : ℝ) : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)

/-- The *hard* summand of the slot pairing: all `a + 1` angular derivatives on the `g`-block. -/
def t1Hard (q : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => t1W q z θ * f z θ * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ
    * Work.Spaces.mixed b a g z θ

/-- The Leibniz sum of the *easy* summands (all splits except `(0,0)`) of the slot pairing,
without the weight. -/
def t1Leib (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
    (if a1 = 0 ∧ b1 = 0 then 0 else
      ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
        * (Work.Spaces.mixed b1 a1 f z θ * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ))

/-- The *easy* summands of the slot pairing, in weighted form. -/
def t1Easy (q : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => t1W q z θ * t1Leib f g a b z θ * Work.Spaces.mixed b a g z θ

/-- The pointwise majorant of the easy summands. -/
def t1EasyAbs (q : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => |t1W q z θ| * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
    (if a1 = 0 ∧ b1 = 0 then 0 else
      |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
        * (Work.Spaces.mixed b1 a1 f z θ
           * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|))
    * |Work.Spaces.mixed b a g z θ|

theorem abs_ite_zero_eq (p : Prop) [Decidable p] (x : ℝ) :
    |if p then (0 : ℝ) else x| = if p then 0 else |x| := by
  by_cases h : p <;> simp [h]

theorem t1EasyAbs_nonneg (q : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) (z θ : ℝ) :
    0 ≤ t1EasyAbs q f g a b z θ := by
  rw [t1EasyAbs]
  refine mul_nonneg (mul_nonneg (abs_nonneg _) ?_) (abs_nonneg _)
  refine Finset.sum_nonneg fun a1 _ => Finset.sum_nonneg fun b1 _ => ?_
  by_cases h : a1 = 0 ∧ b1 = 0
  · rw [if_pos h]
  · rw [if_neg h]
    exact abs_nonneg _

theorem abs_t1Leib_le (f g : ℝ → ℝ → ℝ) (a b : ℕ) (z θ : ℝ) :
    |t1Leib f g a b z θ| ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
      (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
        |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
          * (Work.Spaces.mixed b1 a1 f z θ
             * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|) := by
  calc |t1Leib f g a b z θ|
      = |∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
              * (Work.Spaces.mixed b1 a1 f z θ
                 * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ))| := rfl
    _ ≤ ∑ a1 ∈ Finset.range (a + 1), |∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
              * (Work.Spaces.mixed b1 a1 f z θ
                 * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          |if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
              * (Work.Spaces.mixed b1 a1 f z θ
                 * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)| :=
        Finset.sum_le_sum fun a1 _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
              * (Work.Spaces.mixed b1 a1 f z θ
                 * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|) := by
        refine Finset.sum_congr rfl fun a1 _ => Finset.sum_congr rfl fun b1 _ => ?_
        exact abs_ite_zero_eq _ _

theorem abs_t1Easy_le (q : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) (z θ : ℝ) :
    |t1Easy q f g a b z θ| ≤ t1EasyAbs q f g a b z θ := by
  rw [t1Easy, t1EasyAbs, abs_mul, abs_mul]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    (abs_nonneg _)
  exact abs_t1Leib_le f g a b z θ

/-- A summand of `t1EasyAbs` is dominated by `36` times the corresponding unweighted summand. -/
theorem t1EasyAbs_summand_le {α q : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ}
    (hab : a + b ≤ 4) (ha1 : a1 ≤ a) (hb1 : b1 ≤ b)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
      |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
        * (Work.Spaces.mixed b1 a1 f z θ
           * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|)
      ≤ 36 * (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
        |Work.Spaces.mixed b1 a1 f z θ|
          * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|) := by
  by_cases h : a1 = 0 ∧ b1 = 0
  · rw [if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h]
    have hc : |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))| ≤ 36 := by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast choose_mul_le (a := a) (i := a1) (b := b) (j := b1)
        (by omega) (by omega)
    rw [abs_mul]
    exact mul_le_mul hc (le_of_eq (abs_mul _ _)) (abs_nonneg _) (by norm_num)

theorem t1EasyAbs_le {α q : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ} {a b : ℕ}
    (hab : a + b ≤ 4)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    t1EasyAbs q f g a b z θ ≤ 36 * slotEasySum α f g a b z θ := by
  have hW : |t1W q z θ| ≤ Work.FTS.TransportS.slotW α a z θ := by
    rw [show t1W q z θ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) from rfl,
      abs_of_nonneg (weight_nonneg_of_Iθ q ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)]
    exact weight_le_slotW hα hq0 hqa hz hθ
  have hAnonneg : 0 ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
      (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
        |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
          * (Work.Spaces.mixed b1 a1 f z θ
             * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|) :=
    Finset.sum_nonneg fun a1 _ => Finset.sum_nonneg fun b1 _ => by
      by_cases h : a1 = 0 ∧ b1 = 0
      · rw [if_pos h]
      · rw [if_neg h]; exact abs_nonneg _
  have hBnonneg : 0 ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
      (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
        |Work.Spaces.mixed b1 a1 f z θ|
          * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|) :=
    Finset.sum_nonneg fun a1 _ => Finset.sum_nonneg fun b1 _ => by
      by_cases h : a1 = 0 ∧ b1 = 0
      · rw [if_pos h]
      · rw [if_neg h]; exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hA : (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
          |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
            * (Work.Spaces.mixed b1 a1 f z θ
               * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|))
      ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (36 * (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
          |Work.Spaces.mixed b1 a1 f z θ|
            * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|)) :=
    Finset.sum_le_sum fun a1 ha1 => Finset.sum_le_sum fun b1 hb1 =>
      t1EasyAbs_summand_le hα hab (by have := Finset.mem_range.mp ha1; omega)
        (by have := Finset.mem_range.mp hb1; omega) hq0 hqa hz hθ
  have hfac1 : (36 : ℝ) * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
          |Work.Spaces.mixed b1 a1 f z θ|
            * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|))
      = ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (36 * (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
          |Work.Spaces.mixed b1 a1 f z θ|
            * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|)) := by
    simp only [Finset.mul_sum]
  have hfac2 : Work.FTS.TransportS.slotW α a z θ
        * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|))
        * |Work.Spaces.mixed b a g z θ|
      = ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
          Work.FTS.TransportS.slotW α a z θ * |Work.Spaces.mixed b1 a1 f z θ|
            * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
            * |Work.Spaces.mixed b a g z θ|) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a1 _ => Finset.sum_congr rfl fun b1 _ => ?_
    by_cases h : a1 = 0 ∧ b1 = 0
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  calc t1EasyAbs q f g a b z θ
      = |t1W q z θ| * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
              * (Work.Spaces.mixed b1 a1 f z θ
                 * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|))
          * |Work.Spaces.mixed b a g z θ| := rfl
    _ ≤ Work.FTS.TransportS.slotW α a z θ
          * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
              |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
                * (Work.Spaces.mixed b1 a1 f z θ
                   * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|))
          * |Work.Spaces.mixed b a g z θ| := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hW hAnonneg) (abs_nonneg _)
    _ ≤ Work.FTS.TransportS.slotW α a z θ
          * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (36 * (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
              |Work.Spaces.mixed b1 a1 f z θ|
                * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|)))
          * |Work.Spaces.mixed b a g z θ| := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA (slotW_nonneg α a z θ)) (abs_nonneg _)
    _ = 36 * (Work.FTS.TransportS.slotW α a z θ
          * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
              |Work.Spaces.mixed b1 a1 f z θ|
                * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|))
          * |Work.Spaces.mixed b a g z θ|) := by rw [← hfac1]; ring
    _ = 36 * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            Work.FTS.TransportS.slotW α a z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
              * |Work.Spaces.mixed b a g z θ|)) := by rw [hfac2]
    _ = 36 * slotEasySum α f g a b z θ := by rw [slotEasySum]
end

end Work.FTS.StrongPersist.N6Trans.T1Hon
end
