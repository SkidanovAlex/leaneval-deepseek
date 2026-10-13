/-
# `(C₀ f)² ≤ 64 Ef f` in the open-quadrant class

`C₀ f = L₁₂(Transport f)(0)` is the constant of the projector-derivative term `Z7` of the
`D_z`-decomposition of `𝓛_Γ^T`.  The paper's estimate (`§L² coercivity for 𝓛_Γ^T with one
z-derivative`, proof of the proposition) is

  `(C₀ f)² ≤ Ef f · (C0Ih · C0D) ≤ 64 Ef f`,

where `C0Ih = ∫_θ C0g²`, `C0D = ∫_0^∞ (s(1+s)w(s))^{-2}`.

This file proves the bound in the *open-quadrant* class `SmoothOpen` (`C^∞` on `(0,∞) × (0,π/2)`,
the class of a localised datum), together with the open-class integrability bundle `IntPkgO`.
It is the port of `Work.FTS.CoercivityFix.Transfer.E1Norm.Pieces.C0_sq_le_Ef_CoerAdm`, which
proves the same statement in the frozen class `CoerAdm` (`SmoothQuad` datum, i.e. `C^∞` up to
the strip boundary) — the stronger class is *not* available on the route, cf.
`EpsE4Thr/CoerAdmSlice.lean` and the header of `EpsE4Thr/OpenClass.lean`.

The three class-dependent ingredients are proved in the sibling modules of `C0EfAux/`:

* `C0EfAux.aesm_slice_theta_O`, `C0EfAux.ae_integrableOn_slice_f_O`,
  `C0EfAux.ae_integrableOn_slice_Dth_O`: a.e. strong measurability and a.e. integrability of the
  angular slices (from `SmoothOpen`'s continuity on the open quadrant and the `IntPkgO`
  integrability fields);
* `C0EfAux.C0thetaIBP_O`: the angular integration by parts
  `∫_θ C0h·∂_θf(z,·) = -∫_θ C0g·f(z,·)`, with the endpoint limits of `f` taken from
  `BdryTraces` (the open analogue of `C0thetaIBP_Q`).

Everything here is `sorry`-free.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.CoercivityFix.Coer1T.slotDz_LGammaT
import Submission.Work.FTS.StrongEps.EpsE4Thr.slice_ibp_gen_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.C0EfAux.SliceAe
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.C0EfAux.ThetaIbpO

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
