import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.CoercivityFix.Coer1T.slotDz_LGammaT
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.IntPkgSq_O

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
