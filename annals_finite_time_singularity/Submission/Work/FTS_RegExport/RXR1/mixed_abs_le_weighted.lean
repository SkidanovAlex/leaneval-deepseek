import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Aux.RStep
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.StrongPersist.N6Trans.slotT2Six
import Submission.Work.FTS_EllLimOK.PkgJets.cornerBoundRepair
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.THL.mixed_slice_pointwise_le_noTrace
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EpsEngine.ZTracesAux.sup_theta_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ZTracesAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# `sup_theta_gen` — the uniform angular sup bound for a mixed slot, at every order `m`

For `0 < α ≤ 1` there is a constant `K = K(α) ≥ 0` — the **same** for every `m ≥ 1`, every
datum `f`, and every slot — such that for every mixed slot `D_z^b D_θ^a f` of *total* order
`a + b + 1 ≤ m`

  `(D_z^b D_θ^a f (s,θ) · w(s))² ≤ K · ∫_σ HkIntegrand α m f (s,σ) dσ`

for every `s > 0` and every `θ ∈ (0,π/2)`, where `w(s) = (1+s)²/s²`.

This is the arbitrary-order version of `Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform`
(which is the case `m = 4`, `a + b ≤ 3`), and the proof is the same one: the radial weight `w`
is a function of `s` alone, so the estimate is purely *angular*; the pointwise domination of a
slot by `HkIntegrand` (a summand of the integrand, up to the factor
`sin(2σ)^{±γ} ≤ 1`), the angular Agmon/mean–variation bound
`g(θ)² ≤ (8/π)∫ g² + 2(∫ sin^{γ-2})(∫ g'² sin^{2-γ})` of
`Work.FTS_RegExport.RXT.Slots.angular_meanVar_aux`, and `∫_{Iθ} sin^{γ-2} ≤ 100/(γ-1)` give,
with `g = mixed b a f s ·` and `g' = ∂_θ g = mixed b (a+1) f s · / sin(2·)`,

  `(D_z^bD_θ^af·w)² ≤ (8/π)∫HkIntegrand + 2(∫sin^{γ-2})∫HkIntegrand
     ≤ (8/π + 200/(γ-1))∫HkIntegrand`.

The analytic inputs specific to the general order are the companion lemmas
`Dth_mixed_eq_gen`, `slot_le_HkIntegrand_gen`, `slot_sin_le_HkIntegrand_gen`,
`continuousOn_pth_mixed_slice_gen`, `integrable_slot_sq_gen`, `integrable_pth_sq_sin_gen`
(imported above).
-/

/-- **Uniform angular sup bound for a mixed slot, at every order.** -/
theorem sup_theta_gen {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, 1 ≤ m → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α m f →
      ∀ b a : ℕ, a + b + 1 ≤ m → ∀ s : ℝ, 0 < s → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed b a f s θ * Work.Spaces.w s) ^ 2
        ≤ K * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ) := by
  have hγpos : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam]; linarith
  refine ⟨8 / Real.pi + 200 / (Work.Spaces.gam α - 1), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 8 / Real.pi := by positivity
    have h2 : (0 : ℝ) ≤ 200 / (Work.Spaces.gam α - 1) :=
      div_nonneg (by norm_num) hγpos.le
    linarith
  intro m hm f hSm hmem b a hab s hs θ hθ0 hθ1
  have hsI : s ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hs.le
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- the finite smoothness needed for the slot
  have hF : ContDiffOn ℝ (a + b + 1) (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hSm (a + b + 1)
  have hmixed1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed b a f))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.SmoothOpen.mixed hSm b a).forall 1
  have hslice1 : ContDiffOn ℝ 1 (fun σ => Work.Spaces.mixed b a f s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.StrongEps.EComparison.contDiffOn_slice_t hs hmixed1
  -- the two hypotheses of the angular bound
  have hderiv : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun σ' => Work.Spaces.mixed b a f s σ')
        (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) σ := by
    intro σ hσ
    exact ((hslice1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hσ)).hasDerivAt
  have hcont1 : ContinuousOn (fun σ => Work.Spaces.mixed b a f s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hslice1.continuousOn
  have hgc : ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.mixed b a f) s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_pth_mixed_slice_gen hF b a (le_refl _) hs
  have hpoint1 : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2
        ≤ Work.Spaces.HkIntegrand α m f s σ :=
    fun σ hσ => slot_le_HkIntegrand_gen hα b a (by omega) s hσ
  have hpoint2 : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) ≤ Work.Spaces.HkIntegrand α m f s σ :=
    fun σ hσ => slot_sin_le_HkIntegrand_gen (α := α) b a (by omega) s hσ
  have hident : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.pth (Work.Spaces.mixed b a f) s σ
        = Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ) := by
    intro σ hσ
    have hD := Dth_mixed_eq_gen (f := f) hF b a (le_refl _) hs hσ
    rw [Work.Spaces.Dth] at hD
    rw [eq_div_iff (ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)), mul_comm]
    exact hD
  have hI1 := integrable_slot_sq_gen hmem b a hs hcont1 hpoint1
  have hI2 := integrable_pth_sq_sin_gen hmem b a hs hgc hpoint2 hident
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  have hγ2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  have hang := Work.FTS_RegExport.RXT.Slots.angular_meanVar_aux (γ := Work.Spaces.gam α)
    hγ1 hγ2 hderiv hgc hI1 hI2 θ hθmem
  -- the scalar bounds
  have hAeq : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2) * (Work.Spaces.w s) ^ 2
      = ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2 := by
    rw [mul_comm, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun σ => by ring)
  have hAle : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2) * (Work.Spaces.w s) ^ 2
      ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ := by
    rw [hAeq]
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun σ => sq_nonneg _)
      (hmem.1 s hsI) ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    exact hpoint1 σ hσ
  have hBeq : (∫ σ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w s) ^ 2
      = ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
    rw [mul_comm, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
    have hpth := hident σ hσ
    rw [hpth]
    have h2 : (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
      rw [show (2 : ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
        Real.rpow_add hsin, Real.rpow_ofNat]
    have e1 : (Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ)) ^ 2
        = (Work.Spaces.mixed b (a + 1) f s σ) ^ 2 / (Real.sin (2 * σ)) ^ 2 :=
      div_pow _ _ 2
    have hwne : Work.Spaces.w s ≠ 0 := ne_of_gt (Work.FTS_RegExport.RXT.Slots.w_pos_aux hs)
    rw [e1, h2]
    field_simp <;> ring_nf
  have hBle : (∫ σ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w s) ^ 2
      ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ := by
    rw [hBeq]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 s hsI) ?_
    · filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)) _)
    · filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
      exact hpoint2 σ hσ
  have hGle : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
      ≤ 100 / (Work.Spaces.gam α - 1) := Work.Spaces.integral_sin_rpow α hα hα1
  have hHnn : 0 ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ :=
    MeasureTheory.integral_nonneg fun σ => Work.Spaces.HkIntegrand_nonneg α m f s σ
  have h3 : (0 : ℝ) ≤ 8 / Real.pi := by positivity
  have h4 : (0 : ℝ) ≤ 2 * (∫ σ in Work.Spaces.Iθ,
      (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2)) := by
    refine mul_nonneg (by norm_num) ?_
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    exact Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)) _
  have h5 : 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
      ≤ 200 / (Work.Spaces.gam α - 1) := by
    have h5a : 2 * (100 / (Work.Spaces.gam α - 1)) = 200 / (Work.Spaces.gam α - 1) := by
      field_simp <;> norm_num
    linarith
  -- assembly
  calc (Work.Spaces.mixed b a f s θ * Work.Spaces.w s) ^ 2
      = (Work.Spaces.mixed b a f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 := by ring
    _ ≤ ((8 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2)
          + 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
            * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
              * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)))
        * (Work.Spaces.w s) ^ 2 := mul_le_mul_of_nonneg_right hang (sq_nonneg _)
    _ = (8 / Real.pi) * ((∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2)
            * (Work.Spaces.w s) ^ 2)
        + 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
            * ((∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
                * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w s) ^ 2) := by
      ring
    _ ≤ (8 / Real.pi) * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ)
        + 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
            * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ) :=
      add_le_add (mul_le_mul_of_nonneg_left hAle h3) (mul_le_mul_of_nonneg_left hBle h4)
    _ ≤ (8 / Real.pi + 200 / (Work.Spaces.gam α - 1))
          * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ) := by
      have h6 := mul_le_mul_of_nonneg_right h5 hHnn
      have h7 : (8 / Real.pi) * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ)
            + (200 / (Work.Spaces.gam α - 1))
              * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ)
          = (8 / Real.pi + 200 / (Work.Spaces.gam α - 1))
              * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f s σ) := by
        ring
      linarith [h6, h7]

end Work.FTS.EpsEngine.ZTracesAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.EllPkgCls_E_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongEps.EComparison

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The closure instantiated at the `E`-difference.** -/
theorem EllPkgCls_E_sub_of_theta {α Ce : ℝ} {E : Fn → Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {u v : Fn} (hu : Work.FTS.ClassC.ClassC α u) (hv : Work.FTS.ClassC.ClassC α v)
    (hΘ : ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      Work.Construction.Theta α (fun z θ => u z θ - v z θ) z θ
        = Work.Construction.Theta α u z θ - Work.Construction.Theta α v z θ) :
    EllPkgCls α Ce (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ) :=
  EllPkgCls_sub (EllPkgCls_of_pkg hEll hu) (EllPkgCls_of_pkg hEll hv) hΘ

end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.RsumClassC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

/-- **The `ℋ⁴`-honesty and the sharp (linear-in-the-difference) `ℋ⁴`-bound for the nine
telescoped pieces of the `N₀`-difference, on the class `ClassC`.**

With `h := fun z θ => W₁ z θ - W₂ z θ`, `HkMem α 4 (Rsum α W₁ W₂ h)` holds and
`Xn α (Rsum α W₁ W₂ h) ≤ K·(1 + Xn5 α W₁ + Xn5 α W₂)·Xn5 α h` with a constant `K` that may
depend on `α` (it does: the pieces carry `α^{-1}`, `α^{-1/2}` and `α^{+1}` factors) but not on
`W₁, W₂`.

Route. `Rsum α W₁ W₂ h = P1 + (P2 + (P3 + (P4 + (P5 + (P6 + (P7 + (P8 + P9)))))))`
(`Work.FTS.GalFields.RHS`, `sharpN0_defs.lean`), with, writing `𝓛X := fun z _ => L₁₂ X z`,
`Dth := Work.Spaces.Dth`, `Dz := Work.Spaces.Dz`, `c2m := Work.Construction.c2m`:
`P1 = (1/α)·(𝓛W₁·h)`, `P2 = (1/α)·(𝓛h·W₂)`, `P3 = (3/2α)·(Dth F_* · 𝓛h)`,
`P4 = (3/2α)·(𝓛W₁·Dth h)`, `P5 = (3/2α)·(𝓛h·Dth W₂)`, `P6 = -c2m·(Dz F_* · 𝓛h)`,
`P7 = -c2m·(𝓛W₁·Dz h)`, `P8 = -c2m·(𝓛h·Dz W₂)`, `P9 = -(c2m·𝓛F_*)·Dz h`.

Available universal (package-free) tools:
* `Work.FTS.OpenPkg.prod_field`: for `HQo α 4 f`, `HQo α 4 g` (i.e. `SmoothOpen` + `HkMem α 4`),
  `HkMem α 4 (f·g)` and `Xn α (f·g) ≤ C·α^(-1/2)·Xn α f · Xn α g`;
* `Work.FTS.OpenPkg.wprod_field_winf`: for `SmoothOpen f` with `WlInfMem α 4 f` and `HQo α 4 g`,
  `HkMem α 4 (f·g)` and `Xn α (f·g) ≤ C·α^(-1/2)·WlInf α 4 f·Xn α g`;
* `Work.FTS.OpenPkg.angmul_field`: for an angular factor `a` with `|a θ| ≤ Ca` and the `DthIter`
  bounds `≤ Ca·sin 2θ` on `Iθ` (both hold for `a = c2m` with `Ca = 1000`, see
  `abs_c2m_le_thousand`, `DthIter_c2m_le_sin`), `HkMem α 4 (a·f)` and `Xn α (a·f) ≤ C·Ca·Xn α f`;
* `Work.FTS.OpenPkg.l12H_field`: `HQo α 4 g` and `L₁₂ g 0 = 0` give `HkMem α 4 𝓛g` and
  `Xn α 𝓛g ≤ C·Xn α g`;
* `Work.FTS.GalFields.RHS.c2m_mul_HkSq_le` (with `HkSq α 4` monotonicity) for multiplying by
  `c2m` inside a product;
* the fixed-profile atoms: `Work.FTS.GalFields.RHS.CFdef_spec` (`Dth F_*`: `WlInfMem α 4`,
  `WlInf ≤ CF·α²`), `Cdzdef_spec` (`Dz F_*`: `WlInf ≤ Cdz·α`), `Cwdef_spec`
  (`c2m·𝓛F_*`: `WlInf ≤ Cw·α`), plus `smoothOpen_c2m_ang`, `Work.FTS.StrongPersist.H6Pair6Aux`
  for the smoothness of the `F_*`-atoms.

Derived facts to obtain from `ClassC α W` (`hW : ClassC α W`):
`hW.reg : SmoothOpen W`, `hW.mem` (`HkMem α 7`, hence `HkMem α k` for `k ≤ 7` via
`HkMem_mono_open hW.reg`), `hW.l12 : L₁₂ W 0 = 0`,
`Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_aux hα hW : SmoothOpen 𝓛W`, and the
monotonicity `Xn α W ≤ Xn5 α W` (`Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4)`,
needs `HkMem α 5 W`), `Xn α (Dth W) ≤ Xn5 α W` (`Work.FTS.GalFields.Xn_Dth_le_Xn5`),
`Xn α (Dz W) ≤ Xn5 α W` (`Work.FTS.GalFields.Xn_Dz_le_Xn5`, needs `SmoothOpen`).

For the difference `h` itself: `SmoothOpen h` is `Work.FTS.EllipticEst.smoothOpen_sub`;
`HkMem α k h` comes from `HkMem_add_open` + `Work.FTS.StrongEps.ClassCRHS.mem_neg` +
`Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0` (pointwise `W₁ - W₂ = W₁ + (-W₂)` on `Qd`);
`L₁₂ h 0 = 0` and the *identities* `𝓛h = 𝓛W₁ - 𝓛W₂` (for `z ≥ 0`) come from
`Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen`, from which `SmoothOpen 𝓛h`, `HkMem α 4 𝓛h`
and `Xn α 𝓛h ≤ C·Xn α h ≤ C·Xn5 α h` follow (the last by `l12H_field` applied to `h`).

Every piece bound must end in a factor `Xn5 α h`, and the remaining factors are
`1`, `Xn5 α W₁`, `Xn5 α W₂`; assemble the nine bounds with
`Work.FTS.GalFields.RHS.HkNorm_finset_sum_le` (or `HkNorm_add_le_open`). -/
theorem RsumClassC {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
        (fun z θ => W₁ z θ - W₂ z θ)) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
        (fun z θ => W₁ z θ - W₂ z θ))
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  -- ## the universal constants of the three product rules
  obtain ⟨Cp, hCp, hprod0⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨Cw, hCw, hwprod0⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨C1, hC1, hl120⟩ := Work.FTS.OpenPkg.l12H_field
  -- the single constant dominating all three
  set Ci : ℝ := max Cp (max Cw (max C1 1)) with hCidef
  have hCp_le : Cp ≤ Ci := by rw [hCidef]; exact le_max_left _ _
  have hCw_le : Cw ≤ Ci := by
    rw [hCidef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hC1_le : C1 ≤ Ci := by
    rw [hCidef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have h1_le : (1 : ℝ) ≤ Ci := by
    rw [hCidef]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCi : 0 < Ci := lt_of_lt_of_le one_pos h1_le
  -- ## the two product rules, weakened to the single constant `Ci`
  have hprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g := by
    intro f g hf hg
    obtain ⟨hm, hb⟩ := hprod0 α hα hα1 f g hf hg
    refine ⟨hm, le_trans hb ?_⟩
    have hA : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have h0f : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    have h0g : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCp_le hA) h0f) h0g
  have hwprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g := by
    intro f g hf hfm hg
    obtain ⟨hm, hb⟩ := hwprod0 α hα hα1 f g hf hfm hg
    refine ⟨hm, le_trans hb ?_⟩
    have hA : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have h0g : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCw_le hA)
        (Work.FTS.H2.WPQ.WlInf_nonneg' hfm)) h0g
  have hl12 : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 4 g →
      Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
        ≤ Ci * Work.FTS.Nonlin.Xn α g := by
    intro g hg h0
    obtain ⟨hm, hb⟩ := hl120 α hα hα1 g hg h0
    refine ⟨hm, le_trans hb ?_⟩
    exact mul_le_mul_of_nonneg_right hC1_le (Work.Spaces.HkNorm_nonneg α 4 g)
  refine ⟨1024 * Work.FTS.GalFields.RHS.ksum α Ci Work.FTS.GalFields.RHS.CFdef
      Work.FTS.GalFields.RHS.Cdzdef Work.FTS.GalFields.RHS.Cwdef, ?_, ?_⟩
  · -- ## positivity of the constant
    have hksum : 0 < Work.FTS.GalFields.RHS.ksum α Ci Work.FTS.GalFields.RHS.CFdef
        Work.FTS.GalFields.RHS.Cdzdef Work.FTS.GalFields.RHS.Cwdef := by
      refine lt_of_lt_of_le ?_ (Work.FTS.GalFields.RHS.kA1_le_ksum hα hCi
        Work.FTS.GalFields.RHS.CFdef_pos Work.FTS.GalFields.RHS.Cdzdef_pos
        Work.FTS.GalFields.RHS.Cwdef_pos)
      rw [Work.FTS.GalFields.RHS.kA1]
      exact mul_pos (mul_pos (mul_pos (by positivity) hCi)
        (Real.rpow_pos_of_pos hα (-(1 / 2 : ℝ)))) hCi
    positivity
  · -- ## the estimate
    intro W₁ W₂ hW₁ hW₂
    let h : ℝ → ℝ → ℝ := fun z θ => W₁ z θ - W₂ z θ
    have hD := ClassCDiffData (α := α) hα hα1 hW₁ hW₂
    have hm4₁ : Work.Spaces.HkMem α 4 W₁ :=
      Work.FTS.OpenPkg.HkMem_mono_open hW₁.reg 4 (by norm_num) hW₁.mem
    have hm4₂ : Work.Spaces.HkMem α 4 W₂ :=
      Work.FTS.OpenPkg.HkMem_mono_open hW₂.reg 4 (by norm_num) hW₂.mem
    have hm4h : Work.Spaces.HkMem α 4 h :=
      Work.FTS.OpenPkg.HkMem_mono_open hD.hsm 4 (by norm_num) hD.hmem
    have hL1 := hl12 W₁ ⟨hW₁.reg, hm4₁⟩ hW₁.l12
    have hLh := hl12 h ⟨hD.hsm, hm4h⟩ hD.hLh0
    have hLhXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
        ≤ Ci * Work.FTS.GalFields.Xn5 α h :=
      le_trans hLh.2 (mul_le_mul_of_nonneg_left hD.hXh hCi.le)
    have hA := PiecesAClassC (α := α) (Ci := Ci) (g := W₁) (g' := W₂) (h := h)
      hα hα1 hCi hprod hwprod
      hW₁.reg hW₂.reg hD.hsm hm4₂ hm4h
      hD.hLW₁Sm hD.hLhSm hL1.1 hLh.1 hL1.2 hLhXn
      hD.hXW₁ hD.hXh hD.hXW₂
      hD.hDthSm hD.hDthMem hD.hDthXn
      hD.hDthW₂Sm hD.hDthW₂Mem hD.hDthW₂Xn
      Work.FTS.GalFields.RHS.CFdef Work.FTS.GalFields.RHS.CFdef_pos
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dth
      (Work.FTS.GalFields.RHS.CFdef_spec.2 α hα hα1)
      (Work.Spaces.HkNorm_nonneg α 5 h)
    have hB := PiecesBClassCRow (α := α) (Ci := Ci) (g := W₁) (g' := W₂) (h := h)
      hα hα1 hCi hprod hwprod
      hD.hLW₁Sm hD.hLhSm hL1.1 hLh.1 hL1.2 hLhXn
      hD.hXW₁ hD.hXW₂
      hD.hDzSm hD.hDzMem hD.hDzXn
      hD.hDzW₂Sm hD.hDzW₂Mem hD.hDzW₂Xn
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α)
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dz
      Work.FTS.GalFields.RHS.smoothOpen_c2m_ang
      Work.FTS.GalFields.RHS.Cdzdef Work.FTS.GalFields.RHS.Cwdef
      Work.FTS.GalFields.RHS.Cdzdef_pos Work.FTS.GalFields.RHS.Cwdef_pos
      (Work.FTS.GalFields.RHS.Cdzdef_spec.2 α hα hα1)
      (Work.FTS.GalFields.RHS.Cwdef_spec.2 α hα hα1)
      (Work.Spaces.HkNorm_nonneg α 5 h)
    obtain ⟨A1, A2, A3, A4, A5, sA1, sA2, sA3, sA4, sA5⟩ := hA
    obtain ⟨B6, B7, B8, B9, sB6, sB7, sB8, sB9⟩ := hB
    have hsum := Work.FTS.GalFields.RHS.sharpN0_sums (α := α) (Ci := Ci)
      (g := W₁) (g' := W₂) (h := h) hα hCi
      Work.FTS.GalFields.RHS.CFdef Work.FTS.GalFields.RHS.Cdzdef Work.FTS.GalFields.RHS.Cwdef
      Work.FTS.GalFields.RHS.CFdef_pos Work.FTS.GalFields.RHS.Cdzdef_pos
      Work.FTS.GalFields.RHS.Cwdef_pos
      A1 A2 A3 A4 A5 B6 B7 B8 B9 sA1 sA2 sA3 sA4 sA5 sB6 sB7 sB8 sB9
    refine ⟨hsum.1, ?_⟩
    have hTOF : Work.FTS.GalFields.RHS.TOf α W₁ W₂ h
        = (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := rfl
    have heq : 1024 * Work.FTS.GalFields.RHS.ksum α Ci Work.FTS.GalFields.RHS.CFdef
          Work.FTS.GalFields.RHS.Cdzdef Work.FTS.GalFields.RHS.Cwdef
          * Work.FTS.GalFields.RHS.TOf α W₁ W₂ h
        = 1024 * Work.FTS.GalFields.RHS.ksum α Ci Work.FTS.GalFields.RHS.CFdef
          Work.FTS.GalFields.RHS.Cdzdef Work.FTS.GalFields.RHS.Cwdef
          * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
      rw [hTOF]; ring
    exact le_trans hsum.2.2 (le_of_eq heq)

end Work.FTS.StrongEps.EpsRLX
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.mixed_abs_le_weighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1

/-!
# `mixed_abs_le_weighted` — the *weighted* interior `L^∞`–`ℋ⁴` trade-off

For every `0 < α ≤ 1` there is a constant `C = C(α) ≥ 0` such that every datum `f` which is
`C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)`, honestly in the weighted space `ℋ⁴`
(`Work.Spaces.HkMem α 4 f`) and satisfying the boundary traces `BdryTraces α 4 f`, obeys the
*weighted* pointwise bound

  `|D_z^b D_θ^a f (z,θ)| ≤ C · z^{3/2}/(1+z)² · |f|_{ℋ⁴}`   for `a + b ≤ 2`, `z > 0`, `0 < θ < π/2`.

This is the `z^{3/2}/(1+z)²`-weighted refinement of the interior trade-off
`Work.FTS.StrongEps.SupPort.mixed_abs_le_of_smoothOpen` (`|D_z^bD_θ^a f| ≤ 10/√(γ-1)·|f|_{ℋ⁴}`,
a *constant* bound); the weight encodes the sharp radial behaviour of an `ℋ⁴` datum: it vanishes
like `z^{3/2}` as `z → 0⁺` (the borderline rate forced by the `(1+z)²/z²` weight in the `D_z`-slots
of the norm) and decays like `z^{-1/2}` as `z → ∞`.  The constant bound alone does **not** imply
the weighted one, because `z^{3/2}/(1+z)²` is unbounded below.

The mathematical content is the chain (weighted radial Agmon inequality `agmonZ_weight` applied to
the angular slice, the angular Hardy inequality at fixed `z`, and Tonelli for the `ℋ⁴`-integrand),
which is carried out in `Submission/Work/FTS_RegExport/RXA1w/` for the *weaker* regularity
hypothesis `ContDiffOn ℝ 4 (uncurry f) Q0`:

* `Work.FTS_RegExport.RXA1w.agmonZ_weight` — `(v z)² w(z)² z ≤ 4∫(v w)² + ∫(x v' w)²`,
* `Work.FTS_RegExport.RXA1w.mixed_slice_pointwise_le` — the a.e. slice bound with constant `5`,
* `Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved` — the `C⁴` form of the present
  statement, with the explicit constant `√(500/(γ-1))`.

Since `SmoothOpen f` (all finite orders) implies the `C⁴` hypothesis on `Q0`
(`Work.FTS.EllipticEst.smoothOpen_iff_forall`), the statement below follows from the `C⁴` form
with the same constant.  `Work.FTS.Galerkin.Fn` is an `abbrev` for `ℝ → ℝ → ℝ`, so the two
statements live on the same type.
-/

/-- **The weighted interior `L^∞`–`ℋ⁴` trade-off.**  For `0 < α ≤ 1` there is `C ≥ 0` such that
every `C^∞`-on-the-open-quadrant, `ℋ⁴`-honest datum `f` with the boundary traces `BdryTraces α 4 f`
satisfies `|D_z^b D_θ^a f (z,θ)| ≤ C · z^{3/2}/(1+z)² · |f|_{ℋ⁴}` for all `a + b ≤ 2` and all
interior points `(z,θ) ∈ Q0`. -/
theorem mixed_abs_le_weighted {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.Nonlin.BdryTraces α 4 f →
      ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a f z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * Work.Spaces.HkNorm α 4 f := by
  -- the `C⁴`-form of the statement, with the explicit constant `√(500/(γ-1))`
  obtain ⟨C, hC0, hC⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hα hα1
  refine ⟨C, hC0, fun f hF hmem hbd b a hab z θ hz hθ0 hθ1 => ?_⟩
  -- `SmoothOpen f` gives `ContDiffOn ℝ 4 (uncurry f) Q0`, the regularity of the `C⁴`-form
  exact hC f ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hF 4) hmem hbd b a hab z θ
    hz hθ0 hθ1

end Work.FTS_RegExport.RXR1
end
