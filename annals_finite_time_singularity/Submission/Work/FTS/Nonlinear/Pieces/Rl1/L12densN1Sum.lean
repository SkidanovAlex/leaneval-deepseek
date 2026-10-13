/-
# `L12densN1Sum` — the four-way split of `N₁` at the level of the `L₁₂`-density

`Work.FTS.Nonlinear.Pieces.Rl1.n1Bound` estimates the density integral of the first group
`I^N_1 = N₁ = 2ℛ(Φ̃)F` of the nonlinearity `N` by splitting it into the four pieces
`N₁^{gg}, N₁^{gs}, N₁^{sg}, N₁^{ss}` of the design table.  This file supplies the
*pointwise-in-`s`* half of that step, which is independent of any estimate:

  `‖L₁₂dens (N₁)(s)‖ ≤ ‖L₁₂dens (N₁^{gg})(s)‖ + … + ‖L₁₂dens (N₁^{ss})(s)‖`  for `s > 0`,

under the frozen context of the row (`N4Norm`, `GalClass`, `StarPkg`, `EllPkgG`, `0 < α ≤ 1`).

**Route.**  `N₁ = Σ N₁^{xy}` holds *pointwise on the open quadrant* (`N1_split`), because

* `ℛ` is linear in the triple `(Ψ, ∂_zΨ, ∂_θΨ)` (the `N₁`-analogue of `N2_split`/`n3split`),
  and
* the straightened stream functions add: `Φ̃(F_*+g, Φ_s+Φ_g) = Φ̃_* + Φ̃_g`, which is the
  additivity `L₁₂(F_*+g) = L₁₂(F_*) + L₁₂(g)` of `L12FK_add_ge0` together with the
  differentiability of `z ↦ L₁₂(g)(z)` supplied by `N4Norm.l12diff`.

Since `(0, π/2)` and `Iθ = [0,π/2]` differ by the null set `{0, π/2}`, the identity holds a.e.
for the `θ`-integration at each `s > 0`, so `L₁₂dens (N₁)(s) = L₁₂dens (Σ N₁^{xy})(s)` by
`MeasureTheory.integral_congr_ae`; and `L₁₂dens (Σ N₁^{xy})(s) = Σ L₁₂dens (N₁^{xy})(s)` by
`MeasureTheory.integral_add`, for which the four integrability certificates are produced from
`SmoothQuad` (a.e. strong measurability of the slice) together with the *pointwise* bounds on
the open quadrant that the packages already provide:

* `|ℛ(Φ̃_g)| ≤ 10√(10/α)·max Ce 0·X` (`gPt`), `|ℛ(Φ̃_*)| ≤ max Cs 0·α` (`starPt`),
* `|g| ≤ 10√(10/α)·X` (`abs_le_ten_sqrt_gam`), `|F_*| ≤ C·α` (`Fstar_pointwise`).

The final step is the triangle inequality for `‖·‖` on `ℝ`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.Nonlinear.Pieces.L12FK_add_ge0
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gPt
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.starPt
import Submission.Work.FTS.Nonlinear.Pieces.RNP.Fstar_pointwise
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row10aux.Rop_PhiTs_smoothQuad
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Elliptic.L12densFacts

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

open Work.FTS.Galerkin (Fn)

/-! ## The `N₁`-analogue of `N2_split` / `n3split` -/

/-- **The four-way split of `N₁` on the open quadrant.**  `N₁ = 2ℛ(Φ̃(F,Φ))F` with
`F = F_* + g` and `Φ̃ = Φ̃_* + Φ̃_g`, so that `ℛ` (linear in `(Ψ, ∂_zΨ, ∂_θΨ)`) and `F` split
into the four pieces `N₁^{gg} + N₁^{gs} + N₁^{sg} + N₁^{ss}` of `Work.FTS.Nonlin.Defs`. -/
theorem N1_split {α : ℝ} {g Φs Φg : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hreg : Work.FTS.LocData.SmoothQuad g) (hΦs : Work.FTS.LocData.SmoothQuad Φs)
    (hΦg : Work.FTS.LocData.SmoothQuad Φg)
    (hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α g) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z)
    (hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N1 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
        = Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
          + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ := by
  intro z θ hq
  have hz : 0 < z := hq.1
  have hzI : z ∈ Set.Ioi (-1 : ℝ) := by rw [Set.mem_Ioi]; linarith
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hq.2
  have hF : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.Fstar_smoothQuad α
  have hs2 : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    have h : Work.Construction.s2 = fun θ' : ℝ => Real.sin (2 * θ') := rfl
    rw [h]
    exact Real.differentiableAt_sin.comp θ
      ((differentiableAt_const (2 : ℝ)).mul differentiableAt_id)
  have hPsi1 : Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs
      = fun z' θ' => Φs z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 (Work.Construction.Fstar α) z' := rfl
  have hPsi2 : Work.Construction.PhiTil α g Φg
      = fun z' θ' => Φg z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 g z' := rfl
  -- the `θ`-slices of the two straightened stream functions are differentiable
  have hts1 : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ') θ := by
    rw [hPsi1]
    exact (Work.FTS.Nonlinear.Pieces.differentiableAt_slice_θ hΦs hzI hθ).sub
      (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2).mul (differentiableAt_const _))
  have hts2 : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil α g Φg z θ') θ := by
    rw [hPsi2]
    exact (Work.FTS.Nonlinear.Pieces.differentiableAt_slice_θ hΦg hzI hθ).sub
      (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2).mul (differentiableAt_const _))
  -- the `θ`-slice at `z` of `Φ̃(F_tot, Φs + Φg)` is the sum of the two pieces
  have hsliceθ : (fun θ' => Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ')
      = (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ'
          + Work.Construction.PhiTil α g Φg z θ') := by
    funext θ'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL z hz]
    ring
  have hval : Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
        + Work.Construction.PhiTil α g Φg z θ := congrFun hsliceθ θ
  have hpthP : Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ := by
    have hderiv := congrArg (fun F : ℝ → ℝ => deriv F θ) hsliceθ
    have hsum : Work.Spaces.pth (fun z θ => Work.Construction.PhiTil α
          (Work.Construction.Fstar α) Φs z θ + Work.Construction.PhiTil α g Φg z θ) z θ
        = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ :=
      Work.FTS.Nonlinear.Pieces.pth_add_of_diff hts1 hts2
    simp only [Work.Spaces.pth] at hsum hderiv ⊢
    exact hderiv.trans hsum
  -- the `z`-slices of the two pieces
  have hzs1 : DifferentiableAt ℝ
      (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ) z := by
    rw [hPsi1]
    exact (Work.FTS.Nonlinear.Pieces.differentiableAt_slice_z hΦs hzI hθ).sub
      ((differentiableAt_const (((1 : ℝ) / (4 * α)) * Work.Construction.s2 θ)).mul
        (Work.FTS.Nonlinear.Pieces.differentiableAt_L12_Fstar hα hα1 hz))
  have hzs2 : DifferentiableAt ℝ
      (fun z' => Work.Construction.PhiTil α g Φg z' θ) z := by
    rw [hPsi2]
    exact (Work.FTS.Nonlinear.Pieces.differentiableAt_slice_z hΦg hzI hθ).sub
      ((differentiableAt_const (((1 : ℝ) / (4 * α)) * Work.Construction.s2 θ)).mul
        (hL12 z hz))
  have hslicez : (fun z' => Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ
          + Work.Construction.PhiTil α g Φg z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL z' hz']
    ring
  have hpzP : Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Spaces.pz (Work.Construction.PhiTil α g Φg) z θ := by
    have hderiv := hslicez.deriv_eq
    have hsum : Work.Spaces.pz (fun z θ => Work.Construction.PhiTil α
          (Work.Construction.Fstar α) Φs z θ + Work.Construction.PhiTil α g Φg z θ) z θ
        = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Spaces.pz (Work.Construction.PhiTil α g Φg) z θ :=
      Work.FTS.Nonlinear.Pieces.pz_add_of_diff hzs1 hzs2
    simp only [Work.Spaces.pz] at hsum hderiv ⊢
    exact hderiv.trans hsum
  -- additivity of `ℛ`
  have hRop : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
        + Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ := by
    simp only [Work.Construction.Rop, Work.FTS.Nonlin.PhiTg, Work.FTS.Nonlin.PhiTs]
    rw [hval, hpzP, hpthP]
    ring
  simp only [Work.Construction.N1, Work.FTS.Nonlin.N1gg, Work.FTS.Nonlin.N1gs,
    Work.FTS.Nonlin.N1sg, Work.FTS.Nonlin.N1ss, Work.Construction.Ftot]
  rw [hRop]
  ring

/-! ## Slices: a.e. strong measurability and integrability of `K·f(s,·)/s` -/

/-- `SmoothQuad` data are continuous on the open quadrant `(0,∞) × (0,π/2)`. -/
theorem continuousOn_uncurry_of_smoothQuad {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have h := hsm
  rw [Work.FTS.LocData.SmoothQuad] at h
  refine h.continuousOn.mono (fun p hp => ⟨?_, hp.2⟩)
  exact Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0) hp.1

/-- The angular slice `θ ↦ f(s,θ)` of a `SmoothQuad` datum is a.e. strongly measurable on
`Iθ` for `s > 0`. -/
theorem aesm_slice_of_smoothQuad {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    {s : ℝ} (hs : 0 < s) :
    MeasureTheory.AEStronglyMeasurable (fun θ => f s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  simpa only [Function.uncurry] using
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry f)
      (continuousOn_uncurry_of_smoothQuad hsm) hs

/-- **A bounded, a.e. strongly measurable slice has integrable `K·f(s,·)/s`.**  The kernel
`K(θ) = 3 sinθcos²θ` satisfies `0 ≤ K ≤ 3` on `Iθ`, so the integrand is dominated by the
constant `3C/s`; the measure `volume.restrict Iθ` is finite. -/
theorem integrableOn_K_mul_of_aesm_bound {f : ℝ → ℝ} {C s : ℝ} (hs : 0 < s) (hC : 0 ≤ C)
    (haesm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), ‖f θ‖ ≤ C) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * f θ / s) Work.Spaces.Iθ := by
  have hKcont : Continuous (fun θ : ℝ => Work.Spaces.K θ) := by
    unfold Work.Spaces.K; fun_prop
  have haesm2 : MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.K θ * f θ / s) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun θ => Work.Spaces.K θ * f θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hKcont.aestronglyMeasurable.mul haesm
    exact (h2.mul_const (1 / s)).congr (Eventually.of_forall (fun θ => by
      simp only [div_eq_mul_inv, one_mul]))
  have hmaj : MeasureTheory.Integrable (fun _ : ℝ => 3 * C / s)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; simp)
  refine hmaj.mono' haesm2 ?_
  filter_upwards [hbound, MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hb hmem
  have hθ : θ ∈ Work.Spaces.Iθ := hmem
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hK0 : 0 ≤ Work.Spaces.K θ := by rw [Work.Spaces.K]; positivity
  have hK3 : Work.Spaces.K θ ≤ 3 := by
    rw [Work.Spaces.K]
    have hc2 : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
    nlinarith [hs0, Real.sin_le_one θ]
  have hf : |f θ| ≤ C := by simpa only [Real.norm_eq_abs] using hb
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hK0, abs_of_pos hs]
  have hnum : Work.Spaces.K θ * |f θ| ≤ 3 * C := by nlinarith
  exact div_le_div_of_nonneg_right hnum hs.le

/-- **The integrability certificate used for the four pieces**: a `SmoothQuad` function whose
`θ`-slice at `s` is bounded on the open interval by `C` gives an integrable `K·f(s,·)/s`. -/
theorem integrableOn_K_mul_of_smoothQuad_bound {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) {C s : ℝ} (hs : 0 < s) (hC : 0 ≤ C)
    (hbound : ∀ θ, 0 < θ → θ < π / 2 → ‖f s θ‖ ≤ C) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ :=
  integrableOn_K_mul_of_aesm_bound hs hC (aesm_slice_of_smoothQuad hsm hs)
    (Work.Elliptic.ae_restrict_Iθ_of_Ioo hbound)

/-! ## The target -/

theorem L12densN1Sum {α₂ Ci Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      ∀ s : ℝ, 0 < s →
      ‖Work.Construction.L12dens (Work.Construction.N1 α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) s‖
        ≤ ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1gg α g Φg) s‖
          + ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1gs α g Φg) s‖
          + ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1sg α Φs g) s‖
          + ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1ss α Φs) s‖ := by
  intro α g Φs Φg hgal hstar hell hα hα1 hαα₂ s hs
  have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  -- the `ℋ⁴`/differentiability inputs
  have hsqG : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem4G : Work.Spaces.HkMem α 4 g :=
    (Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num)).2.1
  have hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α g) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z :=
    fun z hz => (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 hα hα1 hgal).1 z hz.le
  have hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z :=
    fun z hz => hN.l12diff α hαIoc g hsqG hmem4G z hz
  -- the pointwise split
  have hsplit := N1_split hα hα1 hsqG hstar.smooth hell.smooth hL hL12
  -- the four pointwise bounds provided by the packages
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hsq10 : 0 ≤ Real.sqrt (10 / α) := Real.sqrt_nonneg _
  have hmaxCe : 0 ≤ max Ce 0 := le_max_right _ _
  have hmaxCs : 0 ≤ max Cs 0 := le_max_right _ _
  have hA0 : 0 ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsq10) hmaxCe) hX0
  have hB0 : 0 ≤ 10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g :=
    mul_nonneg (mul_nonneg (by norm_num) hsq10) hX0
  have hS0 : 0 ≤ max Cs 0 * α := mul_nonneg hmaxCs hα.le
  have hRtg : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
        ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g :=
    (Work.FTS.Nonlinear.Pieces.rl1Tools.gPt hα hα1 hell).1
  have hRs : ∀ z, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ max Cs 0 * α :=
    (Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hstar).1
  have hgb : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      |g z θ| ≤ 10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g := by
    intro z hz θ h0 h1
    have h := Work.FTS.Nonlinear.Pieces.rl1Tools.abs_le_ten_sqrt_gam hα hα1
      (Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num : 4 ≤ 6)) z hz θ h0 h1
    rw [Work.FTS.Nonlinear.Pieces.rl1Tools.ten_div_sqrt_gam hα] at h
    exact h
  obtain ⟨Cfs, hCfs, hFstarAll⟩ := Work.FTS.Nonlinear.Pieces.RNP.Fstar_pointwise
  have hCfsα : 0 ≤ Cfs * α := mul_nonneg hCfs.le hα.le
  have hFb : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      |Work.Construction.Fstar α z θ| ≤ Cfs * α := by
    intro z hz θ h0 h1
    have h := (hFstarAll α hα hα1).1 z hz θ ⟨h0, h1⟩
    have hsmall : z / (1 + z) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    have h' : |Work.Construction.Fstar α z θ| ≤ Cfs * α * (z / (1 + z) ^ 2) := by
      rw [← mul_div_assoc]; exact h
    calc |Work.Construction.Fstar α z θ| ≤ Cfs * α * (z / (1 + z) ^ 2) := h'
      _ ≤ Cfs * α * 1 := mul_le_mul_of_nonneg_left hsmall hCfsα
      _ = Cfs * α := by ring
  -- the four bound constants
  have hC1 : 0 ≤ 2 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
      * (10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g) :=
    mul_nonneg (mul_nonneg (by norm_num) hA0) hB0
  have hC2 : 0 ≤ 2 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
      * (Cfs * α) := mul_nonneg (mul_nonneg (by norm_num) hA0) hCfsα
  have hC3 : 0 ≤ 2 * (max Cs 0 * α) * (10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g) :=
    mul_nonneg (mul_nonneg (by norm_num) hS0) hB0
  have hC4 : 0 ≤ 2 * (max Cs 0 * α) * (Cfs * α) :=
    mul_nonneg (mul_nonneg (by norm_num) hS0) hCfsα
  -- the four pointwise bounds on the open interval
  have hb1 : ∀ θ, 0 < θ → θ < π / 2 →
      ‖Work.FTS.Nonlin.N1gg α g Φg s θ‖
        ≤ 2 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
          * (10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g) := by
    intro θ h0 h1
    have hR := hRtg s hs θ h0 h1
    have hg := hgb s hs θ h0 h1
    rw [Real.norm_eq_abs]
    have habs : |Work.FTS.Nonlin.N1gg α g Φg s θ|
        = 2 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) s θ| * |g s θ| := by
      simp only [Work.FTS.Nonlin.N1gg, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [habs]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hR (by norm_num)) hg (abs_nonneg _)
      (mul_nonneg (by norm_num) hA0)
  have hb2 : ∀ θ, 0 < θ → θ < π / 2 →
      ‖Work.FTS.Nonlin.N1gs α g Φg s θ‖
        ≤ 2 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) * (Cfs * α) := by
    intro θ h0 h1
    have hR := hRtg s hs θ h0 h1
    have hF := hFb s hs θ h0 h1
    rw [Real.norm_eq_abs]
    have habs : |Work.FTS.Nonlin.N1gs α g Φg s θ|
        = 2 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) s θ|
          * |Work.Construction.Fstar α s θ| := by
      simp only [Work.FTS.Nonlin.N1gs, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [habs]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hR (by norm_num)) hF (abs_nonneg _)
      (mul_nonneg (by norm_num) hA0)
  have hb3 : ∀ θ, 0 < θ → θ < π / 2 →
      ‖Work.FTS.Nonlin.N1sg α Φs g s θ‖
        ≤ 2 * (max Cs 0 * α) * (10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g) := by
    intro θ h0 h1
    have hR := hRs s hs θ ⟨h0.le, h1.le⟩
    have hg := hgb s hs θ h0 h1
    rw [Real.norm_eq_abs]
    have habs : |Work.FTS.Nonlin.N1sg α Φs g s θ|
        = 2 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) s θ| * |g s θ| := by
      simp only [Work.FTS.Nonlin.N1sg, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [habs]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hR (by norm_num)) hg (abs_nonneg _)
      (mul_nonneg (by norm_num) hS0)
  have hb4 : ∀ θ, 0 < θ → θ < π / 2 →
      ‖Work.FTS.Nonlin.N1ss α Φs s θ‖ ≤ 2 * (max Cs 0 * α) * (Cfs * α) := by
    intro θ h0 h1
    have hR := hRs s hs θ ⟨h0.le, h1.le⟩
    have hF := hFb s hs θ h0 h1
    rw [Real.norm_eq_abs]
    have habs : |Work.FTS.Nonlin.N1ss α Φs s θ|
        = 2 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) s θ|
          * |Work.Construction.Fstar α s θ| := by
      simp only [Work.FTS.Nonlin.N1ss, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [habs]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hR (by norm_num)) hF (abs_nonneg _)
      (mul_nonneg (by norm_num) hS0)
  -- smoothness of the four pieces
  have hRopG : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) := by
    simpa only [Work.FTS.Nonlin.PhiTg] using hell.R.1.1
  have hRopS : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.Nonlinear.Pieces.RNP.row10aux.Rop_PhiTs_smoothQuad hα hα1 hstar.smooth
  have hsm1 : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.N1gg α g Φg) :=
    Work.FTS.LocData.smoothQuad_mul
      (Work.FTS.LocData.smoothQuad_const_mul 2 hRopG) hsqG
  have hsm2 : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.N1gs α g Φg) :=
    Work.FTS.LocData.smoothQuad_mul
      (Work.FTS.LocData.smoothQuad_const_mul 2 hRopG)
      (Work.FTS.LocData.Fstar_smoothQuad α)
  have hsm3 : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.N1sg α Φs g) :=
    Work.FTS.LocData.smoothQuad_mul
      (Work.FTS.LocData.smoothQuad_const_mul 2 hRopS) hsqG
  have hsm4 : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.N1ss α Φs) :=
    Work.FTS.LocData.smoothQuad_mul
      (Work.FTS.LocData.smoothQuad_const_mul 2 hRopS)
      (Work.FTS.LocData.Fstar_smoothQuad α)
  -- the four integrability certificates
  have hInt1 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS.Nonlin.N1gg α g Φg s θ / s)
      Work.Spaces.Iθ :=
    integrableOn_K_mul_of_smoothQuad_bound hsm1 hs hC1 hb1
  have hInt2 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg s θ / s)
      Work.Spaces.Iθ :=
    integrableOn_K_mul_of_smoothQuad_bound hsm2 hs hC2 hb2
  have hInt3 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g s θ / s)
      Work.Spaces.Iθ :=
    integrableOn_K_mul_of_smoothQuad_bound hsm3 hs hC3 hb3
  have hInt4 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs s θ / s)
      Work.Spaces.Iθ :=
    integrableOn_K_mul_of_smoothQuad_bound hsm4 hs hC4 hb4
  -- the a.e. identity of the integrands
  have hae : (fun θ => Work.Spaces.K θ * Work.Construction.N1 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) s θ / s)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.K θ * Work.FTS.Nonlin.N1gg α g Φg s θ / s
        + (Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg s θ / s
          + (Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g s θ / s
            + Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs s θ / s))) := by
    refine Work.Elliptic.ae_restrict_Iθ_of_Ioo (p := fun θ =>
      Work.Spaces.K θ * Work.Construction.N1 α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) s θ / s
        = Work.Spaces.K θ * Work.FTS.Nonlin.N1gg α g Φg s θ / s
          + (Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg s θ / s
            + (Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g s θ / s
              + Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs s θ / s))) ?_
    intro θ h0 h1
    rw [hsplit s θ ⟨hs, h0, h1⟩]
    ring
  -- the equality of the densities
  have hEq1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Construction.N1 α
        (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) s θ / s)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Work.FTS.Nonlin.N1gg α g Φg s θ / s
          + (Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg s θ / s
            + (Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g s θ / s
              + Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs s θ / s))) :=
    MeasureTheory.integral_congr_ae hae
  have hEq2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Work.FTS.Nonlin.N1gg α g Φg s θ / s
        + (Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg s θ / s
          + (Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g s θ / s
            + Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs s θ / s))))
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.Nonlin.N1gg α g Φg s θ / s)
        + ((∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg s θ / s)
          + ((∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g s θ / s)
            + ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs s θ / s)) := by
    have h1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Work.FTS.Nonlin.N1gg α g Φg s θ / s
          + (Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg s θ / s
            + (Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g s θ / s
              + Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs s θ / s))))
        = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.Nonlin.N1gg α g Φg s θ / s)
          + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg s θ / s
            + (Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g s θ / s
              + Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs s θ / s))) :=
      MeasureTheory.integral_add hInt1 (hInt2.add (hInt3.add hInt4))
    have h2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg s θ / s
          + (Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g s θ / s
            + Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs s θ / s)))
        = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg s θ / s)
          + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g s θ / s
            + Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs s θ / s)) :=
      MeasureTheory.integral_add hInt2 (hInt3.add hInt4)
    have h3 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g s θ / s
          + Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs s θ / s))
        = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g s θ / s)
          + ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs s θ / s :=
      MeasureTheory.integral_add hInt3 hInt4
    rw [h1, h2, h3]
  have hmain : Work.Construction.L12dens (Work.Construction.N1 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) s
      = Work.Construction.L12dens (Work.FTS.Nonlin.N1gg α g Φg) s
        + (Work.Construction.L12dens (Work.FTS.Nonlin.N1gs α g Φg) s
          + (Work.Construction.L12dens (Work.FTS.Nonlin.N1sg α Φs g) s
            + Work.Construction.L12dens (Work.FTS.Nonlin.N1ss α Φs) s)) := by
    show (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Construction.N1 α
        (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) s θ / s)
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.Nonlin.N1gg α g Φg s θ / s)
        + ((∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg s θ / s)
          + ((∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g s θ / s)
            + ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs s θ / s))
    exact hEq1.trans hEq2
  -- the triangle inequality
  calc ‖Work.Construction.L12dens (Work.Construction.N1 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) s‖
      = ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1gg α g Φg) s
          + (Work.Construction.L12dens (Work.FTS.Nonlin.N1gs α g Φg) s
            + (Work.Construction.L12dens (Work.FTS.Nonlin.N1sg α Φs g) s
              + Work.Construction.L12dens (Work.FTS.Nonlin.N1ss α Φs) s))‖ := by
        rw [hmain]
    _ ≤ ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1gg α g Φg) s‖
          + ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1gs α g Φg) s
            + (Work.Construction.L12dens (Work.FTS.Nonlin.N1sg α Φs g) s
              + Work.Construction.L12dens (Work.FTS.Nonlin.N1ss α Φs) s)‖ :=
        norm_add_le _ _
    _ ≤ ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1gg α g Φg) s‖
          + (‖Work.Construction.L12dens (Work.FTS.Nonlin.N1gs α g Φg) s‖
            + ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1sg α Φs g) s
              + Work.Construction.L12dens (Work.FTS.Nonlin.N1ss α Φs) s‖) := by
        linarith [norm_add_le (Work.Construction.L12dens (Work.FTS.Nonlin.N1gs α g Φg) s)
          (Work.Construction.L12dens (Work.FTS.Nonlin.N1sg α Φs g) s
            + Work.Construction.L12dens (Work.FTS.Nonlin.N1ss α Φs) s)]
    _ ≤ ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1gg α g Φg) s‖
          + (‖Work.Construction.L12dens (Work.FTS.Nonlin.N1gs α g Φg) s‖
            + (‖Work.Construction.L12dens (Work.FTS.Nonlin.N1sg α Φs g) s‖
              + ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1ss α Φs) s‖)) := by
        linarith [norm_add_le (Work.Construction.L12dens (Work.FTS.Nonlin.N1sg α Φs g) s)
          (Work.Construction.L12dens (Work.FTS.Nonlin.N1ss α Φs) s)]
    _ = ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1gg α g Φg) s‖
          + ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1gs α g Φg) s‖
          + ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1sg α Φs g) s‖
          + ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1ss α Φs) s‖ := by ring

end Work.FTS.Nonlinear.Pieces.Rl1
