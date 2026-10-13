import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.Nonlinear.Pieces.L12FK_add_ge0
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.starPt
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gPt
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.H2.CS1D
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.StarUBound
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.DthFstarPoint
import Submission.Work.Coercivity.radial_bound

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

/-! ## The density of `N₂` under the context of the `rl1` row

The `rl1` row of `AuxRows` estimates `|L₁₂(N)(0)| ≤ K(α² + √α X + α^{-3/2}X²)` by the sum of the
five density integrals `E_i = ∫_{s>0}‖L₁₂dens(N_i)(s)‖ ds`.  This file proves the `i = 2` term,

  `E₂ ≤ K(α² + √α X + α^{-3/2}X²)`,

under the frozen context `N4Norm Ci α₂`, `GalClass α g`, `StarPkg α Cs Φs`, `EllPkgG α Ce g Φg`,
`0 < α ≤ 1`, `α ≤ α₂`.

**Route.** `N₂ = -2𝒰(Φ̃)∂_θF` with `Φ̃ = Φ̃_* + Φ̃_g` and `F = F_* + g`, so
`N₂ = N₂^{gg} + N₂^{gs} + N₂^{sg} + N₂^{ss}` pointwise on the quadrant (`N2_split`).  The key
device is that the kernel `K(θ) = 3 sin θ cos²θ` satisfies `K = (3/2) cos θ·sin(2θ)`, hence

  `K(θ)·∂_θ f = (3/2)cos θ·D_θ f`   (`K_mul_pth`),

so every term is a product of the *bounded* angular factor `(3/2)cos θ ≤ 3/2` with two of the
quantities `𝒰(Φ̃_*), 𝒰(Φ̃_g)/sin 2θ, D_θF_*, D_θg` (the last two carrying one factor of
`sin 2θ` each).  Those four are controlled by

* `|𝒰(Φ̃_*)| ≤ C·max Cs 0·α` (`StarUBound`),
* `|𝒰(Φ̃_g)/sin 2θ| ≤ 10√(10/α)·max Ce 0·X` (`gPt`),
* `∫_θ |D_θF_*| ≤ C·α²·z/(1+z)²` (`DthFstarPoint`),
* `∫_θ (D_θg)² ≤ (1/w z)∫_θ HkIntegrand α 4 g z θ` (`SliceSlot`),

the last together with Cauchy–Schwarz in `θ` and in `s` (with `1/s = √(w s)/(1+s)` and
`∫_s 1/(1+s)² = 1`) and the identification `√(HkSq α 4 g) = Xn α g`. -/

/-! ## The elementary identity for the kernel -/

/-- `K(θ)·∂_θ f = (3/2)cos θ·D_θ f`, with `K = 3 sinθcos²θ` and `D_θ = sin(2θ)∂_θ`.  This is the
identity that makes the `L₁₂`-kernel cancel the `sin 2θ` of `D_θ`, so that no division by
`sin 2θ` ever appears. -/
theorem K_mul_pth (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.K θ * Work.Spaces.pth f z θ
      = (3 / 2) * Real.cos θ * Work.Spaces.Dth f z θ := by
  simp only [Work.Spaces.K, Work.Spaces.Dth, Work.Construction.s2, Real.sin_two_mul]
  ring

/-! ## The four-way split of `N₂` on the open quadrant -/

/-- The pointwise split `N₂ = N₂^{gg} + N₂^{gs} + N₂^{sg} + N₂^{ss}` on the open quadrant.  This
is the `N₂`-block of `Work.FTS.Nonlinear.Pieces.rl1Tools.Nsplit`, isolated. -/
theorem N2_split {α : ℝ} {g Φs Φg : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.FTS.Nonlin.GalClass α g)
    (hΦs : Work.FTS.LocData.SmoothQuad Φs) (hΦg : Work.FTS.LocData.SmoothQuad Φg)
    (hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N2 α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) z θ
        = Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
          + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ := by
  intro z θ hq
  have hz : 0 < z := hq.1
  have hzI : z ∈ Set.Ioi (-1 : ℝ) := by rw [Set.mem_Ioi]; linarith
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hq.2
  have hreg : Work.FTS.LocData.SmoothQuad g := hg.reg.1
  have hF : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.Fstar_smoothQuad α
  have hL : ∀ z' : ℝ, 0 < z' → Work.Construction.L12 (Work.Construction.Ftot α g) z'
      = Work.Construction.L12 (Work.Construction.Fstar α) z' + Work.Construction.L12 g z' :=
    fun z' hz' => (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 hα hα1 hg).1 z' hz'.le
  -- the identity of the straightened stream functions, at the point (in `θ`) and near it (in `z`)
  have hsliceθ : (fun θ' => Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ')
      = (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ'
          + Work.Construction.PhiTil α g Φg z θ') := by
    funext θ'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL z hz]
    ring
  have hslicez : (fun z' => Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ
          + Work.Construction.PhiTil α g Φg z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL z' hz']
    ring
  have hval : Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
        + Work.Construction.PhiTil α g Φg z θ :=
    congrFun hsliceθ θ
  -- differentiability of the `z`-slices of the two pieces
  have hPsi1 : Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs
      = fun z' θ' => Φs z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 (Work.Construction.Fstar α) z' := rfl
  have hPsi2 : Work.Construction.PhiTil α g Φg
      = fun z' θ' => Φg z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 g z' := rfl
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
  -- additivity of `∂_z` at the point
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
  -- the additivity of `𝒰`
  have hUop : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ := by
    simp only [Work.Construction.Uop]
    rw [hval, hpzP]
    ring
  -- additivity of `∂_θ` on `F = F_* + g`
  have hpthF : Work.Spaces.pth (Work.Construction.Ftot α g) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ :=
    Work.FTS.Nonlinear.Pieces.pth_add_of_smoothQuad hF hreg hzI hθ
  simp only [Work.Construction.N2, Work.FTS.Nonlin.N2gg, Work.FTS.Nonlin.N2gs,
    Work.FTS.Nonlin.N2sg, Work.FTS.Nonlin.N2ss, Work.FTS.Nonlin.PhiTg,
    Work.FTS.Nonlin.PhiTs]
  rw [hUop, hpthF]
  ring

/-! ## Measurability of the angular slices -/

/-- The `θ`-slice `θ ↦ D_θ f z θ` of a `SmoothQuad` function is a.e. strongly measurable on
`Iθ` for `z > 0`. -/
theorem aesm_slice_Dth {f : ℝ → ℝ → ℝ} (hsq : Work.FTS.LocData.SmoothQuad f) {z : ℝ}
    (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => Work.Spaces.Dth f z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  have hD : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dth f)) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_Dth (isOpen_Ioi.prod isOpen_Ioo) hsq
  refine Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hD.continuousOn.mono ?_) hz
  intro p hp
  exact ⟨Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0) hp.1, hp.2⟩

/-- `mixed 0 1 f = D_θ f`. -/
theorem mixed_zero_one (f : ℝ → ℝ → ℝ) : Work.Spaces.mixed 0 1 f = Work.Spaces.Dth f := by
  funext z θ
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
    Work.Spaces.DthIter_zero]

/-- The open `θ`-interval is a.e. equal to `Iθ`. -/
theorem ae_restrict_Iθ_of_Ioo {p : ℝ → Prop}
    (h : ∀ θ, 0 < θ → θ < π / 2 → p θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ :=
  Work.Elliptic.ae_restrict_Iθ_of_Ioo h

/-! ## The pointwise slot inequality for `D_θ` -/

/-- **The pointwise slot inequality.**  For `0 < α`, `1 ≤ k`, `z > 0` and `θ ∈ (0,π/2)`,

  `w z · (D_θ f z θ)² ≤ HkIntegrand α k f z θ`.

Indeed `D_θ f = mixed 0 1 f` and the mixed slot of `HkIntegrand` is
`(mixed 0 1 f · Wt)² = (D_θ f)² w² sin(2θ)^{-γ}`, which dominates `w z·(D_θ f)²` because
`w z ≥ 1` and `sin(2θ)^{-γ} ≥ 1`. -/
theorem Dth_sq_mul_w_le {α : ℝ} (hα : 0 < α) {k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.w z * (Work.Spaces.Dth f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hs2pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs2le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam0 : 0 ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  -- `sin(2θ)^{-γ} ≥ 1`
  have hrpow : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [Real.rpow_neg hs2pos.le, inv_eq_one_div, one_le_div (Real.rpow_pos_of_pos hs2pos _)]
    exact Real.rpow_le_one hs2pos.le hs2le hgam0
  have hw1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
    nlinarith [hz]
  -- `(D_θ f · Wt)² = (D_θ f)² · w² · sin(2θ)^{-γ}`
  have hWt_eq : Work.Spaces.Wt α z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
  have hsqWt : (Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.Dth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
    rw [hWt_eq]; ring
  have hsin2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2,
      ← Real.rpow_mul hs2pos.le]
    norm_num
  have hslot : (Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ 1 0 (by norm_num)
      (by simpa using hk)
    rwa [mixed_zero_one f] at h
  refine le_trans ?_ hslot
  rw [hsqWt, hsin2]
  have hD0 : 0 ≤ (Work.Spaces.Dth f z θ) ^ 2 := sq_nonneg _
  have hw0 : 0 ≤ (Work.Spaces.Dth f z θ) ^ 2 * Work.Spaces.w z :=
    mul_nonneg hD0 (by rw [Work.Spaces.w]; positivity)
  have h1 : 1 ≤ Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    nlinarith [hw1, hrpow]
  calc Work.Spaces.w z * (Work.Spaces.Dth f z θ) ^ 2
      = (Work.Spaces.Dth f z θ) ^ 2 * Work.Spaces.w z * 1 := by ring
    _ ≤ (Work.Spaces.Dth f z θ) ^ 2 * Work.Spaces.w z
          * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_left h1 hw0
    _ = (Work.Spaces.Dth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by ring

/-- `(D_θ f z θ)² ≤ (1/w z)·HkIntegrand α k f z θ` on the open quadrant. -/
theorem Dth_sq_le_div_w {α : ℝ} (hα : 0 < α) {k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.Dth f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ / Work.Spaces.w z := by
  have h := Dth_sq_mul_w_le (f := f) hα hk hz hθ
  rw [le_div_iff₀ (by rw [Work.Spaces.w]; positivity)]
  linarith [h]

/-! ## The `θ`-slice of `D_θ g`: integrability and `L¹`-bounds -/

/-- The square of the `θ`-slice of `D_θ g` is integrable on `Iθ`, dominated by the
`ℋ⁴`-integrand. -/
theorem integrableOn_Dth_sq {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (Work.Spaces.Dth g z θ) ^ 2) Work.Spaces.Iθ := by
  refine Integrable.mono' ((hmem.1 z hz.le).div_const (Work.Spaces.w z))
    ((aesm_slice_Dth hsq hz).pow 2) ?_
  filter_upwards [ae_restrict_Iθ_of_Ioo (p := fun θ =>
    (Work.Spaces.Dth g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ / Work.Spaces.w z)
    (fun θ h0 h1 => Dth_sq_le_div_w hα (by norm_num) hz ⟨h0, h1⟩)] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hθ

/-- The `θ`-slice of `D_θ g` is integrable on `Iθ`. -/
theorem integrableOn_Dth {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => Work.Spaces.Dth g z θ) Work.Spaces.Iθ := by
  have h2 := integrableOn_Dth_sq hα hsq hmem hz
  have hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.Dth g z θ‖ ≤ (1 + (Work.Spaces.Dth g z θ) ^ 2) / 2 := by
    filter_upwards with θ
    have h1 : |Work.Spaces.Dth g z θ| ≤ (1 + (Work.Spaces.Dth g z θ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|Work.Spaces.Dth g z θ| - 1), sq_abs (Work.Spaces.Dth g z θ)]
    simpa only [Real.norm_eq_abs] using h1
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; simp)
  refine Integrable.mono' ?_ (aesm_slice_Dth hsq hz) hbound
  exact (hconst.add h2).div_const 2

/-- `∫_θ (D_θ g z θ)² ≤ (1/w z)·∫_θ HkIntegrand α 4 g z θ`. -/
theorem integral_Dth_sq_le {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) / Work.Spaces.w z := by
  rw [← MeasureTheory.integral_div]
  refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
    ((hmem.1 z hz.le).div_const _) ?_
  filter_upwards [ae_restrict_Iθ_of_Ioo (p := fun θ =>
    (Work.Spaces.Dth g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ / Work.Spaces.w z)
    (fun θ h0 h1 => Dth_sq_le_div_w hα (by norm_num) hz ⟨h0, h1⟩)] with θ hθ
  exact hθ

/-- Cauchy–Schwarz in `θ`: `∫_θ |D_θ g z θ| ≤ √(π/2)·√(∫_θ (D_θ g z θ)²)`. -/
theorem integral_Dth_abs_le {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth g z θ|)
      ≤ Real.sqrt (Real.pi / 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2) := by
  have hmemLp : MemLp (fun θ => Work.Spaces.Dth g z θ) 2
      (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (aesm_slice_Dth hsq hz)).mpr
      (integrableOn_Dth_sq hα hsq hmem hz)
  have hmemLpAbs : MemLp (fun θ => |Work.Spaces.Dth g z θ|) 2
      (volume.restrict Work.Spaces.Iθ) := by
    simpa only [Real.norm_eq_abs] using hmemLp.norm
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict Work.Spaces.Iθ) :=
    memLp_const 1
  have h1 := Work.Spaces.cs_integral (u := fun _ : ℝ => (1 : ℝ))
    (v := fun θ => |Work.Spaces.Dth g z θ|) (s := Work.Spaces.Iθ) hone hmemLpAbs
  simp only [one_mul, one_pow] at h1
  have hpi : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
    rw [MeasureTheory.setIntegral_const]
    have h2 : MeasureTheory.volume.real Work.Spaces.Iθ = Real.pi / 2 := by
      rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    rw [h2, smul_eq_mul, mul_one]
  rw [hpi] at h1
  have habs_sq : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth g z θ| ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [sq_abs]
  rw [habs_sq] at h1
  have hLHS : 0 ≤ ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth g z θ| :=
    integral_nonneg fun θ => abs_nonneg _
  calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth g z θ|)
      = Real.sqrt ((∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth g z θ|) ^ 2) :=
        (Real.sqrt_sq hLHS).symm
    _ ≤ Real.sqrt ((Real.pi / 2)
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2)) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt (Real.pi / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2) := by
        rw [Real.sqrt_mul (by positivity)]

/-! ## The `L₁₂`-density as a divided angular integral -/

/-- `L₁₂dens f s = (∫_θ K(θ)·f s θ)/s` for `s ≠ 0`. -/
theorem L12dens_eq_div (f : ℝ → ℝ → ℝ) {s : ℝ} (hs : s ≠ 0) :
    Work.Construction.L12dens f s
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ) / s := by
  rw [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ, MeasureTheory.integral_div]

/-- `K(θ) ≥ 0` on `Iθ`. -/
theorem K_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  positivity

/-- `K(θ) = (3/2)cos θ·sin(2θ)`. -/
theorem K_eq_s2 (θ : ℝ) :
    Work.Spaces.K θ = (3 / 2) * Real.cos θ * Work.Construction.s2 θ := by
  rw [Work.Spaces.K, Work.Construction.s2, Real.sin_two_mul]; ring

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem s2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Construction.s2 θ := by
  rw [Work.Construction.s2]
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin(2θ) ≤ 1` on `Iθ`. -/
theorem s2_le_one (θ : ℝ) : Work.Construction.s2 θ ≤ 1 := by
  rw [Work.Construction.s2]; exact Real.sin_le_one _

/-- `cos θ ≥ 0` on `Iθ`. -/
theorem cos_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩

/-- `‖L₁₂dens f s‖ ≤ (1/s)·∫_θ K(θ)·‖f s θ‖` for `s > 0`. -/
theorem norm_L12dens_le (f : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    ‖Work.Construction.L12dens f s‖
      ≤ (1 / s) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * ‖f s θ‖ := by
  have h1 : ‖Work.Construction.L12dens f s‖
      = ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ‖ * (1 / s) := by
    rw [L12dens_eq_div f (ne_of_gt hs), norm_div, Real.norm_of_nonneg hs.le]
    ring
  have h2 : ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ‖
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * ‖f s θ‖ := by
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) (le_of_eq ?_)
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (K_nonneg hθ)]
  calc ‖Work.Construction.L12dens f s‖
      = ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ‖ * (1 / s) := h1
    _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * ‖f s θ‖) * (1 / s) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = (1 / s) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * ‖f s θ‖ := by ring

/-- The generic term estimate: `K θ·2·|X|·|p| ≤ 3M|d|` whenever `|X| ≤ M` and
`K θ·|p| ≤ (3/2)|d|`. -/
theorem term_le {θ M X p d : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hM : 0 ≤ M) (hX : |X| ≤ M)
    (hKp : Work.Spaces.K θ * |p| ≤ (3 / 2) * |d|) :
    Work.Spaces.K θ * (2 * (|X| * |p|)) ≤ 3 * M * |d| := by
  calc Work.Spaces.K θ * (2 * (|X| * |p|)) = 2 * |X| * (Work.Spaces.K θ * |p|) := by ring
    _ ≤ 2 * M * ((3 / 2) * |d|) :=
        mul_le_mul (by linarith [hX]) hKp (mul_nonneg (K_nonneg hθ) (abs_nonneg p))
          (by linarith [hM])
    _ = 3 * M * |d| := by ring

/-! ## The pointwise domination of `K·N₂` on the open quadrant -/

/-- **The pointwise domination.**  For `z > 0` and `θ ∈ (0,π/2)`,

  `K(θ)·|N₂(α, F_*+g, Φ̃_*+Φ̃_g)(z,θ)| ≤ 3·(A + B)·(|D_θF_*| + |D_θg|)`

where `A` dominates `|𝒰(Φ̃_*)|` and `B` dominates `|𝒰(Φ̃_g)/sin 2θ|` on the quadrant.  The four
terms of `N2_split` contribute `3B(|D_θg|+|D_θF_*|)` (from `𝒰(Φ̃_g) = (𝒰(Φ̃_g)/sin2θ)·sin2θ`
and `K|∂_θ| ≤ (3/2)|D_θ|`) and `3A(|D_θg|+|D_θF_*|)`. -/
theorem K_N2_le {α Cs Ce c₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hc₁ : 0 ≤ c₁)
    {g Φs Φg : Fn} (hgal : Work.FTS.Nonlin.GalClass α g)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg)
    (hStarU : ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ c₁ * max Cs 0 * α)
    (hAg : ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ|
        ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
    (hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.K θ * |Work.Construction.N2 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ|
      ≤ 3 * (c₁ * max Cs 0 * α + 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
        * (|Work.Spaces.Dth (Work.Construction.Fstar α) z θ| + |Work.Spaces.Dth g z θ|) := by
  set A : ℝ := c₁ * max Cs 0 * α with hAdef
  set B : ℝ := 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have := Work.Spaces.HkNorm_nonneg α 4 g
    positivity
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (mul_nonneg hc₁ (le_max_right Cs 0)) hα.le
  have hθ' : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hs2pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcos0 : 0 ≤ Real.cos θ := cos_nonneg_Iθ hθ'
  have hK0 : 0 ≤ Work.Spaces.K θ := K_nonneg hθ'
  -- the pointwise identity `K·∂_θ = (3/2)cos θ·D_θ`, in absolute value
  have hKpth : ∀ f : ℝ → ℝ → ℝ,
      Work.Spaces.K θ * |Work.Spaces.pth f z θ| ≤ (3 / 2) * |Work.Spaces.Dth f z θ| := by
    intro f
    have h := K_mul_pth f z θ
    have h2 : Work.Spaces.K θ * |Work.Spaces.pth f z θ|
        = |(3 / 2) * Real.cos θ * Work.Spaces.Dth f z θ| := by
      rw [← h, abs_mul, abs_of_nonneg hK0]
    rw [h2, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3 / 2)]
    nlinarith [abs_nonneg (Real.cos θ), Real.abs_cos_le_one θ,
      abs_nonneg (Work.Spaces.Dth f z θ)]
  -- the four terms
  have hgg : Work.Spaces.K θ * |Work.FTS.Nonlin.N2gg α g Φg z θ|
      ≤ 3 * B * |Work.Spaces.Dth g z θ| := by
    have hs2ne : Work.Construction.s2 θ ≠ 0 := ne_of_gt hs2pos
    have hUg : Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
        = (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ)
          * Work.Construction.s2 θ := (div_mul_cancel₀ _ hs2ne).symm
    have hX : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ| ≤ B := by
      rw [hUg, abs_mul, abs_of_nonneg (s2_nonneg_Iθ hθ')]
      have hb : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
          / Work.Construction.s2 θ| ≤ B := by rw [hBdef]; exact hAg z hz θ hθ'
      calc |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
            / Work.Construction.s2 θ| * Work.Construction.s2 θ
          ≤ B * 1 := mul_le_mul hb (s2_le_one θ) (le_of_lt hs2pos) hB0
        _ = B := mul_one B
    simp only [Work.FTS.Nonlin.N2gg]
    rw [show (-2) * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
          * Work.Spaces.pth g z θ
        = -(2 * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
          * Work.Spaces.pth g z θ)) from by ring,
      abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul]
    exact term_le hθ' hB0 hX (hKpth g)
  have hgs : Work.Spaces.K θ * |Work.FTS.Nonlin.N2gs α g Φg z θ|
      ≤ 3 * B * |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| := by
    have hs2ne : Work.Construction.s2 θ ≠ 0 := ne_of_gt hs2pos
    have hUg : Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
        = (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ)
          * Work.Construction.s2 θ := (div_mul_cancel₀ _ hs2ne).symm
    have hX : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ| ≤ B := by
      rw [hUg, abs_mul, abs_of_nonneg (s2_nonneg_Iθ hθ')]
      have hb : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
          / Work.Construction.s2 θ| ≤ B := by rw [hBdef]; exact hAg z hz θ hθ'
      calc |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
            / Work.Construction.s2 θ| * Work.Construction.s2 θ
          ≤ B * 1 := mul_le_mul hb (s2_le_one θ) (le_of_lt hs2pos) hB0
        _ = B := mul_one B
    simp only [Work.FTS.Nonlin.N2gs]
    rw [show (-2) * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        = -(2 * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ)) from by ring,
      abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul]
    exact term_le hθ' hB0 hX (hKpth (Work.Construction.Fstar α))
  have hsg : Work.Spaces.K θ * |Work.FTS.Nonlin.N2sg α Φs g z θ|
      ≤ 3 * A * |Work.Spaces.Dth g z θ| := by
    have hX : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ A := by
      rw [hAdef]; exact hStarU z hz θ hθ'
    simp only [Work.FTS.Nonlin.N2sg]
    rw [show (-2) * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * Work.Spaces.pth g z θ
        = -(2 * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * Work.Spaces.pth g z θ)) from by ring,
      abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul]
    exact term_le hθ' hA0 hX (hKpth g)
  have hss : Work.Spaces.K θ * |Work.FTS.Nonlin.N2ss α Φs z θ|
      ≤ 3 * A * |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| := by
    have hX : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ A := by
      rw [hAdef]; exact hStarU z hz θ hθ'
    simp only [Work.FTS.Nonlin.N2ss]
    rw [show (-2) * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        = -(2 * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ)) from by ring,
      abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul]
    exact term_le hθ' hA0 hX (hKpth (Work.Construction.Fstar α))
  -- assemble
  have hsplit := N2_split hα hα1 hgal hs.smooth hell.smooth hL12 z θ ⟨hz, hθ⟩
  have htri : |Work.Construction.N2 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ|
      ≤ |Work.FTS.Nonlin.N2gg α g Φg z θ| + |Work.FTS.Nonlin.N2gs α g Φg z θ|
        + |Work.FTS.Nonlin.N2sg α Φs g z θ| + |Work.FTS.Nonlin.N2ss α Φs z θ| := by
    rw [hsplit]
    have h1 : |Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
        + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ|
        ≤ |Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
            + Work.FTS.Nonlin.N2sg α Φs g z θ| + |Work.FTS.Nonlin.N2ss α Φs z θ| :=
      abs_add_le _ _
    have h2 : |Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
        + Work.FTS.Nonlin.N2sg α Φs g z θ|
        ≤ |Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ|
          + |Work.FTS.Nonlin.N2sg α Φs g z θ| := abs_add_le _ _
    have h3 : |Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ|
        ≤ |Work.FTS.Nonlin.N2gg α g Φg z θ| + |Work.FTS.Nonlin.N2gs α g Φg z θ| :=
      abs_add_le _ _
    linarith
  calc Work.Spaces.K θ * |Work.Construction.N2 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ|
      ≤ Work.Spaces.K θ * (|Work.FTS.Nonlin.N2gg α g Φg z θ|
          + |Work.FTS.Nonlin.N2gs α g Φg z θ|
          + |Work.FTS.Nonlin.N2sg α Φs g z θ| + |Work.FTS.Nonlin.N2ss α Φs z θ|) :=
        mul_le_mul_of_nonneg_left htri hK0
    _ = (Work.Spaces.K θ * |Work.FTS.Nonlin.N2gg α g Φg z θ|
          + Work.Spaces.K θ * |Work.FTS.Nonlin.N2gs α g Φg z θ|)
        + (Work.Spaces.K θ * |Work.FTS.Nonlin.N2sg α Φs g z θ|
          + Work.Spaces.K θ * |Work.FTS.Nonlin.N2ss α Φs z θ|) := by ring
    _ ≤ (3 * B * |Work.Spaces.Dth g z θ|
          + 3 * B * |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|)
        + (3 * A * |Work.Spaces.Dth g z θ|
          + 3 * A * |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|) :=
        add_le_add (add_le_add hgg hgs) (add_le_add hsg hss)
    _ = 3 * (A + B) * (|Work.Spaces.Dth (Work.Construction.Fstar α) z θ|
        + |Work.Spaces.Dth g z θ|) := by ring
    _ = 3 * (c₁ * max Cs 0 * α + 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
        * (|Work.Spaces.Dth (Work.Construction.Fstar α) z θ| + |Work.Spaces.Dth g z θ|) := by
        rw [hAdef, hBdef]

/-! ## The bound on the density at fixed `s` -/

/-- **The density bound.**  For `s > 0`, the `L₁₂`-density of `N₂` is bounded by

  `3(A+B)·( (π/2)c₂α²/(1+s)² + √(π/2)·√(∫_θ HkIntegrand α 4 g s θ)/(1+s) )`,

with `A = c₁·max Cs 0·α` and `B = 10√(10/α)·max Ce 0·X`. -/
theorem density_bound {α Cs Ce c₁ c₂ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hc₁ : 0 ≤ c₁)
    {g Φs Φg : Fn} (hgal : Work.FTS.Nonlin.GalClass α g)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg)
    (hStarU : ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ c₁ * max Cs 0 * α)
    (hAg : ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ|
        ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
    (hDthFs : ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| ≤ c₂ * α ^ 2 * (z / (1 + z) ^ 2))
    (hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z)
    {s : ℝ} (hspos : 0 < s) :
    ‖Work.Construction.L12dens (Work.Construction.N2 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) s‖
      ≤ 3 * (c₁ * max Cs 0 * α + 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
        * ((Real.pi / 2) * c₂ * α ^ 2 / (1 + s) ^ 2
            + Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 4 g s θ) / (1 + s)) := by
  have hsq : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 g := (Work.FTS.Nonlin.galClass_regQ4 hgal).2.1
  have hFstar : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.Fstar_smoothQuad α
  set A : ℝ := c₁ * max Cs 0 * α with hAdef
  set B : ℝ := 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have := Work.Spaces.HkNorm_nonneg α 4 g
    positivity
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (mul_nonneg hc₁ (le_max_right Cs 0)) hα.le
  -- (1) the `θ`-slice bounds
  have hvol : MeasureTheory.volume.real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hDs_int : IntegrableOn (fun θ => |Work.Spaces.Dth (Work.Construction.Fstar α) s θ|)
      Work.Spaces.Iθ := by
    have hconst : IntegrableOn
        (fun _ : ℝ => c₂ * α ^ 2 * (s / (1 + s) ^ 2)) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; simp)
    have haesm : AEStronglyMeasurable
        (fun θ => |Work.Spaces.Dth (Work.Construction.Fstar α) s θ|)
        (volume.restrict Work.Spaces.Iθ) := by
      simpa only [Real.norm_eq_abs] using (aesm_slice_Dth hFstar hspos).norm
    refine Integrable.mono' hconst haesm ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_abs]
    exact hDthFs s hspos θ hθ
  have hDs_le : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth (Work.Construction.Fstar α) s θ|)
      ≤ (c₂ * α ^ 2 * (s / (1 + s) ^ 2)) * (Real.pi / 2) := by
    have hconst : IntegrableOn
        (fun _ : ℝ => c₂ * α ^ 2 * (s / (1 + s) ^ 2)) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; simp)
    have hmono : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth (Work.Construction.Fstar α) s θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, c₂ * α ^ 2 * (s / (1 + s) ^ 2) :=
      MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall fun θ => abs_nonneg _) hconst
        (by filter_upwards [self_mem_ae_restrict measurableSet_Icc] with θ hθ
            exact hDthFs s hspos θ hθ)
    have hval : (∫ θ in Work.Spaces.Iθ, c₂ * α ^ 2 * (s / (1 + s) ^ 2))
        = (c₂ * α ^ 2 * (s / (1 + s) ^ 2)) * (Real.pi / 2) := by
      rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]
      ring
    rw [hval] at hmono
    exact hmono
  have hDg_int : IntegrableOn (fun θ => |Work.Spaces.Dth g s θ|) Work.Spaces.Iθ :=
    (integrableOn_Dth hα hsq hmem4 hspos).abs
  -- (2) integrability of the `θ`-majorant
  have hsum_int : IntegrableOn (fun θ => |Work.Spaces.Dth (Work.Construction.Fstar α) s θ|
      + |Work.Spaces.Dth g s θ|) Work.Spaces.Iθ := hDs_int.add hDg_int
  have hmaj_int : IntegrableOn (fun θ => 3 * (A + B)
      * (|Work.Spaces.Dth (Work.Construction.Fstar α) s θ| + |Work.Spaces.Dth g s θ|))
      Work.Spaces.Iθ := hsum_int.const_mul _
  -- (3) the pointwise domination, a.e. in `θ`
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Work.Spaces.K θ * ‖Work.Construction.N2 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) s θ‖
      ≤ 3 * (A + B) * (|Work.Spaces.Dth (Work.Construction.Fstar α) s θ|
          + |Work.Spaces.Dth g s θ|) := by
    refine ae_restrict_Iθ_of_Ioo (p := fun θ => Work.Spaces.K θ
      * ‖Work.Construction.N2 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) s θ‖
      ≤ 3 * (A + B) * (|Work.Spaces.Dth (Work.Construction.Fstar α) s θ|
          + |Work.Spaces.Dth g s θ|)) (fun θ h0 h1 => ?_)
    have h := K_N2_le hα hα1 hc₁ hgal hs hell hStarU hAg hL12 hspos ⟨h0, h1⟩
    rw [hAdef, hBdef]
    simpa only [Real.norm_eq_abs] using h
  -- (4) the `θ`-integral bound
  have hInt : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
        * ‖Work.Construction.N2 α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) s θ‖)
      ≤ 3 * (A + B) * ((∫ θ in Work.Spaces.Iθ,
            |Work.Spaces.Dth (Work.Construction.Fstar α) s θ|)
          + ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth g s θ|) := by
    have hmono : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
          * ‖Work.Construction.N2 α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + Φg z θ) s θ‖)
        ≤ ∫ θ in Work.Spaces.Iθ, 3 * (A + B)
          * (|Work.Spaces.Dth (Work.Construction.Fstar α) s θ|
            + |Work.Spaces.Dth g s θ|) :=
      MeasureTheory.integral_mono_of_nonneg
        (by filter_upwards [self_mem_ae_restrict measurableSet_Icc] with θ hθ
            exact mul_nonneg (K_nonneg hθ) (norm_nonneg _)) hmaj_int hpt
    have hsplit_int : (∫ θ in Work.Spaces.Iθ, 3 * (A + B)
        * (|Work.Spaces.Dth (Work.Construction.Fstar α) s θ| + |Work.Spaces.Dth g s θ|))
        = 3 * (A + B) * ((∫ θ in Work.Spaces.Iθ,
              |Work.Spaces.Dth (Work.Construction.Fstar α) s θ|)
            + ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth g s θ|) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hDs_int hDg_int]
    rw [hsplit_int] at hmono
    exact hmono
  -- (5) the two `θ`-bounds
  have hDg_le : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth g s θ|)
      ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dth g s θ) ^ 2) :=
    integral_Dth_abs_le hα hsq hmem4 hspos
  have hDg_sq_le : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g s θ) ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) / Work.Spaces.w s :=
    integral_Dth_sq_le hα hsq hmem4 hspos
  have hH0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ :=
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hsqrt_w : Real.sqrt (Work.Spaces.w s) = (1 + s) / s := by
    rw [Work.Spaces.w, Real.sqrt_div (by positivity : (0:ℝ) ≤ (1 + s) ^ 2), Real.sqrt_sq_eq_abs,
      Real.sqrt_sq_eq_abs, abs_of_pos (by linarith), abs_of_pos hspos]
  -- (6) assembly
  have hstep : ‖Work.Construction.L12dens (Work.Construction.N2 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) s‖
      ≤ (1 / s) * (3 * (A + B) * ((c₂ * α ^ 2 * (s / (1 + s) ^ 2)) * (Real.pi / 2)
          + Real.sqrt (Real.pi / 2) * Real.sqrt ((∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 4 g s θ) / Work.Spaces.w s))) := by
    refine le_trans (norm_L12dens_le _ hspos) ?_
    refine mul_le_mul_of_nonneg_left (le_trans hInt ?_) (by positivity)
    have h1 : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth (Work.Construction.Fstar α) s θ|)
        + (∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth g s θ|)
        ≤ (c₂ * α ^ 2 * (s / (1 + s) ^ 2)) * (Real.pi / 2)
          + Real.sqrt (Real.pi / 2) * Real.sqrt ((∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 4 g s θ) / Work.Spaces.w s) :=
      add_le_add hDs_le (le_trans hDg_le (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hDg_sq_le)
        (Real.sqrt_nonneg _)))
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hsqrtHw : Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
        / Work.Spaces.w s)
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
        * (s / (1 + s)) := by
    rw [Real.sqrt_div hH0, hsqrt_w]
    field_simp
  rw [hsqrtHw] at hstep
  refine le_trans hstep ?_
  rw [hAdef, hBdef]
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hs1 : (1 + s) ≠ 0 := by positivity
  field_simp
  first | exact le_refl _ | ring | ring_nf | nlinarith


/-! ## The `s`-level integration -/

/-- `HkIntegrand` of `SmoothQuad` data is continuous on the open quadrant. -/
theorem continuousOn_HkIntegrand_Qd {f : ℝ → ℝ → ℝ} (hsq : Work.FTS.LocData.SmoothQuad f)
    (α : ℝ) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand
    (hsq.mono (Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)) subset_rfl)) α k

/-- The radial slice integral of `HkIntegrand` is a.e. strongly measurable on `(0,∞)`. -/
theorem aesm_HkSlice {f : ℝ → ℝ → ℝ} (hsq : Work.FTS.LocData.SmoothQuad f) (α : ℝ) (k : ℕ) :
    AEStronglyMeasurable (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f s θ)
      (volume.restrict (Set.Ioi 0)) := by
  have hjoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_HkIntegrand_Qd hsq α k)
  exact (hjoint.integral_prod_right' (μ := volume.restrict Work.Spaces.Iz)).mono_measure
    (MeasureTheory.Measure.restrict_mono Set.Ioi_subset_Ici_self le_rfl)

/-- `∫_{s>0} 1/(1+s)² ≤ 2`. -/
theorem integral_Ioi_inv_one_add_sq_le :
    (∫ s in Set.Ioi (0 : ℝ), 1 / (1 + s) ^ 2) ≤ 2 := by
  have hIntIz := Work.Coercivity.rb_integrableOn_inv_one_add_sq_Iz
  have hmono := MeasureTheory.setIntegral_mono_set hIntIz
    (Eventually.of_forall fun x => by positivity)
    (Eventually.of_forall fun x hx => Set.Ioi_subset_Ici_self hx)
  linarith [hmono, Work.Coercivity.rb_integral_Iz_inv_one_add_sq_le]

/-- `1/(1+s)² ∈ L¹((0,∞))`. -/
theorem integrableOn_Ioi_inv_one_add_sq :
    IntegrableOn (fun s : ℝ => 1 / (1 + s) ^ 2) (Set.Ioi 0) :=
  Work.Coercivity.rb_integrableOn_inv_one_add_sq_Iz.mono_set Set.Ioi_subset_Ici_self

/-- `∫_{s>0} √(∫_θ HkIntegrand α k f s θ)/(1+s) ≤ √2·|f|_{ℋ^k}`. -/
theorem integral_sqrt_HkSlice_le {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsq : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α k f) :
    (∫ s in Set.Ioi (0 : ℝ),
        Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f s θ) / (1 + s))
      ≤ Real.sqrt 2 * Work.Spaces.HkNorm α k f := by
  have haesm : AEStronglyMeasurable
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f s θ)
      (volume.restrict (Set.Ioi 0)) := aesm_HkSlice hsq α k
  have hint : IntegrableOn (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f s θ)
      (Set.Ioi 0) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hpoint : ∀ s, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f s θ :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f s θ
  have hu : MemLp (fun s => Real.sqrt (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f s θ)) 2 (volume.restrict (Set.Ioi 0)) := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable haesm)).mpr ?_
    exact hint.congr (Eventually.of_forall fun s => by simp only [Real.sq_sqrt (hpoint s)])
  have hv : MemLp (fun s : ℝ => 1 / (1 + s)) 2 (volume.restrict (Set.Ioi 0)) := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).mpr ?_
    · have hmeas : Measurable (fun s : ℝ => (1 : ℝ) / (1 + s)) :=
        measurable_const.div (measurable_const.add measurable_id)
      exact hmeas.aestronglyMeasurable
    · refine integrableOn_Ioi_inv_one_add_sq.congr ?_
      filter_upwards with s
      simp only [one_div, inv_pow]
  have hcs := Work.Spaces.cs_integral (u := fun s => Real.sqrt (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f s θ)) (v := fun s : ℝ => 1 / (1 + s))
    (s := Set.Ioi 0) hu hv
  have hspl : (∫ s in Set.Ioi (0 : ℝ), Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f s θ) * (1 / (1 + s)))
      = ∫ s in Set.Ioi (0 : ℝ), Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f s θ) / (1 + s) := by
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun s => ?_)
    ring
  rw [hspl] at hcs
  have hsq_le : (∫ s in Set.Ioi (0 : ℝ), (Real.sqrt (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f s θ)) ^ 2) ≤ Work.Spaces.HkSq α k f := by
    rw [show (∫ s in Set.Ioi (0 : ℝ), (Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f s θ)) ^ 2)
      = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k f s θ from
      MeasureTheory.integral_congr_ae (Eventually.of_forall fun s => by
        simp only [Real.sq_sqrt (hpoint s)])]
    have hmono := MeasureTheory.setIntegral_mono_set hmem.2
      (Eventually.of_forall fun x => hpoint x)
      (Eventually.of_forall fun x hx => Set.Ioi_subset_Ici_self hx)
    simpa only [Work.Spaces.HkSq] using hmono
  have hLHS : 0 ≤ ∫ s in Set.Ioi (0 : ℝ), Real.sqrt (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f s θ) / (1 + s) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hs
    exact div_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hbnd : (∫ s in Set.Ioi (0 : ℝ), Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f s θ) / (1 + s)) ^ 2
      ≤ Work.Spaces.HkSq α k f * 2 := by
    refine le_trans hcs ?_
    have hv2 : (∫ s in Set.Ioi (0 : ℝ), (1 / (1 + s)) ^ 2) ≤ 2 := by
      rw [show (∫ s in Set.Ioi (0 : ℝ), (1 / (1 + s)) ^ 2)
          = ∫ s in Set.Ioi (0 : ℝ), 1 / (1 + s) ^ 2 from
        MeasureTheory.integral_congr_ae (Eventually.of_forall fun s => by
          simp only [one_div, inv_pow])]
      exact integral_Ioi_inv_one_add_sq_le
    exact mul_le_mul hsq_le hv2 (integral_nonneg fun s => sq_nonneg _)
      (Work.Spaces.HkSq_nonneg α k f)
  have h1 : (∫ s in Set.Ioi (0 : ℝ), Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f s θ) / (1 + s))
      ≤ Real.sqrt (Work.Spaces.HkSq α k f * 2) := by
    rw [← Real.sqrt_sq hLHS]
    exact Real.sqrt_le_sqrt hbnd
  calc (∫ s in Set.Ioi (0 : ℝ), Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f s θ) / (1 + s))
      ≤ Real.sqrt (Work.Spaces.HkSq α k f * 2) := h1
    _ = Real.sqrt 2 * Work.Spaces.HkNorm α k f := by
        rw [Real.sqrt_mul (Work.Spaces.HkSq_nonneg α k f), Work.Spaces.HkNorm, mul_comm]

/-! ## Two elementary `α`-inequalities for the final arithmetic -/

/-- `α²·√(10/α) ≤ √10·√α` for `0 < α ≤ 1`. -/
theorem alpha_sq_mul_sqrt_div_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ 2 * Real.sqrt (10 / α) ≤ Real.sqrt 10 * Real.sqrt α := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 10) α]
  have hsp : Real.sqrt α * Real.sqrt α = α := by rw [← sq, Real.sq_sqrt hα.le]
  have hspos : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hL : α ^ 2 * (Real.sqrt 10 / Real.sqrt α) = Real.sqrt 10 * α ^ 2 / Real.sqrt α := by
    field_simp
  rw [hL, div_le_iff₀ hspos, mul_assoc, hsp]
  exact mul_le_mul_of_nonneg_left (by nlinarith [hα1, hα.le]) (Real.sqrt_nonneg 10)

/-- `√(1/α) ≤ α^{-3/2}` for `0 < α ≤ 1`. -/
theorem sqrt_inv_le_rpow {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.sqrt (1 / α) ≤ α ^ (-(3 / 2 : ℝ)) := by
  have hspos : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have h1 : α ^ (-(3 / 2 : ℝ)) = (α ^ (-(1 / 2 : ℝ))) * α ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hα]; norm_num
  rw [h1, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) α, Real.sqrt_one, one_div,
    Real.rpow_neg hα.le, Real.rpow_neg hα.le, Real.rpow_one, Real.sqrt_eq_rpow]
  have hinv : 1 ≤ α⁻¹ := by rw [one_le_inv₀ hα]; exact hα1
  have hnn : 0 ≤ (α ^ (1 / 2 : ℝ))⁻¹ := inv_nonneg.mpr (Real.rpow_nonneg hα.le _)
  calc (α ^ (1 / 2 : ℝ))⁻¹ = (α ^ (1 / 2 : ℝ))⁻¹ * 1 := by ring
    _ ≤ (α ^ (1 / 2 : ℝ))⁻¹ * α⁻¹ := mul_le_mul_of_nonneg_left hinv hnn

/-- The final arithmetic: the four terms of the expanded bound are dominated by
`K·(α² + √α X + α^{-3/2}X²)`. -/
theorem final_arith {α c₁ c₂ cs ce X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂) (hcs : 0 ≤ cs) (hce : 0 ≤ ce) (hX : 0 ≤ X) :
    6 * ((Real.pi / 2) * c₂) * (c₁ * cs * α) * α ^ 2
        + 3 * Real.sqrt Real.pi * (c₁ * cs * α) * X
        + 6 * ((Real.pi / 2) * c₂) * (10 * Real.sqrt (10 / α) * ce * X) * α ^ 2
        + 3 * Real.sqrt Real.pi * (10 * Real.sqrt (10 / α) * ce * X) * X
      ≤ (6 * c₁ * cs * ((Real.pi / 2) * c₂) + 3 * Real.sqrt Real.pi * c₁ * cs
          + 60 * Real.sqrt 10 * ce * ((Real.pi / 2) * c₂)
          + 30 * Real.sqrt (10 * Real.pi) * ce + 1)
        * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
  have hsqa : α ^ 2 ≤ α := by nlinarith
  have hsa : α ≤ Real.sqrt α := by
    rw [Real.le_sqrt hα.le hα.le]; exact hsqa
  have hkey1 : α ^ 2 * Real.sqrt (10 / α) ≤ Real.sqrt 10 * Real.sqrt α :=
    alpha_sq_mul_sqrt_div_le hα hα1
  have hkey2 : Real.sqrt (1 / α) ≤ α ^ (-(3 / 2 : ℝ)) := sqrt_inv_le_rpow hα hα1
  have hkey3 : Real.sqrt (10 / α) = Real.sqrt 10 * Real.sqrt (1 / α) := by
    rw [one_div, Real.sqrt_inv, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 10)]
    ring
  have h10pi : Real.sqrt Real.pi * Real.sqrt 10 = Real.sqrt (10 * Real.pi) := by
    rw [← Real.sqrt_mul Real.pi_pos.le 10]
    congr 1
    ring
  have hP1 : 0 ≤ (Real.pi / 2) * c₂ := by positivity
  have hspa : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
  have hrp : 0 ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  -- the four termwise bounds
  have h1 : 6 * ((Real.pi / 2) * c₂) * (c₁ * cs * α) * α ^ 2
      ≤ 6 * c₁ * cs * ((Real.pi / 2) * c₂) * α ^ 2 := by
    have hcoef : 0 ≤ 6 * ((Real.pi / 2) * c₂) * c₁ * cs := by positivity
    have hcube : α ^ 3 ≤ α ^ 2 := by nlinarith [hsqa, hα.le]
    calc 6 * ((Real.pi / 2) * c₂) * (c₁ * cs * α) * α ^ 2
        = (6 * ((Real.pi / 2) * c₂) * c₁ * cs) * α ^ 3 := by ring
      _ ≤ (6 * ((Real.pi / 2) * c₂) * c₁ * cs) * α ^ 2 := mul_le_mul_of_nonneg_left hcube hcoef
      _ = 6 * c₁ * cs * ((Real.pi / 2) * c₂) * α ^ 2 := by ring
  have h2 : 3 * Real.sqrt Real.pi * (c₁ * cs * α) * X
      ≤ 3 * Real.sqrt Real.pi * c₁ * cs * Real.sqrt α * X := by
    have hcoef : 0 ≤ 3 * Real.sqrt Real.pi * c₁ * cs * X := by positivity
    calc 3 * Real.sqrt Real.pi * (c₁ * cs * α) * X
        = (3 * Real.sqrt Real.pi * c₁ * cs * X) * α := by ring
      _ ≤ (3 * Real.sqrt Real.pi * c₁ * cs * X) * Real.sqrt α :=
          mul_le_mul_of_nonneg_left hsa hcoef
      _ = 3 * Real.sqrt Real.pi * c₁ * cs * Real.sqrt α * X := by ring
  have h3 : 6 * ((Real.pi / 2) * c₂) * (10 * Real.sqrt (10 / α) * ce * X) * α ^ 2
      ≤ 60 * Real.sqrt 10 * ce * ((Real.pi / 2) * c₂) * (Real.sqrt α * X) := by
    have hcoef : 0 ≤ 60 * ((Real.pi / 2) * c₂) * ce * X := by positivity
    calc 6 * ((Real.pi / 2) * c₂) * (10 * Real.sqrt (10 / α) * ce * X) * α ^ 2
        = (60 * ((Real.pi / 2) * c₂) * ce * X) * (α ^ 2 * Real.sqrt (10 / α)) := by ring
      _ ≤ (60 * ((Real.pi / 2) * c₂) * ce * X) * (Real.sqrt 10 * Real.sqrt α) :=
          mul_le_mul_of_nonneg_left hkey1 hcoef
      _ = 60 * Real.sqrt 10 * ce * ((Real.pi / 2) * c₂) * (Real.sqrt α * X) := by ring
  have h4 : 3 * Real.sqrt Real.pi * (10 * Real.sqrt (10 / α) * ce * X) * X
      ≤ 30 * Real.sqrt (10 * Real.pi) * ce * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    have hcoef : 0 ≤ 30 * ce * X ^ 2 * Real.sqrt Real.pi := by positivity
    calc 3 * Real.sqrt Real.pi * (10 * Real.sqrt (10 / α) * ce * X) * X
        = (30 * ce * X ^ 2 * Real.sqrt Real.pi) * Real.sqrt (10 / α) := by ring
      _ = (30 * ce * X ^ 2 * Real.sqrt Real.pi) * (Real.sqrt 10 * Real.sqrt (1 / α)) := by
          rw [hkey3]
      _ ≤ (30 * ce * X ^ 2 * Real.sqrt Real.pi) * (Real.sqrt 10 * α ^ (-(3 / 2 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hcoef
          exact mul_le_mul_of_nonneg_left hkey2 (Real.sqrt_nonneg 10)
      _ = (30 * (Real.sqrt Real.pi * Real.sqrt 10) * ce * X ^ 2) * α ^ (-(3 / 2 : ℝ)) := by
          ring
      _ = 30 * Real.sqrt (10 * Real.pi) * ce * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
          rw [h10pi]; ring
  have hsum : 6 * ((Real.pi / 2) * c₂) * (c₁ * cs * α) * α ^ 2
        + 3 * Real.sqrt Real.pi * (c₁ * cs * α) * X
        + 6 * ((Real.pi / 2) * c₂) * (10 * Real.sqrt (10 / α) * ce * X) * α ^ 2
        + 3 * Real.sqrt Real.pi * (10 * Real.sqrt (10 / α) * ce * X) * X
      ≤ (6 * c₁ * cs * ((Real.pi / 2) * c₂)) * α ^ 2
        + (3 * Real.sqrt Real.pi * c₁ * cs) * (Real.sqrt α * X)
        + (60 * Real.sqrt 10 * ce * ((Real.pi / 2) * c₂)) * (Real.sqrt α * X)
        + (30 * Real.sqrt (10 * Real.pi) * ce) * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    linarith [h1, h2, h3, h4]
  have hnn : 0 ≤ α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by
    have h1' : 0 ≤ α ^ 2 := sq_nonneg α
    have h2' : 0 ≤ Real.sqrt α * X := mul_nonneg hspa hX
    have h3' : 0 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 := mul_nonneg hrp hX2
    linarith
  have hfinal : (6 * c₁ * cs * ((Real.pi / 2) * c₂)) * α ^ 2
        + (3 * Real.sqrt Real.pi * c₁ * cs) * (Real.sqrt α * X)
        + (60 * Real.sqrt 10 * ce * ((Real.pi / 2) * c₂)) * (Real.sqrt α * X)
        + (30 * Real.sqrt (10 * Real.pi) * ce) * (α ^ (-(3 / 2 : ℝ)) * X ^ 2)
      ≤ (6 * c₁ * cs * ((Real.pi / 2) * c₂) + 3 * Real.sqrt Real.pi * c₁ * cs
          + 60 * Real.sqrt 10 * ce * ((Real.pi / 2) * c₂)
          + 30 * Real.sqrt (10 * Real.pi) * ce + 1)
        * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    have hc1 : 0 ≤ 6 * c₁ * cs * ((Real.pi / 2) * c₂) := by positivity
    have hc2 : 0 ≤ 3 * Real.sqrt Real.pi * c₁ * cs := by positivity
    have hc3 : 0 ≤ 60 * Real.sqrt 10 * ce * ((Real.pi / 2) * c₂) := by positivity
    have hc4 : 0 ≤ 30 * Real.sqrt (10 * Real.pi) * ce := by positivity
    have f1 : 0 ≤ α ^ 2 := sq_nonneg α
    have f2 : 0 ≤ Real.sqrt α * X := mul_nonneg hspa hX
    have f3 : 0 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 := mul_nonneg hrp hX2
    nlinarith [hnn, mul_nonneg hc1 f2, mul_nonneg hc1 f3, mul_nonneg hc2 f1, mul_nonneg hc2 f3,
      mul_nonneg hc3 f1, mul_nonneg hc3 f2, mul_nonneg hc4 f1, mul_nonneg hc4 f2]
  linarith [hsum, hfinal]

theorem n2Bound {α₂ Ci Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      (∫ s in Set.Ioi (0 : ℝ), ‖Work.Construction.L12dens (Work.Construction.N2 α
          (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) s‖)
        ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨c₁, hc₁pos, hStarU₀⟩ := StarUBound
  obtain ⟨c₂, hc₂pos, hDthFs₀⟩ := DthFstarPoint
  refine ⟨6 * c₁ * max Cs 0 * ((Real.pi / 2) * c₂) + 3 * Real.sqrt Real.pi * c₁ * max Cs 0
      + 60 * Real.sqrt 10 * max Ce 0 * ((Real.pi / 2) * c₂)
      + 30 * Real.sqrt (10 * Real.pi) * max Ce 0 + 1, ?_, ?_⟩
  · have h1 : 0 ≤ max Cs 0 := le_max_right _ _
    have h2 : 0 ≤ max Ce 0 := le_max_right _ _
    have h3 : 0 < (Real.pi / 2) * c₂ := by positivity
    have h4 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have h5 : 0 < Real.sqrt 10 := Real.sqrt_pos.mpr (by norm_num)
    have h6 : 0 < Real.sqrt (10 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have h7 : 0 ≤ 6 * c₁ * max Cs 0 * ((Real.pi / 2) * c₂) := by positivity
    have h8 : 0 ≤ 3 * Real.sqrt Real.pi * c₁ * max Cs 0 := by positivity
    have h9 : 0 ≤ 60 * Real.sqrt 10 * max Ce 0 * ((Real.pi / 2) * c₂) := by positivity
    have h10 : 0 ≤ 30 * Real.sqrt (10 * Real.pi) * max Ce 0 := by positivity
    linarith
  · intro α g Φs Φg hgal hs hell hα hα1 hαα₂
    have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hcs : 0 ≤ max Cs 0 := le_max_right _ _
    have hce : 0 ≤ max Ce 0 := le_max_right _ _
    have hsq : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
    have hmem4 : Work.Spaces.HkMem α 4 g := (Work.FTS.Nonlin.galClass_regQ4 hgal).2.1
    have hL12 : ∀ z : ℝ, 0 < z →
        DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z :=
      fun z hz => hN.l12diff α ⟨hα, hαα₂⟩ g hsq hmem4 z hz
    have hStarU : ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ c₁ * max Cs 0 * α :=
      fun z hz θ hθ => hStarU₀ hs hα hα1 z hz θ hθ
    have hDthFs : ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| ≤ c₂ * α ^ 2 * (z / (1 + z) ^ 2) :=
      fun z hz θ hθ => hDthFs₀ α hα hα1 z hz θ hθ
    have hAgB : ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ|
          ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g := by
      intro z hz θ hθ
      rcases eq_or_lt_of_le hθ.1 with h0 | hpos
      · subst h0
        rw [show Work.Construction.s2 0 = 0 from by
          rw [Work.Construction.s2, mul_zero, Real.sin_zero], div_zero, abs_zero]
        have := Work.Spaces.HkNorm_nonneg α 4 g
        positivity
      rcases eq_or_lt_of_le hθ.2 with h2 | h2
      · rw [h2]
        rw [show Work.Construction.s2 (π / 2) = 0 from by
          rw [Work.Construction.s2, show 2 * (π / 2) = Real.pi from by ring, Real.sin_pi],
          div_zero, abs_zero]
        have := Work.Spaces.HkNorm_nonneg α 4 g
        positivity
      · exact (Work.FTS.Nonlinear.Pieces.rl1Tools.gPt hα hα1 hell).2.1 z hz θ hpos h2
    set A : ℝ := c₁ * max Cs 0 * α with hAdef
    set B : ℝ := 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g with hBdef
    set Hg : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ
      with hHgdef
    have hA0 : 0 ≤ A := by rw [hAdef]; positivity
    have hB0 : 0 ≤ B := by rw [hBdef]; positivity
    have hdens : ∀ s : ℝ, 0 < s → ‖Work.Construction.L12dens (Work.Construction.N2 α
          (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) s‖
        ≤ 3 * (A + B) * ((Real.pi / 2) * c₂ * α ^ 2 / (1 + s) ^ 2
            + Real.sqrt (Real.pi / 2) * Real.sqrt (Hg s) / (1 + s)) := by
      intro s hspos
      have h := density_bound hα hα1 hc₁pos.le hgal hs hell hStarU hAgB hDthFs hL12 hspos
      rw [hAdef, hBdef, hHgdef]
      exact h
    -- integrability
    have hHg_int : IntegrableOn Hg (Set.Ioi 0) := by
      rw [hHgdef]
      exact hmem4.2.mono_set Set.Ioi_subset_Ici_self
    have hsqrt_int : IntegrableOn (fun s => Real.sqrt (Hg s) / (1 + s)) (Set.Ioi 0) := by
      have haesm : AEStronglyMeasurable (fun s => Real.sqrt (Hg s) / (1 + s))
          (volume.restrict (Set.Ioi 0)) := by
        have h1 : AEStronglyMeasurable (fun s => Real.sqrt (Hg s))
            (volume.restrict (Set.Ioi 0)) :=
          Real.continuous_sqrt.comp_aestronglyMeasurable (aesm_HkSlice hsq α 4)
        have h2 : AEStronglyMeasurable (fun s : ℝ => (1 + s)⁻¹)
            (volume.restrict (Set.Ioi 0)) :=
          ((measurable_const.add measurable_id).inv).aestronglyMeasurable
        exact (h1.mul h2).congr (Eventually.of_forall fun s => by
          simp only [Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv])
      refine Integrable.mono' ((hHg_int.add integrableOn_Ioi_inv_one_add_sq).div_const 2)
        haesm ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hs0 : 0 < s := hs
      have hHg0 : 0 ≤ Hg s := by
        rw [hHgdef]
        exact integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ
      have h1s : (0 : ℝ) < 1 + s := by linarith
      have hAM : Real.sqrt (Hg s) / (1 + s) ≤ (Hg s + 1 / (1 + s) ^ 2) / 2 := by
        have hb : ((1 + s)⁻¹) ^ 2 = (1 : ℝ) / (1 + s) ^ 2 := by field_simp
        rw [← hb, div_eq_mul_inv (Real.sqrt (Hg s)) (1 + s)]
        nlinarith [Real.sq_sqrt hHg0, sq_nonneg (Real.sqrt (Hg s) - (1 + s)⁻¹)]
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) h1s.le)]
      exact hAM
    have hmaj_int : IntegrableOn (fun s => 3 * (A + B) * ((Real.pi / 2) * c₂ * α ^ 2 / (1 + s) ^ 2
        + Real.sqrt (Real.pi / 2) * Real.sqrt (Hg s) / (1 + s))) (Set.Ioi 0) := by
      have h1 : IntegrableOn (fun s => ((Real.pi / 2) * c₂ * α ^ 2) * (1 / (1 + s) ^ 2))
          (Set.Ioi 0) := integrableOn_Ioi_inv_one_add_sq.const_mul _
      have h2 : IntegrableOn (fun s => Real.sqrt (Real.pi / 2) * (Real.sqrt (Hg s) / (1 + s)))
          (Set.Ioi 0) := hsqrt_int.const_mul _
      have h3 : IntegrableOn (fun s => ((Real.pi / 2) * c₂ * α ^ 2) * (1 / (1 + s) ^ 2)
          + Real.sqrt (Real.pi / 2) * (Real.sqrt (Hg s) / (1 + s))) (Set.Ioi 0) := h1.add h2
      refine (h3.const_mul (3 * (A + B))).congr ?_
      filter_upwards with s
      ring
    have hmain : (∫ s in Set.Ioi 0, ‖Work.Construction.L12dens (Work.Construction.N2 α
          (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) s‖)
        ≤ ∫ s in Set.Ioi 0, 3 * (A + B) * ((Real.pi / 2) * c₂ * α ^ 2 / (1 + s) ^ 2
            + Real.sqrt (Real.pi / 2) * Real.sqrt (Hg s) / (1 + s)) :=
      MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun s => norm_nonneg _) hmaj_int
        (by filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
            exact hdens s hs)
    have hsplit : (∫ s in Set.Ioi 0, 3 * (A + B) * ((Real.pi / 2) * c₂ * α ^ 2 / (1 + s) ^ 2
          + Real.sqrt (Real.pi / 2) * Real.sqrt (Hg s) / (1 + s)))
        = 3 * (A + B) * (((Real.pi / 2) * c₂ * α ^ 2) * (∫ s in Set.Ioi 0, 1 / (1 + s) ^ 2)
            + Real.sqrt (Real.pi / 2) * (∫ s in Set.Ioi 0, Real.sqrt (Hg s) / (1 + s))) := by
      have hfun : (fun s => 3 * (A + B) * ((Real.pi / 2) * c₂ * α ^ 2 / (1 + s) ^ 2
            + Real.sqrt (Real.pi / 2) * Real.sqrt (Hg s) / (1 + s)))
          = fun s => 3 * (A + B) * (((Real.pi / 2) * c₂ * α ^ 2) * (1 / (1 + s) ^ 2)
            + Real.sqrt (Real.pi / 2) * (Real.sqrt (Hg s) / (1 + s))) := by
        funext s; ring
      rw [hfun, MeasureTheory.integral_const_mul]
      have h1 : IntegrableOn (fun s => ((Real.pi / 2) * c₂ * α ^ 2) * (1 / (1 + s) ^ 2))
          (Set.Ioi 0) := integrableOn_Ioi_inv_one_add_sq.const_mul _
      have h2 : IntegrableOn (fun s => Real.sqrt (Real.pi / 2) * (Real.sqrt (Hg s) / (1 + s)))
          (Set.Ioi 0) := hsqrt_int.const_mul _
      rw [MeasureTheory.integral_add h1 h2, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
    have hI1 : (∫ s : ℝ in Set.Ioi (0 : ℝ), 1 / (1 + s) ^ 2) ≤ 2 :=
      integral_Ioi_inv_one_add_sq_le
    have hI2 : (∫ s : ℝ in Set.Ioi (0 : ℝ), Real.sqrt (Hg s) / (1 + s))
        ≤ Real.sqrt 2 * Work.FTS.Nonlin.Xn α g := by
      rw [hHgdef]
      exact integral_sqrt_HkSlice_le hsq hmem4
    have hpi2 : Real.sqrt (Real.pi / 2) * Real.sqrt 2 = Real.sqrt Real.pi := by
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
      congr 1
      ring
    have h3AB : 0 ≤ 3 * (A + B) := by linarith
    have hinner : ((Real.pi / 2) * c₂ * α ^ 2) * (∫ s in Set.Ioi 0, 1 / (1 + s) ^ 2)
          + Real.sqrt (Real.pi / 2) * (∫ s in Set.Ioi 0, Real.sqrt (Hg s) / (1 + s))
        ≤ ((Real.pi / 2) * c₂ * α ^ 2) * 2
          + Real.sqrt (Real.pi / 2) * (Real.sqrt 2 * Work.FTS.Nonlin.Xn α g) :=
      add_le_add (mul_le_mul_of_nonneg_left hI1 (by positivity))
        (mul_le_mul_of_nonneg_left hI2 (Real.sqrt_nonneg _))
    refine le_trans hmain ?_
    rw [hsplit]
    refine le_trans (mul_le_mul_of_nonneg_left hinner h3AB) ?_
    have hrewrite : 3 * (A + B) * (((Real.pi / 2) * c₂ * α ^ 2) * 2
          + Real.sqrt (Real.pi / 2) * (Real.sqrt 2 * Work.FTS.Nonlin.Xn α g))
        = 3 * (A + B) * (2 * ((Real.pi / 2) * c₂ * α ^ 2)
            + Real.sqrt Real.pi * Work.FTS.Nonlin.Xn α g) := by
      rw [show Real.sqrt (Real.pi / 2) * (Real.sqrt 2 * Work.FTS.Nonlin.Xn α g)
          = (Real.sqrt (Real.pi / 2) * Real.sqrt 2) * Work.FTS.Nonlin.Xn α g from by ring, hpi2]
      ring
    rw [hrewrite]
    have hexpand : 3 * (A + B) * (2 * ((Real.pi / 2) * c₂ * α ^ 2)
          + Real.sqrt Real.pi * Work.FTS.Nonlin.Xn α g)
        = 6 * ((Real.pi / 2) * c₂) * (c₁ * max Cs 0 * α) * α ^ 2
          + 3 * Real.sqrt Real.pi * (c₁ * max Cs 0 * α) * Work.FTS.Nonlin.Xn α g
          + 6 * ((Real.pi / 2) * c₂) * (10 * Real.sqrt (10 / α) * max Ce 0
              * Work.FTS.Nonlin.Xn α g) * α ^ 2
          + 3 * Real.sqrt Real.pi * (10 * Real.sqrt (10 / α) * max Ce 0
              * Work.FTS.Nonlin.Xn α g) * Work.FTS.Nonlin.Xn α g := by
      rw [hAdef, hBdef]
      ring
    rw [hexpand]
    have hFA := final_arith (α := α) (c₁ := c₁) (c₂ := c₂) (cs := max Cs 0) (ce := max Ce 0)
      (X := Work.FTS.Nonlin.Xn α g) hα hα1 hc₁pos hc₂pos hcs hce hX0
    linarith [hFA]

end Work.FTS.Nonlinear.Pieces.Rl1
