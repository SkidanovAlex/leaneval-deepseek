import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_StreamBdry.SB4.lim_mixed_plainE
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS_MuLipC.LinQuad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_MuLipC

open Work.FTS.Galerkin (Fn Fam slice muDyn)

set_option autoImplicit false

/-! ## The `N₀` block -/

/-- The `g`-independent part of `N₀ α (F_*+g) g`. -/
def C0 (α : ℝ) : Fn := fun z θ =>
  (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ







/-! ## The `N` block -/

/-- The part of `Φ̃ = Φ − (1/(4α))·sin(2θ)·L₁₂(F)` that is *linear* in the profile `g`, when
`F = F_* + g` and `Φ = Φ_s + E g`: `U_g = E g − (1/(4α))·sin(2θ)·L₁₂(g)`. -/
def Ug (α : ℝ) (E : Fn → Fn) (g : Fn) : Fn := fun z θ =>
  E g z θ - (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g z

/-- The `g`-independent part of `N α (F_*+g) (Φ_s + E g)`. -/
def C1 (α : ℝ) (Φs : Fn) : Fn := fun z θ =>
  2 * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      * Work.Construction.Fstar α z θ
    - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
    - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Construction.Fstar α z θ

/-- The part of `N α (F_*+g) (Φ_s + E g)` linear in `g`. -/
def Lin1 (α : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fn) : Fn := fun z θ =>
  2 * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      * g z θ
    - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      * Work.Spaces.pth g z θ
    - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      * Work.Spaces.Dz g z θ
    + 2 * Work.Construction.Rop α (Ug α E g) z θ * Work.Construction.Fstar α z θ
    - 2 * Work.Construction.Uop α (Ug α E g) z θ
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - 2 * α * Work.Construction.Vop (Ug α E g) z θ
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
    - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.pth g z θ
    - Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z * g z θ
    - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK g z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - Real.sin θ ^ 2 * Work.Construction.FK g z * Work.Construction.Fstar α z θ

/-- The part of `N α (F_*+g) (Φ_s + E g)` quadratic in `g`. -/
def Quad1 (α : ℝ) (E : Fn → Fn) (g : Fn) : Fn := fun z θ =>
  2 * Work.Construction.Rop α (Ug α E g) z θ * g z θ
    - 2 * Work.Construction.Uop α (Ug α E g) z θ * Work.Spaces.pth g z θ
    - 2 * α * Work.Construction.Vop (Ug α E g) z θ * Work.Spaces.Dz g z θ
    - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK g z * Work.Spaces.pth g z θ
    - Real.sin θ ^ 2 * Work.Construction.FK g z * g z θ

/-- The symmetric bilinear form of `Quad1`: `Quad1 α E u = Bil1 α E u u` and
`Quad1 α E (u+d) = Quad1 α E u + Bil1 α E u d + Bil1 α E d u + Quad1 α E d` (the second identity
needs `E` additive, `L₁₂`-additivity on the profiles and the additivity of `Rop`, `Uop`, `Vop`,
`FK`, `pth`, `Dz` on the relevant sums). -/
def Bil1 (α : ℝ) (E : Fn → Fn) (u d : Fn) : Fn := fun z θ =>
  2 * Work.Construction.Rop α (Ug α E u) z θ * d z θ
    - 2 * Work.Construction.Uop α (Ug α E u) z θ * Work.Spaces.pth d z θ
    - 2 * α * Work.Construction.Vop (Ug α E u) z θ * Work.Spaces.Dz d z θ
    - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK u z * Work.Spaces.pth d z θ
    - Real.sin θ ^ 2 * Work.Construction.FK u z * d z θ


end Work.FTS_MuLipC
end
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowN.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The elliptic residual of a perturbation -/

/-- `Φ̃_g = PhiTil α g (E g)`. -/
def PhiTilg (α : ℝ) (E : Fn → Fn) (g : Fn) : Fn :=
  fun z θ => E g z θ
    - (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g z

/-- The star part `Φ̃_* = PhiTil α F_* Φ_s`. -/
def Zs (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => Φs z θ
    - (1 / (4 * α)) * Work.Construction.s2 θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z



@[simp] theorem PhiTilg_apply (α : ℝ) (E : Fn → Fn) (g : Fn) (z θ : ℝ) :
    PhiTilg α E g z θ = E g z θ
      - (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g z := rfl

@[simp] theorem Zs_apply (α : ℝ) (Φs : Fn) (z θ : ℝ) :
    Zs α Φs z θ = Φs z θ
      - (1 / (4 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z := rfl

/-! ## The atoms -/









/-! ## The constant parts -/

/-- `F_*`. -/
def cF (α : ℝ) : Fn := Work.Construction.Fstar α



/-- `FK F_*`. -/
def cK (α : ℝ) : Fn := fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z

/-- `ℛ(Φ̃_*)`. -/
def cR (α : ℝ) (Φs : Fn) : Fn := Work.Construction.Rop α (Zs α Φs)



end Work.FTS_MuLipC.RowN
end
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowT.Tf_dens_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowT

set_option autoImplicit false

/-! ## Elementary bounds

Two elementary facts are used repeatedly below: `|K θ| ≤ 3` on the whole line, and
`√(w s) = (1+s)/s` for `s > 0` (the weight is `w s = (1+s)²/s²`). -/

/-- `|K θ| ≤ 3` for every `θ`. -/
lemma abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hcos0 : (0 : ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hcos1 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num),
    abs_of_nonneg hcos0]
  calc 3 * |Real.sin θ| * Real.cos θ ^ 2
      ≤ 3 * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsin (by norm_num : (0 : ℝ) ≤ 3)) hcos1 hcos0
          (by norm_num)
    _ = 3 := by norm_num

/-- `√(w s) = (1+s)/s` for `s > 0`. -/
lemma sqrt_w_eq {s : ℝ} (hs : 0 < s) : Real.sqrt (Work.Spaces.w s) = (1 + s) / s := by
  rw [Work.Spaces.w, Real.sqrt_div' ((1 + s) ^ 2) (by positivity : (0 : ℝ) ≤ s ^ 2),
    Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 1 + s), Real.sqrt_sq (le_of_lt hs)]

/-- `√x ≤ 1 + x` for `x ≥ 0`. -/
lemma sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  rw [Real.sqrt_le_iff]
  exact ⟨by linarith, by nlinarith⟩

/-! ## The pointwise bound on the angular integrand

The single pointwise input is `dth_sq_mul_w_le_HkIntegrand`,
`(D_θg s θ)²·w s ≤ HkIntegrand α 4 g s θ` on the open quadrant, together with the identity
`√(w s)·s = 1 + s`. -/

/-- For `s > 0` and `θ ∈ (0,π/2)` the transport integrand is dominated by
`9/(1+s)²·√(HkIntegrand α 4 g s θ)`. -/
lemma abs_K_mul_Tf_le {α s θ : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} (hs : 0 < s)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ‖Work.Spaces.K θ * Work.FTS_MuLipC.Tf g s θ / s‖
      ≤ 9 / (1 + s) ^ 2 * Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hs1 : (1 : ℝ) + s ≠ 0 := by positivity
  have hw : 0 ≤ Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  -- the `D_θ`-factor: `|D_θ g s θ| ≤ √Hk · s/(1+s)`
  have hkey : (Work.Spaces.Dth g s θ * Real.sqrt (Work.Spaces.w s)) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
    have h := Work.FTS.Nonlinear.Pieces.dth_sq_mul_w_le_HkIntegrand α g hα hs hθ
    calc (Work.Spaces.Dth g s θ * Real.sqrt (Work.Spaces.w s)) ^ 2
        = Work.Spaces.Dth g s θ ^ 2 * Work.Spaces.w s := by
          rw [mul_pow, Real.sq_sqrt hw]
      _ ≤ Work.Spaces.HkIntegrand α 4 g s θ := h
  have hDax : |Work.Spaces.Dth g s θ| * ((1 + s) / s)
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) := by
    have h := Real.abs_le_sqrt hkey
    rwa [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), sqrt_w_eq hs] at h
  have hD : |Work.Spaces.Dth g s θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) * s / (1 + s) := by
    have hcancel : ((1 + s) / s) * (s / (1 + s)) = 1 := by field_simp
    have hmul := mul_le_mul_of_nonneg_right hDax (by positivity : (0 : ℝ) ≤ s / (1 + s))
    have h1 : (|Work.Spaces.Dth g s θ| * ((1 + s) / s)) * (s / (1 + s))
        = |Work.Spaces.Dth g s θ| := by rw [mul_assoc, hcancel, mul_one]
    calc |Work.Spaces.Dth g s θ|
        = (|Work.Spaces.Dth g s θ| * ((1 + s) / s)) * (s / (1 + s)) := h1.symm
      _ ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) * (s / (1 + s)) := hmul
      _ = Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) * s / (1 + s) := by ring
  -- the coefficient
  have hA : ‖Work.Spaces.K θ * 3 / ((1 + s) * s)‖ ≤ 9 / ((1 + s) * s) := by
    have hden : (0 : ℝ) < (1 + s) * s := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_div_iff_of_pos_right hden]
    have h2 : |Work.Spaces.K θ * 3| = |Work.Spaces.K θ| * 3 := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)]
    rw [h2]
    nlinarith [abs_K_le_three θ]
  -- the factorisation `K·Tf/s = (K·3/((1+s)s))·D_θg`
  have hfac : Work.Spaces.K θ * Work.FTS_MuLipC.Tf g s θ / s
      = (Work.Spaces.K θ * 3 / ((1 + s) * s)) * Work.Spaces.Dth g s θ := by
    rw [Work.FTS_MuLipC.Tf_apply]
    field_simp
  calc ‖Work.Spaces.K θ * Work.FTS_MuLipC.Tf g s θ / s‖
      = ‖Work.Spaces.K θ * 3 / ((1 + s) * s)‖ * ‖Work.Spaces.Dth g s θ‖ := by
        rw [hfac, norm_mul]
    _ ≤ (9 / ((1 + s) * s))
          * (Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) * s / (1 + s)) :=
        mul_le_mul hA hD (norm_nonneg _) (by positivity)
    _ = 9 / (1 + s) ^ 2 * Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) := by
        field_simp

/-! ## The density estimate at fixed `s` -/

/-- For `s > 0` the density of the transport field is bounded by `9/(1+s)²` times the angular
integral of `√(HkIntegrand α 4 g)`. -/
lemma abs_L12dens_Tf_le {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ} (hs : 0 < s) :
    |Work.Construction.L12dens (Work.FTS_MuLipC.Tf g) s|
      ≤ 9 / (1 + s) ^ 2
        * ((∫ θ in Work.Spaces.Iθ, (1 : ℝ))
            + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
  have hIoo_ae : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    MeasureTheory.Ioo_ae_eq_Icc.symm
  -- the a.e. pointwise bound on the angular slice
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K θ * Work.FTS_MuLipC.Tf g s θ / s‖
        ≤ 9 / (1 + s) ^ 2 * Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) := by
    rw [MeasureTheory.Measure.restrict_congr_set hIoo_ae]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => abs_K_mul_Tf_le hα hs hθ)
  -- integrability of the angular pieces
  have hHk : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g s θ) Work.Spaces.Iθ :=
    hmem.1 s hs.le
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    continuous_const.integrableOn_Icc
  have h1Hk : IntegrableOn (fun θ => (1 : ℝ) + Work.Spaces.HkIntegrand α 4 g s θ)
      Work.Spaces.Iθ := h1.add hHk
  have hsqrt_le : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ)
        ≤ 1 + Work.Spaces.HkIntegrand α 4 g s θ :=
    Filter.Eventually.of_forall fun θ =>
      sqrt_le_one_add (Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
  have hsqrt_le_norm : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ)‖
        ≤ 1 + Work.Spaces.HkIntegrand α 4 g s θ := by
    filter_upwards [hsqrt_le] with θ hθ
    rwa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsqrt_int : IntegrableOn (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ))
      Work.Spaces.Iθ :=
    h1Hk.mono' (Real.continuous_sqrt.comp_aestronglyMeasurable hHk.aestronglyMeasurable)
      hsqrt_le_norm
  have hInt_le : ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ)
      ≤ ∫ θ in Work.Spaces.Iθ, ((1 : ℝ) + Work.Spaces.HkIntegrand α 4 g s θ) :=
    MeasureTheory.integral_mono_ae hsqrt_int h1Hk hsqrt_le
  have hInt_eq : ∫ θ in Work.Spaces.Iθ, ((1 : ℝ) + Work.Spaces.HkIntegrand α 4 g s θ)
      = (∫ θ in Work.Spaces.Iθ, (1 : ℝ))
        + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ :=
    MeasureTheory.integral_add h1 hHk
  calc |Work.Construction.L12dens (Work.FTS_MuLipC.Tf g) s|
      = ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS_MuLipC.Tf g s θ / s‖ := by
        rw [Real.norm_eq_abs]
        congr 1
    _ ≤ ∫ θ in Work.Spaces.Iθ, ‖Work.Spaces.K θ * Work.FTS_MuLipC.Tf g s θ / s‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ θ in Work.Spaces.Iθ,
          9 / (1 + s) ^ 2 * Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) :=
        MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => norm_nonneg _)
          (hsqrt_int.const_mul _) hpt
    _ = 9 / (1 + s) ^ 2
          * ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ 9 / (1 + s) ^ 2
          * ((∫ θ in Work.Spaces.Iθ, (1 : ℝ))
              + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← hInt_eq]
        exact hInt_le

/-! ## Integrability of the radial weight -/

/-- `s ↦ (1+s)^{-2}` is integrable on `(0,∞)`. -/
lemma integrableOn_one_add_pow_neg_two :
    IntegrableOn (fun s : ℝ => (1 + s) ^ (-(2 : ℝ))) (Set.Ioi 0) := by
  have h : IntegrableOn (fun s : ℝ => (s + 1) ^ (-(2 : ℝ))) (Set.Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt (a := -(2 : ℝ)) (c := 0) (m := 1) (by norm_num)
      (by norm_num)
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  rw [add_comm]

/-- **The `L₁₂`-density of the transport field is `L¹`.**  For a profile `g` which is `C^∞` on the
open quadrant `(0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.SmoothOpen`) and honestly in `ℋ⁴_α`
(`Work.Spaces.HkMem α 4 g`), the `L₁₂`-density of the transport field
`Work.FTS_MuLipC.Tf g = fun z θ => 3·D_θg z θ/(1+z)`,
`Work.Construction.L12dens (Tf g) = fun s => ∫ θ in Iθ, K θ · Tf g s θ / s`,
is integrable on `(0,∞)`.  This is precisely the `h3`/`h4` input of
`Work.FTS.LocData.L12_add_mul` at the fields `a = Tf f'`, `b = Tf (f - f')`, and together with
`Work.FTS_MuLipC.RowT.Tf_slice_integrable` it is what makes the transport zero-mode additive over
a difference of class-`C` profiles.

Route.  A.e. strong measurability: the integrand `(s,θ) ↦ K θ · Tf g s θ/s` is continuous on the
open quadrant `Q0` (from `hg.Dth.continuousOn`, continuity of `K`, and `s > 0`), so
`Work.Spaces.aesm_of_continuousOn_Qd` + `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`
give it — exactly as in `Work.FTS.GalBasis.cc.aesm_L12dens_of_SmoothOpen` (whose proof can be
copied verbatim with `Tf g` in place of `F`).  Integrability: the pointwise domination
`|D_θg s θ| ≤ √(HkIntegrand α 4 g s θ)/w s` (`s > 0`, `θ ∈ (0,π/2)`, from
`Work.FTS.Nonlinear.Pieces.slot_mixed_le_HkIntegrand` at `(j,i) = (0,1)`, `mixed 0 1 g = D_θ g`,
plus `Wt α s θ = w s·sin(2θ)^{-γ/2}` and `sin(2θ)^{-γ} ≥ 1`) gives, for `s > 0`,
`|L12dens (Tf g) s| ≤ ∫ θ in Iθ, 9s/(1+s)³·√(HkIntegrand α 4 g s θ)
   ≤ 9s/(1+s)³·(π/4 + H s/2)`, `H s := ∫ θ in Iθ, HkIntegrand α 4 g s θ`,
using `‖∫‖ ≤ ∫‖·‖` and `√x ≤ (1+x)/2`.  The majorant is integrable on `(0,∞)`:
`s ↦ s/(1+s)³` is integrable there, and `s/(1+s)³ ≤ 4/27` for `s ≥ 0`, so the second summand is
dominated by `(2/3)·H` with `H` integrable by `hmem.2`. -/
theorem Tf_dens_integrable {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS_MuLipC.Tf g))
      (Set.Ioi (0 : ℝ)) := by
  -- a.e. strong measurability of the density, from continuity of the integrand on the quadrant
  have hcontK : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hjoint : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.K p.2 * Work.FTS_MuLipC.Tf g p.1 p.2 / p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hDth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth g p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hg.Dth.continuousOn
    have hnum : ContinuousOn (fun p : ℝ × ℝ => (3 : ℝ) * Work.Spaces.Dth g p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_const.mul hDth
    have hden : ContinuousOn (fun p : ℝ × ℝ => 1 + p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_const.add continuousOn_fst
    have hTf : ContinuousOn (fun p : ℝ × ℝ => Work.FTS_MuLipC.Tf g p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      hnum.div hden (fun p hp => by
        have h1 : (0 : ℝ) < p.1 := (Set.mem_prod.mp hp).1
        positivity)
    have hK2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hcontK.comp continuous_snd).continuousOn
    exact (hK2.mul hTf).div continuousOn_fst (fun p hp => by
      have h1 : (0 : ℝ) < p.1 := (Set.mem_prod.mp hp).1
      positivity)
  have haesm : AEStronglyMeasurable (Work.Construction.L12dens (Work.FTS_MuLipC.Tf g))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hjointAesm := Work.Spaces.aesm_of_continuousOn_Qd _ hjoint
    have h3 := hjointAesm.integral_prod_right'
    have h4 : AEStronglyMeasurable (Work.Construction.L12dens (Work.FTS_MuLipC.Tf g))
        (volume.restrict Work.Spaces.Iz) := by
      convert h3 using 1
      funext z
      rfl
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))]
    exact h4
  -- the integrable majorant
  set V : ℝ := ∫ θ in Work.Spaces.Iθ, (1 : ℝ) with hV
  set T : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ with hT
  set Φ : ℝ → ℝ := fun s => 9 / (1 + s) ^ 2 * (V + T s) with hΦ
  have hT_int : IntegrableOn T (Set.Ioi 0) := by
    rw [hT]
    exact hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hbase : IntegrableOn (fun s : ℝ => (1 + s) ^ (-(2 : ℝ))) (Set.Ioi 0) :=
    integrableOn_one_add_pow_neg_two
  have hVpart : IntegrableOn (fun s : ℝ => 9 / (1 + s) ^ 2 * V) (Set.Ioi 0) := by
    have h : IntegrableOn (fun s : ℝ => (9 * V) * ((1 + s) ^ (-(2 : ℝ)))) (Set.Ioi 0) :=
      hbase.const_mul (9 * V)
    refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
    have hs0 : (0 : ℝ) < 1 + s := by
      have := Set.mem_Ioi.mp hs
      linarith
    show (9 * V) * ((1 + s) ^ (-((2 : ℕ) : ℝ))) = 9 / (1 + s) ^ 2 * V
    rw [Real.rpow_neg hs0.le, Real.rpow_natCast, div_eq_mul_inv]
    ring
  have hTpart : IntegrableOn (fun s : ℝ => 9 / (1 + s) ^ 2 * T s) (Set.Ioi 0) := by
    have hb : IntegrableOn (fun s : ℝ => 9 * |T s|) (Set.Ioi 0) := hT_int.abs.const_mul 9
    refine hb.mono' ?_ ?_
    · have hcont : ContinuousOn (fun s : ℝ => 9 / (1 + s) ^ 2) (Set.Ioi 0) := by
        refine ContinuousOn.div continuousOn_const
          ((continuousOn_const.add continuousOn_id).pow 2) ?_
        intro s hs
        have hs0 : (0 : ℝ) < 1 + s := by
          have := Set.mem_Ioi.mp hs
          linarith
        positivity
      exact (hcont.aestronglyMeasurable measurableSet_Ioi).mul hT_int.aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hspos : (0 : ℝ) < s := Set.mem_Ioi.mp hs
      have hnn : (0 : ℝ) ≤ 9 / (1 + s) ^ 2 := by positivity
      have hle : 9 / (1 + s) ^ 2 ≤ 9 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + s) ^ 2)]
        nlinarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  have hΦ_int : IntegrableOn Φ (Set.Ioi 0) := by
    have hsum := hVpart.add hTpart
    refine hsum.congr_fun (fun s _ => ?_) measurableSet_Ioi
    show 9 / (1 + s) ^ 2 * V + 9 / (1 + s) ^ 2 * T s = Φ s
    simp only [hΦ]
    ring
  -- assemble
  refine hΦ_int.mono' haesm ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun s hs => ?_
  have hs0 : (0 : ℝ) < s := Set.mem_Ioi.mp hs
  rw [Real.norm_eq_abs]
  have hle := abs_L12dens_Tf_le hα hmem hs0
  simp only [hΦ, hV, hT]
  exact hle

end Work.FTS_MuLipC.RowT
end
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowT.Tf_slice_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowT

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The transport field `Tf g` of `FTS_MuLipC` is the coercivity transport field

`Work.FTS_MuLipC.Tf g = fun z θ => 3·D_θg z θ/(1+z)` and
`Work.Coercivity.Transport g = fun z θ => 3·D_θg z θ/(1+z)` have the same body, so they are
definitionally equal; this lets us use the (already proved) `L₁₂`-machinery built for the
coercivity transport term (`Work.FTS.StrongPersist.L3Aux`), in particular the factorisation
`K θ·3 D_θg s θ/(s(1+s)) = Wlam3 s · (KG α θ · (D_θg s θ · Wt α s θ))` of the angular slice. -/

/-- `Tf g` is `Work.Coercivity.Transport g` (the two definitions have the same body, so this
is `rfl`). -/
private theorem tf_eq_Transport (g : ℝ → ℝ → ℝ) : Tf g = Work.Coercivity.Transport g := rfl

/-- The joint integrand `(z,θ) ↦ K θ·Tf g z θ/z` is continuous on the open quadrant, for `g`
of class `SmoothOpen`. -/
private theorem tf_integrand_continuousOn {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Tf g p.1 p.2 / p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hg.Dth.continuousOn
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hc : Continuous fun θ : ℝ => Work.Spaces.K θ := by
      change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
      fun_prop
    exact (hc.comp continuous_snd).continuousOn
  have hden : ContinuousOn (fun p : ℝ × ℝ => (1 + p.1 : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_const.add continuousOn_fst
  refine ContinuousOn.div (hK.mul ?_) continuousOn_fst
    (fun p hp => ne_of_gt (Set.mem_prod.mp hp).1)
  refine ContinuousOn.div (continuousOn_const.mul hD) hden (fun p hp => ?_)
  have h1 : (0 : ℝ) < p.1 := (Set.mem_prod.mp hp).1
  linarith

/-- **Pointwise bound on an angular slice.**  For `s > 0` and `θ ∈ Iθ`, the slice integrand of
the `L₁₂`-density of `Tf g` is dominated by `Wlam3 s·9(1 + HkIntegrand α 4 g s θ)/2`, an
integrable function of `θ` as soon as `g ∈ ℋ⁴_α`.  The `ℋ⁴`-slot used is the `(i,j) = (1,0)`
one, `(D_θg·W)² ≤ HkIntegrand α 4 g`, and the angular profile `KG α` is bounded by `9`. -/
private theorem tf_slice_pointwise_le {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} {s θ : ℝ}
    (hs : 0 < s) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * Tf g s θ / s|
      ≤ Work.FTS.StrongPersist.L3Aux.Wlam3 s
        * (9 * (1 + Work.Spaces.HkIntegrand α 4 g s θ) / 2) := by
  have hW3 : 0 ≤ Work.FTS.StrongPersist.L3Aux.Wlam3 s :=
    Work.FTS.StrongPersist.L3Aux.tl12_Wlam3_nonneg (le_of_lt hs)
  have hTf : Tf g = Work.Coercivity.Transport g := tf_eq_Transport g
  rw [hTf, Work.FTS.StrongPersist.L3Aux.tl12_Transport_integrand_eq α g hs hθ]
  rw [abs_mul, abs_of_nonneg hW3]
  refine mul_le_mul_of_nonneg_left ?_ hW3
  have hKGnn : 0 ≤ Work.FTS.StrongPersist.L3Aux.KG α θ :=
    Work.FTS.StrongPersist.L3Aux.tl12_KG_nonneg α hθ
  have hKGle : Work.FTS.StrongPersist.L3Aux.KG α θ ≤ 9 :=
    Work.FTS.StrongPersist.L3Aux.tl12_KG_le_nine α hθ
      (Work.FTS.StrongPersist.L3Aux.tl12_gam_half_nonneg hα)
  have hsq : (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g s θ :=
    Work.Spaces.sq_le_HkIntegrand_mixed α 4 g s θ 1 0 (le_refl 1) (by norm_num)
  have hb : |Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  have hAM := Work.FTS.GalBasis.cc.sqrt_le_half_one_add
    (Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
  calc |Work.FTS.StrongPersist.L3Aux.KG α θ
        * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ)|
      = Work.FTS.StrongPersist.L3Aux.KG α θ
          * |Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ| := by
        rw [abs_mul, abs_of_nonneg hKGnn]
    _ ≤ 9 * Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) :=
        mul_le_mul hKGle hb (abs_nonneg _) (by norm_num)
    _ ≤ 9 * (1 + Work.Spaces.HkIntegrand α 4 g s θ) / 2 := by
        have h := mul_le_mul_of_nonneg_left hAM (by norm_num : (0 : ℝ) ≤ 9)
        linarith

/-- **The angular slice of the transport field is `L¹`.**  For a profile `g` which is `C^∞` on the
open quadrant `(0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.SmoothOpen`) and honestly in `ℋ⁴_α`
(`Work.Spaces.HkMem α 4 g`), the slice of the `L₁₂`-integrand of the transport field
`Work.FTS_MuLipC.Tf g = fun z θ => 3·D_θg z θ/(1+z)` is integrable on `Iθ = [0,π/2]` for every
`s > 0`.  This is precisely the `h1`/`h2` input of `Work.FTS.LocData.L12_add_mul` at the fields
`a = Tf f'`, `b = Tf (f - f')`, and it is what makes the transport zero-mode additive over a
difference of class-`C` profiles.

Route (mirror `Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem`, for `Tf g` in place
of `g`): the pointwise domination
`|D_θg s θ| ≤ √(HkIntegrand α 4 g s θ)/w s`  (`s > 0`, `θ ∈ (0,π/2)`) — from
`Work.FTS.Nonlinear.Pieces.slot_mixed_le_HkIntegrand` at `(j,i) = (0,1)` (since `mixed 0 1 g = D_θ g`
by `Work.Spaces.mixed_zero_left`/`DthIter`) together with `Wt α s θ = w s · sin(2θ)^{-γ/2}` and
`(sin 2θ)^{-γ} ≥ 1` — turns the slice into
`≤ 9s/(1+s)³·√(HkIntegrand α 4 g s θ) ≤ 9s/(1+s)³·(1 + HkIntegrand α 4 g s θ)/2`, which is
integrable in `θ` by `hmem.1 s hs.le`.  Then close with `Integrable.mono'`, the a.e. strong
measurability coming from continuity of the slice (from `hg.Dth` and
`Work.Spaces.aesm_slice_of_continuousOn_Qd`). -/
theorem Tf_slice_integrable {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ s ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS_MuLipC.Tf g s θ / s) Work.Spaces.Iθ := by
  intro s hs
  have hs' : 0 < s := hs
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hHk : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g s θ) Work.Spaces.Iθ :=
    hmem.1 s hs'.le
  have haesm : AEStronglyMeasurable
      (fun θ => Work.Spaces.K θ * Tf g s θ / s) (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ (tf_integrand_continuousOn hg) hs'
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    continuous_const.integrableOn_Icc
  have hmaj : IntegrableOn (fun θ => Work.FTS.StrongPersist.L3Aux.Wlam3 s
      * (9 * (1 + Work.Spaces.HkIntegrand α 4 g s θ) / 2)) Work.Spaces.Iθ := by
    have h1 : IntegrableOn (fun θ => (Work.FTS.StrongPersist.L3Aux.Wlam3 s * (9 / 2))
        * (1 + Work.Spaces.HkIntegrand α 4 g s θ)) Work.Spaces.Iθ :=
      (hconst.add hHk).const_mul _
    refine h1.congr_fun (fun θ _ => ?_) hIθ
    ring
  refine hmaj.mono' haesm ?_
  rw [ae_restrict_iff' hIθ]
  exact Eventually.of_forall fun θ hθ => by
    rw [Real.norm_eq_abs]
    exact tf_slice_pointwise_le hα hs' hθ

end Work.FTS_MuLipC.RowT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.pthIter_le_of_weighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS_RegExport.RXR1

/-!
# `Work.FTS_RegExport.RXR1.pthIter_le_of_weighted`

The angular analogue of `Work.FTS_RegExport.RXR1.pzIter_le_of_weighted`: the weighted slot
hypothesis `HwBnd β C` bounds the *mixed* slots `mixed b a f = D_z^b D_θ^a f` of order
`a + b ≤ 2`, and the two pure angular derivatives `∂_θ f` and `∂_θ² f` are recovered from
them by dividing by `sin(2θ)`.

* `mixed 0 1 f = sin(2θ) · ∂_θ f` is *definitional* (`D_θ f = sin(2θ) ∂_θ f`), giving the
  first slot with the loss `1/sin(2θ)`;
* `mixed 0 2 f = sin(2θ)² ∂_θ² f + 2 sin(2θ) cos(2θ) ∂_θ f` is the product rule applied to
  `θ' ↦ sin(2θ') ∂_θ f (z,θ')` (the only place where the smoothness `SmoothOpen f` is used),
  giving the second slot with the loss `1/sin(2θ)²`.

Both bounds are stated with the same constant `K = 3C` (the `2` accounting for the cross
term `2 sin(2θ) cos(2θ) ∂_θ f`, and the `1` for `|cos(2θ)| ≤ 1`).
-/

/-- The derivative of `θ ↦ sin(2θ)`. -/
lemma deriv_sin_two_slice (θ : ℝ) :
    deriv (fun t : ℝ => Real.sin (2 * t)) θ = 2 * Real.cos (2 * θ) := by
  simp [mul_comm]

/-- **The product-rule expansion of the second angular slot.**  For `f` of class `C^∞` on the
open quadrant and `(z,θ)` in it,

`D_θ² f (z,θ) = sin(2θ)² ∂_θ² f (z,θ) + 2 sin(2θ) cos(2θ) ∂_θ f (z,θ)`.

(With `mixed 0 i f = D_θ^i f`, this is the `D_θ²`-instance of
`Work.EllipticEst.RegQ.Vop.DthIter_two_eq`.) -/
lemma mixed_zero_two_expand {f : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed 0 2 f z θ
      = Real.sin (2 * θ) ^ 2 * Work.Spaces.pthIter 2 f z θ
        + 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ := by
  have hP1 : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pth f z t) θ :=
    ((hS.pth.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hmain : Work.Spaces.mixed 0 2 f z θ
      = Real.sin (2 * θ) * (2 * Real.cos (2 * θ) * Work.Spaces.pth f z θ
          + Real.sin (2 * θ) * Work.Spaces.pthIter 2 f z θ) := by
    show Real.sin (2 * θ)
        * deriv (fun t : ℝ => Real.sin (2 * t) * Work.Spaces.pth f z t) θ = _
    rw [show (fun t : ℝ => Real.sin (2 * t) * Work.Spaces.pth f z t)
        = (fun t : ℝ => Real.sin (2 * t)) * (fun t : ℝ => Work.Spaces.pth f z t) from rfl,
      deriv_mul (by fun_prop) hP1, deriv_sin_two_slice]
    rw [show deriv (fun t : ℝ => Work.Spaces.pth f z t) θ
        = Work.Spaces.pthIter 2 f z θ from rfl]
  rw [hmain, show Work.Spaces.pthIter 1 f z θ = Work.Spaces.pth f z θ from rfl]
  ring

theorem pthIter_le_of_weighted {β C : ℝ} (hC : 0 ≤ C)
    (hw : Work.FTS_RegExport.RXR1.HwBnd β C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem β 4 f → Work.FTS.Nonlin.BdryTraces β 4 f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.pthIter 1 f z θ|
            ≤ K * (Work.FTS_RegExport.RXR1.SliceW z / Real.sin (2 * θ))
              * Work.Spaces.HkNorm β 4 f ∧
        |Work.Spaces.pthIter 2 f z θ|
            ≤ K * (Work.FTS_RegExport.RXR1.SliceW z
              / (Real.sin (2 * θ) * Real.sin (2 * θ))) * Work.Spaces.HkNorm β 4 f := by
  refine ⟨3 * C, by linarith, ?_⟩
  intro f hS hH hB z θ hz hθ0 hθ1
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hW : 0 ≤ SliceW z := SliceW_nonneg hz.le
  have hN : 0 ≤ Work.Spaces.HkNorm β 4 f := Real.sqrt_nonneg _
  have hCWN : 0 ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f :=
    mul_nonneg (mul_nonneg hC hW) hN
  have hθm : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- ## first slot: `∂_θ f = mixed 0 1 f / sin(2θ)`
  have hb1 : |Work.Spaces.mixed 0 1 f z θ| ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f :=
    hw f hS hH hB 0 1 (by norm_num) z θ hz hθ0 hθ1
  have hsx : Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ|
      ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f := by
    calc Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ|
        = |Work.Spaces.mixed 0 1 f z θ| := by
          rw [mixed_zero_one_eq, abs_mul, abs_of_pos hs]
      _ ≤ _ := hb1
  have hx1 : |Work.Spaces.pthIter 1 f z θ|
      ≤ 3 * C * (SliceW z / Real.sin (2 * θ)) * Work.Spaces.HkNorm β 4 f := by
    have h1 : |Work.Spaces.pthIter 1 f z θ|
        ≤ (C * SliceW z * Work.Spaces.HkNorm β 4 f) / Real.sin (2 * θ) := by
      rw [le_div_iff₀ hs]
      calc |Work.Spaces.pthIter 1 f z θ| * Real.sin (2 * θ)
          = Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ| := by ring
        _ ≤ _ := hsx
    have h2 : (C * SliceW z * Work.Spaces.HkNorm β 4 f) / Real.sin (2 * θ)
        ≤ 3 * C * (SliceW z / Real.sin (2 * θ)) * Work.Spaces.HkNorm β 4 f := by
      have h4 := div_le_div_of_nonneg_right (show C * SliceW z * Work.Spaces.HkNorm β 4 f
          ≤ 3 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) by linarith [hCWN]) hs.le
      have h5 : (3 * (C * SliceW z * Work.Spaces.HkNorm β 4 f)) / Real.sin (2 * θ)
          = 3 * C * (SliceW z / Real.sin (2 * θ)) * Work.Spaces.HkNorm β 4 f := by
        ring_nf
      rw [h5] at h4
      exact h4
    exact le_trans h1 h2
  -- ## second slot: `sin(2θ)² ∂_θ² f = mixed 0 2 f - 2 sin(2θ)cos(2θ) ∂_θ f`
  have hb2 : |Work.Spaces.mixed 0 2 f z θ| ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f :=
    hw f hS hH hB 0 2 (by norm_num) z θ hz hθ0 hθ1
  have hid := mixed_zero_two_expand hS hz hθm
  have hkey : Real.sin (2 * θ) ^ 2 * Work.Spaces.pthIter 2 f z θ
      = Work.Spaces.mixed 0 2 f z θ
        - 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ := by
    rw [hid]; ring
  have hsq : Real.sin (2 * θ) ^ 2 * |Work.Spaces.pthIter 2 f z θ|
      = |Work.Spaces.mixed 0 2 f z θ
        - 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ| := by
    rw [← hkey, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  have hBle : |2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ|
      ≤ 2 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) := by
    have habs : |(2 : ℝ) * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ|
        = 2 * (Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ|) * |Real.cos (2 * θ)| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hs]
      ring
    rw [habs]
    have h1 : 2 * (Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ|) * |Real.cos (2 * θ)|
        ≤ 2 * (Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ|) * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
        (by positivity : (0 : ℝ) ≤ 2 * (Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ|))
    have h2 : 2 * (Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ|) * 1
        ≤ 2 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) := by
      simpa using mul_le_mul_of_nonneg_left hsx (by norm_num : (0 : ℝ) ≤ 2)
    exact le_trans h1 h2
  have htri : Real.sin (2 * θ) ^ 2 * |Work.Spaces.pthIter 2 f z θ|
      ≤ 3 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) := by
    rw [hsq]
    calc |Work.Spaces.mixed 0 2 f z θ - 2 * Real.sin (2 * θ) * Real.cos (2 * θ)
            * Work.Spaces.pthIter 1 f z θ|
        = |Work.Spaces.mixed 0 2 f z θ
            + (-(2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ))| := by
          rw [sub_eq_add_neg]
      _ ≤ |Work.Spaces.mixed 0 2 f z θ|
            + |-(2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ)| :=
          abs_add_le _ _
      _ = |Work.Spaces.mixed 0 2 f z θ|
            + |2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ| := by
          rw [abs_neg]
      _ ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f
            + 2 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) :=
          add_le_add hb2 hBle
      _ = 3 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) := by ring
  have hx2 : |Work.Spaces.pthIter 2 f z θ|
      ≤ 3 * C * (SliceW z / (Real.sin (2 * θ) * Real.sin (2 * θ)))
          * Work.Spaces.HkNorm β 4 f := by
    have hX : 3 * C * (SliceW z / (Real.sin (2 * θ) * Real.sin (2 * θ)))
          * Work.Spaces.HkNorm β 4 f
        = (3 * C * SliceW z * Work.Spaces.HkNorm β 4 f)
          / (Real.sin (2 * θ) * Real.sin (2 * θ)) := by
      ring_nf
    rw [hX, le_div_iff₀ (mul_pos hs hs)]
    calc |Work.Spaces.pthIter 2 f z θ| * (Real.sin (2 * θ) * Real.sin (2 * θ))
        = Real.sin (2 * θ) ^ 2 * |Work.Spaces.pthIter 2 f z θ| := by ring
      _ ≤ 3 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) := htri
      _ = 3 * C * SliceW z * Work.Spaces.HkNorm β 4 f := by ring
  exact ⟨hx1, hx2⟩

end Work.FTS_RegExport.RXR1
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.pzIter_bound_weighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.pzIter_bound_weighted`

Consequence of the *weighted slot bound* `HwBnd β C` (which controls the mixed slots
`D_z^b D_θ^a f` of order `a + b ≤ 2` of an honest `ℋ⁴` datum by `C · z^{3/2}/(1+z)² · |f|_{ℋ⁴}`,
cf. `Work.FTS_RegExport.RXR1.mixed_abs_le_weighted`): the plain `z`-derivatives `∂_z f` and
`∂_z² f` obey the same weighted bound with the two powers of `z` divided out,

  `|∂_z f(z,θ)| ≤ K · (W(z)/z) · |f|_{ℋ⁴}`,  `|∂_z² f(z,θ)| ≤ K · (W(z)/z²) · |f|_{ℋ⁴}`,

with `W = SliceW = z^{3/2}/(1+z)²` and `K = 2C`.

The two inputs are the definitional identities

* `mixed 1 0 f = z · ∂_z f`  (`SliceDiffAux.mixed_one_zero_eq`),
* `D_z² f = D_z f + z² · ∂_z² f`  (`dziter_two_eq_add` below, the `n = 2` case of the expansion
  of `D_z = z ∂_z` in powers of `z^k∂_z^k`, obtained from the one-variable product rule alone).

The second identity needs only that the `z`-slice of `∂_z f` be differentiable at the point,
which `SmoothOpen f` supplies through `SmoothOpen.hasDerivAt_slice_pzIter`.
-/

noncomputable section

open scoped Real Topology
open Filter Set

namespace Work.FTS_RegExport.RXR1

set_option autoImplicit false

/-- **The bridge `D_z²F = D_zF + z²∂_z²F`.**

If the `z`-slice of `∂_zF` is differentiable at `z`, then `D_z²F = D_zF + z²∂_z²F` at `(z,θ)`.
(The `n = 2` case of the expansion of `D_z = z∂_z` in powers of `z^k∂_z^k`, with the Stirling
coefficients `S(2,1) = S(2,2) = 1`; only the product rule is used, so no higher smoothness is
required.) -/
private lemma dziter_two_eq_add (F : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun z' => Work.Spaces.pz F z' θ) z) :
    Work.Spaces.DzIter 2 F z θ
      = Work.Spaces.DzIter 1 F z θ + z ^ 2 * Work.Spaces.pzIter 2 F z θ := by
  have hdmul : deriv (fun z' : ℝ => z' * Work.Spaces.pz F z' θ) z
      = Work.Spaces.pz F z θ + z * Work.Spaces.pz (Work.Spaces.pz F) z θ := by
    have h1 : HasDerivAt (fun z' : ℝ => z') (1 : ℝ) z := hasDerivAt_id' z
    have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz F z' θ)
        (Work.Spaces.pz (Work.Spaces.pz F) z θ) z := hd.hasDerivAt
    have h3 : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pz F z' θ)
        (1 * Work.Spaces.pz F z θ + z * Work.Spaces.pz (Work.Spaces.pz F) z θ) z :=
      (h1.mul h2).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext z'; rfl))
    simpa only [one_mul] using h3.deriv
  show z * deriv (fun z' : ℝ => z' * Work.Spaces.pz F z' θ) z
      = z * Work.Spaces.pz F z θ + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz F) z θ
  rw [hdmul]
  ring

/-- The requested lemma: from the weighted slot bound `HwBnd β C` on the mixed slots of order
`≤ 2` one gets the weighted bounds `|∂_z^j f| ≤ 2C·SliceW z / z^j · |f|_{ℋ⁴}` for `j = 1, 2`. -/
theorem pzIter_bound_weighted {β C : ℝ} (hC : 0 ≤ C)
    (hw : Work.FTS_RegExport.RXR1.HwBnd β C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem β 4 f → Work.FTS.Nonlin.BdryTraces β 4 f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.pzIter 1 f z θ| ≤ K * (Work.FTS_RegExport.RXR1.SliceW z / z)
            * Work.Spaces.HkNorm β 4 f ∧
        |Work.Spaces.pzIter 2 f z θ| ≤ K * (Work.FTS_RegExport.RXR1.SliceW z / (z * z))
            * Work.Spaces.HkNorm β 4 f := by
  refine ⟨2 * C, by linarith, ?_⟩
  intro f hf hmem hbd z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hnorm : 0 ≤ Work.Spaces.HkNorm β 4 f := Real.sqrt_nonneg _
  have hW : 0 ≤ SliceW z := SliceW_nonneg hz.le
  have hN : 0 ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f :=
    mul_nonneg (mul_nonneg hC hW) hnorm
  -- the weighted slot bounds from `hw`
  have hb1 : z * |Work.Spaces.pzIter 1 f z θ| ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f := by
    have h := hw f hf hmem hbd 1 0 (by norm_num) z θ hz hθ0 hθ1
    rw [mixed_one_zero_eq, abs_mul, abs_of_pos hz] at h
    exact h
  have hb2 : |Work.Spaces.mixed 2 0 f z θ| ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f :=
    hw f hf hmem hbd 2 0 (by norm_num) z θ hz hθ0 hθ1
  have hm1eq : |Work.Spaces.mixed 1 0 f z θ| = z * |Work.Spaces.pzIter 1 f z θ| := by
    rw [mixed_one_zero_eq, abs_mul, abs_of_pos hz]
  -- the expansion `D_z²f = D_zf + z²∂_z²f`
  have hd : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z :=
    (hf.hasDerivAt_slice_pzIter 1 hθ hz).differentiableAt
  have hexp : Work.Spaces.DzIter 2 f z θ
      = Work.Spaces.DzIter 1 f z θ + z ^ 2 * Work.Spaces.pzIter 2 f z θ :=
    dziter_two_eq_add f hd
  have hprod : z ^ 2 * Work.Spaces.pzIter 2 f z θ
      = Work.Spaces.mixed 2 0 f z θ - Work.Spaces.mixed 1 0 f z θ := by
    show z ^ 2 * Work.Spaces.pzIter 2 f z θ
      = Work.Spaces.DzIter 2 f z θ - Work.Spaces.DzIter 1 f z θ
    linarith [hexp]
  have hB : |Work.Spaces.pzIter 2 f z θ| * z ^ 2
      ≤ 2 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) := by
    have h2 := abs_sub (Work.Spaces.mixed 2 0 f z θ) (Work.Spaces.mixed 1 0 f z θ)
    have h4 : |Work.Spaces.pzIter 2 f z θ| * z ^ 2 = |z ^ 2 * Work.Spaces.pzIter 2 f z θ| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg z)]; ring
    rw [h4, hprod]
    linarith [h2, hb1, hb2, hm1eq]
  -- divide the two powers of `z` out
  have hAeq : 2 * C * (SliceW z / z) * Work.Spaces.HkNorm β 4 f
      = 2 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) / z := by
    field_simp
  have hBeq : 2 * C * (SliceW z / (z * z)) * Work.Spaces.HkNorm β 4 f
      = 2 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) / (z * z) := by
    field_simp
  constructor
  · rw [hAeq, le_div_iff₀ hz]
    nlinarith [hb1, hN]
  · rw [hBeq, le_div_iff₀ (by positivity)]
    nlinarith [hB]

end Work.FTS_RegExport.RXR1
end
end
