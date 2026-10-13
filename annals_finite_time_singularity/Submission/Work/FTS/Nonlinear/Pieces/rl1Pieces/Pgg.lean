import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gPt
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Interface
import Submission.Work.FTS.LocDataExt.Monotone
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggParts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Pgg` — the `gg`-row of the `L₁₂`-type estimate

The five `gg`-pieces `N₁^{gg}, …, N₅^{gg}` of the §8 nonlinearity are estimated in

  `E(f) = ∫⁻ r in Ioi 0, r⁻¹ · (∫⁻ θ in Iθ, |K(θ) · f r θ|)`,

each by a constant times `α^{p}·|g|_{ℋ⁴}²`, with `p = -1/2` for `N₁^{gg}`, `N₂^{gg}`,
`p = 1/2` for `N₃^{gg}` and `p = 0` for `N₄^{gg}`, `N₅^{gg}`.

Each piece is a product `A·B` of an elliptic coefficient (`Rop`, `Uop/sin2θ`, `Vop` of the
perturbation's stream function, or the angular moment `FK g`) and a slot (`g`, `D_θg`,
`D_zg`); the estimate is Cauchy–Schwarz in `θ` (`inner_lintegral_le`), the weighted
`H⁴`-energy bound for the slot (`Phi0/1/2_props`), and Cauchy–Schwarz in `r` with
`r⁻¹ = w^{1/2}/(1+r)` (`outer_of_inner`, `outer_of_inner_pair`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)

theorem abs_sin_sq_le_one (θ : ℝ) : (Real.sin θ) ^ 2 ≤ 1 := Real.sin_sq_le_one θ

/-- `10√(10/α)·max Ce 0·|g|` is nonnegative. -/
theorem Mbase_nonneg (α Ce : ℝ) (g : Fn) :
    0 ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (le_max_right _ _)) (Work.Spaces.HkNorm_nonneg α 4 g)

/-! ## The coefficient functions of the five pieces -/

/-- `A₁ = 2ℛ(Φ̃_g)`. -/
def A1 (α : ℝ) (g Φg : Fn) : ℝ → ℝ → ℝ :=
  fun z θ => 2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ

/-- `A₂ = -2U(Φ̃_g)/sin 2θ`. -/
def A2 (α : ℝ) (g Φg : Fn) : ℝ → ℝ → ℝ :=
  fun z θ => -2 * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
    / Work.Construction.s2 θ)

/-- `A₃ = -2α𝒱(Φ̃_g)`. -/
def A3 (α : ℝ) (g Φg : Fn) : ℝ → ℝ → ℝ :=
  fun z θ => -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ

/-- `A₄ = -(1/2)FK(g)`. -/
def A4 (g : Fn) : ℝ → ℝ → ℝ := fun z _ => -(1 / 2) * Work.Construction.FK g z

/-- `A₅ = -sin²θ·FK(g)`. -/
def A5 (g : Fn) : ℝ → ℝ → ℝ := fun z θ => -(Real.sin θ) ^ 2 * Work.Construction.FK g z

theorem N1gg_eq (α : ℝ) (g Φg : Fn) :
    Work.FTS.Nonlin.N1gg α g Φg = fun z θ => A1 α g Φg z θ * g z θ := rfl

theorem N3gg_eq (α : ℝ) (g Φg : Fn) :
    Work.FTS.Nonlin.N3gg α g Φg = fun z θ => A3 α g Φg z θ * Work.Spaces.Dz g z θ := rfl

theorem N4gg_eq (α : ℝ) (g : Fn) :
    Work.FTS.Nonlin.N4gg α g = fun z θ => A4 g z θ * Work.Spaces.Dth g z θ := rfl

theorem N5gg_eq (g : Fn) :
    Work.FTS.Nonlin.N5gg g = fun z θ => A5 g z θ * g z θ := rfl

theorem N2gg_eq (α : ℝ) (g Φg : Fn) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.Nonlin.N2gg α g Φg z θ = A2 α g Φg z θ * Work.Spaces.Dth g z θ := by
  have hs : Real.sin (2 * θ) ≠ 0 := ne_of_gt (sin_two_pos_aux hθ)
  simp only [A2, Work.FTS.Nonlin.N2gg, Work.Spaces.Dth, Work.Construction.s2]
  field_simp

/-! ## The five piece estimates -/

/-- `N₁^{gg} = 2ℛ(Φ̃_g)·g`, estimated by `60√(10π)·max Ce 0·α^{-1/2}·|g|²`. -/
theorem N1gg_bound {α Ce : ℝ} {g Φg : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hGal : Work.FTS.Nonlin.GalClass α g) (hEll : Work.FTS.Nonlin.EllPkgG α Ce g Φg) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N1gg α g Φg r θ|))
      ≤ ENNReal.ofReal (60 * Real.sqrt (10 * Real.pi) * max Ce 0 * α ^ (-(1 / 2 : ℝ))
          * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨hRreg, -⟩ := hEll.R
  have hsqR := hRreg.1
  have hsqg : Work.FTS.LocData.SmoothQuad g := hGal.reg.1
  have hmemg : Work.Spaces.HkMem α 4 g :=
    Work.FTS.LocDataExt.HkMem_mono (by norm_num) hsqg hGal.reg.2.1
  obtain ⟨hΦ0nn, hΦ0slice, hΦ0meas, hΦ0int, hΦ0le⟩ :=
    Phi0_props hsqg hmemg (aesm_slice_zero_of_axis fun θ hθ => (hGal.axis θ hθ).1)
  obtain ⟨hgR, -, -⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.gPt hα hα1 hEll
  set M : ℝ := 2 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]; exact mul_nonneg (by norm_num) (Mbase_nonneg α Ce g)
  have hinn : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * A1 α g Φg r θ * g r θ|)
        ≤ ENNReal.ofReal (3 * M * Real.sqrt (Real.pi / 2))
            * (ENNReal.ofReal (Phi0 g r)) ^ (1 / 2 : ℝ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hAmeas : MeasureTheory.AEStronglyMeasurable (fun θ => A1 α g Φg r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      simp only [A1]
      exact MeasureTheory.AEStronglyMeasurable.const_mul (aesm_slice_of_smoothQuad hsqR hr) 2
    have hBmeas : MeasureTheory.AEStronglyMeasurable (fun θ => g r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := aesm_slice_of_smoothQuad hsqg hr
    have hAb : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        |A1 α g Φg r θ| ≤ M := by
      filter_upwards [ae_mem_Ioo_Iθ_aux] with θ hθ
      have h1 := hgR r hr θ hθ.1 hθ.2
      simp only [A1]
      rw [hMdef, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    have hB : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((g r θ) ^ 2))
        ≤ ENNReal.ofReal (Phi0 g r) := by
      rw [Phi0, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hΦ0slice r hr)
        (Filter.Eventually.of_forall fun θ => sq_nonneg _)]
    exact Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.inner_lintegral_le hMnn
      (Phi0_nonneg g r) hAmeas hBmeas hAb hB
  have hc : 0 ≤ 3 * M * Real.sqrt (Real.pi / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hMnn) (Real.sqrt_nonneg _)
  have hmain := outer_of_inner (A := A1 α g Φg) (B := g) (Φ := Phi0 g)
    (Xs := Work.Spaces.HkSq α 4 g) (c := 3 * M * Real.sqrt (Real.pi / 2))
    hc hinn hΦ0nn hΦ0meas hΦ0int hΦ0le
  calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N1gg α g Φg r θ|))
      = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * (A1 α g Φg r θ * g r θ)|)) := by
        simp only [N1gg_eq]
    _ = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * A1 α g Φg r θ * g r θ|)) := by
        refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
        refine congrArg (fun t => ENNReal.ofReal r⁻¹ * t) ?_
        refine MeasureTheory.lintegral_congr (fun θ => ?_)
        rw [mul_assoc]
    _ ≤ ENNReal.ofReal (3 * M * Real.sqrt (Real.pi / 2)
          * (Real.sqrt 2 * Real.sqrt (Work.Spaces.HkSq α 4 g))) := hmain
    _ ≤ ENNReal.ofReal (60 * Real.sqrt (10 * Real.pi) * max Ce 0 * α ^ (-(1 / 2 : ℝ))
          * Work.FTS.Nonlin.Xn α g ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show Real.sqrt (Work.Spaces.HkSq α 4 g) = Work.FTS.Nonlin.Xn α g from rfl, hMdef]
        have h1 := sqrt_pi_div_two_mul_sqrt_two
        have h2 := sqrt_ten_div_mul_sqrt_pi hα
        calc 3 * (2 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g))
              * Real.sqrt (Real.pi / 2) * (Real.sqrt 2 * Work.FTS.Nonlin.Xn α g)
            = 60 * (Real.sqrt (10 / α) * (Real.sqrt (Real.pi / 2) * Real.sqrt 2)) * max Ce 0
                * Work.FTS.Nonlin.Xn α g ^ 2 := by ring
          _ = 60 * (Real.sqrt (10 / α) * Real.sqrt Real.pi) * max Ce 0
                * Work.FTS.Nonlin.Xn α g ^ 2 := by rw [h1]
          _ = 60 * (Real.sqrt (10 * Real.pi) * α ^ (-(1 / 2 : ℝ))) * max Ce 0
                * Work.FTS.Nonlin.Xn α g ^ 2 := by rw [h2]
          _ ≤ 60 * Real.sqrt (10 * Real.pi) * max Ce 0 * α ^ (-(1 / 2 : ℝ))
                * Work.FTS.Nonlin.Xn α g ^ 2 := le_of_eq (by ring)

/-- `N₂^{gg} = -2U(Φ̃_g)∂_θg = -2(U(Φ̃_g)/sin2θ)·D_θg`, the same constant as `N₁^{gg}`. -/
theorem N2gg_bound {α Ce : ℝ} {g Φg : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hGal : Work.FTS.Nonlin.GalClass α g) (hEll : Work.FTS.Nonlin.EllPkgG α Ce g Φg) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N2gg α g Φg r θ|))
      ≤ ENNReal.ofReal (60 * Real.sqrt (10 * Real.pi) * max Ce 0 * α ^ (-(1 / 2 : ℝ))
          * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨hUreg, -⟩ := hEll.U
  have hsqU : Work.FTS.LocData.SmoothQuad
      (fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
        / Work.Construction.s2 θ) := hUreg.1
  have hsqg : Work.FTS.LocData.SmoothQuad g := hGal.reg.1
  have hmemg : Work.Spaces.HkMem α 4 g :=
    Work.FTS.LocDataExt.HkMem_mono (by norm_num) hsqg hGal.reg.2.1
  obtain ⟨hΦ1nn, hΦ1slice, hΦ1meas, hΦ1int, hΦ1le⟩ :=
    Phi1_props hα.le hsqg hmemg (aesm_slice_zero_Dth_of_axis fun θ hθ => (hGal.axis θ hθ).1)
  obtain ⟨-, hgU, -⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.gPt hα hα1 hEll
  set M : ℝ := 2 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]; exact mul_nonneg (by norm_num) (Mbase_nonneg α Ce g)
  have hinn : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * A2 α g Φg r θ * Work.Spaces.Dth g r θ|)
        ≤ ENNReal.ofReal (3 * M * Real.sqrt (Real.pi / 2))
            * (ENNReal.ofReal (Phi1 g r)) ^ (1 / 2 : ℝ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hAmeas : MeasureTheory.AEStronglyMeasurable (fun θ => A2 α g Φg r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      simp only [A2]
      exact MeasureTheory.AEStronglyMeasurable.const_mul (aesm_slice_of_smoothQuad hsqU hr) (-2)
    have hBmeas : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.Dth g r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := aesm_slice_Dth_of_smoothQuad hsqg hr
    have hAb : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        |A2 α g Φg r θ| ≤ M := by
      filter_upwards [ae_mem_Ioo_Iθ_aux] with θ hθ
      have h1 := hgU r hr θ hθ.1 hθ.2
      simp only [A2]
      rw [hMdef, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    have hB : (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.Spaces.Dth g r θ) ^ 2)) ≤ ENNReal.ofReal (Phi1 g r) := by
      rw [Phi1, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hΦ1slice r hr)
        (Filter.Eventually.of_forall fun θ => sq_nonneg _)]
    exact Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.inner_lintegral_le hMnn
      (Phi1_nonneg g r) hAmeas hBmeas hAb hB
  have hc : 0 ≤ 3 * M * Real.sqrt (Real.pi / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hMnn) (Real.sqrt_nonneg _)
  have hmain := outer_of_inner (A := A2 α g Φg) (B := Work.Spaces.Dth g) (Φ := Phi1 g)
    (Xs := Work.Spaces.HkSq α 4 g) (c := 3 * M * Real.sqrt (Real.pi / 2))
    hc hinn hΦ1nn hΦ1meas hΦ1int hΦ1le
  calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N2gg α g Φg r θ|))
      = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * A2 α g Φg r θ * Work.Spaces.Dth g r θ|)) := by
        refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
        refine congrArg (fun t => ENNReal.ofReal r⁻¹ * t) ?_
        refine MeasureTheory.lintegral_congr_ae ?_
        filter_upwards [ae_mem_Ioo_Iθ_aux] with θ hθ
        rw [N2gg_eq α g Φg hθ, mul_assoc]
    _ ≤ ENNReal.ofReal (3 * M * Real.sqrt (Real.pi / 2)
          * (Real.sqrt 2 * Real.sqrt (Work.Spaces.HkSq α 4 g))) := hmain
    _ ≤ ENNReal.ofReal (60 * Real.sqrt (10 * Real.pi) * max Ce 0 * α ^ (-(1 / 2 : ℝ))
          * Work.FTS.Nonlin.Xn α g ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show Real.sqrt (Work.Spaces.HkSq α 4 g) = Work.FTS.Nonlin.Xn α g from rfl, hMdef]
        have h1 := sqrt_pi_div_two_mul_sqrt_two
        have h2 := sqrt_ten_div_mul_sqrt_pi hα
        calc 3 * (2 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g))
              * Real.sqrt (Real.pi / 2) * (Real.sqrt 2 * Work.FTS.Nonlin.Xn α g)
            = 60 * (Real.sqrt (10 / α) * (Real.sqrt (Real.pi / 2) * Real.sqrt 2)) * max Ce 0
                * Work.FTS.Nonlin.Xn α g ^ 2 := by ring
          _ = 60 * (Real.sqrt (10 / α) * Real.sqrt Real.pi) * max Ce 0
                * Work.FTS.Nonlin.Xn α g ^ 2 := by rw [h1]
          _ = 60 * (Real.sqrt (10 * Real.pi) * α ^ (-(1 / 2 : ℝ))) * max Ce 0
                * Work.FTS.Nonlin.Xn α g ^ 2 := by rw [h2]
          _ ≤ 60 * Real.sqrt (10 * Real.pi) * max Ce 0 * α ^ (-(1 / 2 : ℝ))
                * Work.FTS.Nonlin.Xn α g ^ 2 := le_of_eq (by ring)

/-- `N₃^{gg} = -2α𝒱(Φ̃_g)·D_zg`, estimated by `60√(10π)·max Ce 0·α^{1/2}·|g|²`. -/
theorem N3gg_bound {α Ce : ℝ} {g Φg : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hGal : Work.FTS.Nonlin.GalClass α g) (hEll : Work.FTS.Nonlin.EllPkgG α Ce g Φg) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N3gg α g Φg r θ|))
      ≤ ENNReal.ofReal (60 * Real.sqrt (10 * Real.pi) * max Ce 0 * α ^ (1 / 2 : ℝ)
          * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨hVreg, -⟩ := hEll.V
  have hsqV := hVreg.1
  have hsqg : Work.FTS.LocData.SmoothQuad g := hGal.reg.1
  have hmemg : Work.Spaces.HkMem α 4 g :=
    Work.FTS.LocDataExt.HkMem_mono (by norm_num) hsqg hGal.reg.2.1
  obtain ⟨hΦ2nn, hΦ2slice, hΦ2meas, hΦ2int, hΦ2le⟩ := Phi2_props hsqg hmemg
  obtain ⟨-, -, hgV⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.gPt hα hα1 hEll
  set M : ℝ := 2 * α * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
    with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (mul_nonneg (by norm_num) hα.le) (Mbase_nonneg α Ce g)
  have hinn : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * A3 α g Φg r θ * Work.Spaces.Dz g r θ|)
        ≤ ENNReal.ofReal (3 * M * Real.sqrt (Real.pi / 2))
            * (ENNReal.ofReal (Phi2 g r)) ^ (1 / 2 : ℝ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hAmeas : MeasureTheory.AEStronglyMeasurable (fun θ => A3 α g Φg r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      simp only [A3]
      exact MeasureTheory.AEStronglyMeasurable.const_mul (aesm_slice_of_smoothQuad hsqV hr)
        (-2 * α)
    have hBmeas : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.Dz g r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := aesm_slice_Dz_of_smoothQuad hsqg hr
    have hAb : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        |A3 α g Φg r θ| ≤ M := by
      filter_upwards [ae_mem_Ioo_Iθ_aux] with θ hθ
      have h1 : |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
          ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g :=
        hgV r hr θ hθ.1 hθ.2
      have h2 : |A3 α g Φg r θ| = 2 * α
          * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) r θ| := by
        simp only [A3]
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg hα.le]
      rw [h2, hMdef]
      exact mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * α)
    have hB : (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.Spaces.Dz g r θ) ^ 2)) ≤ ENNReal.ofReal (Phi2 g r) := by
      rw [Phi2, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hΦ2slice r hr)
        (Filter.Eventually.of_forall fun θ => sq_nonneg _)]
    exact Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.inner_lintegral_le hMnn
      (Phi2_nonneg g r) hAmeas hBmeas hAb hB
  have hc : 0 ≤ 3 * M * Real.sqrt (Real.pi / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hMnn) (Real.sqrt_nonneg _)
  have hmain := outer_of_inner (A := A3 α g Φg) (B := Work.Spaces.Dz g) (Φ := Phi2 g)
    (Xs := Work.Spaces.HkSq α 4 g) (c := 3 * M * Real.sqrt (Real.pi / 2))
    hc hinn hΦ2nn hΦ2meas hΦ2int hΦ2le
  calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N3gg α g Φg r θ|))
      = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ
            * (A3 α g Φg r θ * Work.Spaces.Dz g r θ)|)) := by
        simp only [N3gg_eq]
    _ = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * A3 α g Φg r θ * Work.Spaces.Dz g r θ|)) := by
        refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
        refine congrArg (fun t => ENNReal.ofReal r⁻¹ * t) ?_
        refine MeasureTheory.lintegral_congr (fun θ => ?_)
        rw [mul_assoc]
    _ ≤ ENNReal.ofReal (3 * M * Real.sqrt (Real.pi / 2)
          * (Real.sqrt 2 * Real.sqrt (Work.Spaces.HkSq α 4 g))) := hmain
    _ ≤ ENNReal.ofReal (60 * Real.sqrt (10 * Real.pi) * max Ce 0 * α ^ (1 / 2 : ℝ)
          * Work.FTS.Nonlin.Xn α g ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show Real.sqrt (Work.Spaces.HkSq α 4 g) = Work.FTS.Nonlin.Xn α g from rfl, hMdef]
        have h1 := sqrt_pi_div_two_mul_sqrt_two
        have h2 := alpha_mul_sqrt_ten_div hα
        calc 3 * (2 * α * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g))
              * Real.sqrt (Real.pi / 2) * (Real.sqrt 2 * Work.FTS.Nonlin.Xn α g)
            = 60 * (α * Real.sqrt (10 / α)
                * (Real.sqrt (Real.pi / 2) * Real.sqrt 2)) * max Ce 0
                * Work.FTS.Nonlin.Xn α g ^ 2 := by ring
          _ = 60 * (α * Real.sqrt (10 / α) * Real.sqrt Real.pi) * max Ce 0
                * Work.FTS.Nonlin.Xn α g ^ 2 := by rw [h1]
          _ = 60 * (Real.sqrt (10 * Real.pi) * α ^ (1 / 2 : ℝ)) * max Ce 0
                * Work.FTS.Nonlin.Xn α g ^ 2 := by rw [h2]
          _ ≤ 60 * Real.sqrt (10 * Real.pi) * max Ce 0 * α ^ (1 / 2 : ℝ)
                * Work.FTS.Nonlin.Xn α g ^ 2 := le_of_eq (by ring)

/-- `N₄^{gg} = -(1/2)FK(g)·D_θg`, estimated by `(9π/4)·|g|²`. -/
theorem N4gg_bound {α Ce : ℝ} {g Φg : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hGal : Work.FTS.Nonlin.GalClass α g) (hEll : Work.FTS.Nonlin.EllPkgG α Ce g Φg) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4gg α g r θ|))
      ≤ ENNReal.ofReal (9 * Real.pi / 4 * Work.FTS.Nonlin.Xn α g ^ 2) := by
  have hsqg : Work.FTS.LocData.SmoothQuad g := hGal.reg.1
  have hmemg : Work.Spaces.HkMem α 4 g :=
    Work.FTS.LocDataExt.HkMem_mono (by norm_num) hsqg hGal.reg.2.1
  obtain ⟨hΦ0nn, hΦ0slice, hΦ0meas, hΦ0int, hΦ0le⟩ :=
    Phi0_props hsqg hmemg (aesm_slice_zero_of_axis fun θ hθ => (hGal.axis θ hθ).1)
  obtain ⟨hΦ1nn, hΦ1slice, hΦ1meas, hΦ1int, hΦ1le⟩ :=
    Phi1_props hα.le hsqg hmemg (aesm_slice_zero_Dth_of_axis fun θ hθ => (hGal.axis θ hθ).1)
  have hinn : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * A4 g r θ * Work.Spaces.Dth g r θ|)
        ≤ ENNReal.ofReal (9 * Real.pi / 4)
            * ((ENNReal.ofReal (Phi0 g r)) ^ (1 / 2 : ℝ)
              * (ENNReal.ofReal (Phi1 g r)) ^ (1 / 2 : ℝ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hAmeas : MeasureTheory.AEStronglyMeasurable (fun θ => A4 g r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      simp only [A4]
      exact MeasureTheory.AEStronglyMeasurable.const_mul aestronglyMeasurable_const (-(1 / 2))
    have hBmeas : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.Dth g r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := aesm_slice_Dth_of_smoothQuad hsqg hr
    have hAb : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        |A4 g r θ| ≤ |Work.Construction.FK g r| / 2 := by
      filter_upwards with θ
      have h2 : |A4 g r θ| = |Work.Construction.FK g r| / 2 := by
        simp only [A4]
        rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        ring
      rw [h2]
    have hB : (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.Spaces.Dth g r θ) ^ 2)) ≤ ENNReal.ofReal (Phi1 g r) := by
      rw [Phi1, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hΦ1slice r hr)
        (Filter.Eventually.of_forall fun θ => sq_nonneg _)]
    have hstep := Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.inner_lintegral_le
      (by positivity : (0 : ℝ) ≤ |Work.Construction.FK g r| / 2) (Phi1_nonneg g r)
      hAmeas hBmeas hAb hB
    refine le_trans hstep ?_
    have hconst : ENNReal.ofReal (3 * (|Work.Construction.FK g r| / 2)
          * Real.sqrt (Real.pi / 2))
        ≤ ENNReal.ofReal (9 * Real.pi / 4) * (ENNReal.ofReal (Phi0 g r)) ^ (1 / 2 : ℝ) := by
      rw [← ofReal_mul_sqrt (show (0 : ℝ) ≤ 9 * Real.pi / 4 by positivity) (Phi0_nonneg g r)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hFK := Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.FK_pointwise_le (g := g) (z := r)
        (integrableOn_mul_K_of_sq (aesm_slice_of_smoothQuad hsqg hr) (hΦ0slice r hr))
        (hΦ0slice r hr)
      have hsq : Real.sqrt (Real.pi / 2) * Real.sqrt (Real.pi / 2) = Real.pi / 2 :=
        Real.mul_self_sqrt (by positivity)
      have h2 : |Work.Construction.FK g r|
          ≤ 3 * Real.sqrt (Real.pi / 2) * Real.sqrt (Phi0 g r) := by
        simpa only [Phi0] using hFK
      calc 3 * (|Work.Construction.FK g r| / 2) * Real.sqrt (Real.pi / 2)
          ≤ 3 * ((3 * Real.sqrt (Real.pi / 2) * Real.sqrt (Phi0 g r)) / 2)
              * Real.sqrt (Real.pi / 2) := by gcongr
        _ = 9 * Real.pi / 4 * Real.sqrt (Phi0 g r) := by
            have h3 : (3 : ℝ) * (3 * Real.sqrt (Real.pi / 2) * Real.sqrt (Phi0 g r) / 2)
                * Real.sqrt (Real.pi / 2)
                = (9 / 2) * (Real.sqrt (Real.pi / 2) * Real.sqrt (Real.pi / 2))
                  * Real.sqrt (Phi0 g r) := by ring
            rw [h3, hsq]
            ring
    calc ENNReal.ofReal (3 * (|Work.Construction.FK g r| / 2) * Real.sqrt (Real.pi / 2))
          * (ENNReal.ofReal (Phi1 g r)) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (9 * Real.pi / 4) * (ENNReal.ofReal (Phi0 g r)) ^ (1 / 2 : ℝ))
            * (ENNReal.ofReal (Phi1 g r)) ^ (1 / 2 : ℝ) := mul_le_mul_left hconst _
      _ = ENNReal.ofReal (9 * Real.pi / 4) * ((ENNReal.ofReal (Phi0 g r)) ^ (1 / 2 : ℝ)
            * (ENNReal.ofReal (Phi1 g r)) ^ (1 / 2 : ℝ)) := by ring
  have hmain := outer_of_inner_pair (A := A4 g) (B := Work.Spaces.Dth g)
    (Φ := Phi0 g) (Ψ := Phi1 g) (Xs := Work.Spaces.HkSq α 4 g)
    (Ys := Work.Spaces.HkSq α 4 g) (c := 9 * Real.pi / 4) (by positivity) hinn
    hΦ0nn hΦ1nn hΦ0meas hΦ1meas hΦ0int hΦ1int hΦ0le hΦ1le
  calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4gg α g r θ|))
      = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ
            * (A4 g r θ * Work.Spaces.Dth g r θ)|)) := by
        simp only [N4gg_eq]
    _ = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * A4 g r θ * Work.Spaces.Dth g r θ|)) := by
        refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
        refine congrArg (fun t => ENNReal.ofReal r⁻¹ * t) ?_
        refine MeasureTheory.lintegral_congr (fun θ => ?_)
        rw [mul_assoc]
    _ ≤ ENNReal.ofReal (9 * Real.pi / 4
          * (Real.sqrt (Work.Spaces.HkSq α 4 g) * Real.sqrt (Work.Spaces.HkSq α 4 g))) := hmain
    _ = ENNReal.ofReal (9 * Real.pi / 4 * Work.FTS.Nonlin.Xn α g ^ 2) := by
        rw [show Real.sqrt (Work.Spaces.HkSq α 4 g) = Work.FTS.Nonlin.Xn α g from rfl, sq]

/-- `N₅^{gg} = -sin²θ·FK(g)·g`, estimated by `(9π/2)·|g|²`. -/
theorem N5gg_bound {α Ce : ℝ} {g Φg : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hGal : Work.FTS.Nonlin.GalClass α g) (hEll : Work.FTS.Nonlin.EllPkgG α Ce g Φg) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5gg g r θ|))
      ≤ ENNReal.ofReal (9 * Real.pi / 2 * Work.FTS.Nonlin.Xn α g ^ 2) := by
  have hsqg : Work.FTS.LocData.SmoothQuad g := hGal.reg.1
  have hmemg : Work.Spaces.HkMem α 4 g :=
    Work.FTS.LocDataExt.HkMem_mono (by norm_num) hsqg hGal.reg.2.1
  obtain ⟨hΦ0nn, hΦ0slice, hΦ0meas, hΦ0int, hΦ0le⟩ :=
    Phi0_props hsqg hmemg (aesm_slice_zero_of_axis fun θ hθ => (hGal.axis θ hθ).1)
  have hinn : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * A5 g r θ * g r θ|)
        ≤ ENNReal.ofReal (9 * Real.pi / 2)
            * ((ENNReal.ofReal (Phi0 g r)) ^ (1 / 2 : ℝ)
              * (ENNReal.ofReal (Phi0 g r)) ^ (1 / 2 : ℝ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hAmeas : MeasureTheory.AEStronglyMeasurable (fun θ => A5 g r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      simp only [A5]
      exact (Real.continuous_sin.pow 2).neg.aestronglyMeasurable.mul_const _
    have hBmeas : MeasureTheory.AEStronglyMeasurable (fun θ => g r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := aesm_slice_of_smoothQuad hsqg hr
    have hAb : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        |A5 g r θ| ≤ |Work.Construction.FK g r| := by
      filter_upwards with θ
      have h2 : |A5 g r θ| = (Real.sin θ) ^ 2 * |Work.Construction.FK g r| := by
        simp only [A5]
        rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))]
      rw [h2]
      calc (Real.sin θ) ^ 2 * |Work.Construction.FK g r|
          ≤ 1 * |Work.Construction.FK g r| :=
            mul_le_mul_of_nonneg_right (abs_sin_sq_le_one θ) (abs_nonneg _)
        _ = |Work.Construction.FK g r| := one_mul _
    have hB : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((g r θ) ^ 2))
        ≤ ENNReal.ofReal (Phi0 g r) := by
      rw [Phi0, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hΦ0slice r hr)
        (Filter.Eventually.of_forall fun θ => sq_nonneg _)]
    have hstep := Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.inner_lintegral_le
      (abs_nonneg _) (Phi0_nonneg g r) hAmeas hBmeas hAb hB
    refine le_trans hstep ?_
    have hconst : ENNReal.ofReal (3 * |Work.Construction.FK g r| * Real.sqrt (Real.pi / 2))
        ≤ ENNReal.ofReal (9 * Real.pi / 2) * (ENNReal.ofReal (Phi0 g r)) ^ (1 / 2 : ℝ) := by
      rw [← ofReal_mul_sqrt (show (0 : ℝ) ≤ 9 * Real.pi / 2 by positivity) (Phi0_nonneg g r)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hFK := Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.FK_pointwise_le (g := g) (z := r)
        (integrableOn_mul_K_of_sq (aesm_slice_of_smoothQuad hsqg hr) (hΦ0slice r hr))
        (hΦ0slice r hr)
      have hsq : Real.sqrt (Real.pi / 2) * Real.sqrt (Real.pi / 2) = Real.pi / 2 :=
        Real.mul_self_sqrt (by positivity)
      have h2 : |Work.Construction.FK g r|
          ≤ 3 * Real.sqrt (Real.pi / 2) * Real.sqrt (Phi0 g r) := by
        simpa only [Phi0] using hFK
      calc 3 * |Work.Construction.FK g r| * Real.sqrt (Real.pi / 2)
          ≤ 3 * (3 * Real.sqrt (Real.pi / 2) * Real.sqrt (Phi0 g r))
              * Real.sqrt (Real.pi / 2) := by gcongr
        _ = 9 * Real.pi / 2 * Real.sqrt (Phi0 g r) := by
            have h3 : (3 : ℝ) * (3 * Real.sqrt (Real.pi / 2) * Real.sqrt (Phi0 g r))
                * Real.sqrt (Real.pi / 2)
                = 9 * (Real.sqrt (Real.pi / 2) * Real.sqrt (Real.pi / 2))
                  * Real.sqrt (Phi0 g r) := by ring
            rw [h3, hsq]
            ring
    calc ENNReal.ofReal (3 * |Work.Construction.FK g r| * Real.sqrt (Real.pi / 2))
          * (ENNReal.ofReal (Phi0 g r)) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (9 * Real.pi / 2) * (ENNReal.ofReal (Phi0 g r)) ^ (1 / 2 : ℝ))
            * (ENNReal.ofReal (Phi0 g r)) ^ (1 / 2 : ℝ) := mul_le_mul_left hconst _
      _ = ENNReal.ofReal (9 * Real.pi / 2) * ((ENNReal.ofReal (Phi0 g r)) ^ (1 / 2 : ℝ)
            * (ENNReal.ofReal (Phi0 g r)) ^ (1 / 2 : ℝ)) := by ring
  have hmain := outer_of_inner_pair (A := A5 g) (B := g)
    (Φ := Phi0 g) (Ψ := Phi0 g) (Xs := Work.Spaces.HkSq α 4 g)
    (Ys := Work.Spaces.HkSq α 4 g) (c := 9 * Real.pi / 2) (by positivity) hinn
    hΦ0nn hΦ0nn hΦ0meas hΦ0meas hΦ0int hΦ0int hΦ0le hΦ0le
  calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5gg g r θ|))
      = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * (A5 g r θ * g r θ)|)) := by
        simp only [N5gg_eq]
    _ = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * A5 g r θ * g r θ|)) := by
        refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
        refine congrArg (fun t => ENNReal.ofReal r⁻¹ * t) ?_
        refine MeasureTheory.lintegral_congr (fun θ => ?_)
        rw [mul_assoc]
    _ ≤ ENNReal.ofReal (9 * Real.pi / 2
          * (Real.sqrt (Work.Spaces.HkSq α 4 g) * Real.sqrt (Work.Spaces.HkSq α 4 g))) := hmain
    _ = ENNReal.ofReal (9 * Real.pi / 2 * Work.FTS.Nonlin.Xn α g ^ 2) := by
        rw [show Real.sqrt (Work.Spaces.HkSq α 4 g) = Work.FTS.Nonlin.Xn α g from rfl, sq]

/-! ## The constant and the theorem -/

/-- The constant of `Pgg`; only `Ce` matters, the other parameters are included so that a
single choice works for all five pieces. -/
def PggK (Ce Ci Cs α₂ : ℝ) : ℝ :=
  1000 * (1 + |Ce| + |Ci| + |Cs| + |α₂|) * (1 + Real.sqrt (10 * Real.pi))

theorem PggK_pos (Ce Ci Cs α₂ : ℝ) : 0 < PggK Ce Ci Cs α₂ := by
  have h1 : (0 : ℝ) < 1 + |Ce| + |Ci| + |Cs| + |α₂| := by
    have h2 : (0 : ℝ) ≤ |Ce| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ |Ci| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ |Cs| := abs_nonneg _
    have h5 : (0 : ℝ) ≤ |α₂| := abs_nonneg _
    linarith
  have h2 : (0 : ℝ) < 1 + Real.sqrt (10 * Real.pi) := by
    linarith [Real.sqrt_nonneg (10 * Real.pi)]
  unfold PggK
  positivity

theorem const_le_PggK {Ce Ci Cs α₂ : ℝ} :
    60 * Real.sqrt (10 * Real.pi) * max Ce 0 ≤ PggK Ce Ci Cs α₂ := by
  have hA : (0 : ℝ) ≤ 1 + |Ce| + |Ci| + |Cs| + |α₂| := by
    have h2 : (0 : ℝ) ≤ |Ce| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ |Ci| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ |Cs| := abs_nonneg _
    have h5 : (0 : ℝ) ≤ |α₂| := abs_nonneg _
    linarith
  have hB : (0 : ℝ) ≤ 1 + Real.sqrt (10 * Real.pi) := by
    linarith [Real.sqrt_nonneg (10 * Real.pi)]
  have hX1 : max Ce 0 ≤ 1 + |Ce| + |Ci| + |Cs| + |α₂| := by
    have h1 : Ce ≤ |Ce| := le_abs_self Ce
    have h2 : (0 : ℝ) ≤ |Ce| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ |Ci| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ |Cs| := abs_nonneg _
    have h5 : (0 : ℝ) ≤ |α₂| := abs_nonneg _
    rcases le_total Ce 0 with h6 | h6
    · rw [max_eq_right h6]; linarith
    · rw [max_eq_left h6]; linarith
  calc 60 * Real.sqrt (10 * Real.pi) * max Ce 0
      ≤ 60 * (1 + Real.sqrt (10 * Real.pi)) * (1 + |Ce| + |Ci| + |Cs| + |α₂|) := by
        gcongr
        linarith [Real.sqrt_nonneg (10 * Real.pi)]
    _ ≤ 1000 * (1 + |Ce| + |Ci| + |Cs| + |α₂|) * (1 + Real.sqrt (10 * Real.pi)) := by
        nlinarith [hA, hB]
    _ ≤ PggK Ce Ci Cs α₂ := le_of_eq (by rw [PggK])

theorem seven_le_PggK {Ce Ci Cs α₂ : ℝ} :
    9 * Real.pi / 2 ≤ PggK Ce Ci Cs α₂ := by
  have hA : (1 : ℝ) ≤ 1 + |Ce| + |Ci| + |Cs| + |α₂| := by
    have h2 : (0 : ℝ) ≤ |Ce| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ |Ci| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ |Cs| := abs_nonneg _
    have h5 : (0 : ℝ) ≤ |α₂| := abs_nonneg _
    linarith
  have hB : (1 : ℝ) ≤ 1 + Real.sqrt (10 * Real.pi) := by
    linarith [Real.sqrt_nonneg (10 * Real.pi)]
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hAB : (1 : ℝ) ≤ (1 + |Ce| + |Ci| + |Cs| + |α₂|) * (1 + Real.sqrt (10 * Real.pi)) :=
    one_le_mul_of_one_le_of_one_le hA hB
  have h9 : 9 * Real.pi / 2 ≤ 1000 := by nlinarith [Real.pi_pos, hpi]
  rw [PggK]
  calc 9 * Real.pi / 2 ≤ 1000 := h9
    _ = 1000 * 1 := (mul_one 1000).symm
    _ ≤ 1000 * ((1 + |Ce| + |Ci| + |Cs| + |α₂|) * (1 + Real.sqrt (10 * Real.pi))) :=
        mul_le_mul_of_nonneg_left hAB (by norm_num)
    _ ≤ 1000 * (1 + |Ce| + |Ci| + |Cs| + |α₂|) * (1 + Real.sqrt (10 * Real.pi)) :=
        le_of_eq (by ring)

theorem Pgg {α₂ Ci Ce Cs : ℝ} :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.N4Norm Ci α₂ →
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg →
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N1gg α g Φg r θ|))
        ≤ ENNReal.ofReal (K * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N2gg α g Φg r θ|))
        ≤ ENNReal.ofReal (K * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N3gg α g Φg r θ|))
        ≤ ENNReal.ofReal (K * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4gg α g r θ|))
        ≤ ENNReal.ofReal (K * Work.FTS.Nonlin.Xn α g ^ 2) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5gg g r θ|))
        ≤ ENNReal.ofReal (K * Work.FTS.Nonlin.Xn α g ^ 2) := by
  refine ⟨PggK Ce Ci Cs α₂, PggK_pos Ce Ci Cs α₂, ?_⟩
  intro α g Φs Φg hα hα1 hα2 hN hGal hStar hEll
  have hK := const_le_PggK (Ce := Ce) (Ci := Ci) (Cs := Cs) (α₂ := α₂)
  have hK7 := seven_le_PggK (Ce := Ce) (Ci := Ci) (Cs := Cs) (α₂ := α₂)
  have hXn : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g ^ 2 := sq_nonneg _
  have hαp : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hα _).le
  have hαq : (0 : ℝ) ≤ α ^ (1 / 2 : ℝ) := (Real.rpow_pos_of_pos hα _).le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans (N1gg_bound hα hα1 hGal hEll) (ENNReal.ofReal_le_ofReal ?_)
    calc 60 * Real.sqrt (10 * Real.pi) * max Ce 0 * α ^ (-(1 / 2 : ℝ))
          * Work.FTS.Nonlin.Xn α g ^ 2
        ≤ PggK Ce Ci Cs α₂ * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := by
          gcongr
      _ = PggK Ce Ci Cs α₂ * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := rfl
  · refine le_trans (N2gg_bound hα hα1 hGal hEll) (ENNReal.ofReal_le_ofReal ?_)
    calc 60 * Real.sqrt (10 * Real.pi) * max Ce 0 * α ^ (-(1 / 2 : ℝ))
          * Work.FTS.Nonlin.Xn α g ^ 2
        ≤ PggK Ce Ci Cs α₂ * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := by
          gcongr
      _ = PggK Ce Ci Cs α₂ * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := rfl
  · refine le_trans (N3gg_bound hα hα1 hGal hEll) (ENNReal.ofReal_le_ofReal ?_)
    calc 60 * Real.sqrt (10 * Real.pi) * max Ce 0 * α ^ (1 / 2 : ℝ)
          * Work.FTS.Nonlin.Xn α g ^ 2
        ≤ PggK Ce Ci Cs α₂ * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2 := by
          gcongr
      _ = PggK Ce Ci Cs α₂ * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2 := rfl
  · refine le_trans (N4gg_bound hα hα1 hGal hEll) (ENNReal.ofReal_le_ofReal ?_)
    calc 9 * Real.pi / 4 * Work.FTS.Nonlin.Xn α g ^ 2
        ≤ PggK Ce Ci Cs α₂ * Work.FTS.Nonlin.Xn α g ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ hXn
          linarith [hK7, Real.pi_pos]
      _ = PggK Ce Ci Cs α₂ * Work.FTS.Nonlin.Xn α g ^ 2 := rfl
  · refine le_trans (N5gg_bound hα hα1 hGal hEll) (ENNReal.ofReal_le_ofReal ?_)
    calc 9 * Real.pi / 2 * Work.FTS.Nonlin.Xn α g ^ 2
        ≤ PggK Ce Ci Cs α₂ * Work.FTS.Nonlin.Xn α g ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ hXn
          linarith [hK7, Real.pi_pos]
      _ = PggK Ce Ci Cs α₂ * Work.FTS.Nonlin.Xn α g ^ 2 := rfl

end Work.FTS.Nonlinear.Pieces.rl1Pieces
