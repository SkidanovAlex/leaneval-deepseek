/-
# The `I₁ + I₂` combination of `N₀` at level `ℋ⁶`

The two `F_*`-quadratic terms of `N₀` (`Work.Construction.N0`, paper tex 1398--1402),

`(3/(2α)) sin(2θ) L₁₂(F_*) ∂_θF_*  -  c2m(θ) L₁₂(F_*) D_zF_*`,

each of which is only `O(z)` at the axis `z = 0`, collapse (by
`Work.Construction.N0_first_two_eq'`, which rests on the identity
`3 sin(2θ) ∂_θΓ = 2α c2m Γ` for `Γ = Spaces.Gam α`) to the *quadratic-vanishing*
separable datum

`close6 α (z,θ) = 8α² c2m(θ) z² Γ(θ) / (c(α) (1+z)⁴) = Kfac α · rhoR z · psiA α θ`.

This file proves that the combination lies in `ℋ⁶` with `ℋ⁶`-norm `≤ K α²`, uniformly in
`0 < α ≤ 1` (the `I₁ + I₂` row of the §Modulation table at level six).

## The route

`HkSq`/`HkNorm` only see the values on the open quadrant (`Work.FTS.EllipticEst.HkSq_congr_open`
and `Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0`), so it suffices to treat the separable
datum `sep6 α`.  For a separable `f (z,θ) = a(z)·b(θ)` one has

* `D_z^i f = (Zop^[i] a)·b` and `mixed j i f = (Zop^[j] a)·(Lop^[i] b)` (`sepF_DzIter`,
  `sepF_mixed` of `Work.Construction.GammaTermAux`), and
* the weights factor as `w(z)² = w(z)·w(z)` and `(Wt α z θ)² = w(z)² sin(2θ)^{-γ}`
  (`Work.Spaces.bt_Wt_sq`),

so `HkIntegrand α 6 (sep6 α)` is dominated on `Iz × Iθ` by the separable majorant

`(Kfac α)² (M/(1+z)²)² · gammaAngMaj6 α D θ`,

where `M` prices the radial jets `|Zop^[j] rhoR · w| ≤ M/(1+z)²` (`j ≤ 6`) and `D` the
angular jets `|Lop^[i] psiA| ≤ D Γ (sin²2θ + α)` (`1 ≤ i ≤ 6`).  The two computational cores
are `Work.Construction.H6N_GammaTerm_rho_bound` and
`Work.Construction.H6N_GammaTerm_Lop_bound`; the pointwise domination itself is
`Work.Construction.H6N_GammaTerm_sep_le`.  Integrating the majorant (`∫_z (1/(1+z)²)² ≤ 2`,
`∫_θ gammaAngMaj6 ≤ H6AngConst D`) gives `HkSq α 6 ≤ 6400 · M² · (2 H6AngConst D) · α⁴`,
whence `HkNorm α 6 ≤ √(6400 · M² · (2 H6AngConst D)) · α²`.

The `ℋ⁶`-membership itself comes from `Work.FTS.LocData.HkMem_of_majorant` (the integrand is
continuous on the open quadrant because `sep6 α` is `C⁶` there).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Construction.Basic
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.Construction.GammaTermAux
import Submission.Work.Construction.GammaN0
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.Construction.H6N_GammaTerm_sep_le
import Submission.Work.Construction.H6N_GammaTerm_Lop_bound
import Submission.Work.Construction.H6N_GammaTerm_rho_bound
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.Good
import Submission.Work.Spaces.bt_aux
import Submission.Work.Elliptic.WtoH
import Submission.Work.Elliptic.WtoH_IntZ
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The three forms of the datum, and the majorant -/

/-- The separable form `a(z)·b(θ)` of the collapsed pair, with `a = Kfac α · rhoR` and
`b = psiA α`. -/
noncomputable def sep6 (α : ℝ) : ℝ → ℝ → ℝ :=
  Work.Construction.sepF (fun z => Work.Construction.Kfac α * Work.Construction.rhoR z)
    (Work.Construction.psiA α)

/-- The closed form `8α² c2m(θ) z² Γ(θ)/(c(α)(1+z)⁴)` of the collapsed pair
(`Work.Construction.N0_first_two_eq'`). -/
noncomputable def close6 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ
    / (Work.Spaces.c α * (1 + z) ^ 4)

/-- The literal function appearing in the target statement: the `I₁ + I₂` combination of
`N₀`. -/
noncomputable def N012 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 (Work.Construction.Fstar α) z
    * Work.Spaces.pth (Work.Construction.Fstar α) z θ
  - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
    * Work.Spaces.Dz (Work.Construction.Fstar α) z θ

/-- The angular majorant of the level-six `ℋ⁶`-integrand of the separable datum: the `7`
radial slots contribute `28 sin(2θ)^{-η}` and the `49` entries of the mixed double sum
contribute `98 D²(sin(2θ)^{-η} + α² sin(2θ)^{2α/3-γ})`. -/
noncomputable def gammaAngMaj6 (α D θ : ℝ) : ℝ :=
  (28 + 98 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + 98 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)

/-- The value of the `θ`-integral of `gammaAngMaj6`: `(28+98D²)·10⁴ + 98D²·(3000/17)`
(from `∫ sin(2θ)^{-η} ≤ 10⁴` and `α² ∫ sin(2θ)^{2α/3-γ} ≤ 3000/17`). -/
noncomputable def H6AngConst (D : ℝ) : ℝ :=
  (28 + 98 * D ^ 2) * 10000 + 98 * D ^ 2 * (3000 / 17)

/-! ## Elementary properties of the majorant -/

theorem H6AngConst_pos {D : ℝ} (hD : 0 < D) : 0 < H6AngConst D := by
  rw [H6AngConst]
  nlinarith [sq_nonneg D, hD]

theorem gammaAngMaj6_nonneg {α D θ : ℝ} (hD : 0 ≤ D) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ gammaAngMaj6 α D θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.Construction.sin_two_nonneg_of_mem_Iθ hθ
  rw [gammaAngMaj6]
  exact add_nonneg
    (mul_nonneg (by nlinarith [sq_nonneg D]) (Real.rpow_nonneg hs _))
    (mul_nonneg (by positivity) (Real.rpow_nonneg hs _))

theorem integrableOn_gammaAngMaj6 {α D : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ => gammaAngMaj6 α D θ) Work.Spaces.Iθ := by
  have hη1 : -1 < -(Work.Spaces.eta) := by have := Work.Spaces.eta_lt_one; linarith
  have hη2 : -(Work.Spaces.eta) ≤ 0 := by have := Work.Spaces.eta_pos; linarith
  have hg1 : -1 < 2 * α / 3 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hg2 : 2 * α / 3 - Work.Spaces.gam α ≤ 0 := by rw [Work.Spaces.gam]; linarith
  have hunfold : gammaAngMaj6 α D = fun θ =>
      (28 + 98 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + 98 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := rfl
  rw [hunfold]
  exact ((Work.Spaces.sin_two_rpow _ hη1 hη2).1.const_mul _).add
    ((Work.Spaces.sin_two_rpow _ hg1 hg2).1.const_mul _)

theorem integral_gammaAngMaj6_le {α D : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ ≤ H6AngConst D := by
  have hη1 : -1 < -(Work.Spaces.eta) := by have := Work.Spaces.eta_lt_one; linarith
  have hη2 : -(Work.Spaces.eta) ≤ 0 := by have := Work.Spaces.eta_pos; linarith
  have hp : 2 * α / 3 - Work.Spaces.gam α = -1 + 17 * α / 30 := by
    rw [Work.Spaces.gam]; ring
  have hpe1 : -1 < 2 * α / 3 - Work.Spaces.gam α := by rw [hp]; linarith
  have hpe2 : 2 * α / 3 - Work.Spaces.gam α ≤ 0 := by rw [hp]; linarith
  have hint1 : Integrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := (Work.Spaces.sin_two_rpow _ hη1 hη2).1
  have hint2 : Integrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
      (volume.restrict Work.Spaces.Iθ) := (Work.Spaces.sin_two_rpow _ hpe1 hpe2).1
  have hval1 : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ 10000 := by
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_nonneg])).2
    have hden : (-(Work.Spaces.eta)) + 1 = 1 / 100 := by rw [Work.Spaces.eta]; norm_num
    rw [hden] at h
    norm_num at h
    linarith
  have hval2 : α ^ 2 * (∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) ≤ 3000 / 17 := by
    have h := (Work.Spaces.sin_two_rpow (2 * α / 3 - Work.Spaces.gam α) hpe1 hpe2).2
    have hden : (2 * α / 3 - Work.Spaces.gam α) + 1 = 17 * α / 30 := by
      rw [Work.Spaces.gam]; ring
    rw [hden] at h
    calc α ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
        ≤ α ^ 2 * (100 / (17 * α / 30)) := mul_le_mul_of_nonneg_left h (sq_nonneg α)
      _ = 3000 * α / 17 := by field_simp; ring
      _ ≤ 3000 / 17 := by nlinarith [hα1]
  have hunfold : gammaAngMaj6 α D = fun θ =>
      (28 + 98 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + 98 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := rfl
  rw [hunfold, MeasureTheory.integral_add (hint1.const_mul _) (hint2.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have h1 : (28 + 98 * D ^ 2) * (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ (28 + 98 * D ^ 2) * 10000 :=
    mul_le_mul_of_nonneg_left hval1 (by nlinarith [sq_nonneg D])
  have h2 : 98 * D ^ 2 * α ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
      ≤ 98 * D ^ 2 * (3000 / 17) := by
    calc 98 * D ^ 2 * α ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
        = 98 * D ^ 2 * (α ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by ring
      _ ≤ 98 * D ^ 2 * (3000 / 17) := mul_le_mul_of_nonneg_left hval2 (by positivity)
  rw [H6AngConst]
  linarith

/-! ## The closed and separable forms on the open quadrant -/

theorem sep6_eq_close6 (α z θ : ℝ) : sep6 α z θ = close6 α z θ := by
  simp only [sep6, close6, Work.Construction.sepF, Work.Construction.Kfac,
    Work.Construction.rhoR, Work.Construction.psiA]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  ring

theorem sep6_eq_N012 {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) : sep6 α z θ = N012 α z θ := by
  rw [sep6_eq_close6, N012]
  exact (Work.Construction.N0_first_two_eq' hα hα1 hz hθ).symm

/-! ## The `C⁶`-regularity of the separable datum on the open quadrant -/

/-- `sep6 α` is `C⁶` on the open quadrant: the radial factor `Kfac α · rhoR` is a rational
function with its only pole at `z = -1`, and the angular factor `psiA α = c2m · Gam α` is
`C⁶` there. -/
theorem contDiffOn_uncurry_sep6 (α : ℝ) :
    ContDiffOn ℝ (6 : ℕ) (Function.uncurry (sep6 α)) Work.FTS.OpenPkg.Q0 := by
  have hrad : ContDiffOn ℝ (6 : ℕ)
      (fun p : ℝ × ℝ => Work.Construction.Kfac α * Work.Construction.rhoR p.1)
      Work.FTS.OpenPkg.Q0 := by
    have h1 : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => p.1 ^ 2) Work.FTS.OpenPkg.Q0 :=
      contDiffOn_fst.pow 2
    have h2 : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => (1 + p.1) ^ 4)
        Work.FTS.OpenPkg.Q0 := (contDiffOn_const.add contDiffOn_fst).pow 4
    have h3 : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => p.1 ^ 2 / (1 + p.1) ^ 4)
        Work.FTS.OpenPkg.Q0 :=
      h1.div h2 (fun p hp => pow_ne_zero 4 (ne_of_gt (by
        have hmem : (0 : ℝ) < p.1 := by
          rw [Work.FTS.OpenPkg.Q0] at hp; exact hp.1
        linarith)))
    have h4 : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => Work.Construction.rhoR p.1)
        Work.FTS.OpenPkg.Q0 := by
      simpa only [Work.Construction.rhoR] using h3
    exact contDiffOn_const.mul h4
  have hang : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => Work.Construction.psiA α p.2)
      Work.FTS.OpenPkg.Q0 := by
    have hc2m : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
        Work.FTS.OpenPkg.Q0 := by
      have h1 : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => Real.cos (2 * p.2))
          Work.FTS.OpenPkg.Q0 :=
        (((Real.contDiff_cos.comp (contDiff_const.mul contDiff_snd)).contDiffOn).of_le le_top)
      have h2 : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => Real.sin p.2 ^ 2)
          Work.FTS.OpenPkg.Q0 :=
        ((((Real.contDiff_sin.comp contDiff_snd).pow 2).contDiffOn).of_le le_top)
      simpa only [Work.Construction.c2m] using h1.sub h2
    have hGam : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
        Work.FTS.OpenPkg.Q0 := Work.FTS.OpenPkg.contDiffOn_Gam_Q0 α 6
    simpa only [Work.Construction.psiA] using hc2m.mul hGam
  refine (hrad.mul hang).congr ?_
  intro p _
  rfl

/-! ## The `ℋ⁶`-membership of the separable datum -/

/-- `z ↦ (1/(1+z)²)²` is integrable on `Iz` (it is bounded by `1/(1+z)²`, whose integral is
`≤ 2`, `Work.Elliptic.WtoH_IntZ`). -/
theorem integrableOn_inv_one_add_pow_four :
    IntegrableOn (fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2) Work.Spaces.Iz := by
  refine Work.Elliptic.WtoH_IntZ.1.mono' ?_ ?_
  · exact (by fun_prop : Measurable fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have hz0 : (0 : ℝ) ≤ z := hz
    have h1 : (0 : ℝ) ≤ 1 / (1 + z) ^ 2 := by positivity
    have h2 : 1 / (1 + z) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [h1, h2]

theorem HkMem_sep6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {M D : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (sep6 α) z θ
        ≤ (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ) :
    Work.Spaces.HkMem α 6 (sep6 α) := by
  refine Work.FTS.LocData.HkMem_of_majorant α 6
    (M := fun z θ => (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
      * gammaAngMaj6 α D θ) ?_ ?_ ?_ ?_
  · exact Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α (n := 6) (k := 6) le_rfl
      (contDiffOn_uncurry_sep6 α)
  · intro z hz
    exact (integrableOn_gammaAngMaj6 (α := α) (D := D) hα hα1).const_mul _
  · have hbase : IntegrableOn (fun z : ℝ => ((Work.Construction.Kfac α) ^ 2 * M ^ 2
        * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)) * (1 / (1 + z) ^ 2) ^ 2)
        Work.Spaces.Iz := integrableOn_inv_one_add_pow_four.const_mul _
    refine hbase.congr_fun ?_ measurableSet_Ici
    intro z hz
    dsimp only
    rw [MeasureTheory.integral_const_mul]
    ring
  · intro z hz θ hθ
    exact hpt z hz θ hθ

/-! ## The `ℋ⁶`-square bound -/

theorem Kfac_nonneg {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : 0 ≤ Work.Construction.Kfac α := by
  have hc : 0 < Work.Spaces.c α := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  rw [Work.Construction.Kfac]
  positivity

theorem Kfac_sq_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (Work.Construction.Kfac α) ^ 2 ≤ 6400 * α ^ 4 := by
  have hc1 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hc2 : (1 / 100 : ℝ) ≤ (Work.Spaces.c α) ^ 2 := by nlinarith
  have hα4 : (0 : ℝ) < α ^ 4 := pow_pos hα 4
  rw [Work.Construction.Kfac, div_pow]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Work.Spaces.c α) ^ 2)]
  nlinarith [hc2, hα4]

theorem HkSq_sep6_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {M D : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (sep6 α) z θ
        ≤ (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ) :
    Work.Spaces.HkSq α 6 (sep6 α) ≤ 6400 * M ^ 2 * (2 * H6AngConst D) * α ^ 4 := by
  have hKfSq : (Work.Construction.Kfac α) ^ 2 ≤ 6400 * α ^ 4 := Kfac_sq_le hα hα1
  have hKfnn : 0 ≤ Work.Construction.Kfac α := Kfac_nonneg hα hα1
  have hBigint : Integrable (fun θ : ℝ => gammaAngMaj6 α D θ)
      (volume.restrict Work.Spaces.Iθ) := integrableOn_gammaAngMaj6 hα hα1
  have hBigval : ∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ ≤ H6AngConst D :=
    integral_gammaAngMaj6_le hα hα1
  have hBignn : 0 ≤ ∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      gammaAngMaj6_nonneg (le_of_lt hD) hθ
  have hzint : Integrable (fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2)
      (volume.restrict Work.Spaces.Iz) := integrableOn_inv_one_add_pow_four
  have hzval : ∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2 ≤ 2 := by
    have hle : (fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2)
        ≤ᵐ[volume.restrict Work.Spaces.Iz] (fun z : ℝ => 1 / (1 + z) ^ 2) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      have hz0 : (0 : ℝ) ≤ z := hz
      have h2 : 1 / (1 + z) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith
      have h3 : (0 : ℝ) ≤ 1 / (1 + z) ^ 2 := by positivity
      nlinarith [h2, h3]
    exact le_trans (MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall fun z => by positivity) Work.Elliptic.WtoH_IntZ.1 hle)
      Work.Elliptic.WtoH_IntZ.2
  have hWint : 0 ≤ ∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z hz => by positivity
  have hinner_eq : ∀ z : ℝ, ∫ θ in Work.Spaces.Iθ,
        (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ
      = (Work.Construction.Kfac α) ^ 2 * M ^ 2 * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)
          * (1 / (1 + z) ^ 2) ^ 2 := by
    intro z
    rw [MeasureTheory.integral_const_mul]
    ring
  have houter_eq : ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ
      = (Work.Construction.Kfac α) ^ 2 * M ^ 2 * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)
          * (∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2) := by
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ)
        = fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2
            * ((Work.Construction.Kfac α) ^ 2 * M ^ 2
              * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)) from by
      funext z; rw [hinner_eq z]; ring]
    rw [MeasureTheory.integral_mul_const]
    ring
  have hMajint : Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ)
      (volume.restrict Work.Spaces.Iz) := by
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ)
        = fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2
            * ((Work.Construction.Kfac α) ^ 2 * M ^ 2
              * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)) from by
      funext z; rw [hinner_eq z]; ring]
    exact hzint.mul_const _
  have hmono : ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 (sep6 α) z θ
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ :=
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 6 (sep6 α) z θ))
      hMajint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun z hz => MeasureTheory.integral_mono_of_nonneg
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ =>
            Work.Spaces.HkIntegrand_nonneg α 6 (sep6 α) z θ))
          (hBigint.const_mul _)
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (hpt z hz))))
  have hfinal : (Work.Construction.Kfac α) ^ 2 * M ^ 2
        * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)
        * (∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2)
      ≤ 6400 * M ^ 2 * (2 * H6AngConst D) * α ^ 4 := by
    have h1 : (Work.Construction.Kfac α) ^ 2 * M ^ 2
          * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)
        ≤ (Work.Construction.Kfac α) ^ 2 * M ^ 2 * H6AngConst D :=
      mul_le_mul_of_nonneg_left hBigval
        (mul_nonneg (sq_nonneg (Work.Construction.Kfac α)) (sq_nonneg M))
    have h2 : (Work.Construction.Kfac α) ^ 2 * M ^ 2
          * (∫ θ in Work.Spaces.Iθ, gammaAngMaj6 α D θ)
          * (∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) ^ 2)
        ≤ (Work.Construction.Kfac α) ^ 2 * M ^ 2 * H6AngConst D * 2 :=
      mul_le_mul h1 hzval hWint
        (mul_nonneg (mul_nonneg (sq_nonneg (Work.Construction.Kfac α)) (sq_nonneg M))
          (le_of_lt (H6AngConst_pos hD)))
    have hnn : 0 ≤ M ^ 2 * H6AngConst D * 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg M) (le_of_lt (H6AngConst_pos hD))) (by norm_num)
    have h3 : (Work.Construction.Kfac α) ^ 2 * M ^ 2 * H6AngConst D * 2
        ≤ 6400 * M ^ 2 * (2 * H6AngConst D) * α ^ 4 := by
      calc (Work.Construction.Kfac α) ^ 2 * M ^ 2 * H6AngConst D * 2
          = (Work.Construction.Kfac α) ^ 2 * (M ^ 2 * H6AngConst D * 2) := by ring
        _ ≤ (6400 * α ^ 4) * (M ^ 2 * H6AngConst D * 2) :=
            mul_le_mul_of_nonneg_right hKfSq hnn
        _ = 6400 * M ^ 2 * (2 * H6AngConst D) * α ^ 4 := by ring
    linarith
  rw [Work.Spaces.HkSq]
  exact le_trans (le_trans hmono (le_of_eq houter_eq)) hfinal

/-! ## The target -/

/-- The target, with the two computational cores supplied as hypotheses (`M`, `D` price the
radial and angular jets of the separable datum). -/
theorem FstarI12H6_of_sep {M D : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hpt : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (sep6 α) z θ
        ≤ (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ) :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.HkMem α 6 (N012 α) ∧
      Work.Spaces.HkNorm α 6 (N012 α) ≤ K * α ^ 2 := by
  refine ⟨Real.sqrt (6400 * M ^ 2 * (2 * H6AngConst D)), ?_, fun α hα hα1 => ?_⟩
  · have h1 : 0 < M ^ 2 := pow_pos hM 2
    have h2 : 0 < H6AngConst D := H6AngConst_pos hD
    exact Real.sqrt_pos.mpr (by positivity)
  · have hptα : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 (sep6 α) z θ
          ≤ (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj6 α D θ :=
      hpt α hα hα1
    have hmem : Work.Spaces.HkMem α 6 (sep6 α) := HkMem_sep6 α hα hα1 hM hD hptα
    have hSq : Work.Spaces.HkSq α 6 (sep6 α) ≤ 6400 * M ^ 2 * (2 * H6AngConst D) * α ^ 4 :=
      HkSq_sep6_le α hα hα1 hM hD hptα
    have hnorm : Work.Spaces.HkNorm α 6 (sep6 α)
        ≤ Real.sqrt (6400 * M ^ 2 * (2 * H6AngConst D)) * α ^ 2 := by
      rw [Work.Spaces.HkNorm]
      calc Real.sqrt (Work.Spaces.HkSq α 6 (sep6 α))
          ≤ Real.sqrt (6400 * M ^ 2 * (2 * H6AngConst D) * α ^ 4) := Real.sqrt_le_sqrt hSq
        _ = Real.sqrt (6400 * M ^ 2 * (2 * H6AngConst D)) * α ^ 2 := by
            have hpos : (0 : ℝ) ≤ 6400 * M ^ 2 * (2 * H6AngConst D) :=
              mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg M))
                (by have := H6AngConst_pos hD; linarith)
            rw [Real.sqrt_mul hpos]
            congr 1
            rw [show α ^ 4 = (α ^ 2) ^ 2 by ring]
            exact Real.sqrt_sq (by positivity)
    have hsqeq : Work.Spaces.HkSq α 6 (N012 α) = Work.Spaces.HkSq α 6 (sep6 α) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 6
        (fun z θ hz hθ hθ2 => (sep6_eq_N012 hα hα1 hz.le ⟨hθ.le, hθ2.le⟩).symm)
    constructor
    · exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 6 hmem
        (fun z hz θ hθ => sep6_eq_N012 hα hα1 hz.le ⟨hθ.1.le, hθ.2.le⟩)
    · rw [Work.Spaces.HkNorm, hsqeq]
      exact hnorm

/-- The `I₁ + I₂` combination of `N₀` (`Construction.N0`, paper tex 1398--1402): by the
exact form of `Γ = Spaces.Gam α` one has the identity `3 sin 2θ ∂_θΓ = 2α c2m Γ`, and the sum
`(3/(2α)) sin2θ L₁₂(F_*) ∂_θF_* - c2m L₁₂(F_*) D_zF_*` collapses to
`8α² z² c2m(θ) Γ(θ)/(c(α)(1+z)⁴)` — in particular it is `O(α²)` with bounded `D`-derivatives
and `ℋ⁶`-norm `≤ K α²`.  (The closed form is already in the tree as
`Work.Construction.N0_first_two_eq'`; only the `ℋ⁶`-membership and the norm bound are new.) -/
theorem FstarI12H6 : ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.HkMem α 6 (fun z θ =>
        (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ∧
    Work.Spaces.HkNorm α 6 (fun z θ =>
        (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ K * α ^ 2 := by
  obtain ⟨M, hM, hMr⟩ := Work.Construction.H6N_GammaTerm_rho_bound
  obtain ⟨D, hD, hDl⟩ := Work.Construction.H6N_GammaTerm_Lop_bound
  refine FstarI12H6_of_sep hM hD ?_
  intro α hα hα1 z hz θ hθ
  simpa only [sep6, gammaAngMaj6] using
    (Work.Construction.H6N_GammaTerm_sep_le α hα hα1 hM hD hMr (hDl α hα hα1) z hz θ hθ)

end Work.FTS.StrongPersist.H6Rows
