/-
Copyright: work module for the Elgindi finite-time singularity project.

# Proposition `L12H` (tex lines 1276--1290): `L₁₂` maps `ℋ⁴` to `ℋ⁴`

There is a universal constant `C > 0` so that for every `g ∈ ℋ⁴` with `L₁₂(g)(0) = 0`
one has `L₁₂(g) ∈ ℋ⁴` and `|L₁₂(g)|_{ℋ⁴} ≤ C |g|_{ℋ⁴}`.

The proof follows the paper: `L₁₂(g)` is independent of `θ`, so only the pure `D_z`
terms of the `ℋ⁴`-norm are non-zero, and

* `D_z^k L₁₂(g) = -∫_θ K(θ) D_z^{k-1} g (z,θ) dθ` for `k ≥ 1`, whence those terms are
  bounded by Cauchy–Schwarz in `θ` against `|g|_{ℋ⁴}`;
* the `k = 0` term needs the Hardy-type inequality
  `∫ u² w² ≤ C ∫ (z u')² w²`, proved on `(0,1)` (`HardyLeft`) and on `(1,∞)`
  (`HardyRight`) separately, using `L₁₂(g)(0) = 0` and `L₁₂(g) → 0` at `∞`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.L12_eq_radial
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HardyZ
import Submission.Work.FM.Core2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
-- import Submission.Work.Elliptic.HardyLeft
-- import Submission.Work.Elliptic.HardyRight

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Vocabulary -/

/-- The angular moment `Q_j(z) = ∫_θ K(θ) · (D_z^j g)(z,θ) dθ`.  Note `Q_0(z) = z · L12dens g z`
and `L₁₂(g)(z) = ∫_z^∞ Q_0(s)/s ds`. -/
def Qang (g : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Ktheta θ * Work.Spaces.DzIter j g z θ

/-- The one-dimensional operator `z ∂_z` acting on functions of `z` alone. -/
def Dzd (u : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv u z

/-- Iterated `z ∂_z` on functions of one variable. -/
def DzdIter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, u => u
  | k + 1, u => Dzd (DzdIter k u)

@[simp] theorem DzdIter_zero (u : ℝ → ℝ) : DzdIter 0 u = u := rfl
@[simp] theorem DzdIter_succ (k : ℕ) (u : ℝ → ℝ) :
    DzdIter (k + 1) u = Dzd (DzdIter k u) := rfl

/-- `L12dens` is `Q_0` divided by `z`. -/
theorem L12dens_eq_Qang_div (g : ℝ → ℝ → ℝ) (s : ℝ) :
    L12dens g s = Qang g 0 s / s := by
  rw [L12dens, Qang]
  simp only [Work.Spaces.DzIter_zero]
  rw [MeasureTheory.integral_div]

/-! ## `D_z`-iterates of a radial function -/

theorem DzIter_rad (u : ℝ → ℝ) : ∀ (k : ℕ) (z θ : ℝ),
    Work.Spaces.DzIter k (fun z θ => u z) z θ = DzdIter k u z := by
  intro k
  induction k with
  | zero => intro z θ; rfl
  | succ k ih =>
      intro z θ
      have hfun : (fun z' => Work.Spaces.DzIter k (fun z θ => u z) z' θ) = DzdIter k u :=
        funext fun z' => ih z' θ
      have h1 : Work.Spaces.DzIter (k + 1) (fun z θ => u z) z θ
          = z * deriv (fun z' => Work.Spaces.DzIter k (fun z θ => u z) z' θ) z := rfl
      rw [h1, hfun]
      rfl

theorem DthIter_rad_succ (u : ℝ → ℝ) : ∀ (k : ℕ),
    Work.Spaces.DthIter (k + 1) (fun z θ => u z) = fun _ _ => (0 : ℝ) := by
  intro k
  induction k with
  | zero =>
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => u z) θ = 0
      rw [deriv_const]
      ring
  | succ k ih =>
      funext z θ
      have h1 : Work.Spaces.DthIter (k + 1 + 1) (fun z θ => u z)
          = Work.Spaces.Dth (Work.Spaces.DthIter (k + 1) (fun z θ => u z)) := rfl
      rw [h1, ih]
      show Real.sin (2 * θ) * deriv (fun θ' => (0 : ℝ)) θ = 0
      rw [deriv_const]
      ring

theorem mixed_rad_eq_zero (u : ℝ → ℝ) {j i : ℕ} (hi : 1 ≤ i) :
    Work.Spaces.mixed j i (fun z θ => u z) = fun _ _ => (0 : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [Work.Spaces.mixed, DthIter_rad_succ u k]
  induction j with
  | zero => rfl
  | succ j ih =>
      funext z θ
      show z * deriv (fun z' => Work.Spaces.DzIter j (fun _ _ => (0:ℝ)) z' θ) z = 0
      have hfun : (fun z' => Work.Spaces.DzIter j (fun _ _ => (0:ℝ)) z' θ) = fun _ => (0:ℝ) :=
        funext fun z' => congrFun (congrFun ih z') θ
      rw [hfun, deriv_const]
      ring

/-! ## The `H^k`-integrand and the `H^k`-norm of a radial function -/

theorem sin_two_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], ?_⟩
  have := hθ.2
  linarith [Real.pi_pos]

/-! ## Integrability of the `H^4`-integrand on the product measure -/

theorem contDiffOn_uncurry_of_smoothNbhd {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g) :
    ContDiffOn ℝ ⊤ (Function.uncurry g) Work.Spaces.quadU :=
  hsm.mono fun p hp =>
    ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩

/-- `HkIntegrand α 4 g` is integrable for the product of the restrictions of Lebesgue measure
to `Iz` and `Iθ`, under the standing hypotheses `SmoothNbhd g` and `HkMem α 4 g`. -/
theorem HkIntegrand_integrable_prod (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α 4 g) :
    Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hquad := contDiffOn_uncurry_of_smoothNbhd hsm
  obtain ⟨_, haesm⟩ := Work.Spaces.aesm_HkIntegrand_quad α g hquad
  refine ⟨haesm, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  have hcongr1 : ∫⁻ (p : ℝ × ℝ), ‖Work.Spaces.HkIntegrand α 4 g p.1 p.2‖ₑ
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
      = ∫⁻ (p : ℝ × ℝ), ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 g p.1 p.2)
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    lintegral_congr fun p => Real.enorm_eq_ofReal (Work.Spaces.HkIntegrand_nonneg α 4 g p.1 p.2)
  rw [hcongr1]
  rw [MeasureTheory.lintegral_prod _
    (AEMeasurable.ennreal_ofReal (AEStronglyMeasurable.aemeasurable haesm))]
  have hcongr2 : ∫⁻ (z : ℝ), ∫⁻ (θ : ℝ), ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 g z θ)
        ∂(volume.restrict Work.Spaces.Iθ) ∂(volume.restrict Work.Spaces.Iz)
      = ∫⁻ (z : ℝ), ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        ∂(volume.restrict Work.Spaces.Iz) := by
    refine lintegral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)).symm
  rw [hcongr2]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
    (Eventually.of_forall fun z => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)]
  exact ENNReal.ofReal_lt_top

/-! ## Smoothness on the neighbourhood `nbhU` and the pointwise domination -/

theorem contDiffOn_uncurry_Dz_nbhU {g : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry g) Work.Spaces.nbhU) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dz g)) Work.Spaces.nbhU := by
  have hpz := Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_nbhU h
  have h1 : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz g) p)
      Work.Spaces.nbhU := contDiffOn_fst.mul hpz
  refine h1.congr ?_
  intro p hp
  rfl

theorem contDiffOn_uncurry_DzIter_nbhU {g : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry g) Work.Spaces.nbhU) (n : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter n g)) Work.Spaces.nbhU := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [Work.Spaces.DzIter_succ]; exact contDiffOn_uncurry_Dz_nbhU ih

theorem contDiffOn_uncurry_smoothNbhd {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g) :
    ContDiffOn ℝ ⊤ (Function.uncurry g) Work.Spaces.nbhU := hsm

/-- A.e. (for the product measure) a point of `Iz × Iθ` lies in the open quadrant. -/
theorem ae_mem_Qd_prod :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      p ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (π/2) := by
  rw [MeasureTheory.Measure.prod_restrict]
  change ∀ᵐ p ∂(volume.prod volume).restrict (Set.Ici (0:ℝ) ×ˢ Set.Icc 0 (π / 2)),
      p ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (π / 2)
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Measure.set_prod_ae_eq (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm)]
  exact MeasureTheory.ae_restrict_mem ((isOpen_Ioi.prod isOpen_Ioo).measurableSet)

theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (pow_pos hz 2)]
  nlinarith

theorem one_le_sin_two_rpow_neg_eta {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π/2) :
    (1:ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have := Real.rpow_le_rpow_of_nonpos hsin hle
    (by linarith [Work.Spaces.eta_pos] : -(Work.Spaces.eta) ≤ 0)
  rwa [Real.one_rpow] at this

/-- Pointwise domination on the open quadrant: any pure `D_z`-term of the `H^4`-integrand
is dominated by the whole integrand. -/
theorem sq_DzIter_le_HkIntegrand_Qd (α : ℝ) (g : ℝ → ℝ → ℝ) {j : ℕ} (hj : j ≤ 4)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π/2) :
    (Work.Spaces.DzIter j g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw := one_le_w hz
  have hsinp := one_le_sin_two_rpow_neg_eta hθ0 hθ1
  have hw2 : (1:ℝ) ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
  have hstep : (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    calc (Work.Spaces.DzIter j g z θ) ^ 2
        = (Work.Spaces.DzIter j g z θ) ^ 2 * 1 * 1 := by ring
      _ ≤ (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)) hsinp ?_ (by positivity)
          positivity
  have heq : (Work.Spaces.DzIter j g z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have hs : 0 ≤ Real.sin (2 * θ) := hsin.le
    have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
      norm_num
    rw [mul_pow, div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
    ring
  rw [← heq] at hstep
  exact le_trans hstep (Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ j hj)

theorem ae_DzIter_sq_mul_w_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) {j : ℕ} (hj : j ≤ 4) :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.DzIter j g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g p.1 p.2 := by
  filter_upwards [ae_mem_Qd_prod] with p hp
  obtain ⟨hz, hθ0, hθ1⟩ := hp
  have hsinp := one_le_sin_two_rpow_neg_eta hθ0 hθ1
  have hsin : 0 < Real.sin (2 * p.2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsq : 0 ≤ (Work.Spaces.DzIter j g p.1 p.2) ^ 2 := sq_nonneg _
  have hw2 : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
  calc (Work.Spaces.DzIter j g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
      ≤ (Work.Spaces.DzIter j g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
        nlinarith [mul_nonneg hsq hw2, hsinp]
    _ = (Work.Spaces.DzIter j g p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        have hs : 0 ≤ Real.sin (2 * p.2) := hsin.le
        have hsq' : (Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2)) ^ 2
            = Real.sin (2 * p.2) ^ (Work.Spaces.eta) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
          norm_num
        rw [mul_pow, div_pow, hsq', div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
        ring
    _ ≤ Work.Spaces.HkIntegrand α 4 g p.1 p.2 :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 g p.1 p.2 j hj

/-- Product-integrability of `(D_z^j g)² w²`. -/
theorem integrable_prod_DzIter_sq_mul_w_sq (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 4) :
    Integrable (fun p : ℝ × ℝ => (Work.Spaces.DzIter j g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hsub : Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (π/2) ⊆ Work.Spaces.nbhU := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    rw [Set.mem_Ioi] at hz
    rw [Set.mem_Ioo] at hθ
    exact Work.Spaces.mem_nbhU (show z ∈ Work.Spaces.Iz from hz.le)
      (show θ ∈ Work.Spaces.Iθ from ⟨hθ.1.le, hθ.2.le⟩)
  have hcont1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter j g p.1 p.2) ^ 2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (π/2)) :=
    (((contDiffOn_uncurry_DzIter_nbhU hsm j).continuousOn).mono hsub).pow 2
  have hcont2 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (π/2)) := by
    simp only [Work.Spaces.w]
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) ?_
    intro p hp
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  refine MeasureTheory.Integrable.mono' (HkIntegrand_integrable_prod α g hsm hmem)
    (Work.Spaces.aesm_of_continuousOn_Qd _ (hcont1.mul hcont2)) ?_
  filter_upwards [ae_DzIter_sq_mul_w_sq_le_HkIntegrand α g hsm hj] with p hp
  rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]

/-- The `z`-integral of `w² ∫_θ (D_z^j g)²` is dominated by `HkSq`. -/
theorem integrableOn_w_sq_mul_int_sq (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 4) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2)) Work.Spaces.Iz
    ∧ (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2)) ≤ Work.Spaces.HkSq α 4 g := by
  have hprod := integrable_prod_DzIter_sq_mul_w_sq α g hsm hmem hj
  have hInt2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    HkIntegrand_integrable_prod α g hsm hmem
  have hkey : (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2))
      = fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    funext z
    rw [MeasureTheory.integral_mul_const]
    ring
  have hHk : (∫ p : ℝ × ℝ, Work.Spaces.HkIntegrand α 4 g p.1 p.2
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = Work.Spaces.HkSq α 4 g := (MeasureTheory.integral_prod _ hInt2).trans rfl
  constructor
  · rw [hkey]
    exact MeasureTheory.Integrable.integral_prod_left hprod
  · rw [hkey, ← MeasureTheory.integral_prod _ hprod]
    have h := MeasureTheory.integral_mono_ae hprod hInt2
      (ae_DzIter_sq_mul_w_sq_le_HkIntegrand α g hsm hj)
    rw [hHk] at h
    exact h

/-- The integral over `Iθ` is the interval integral over `0..π/2`. -/
theorem integral_Iθ_eq_interval (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0:ℝ)..(π/2), f θ := by
  rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ π/2)]
  change (∫ θ in Set.Icc (0:ℝ) (π/2), f θ) = ∫ θ in Set.Ioc (0:ℝ) (π/2), f θ
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm]

/-- Cauchy–Schwarz in `θ` for the angular moment: `Q_j(z)² ≤ (∫K²)·(∫(D_z^j g)²)`. -/
theorem Qang_sq_le (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g) (j : ℕ)
    {z : ℝ} (hz : -1 < z) :
    (Qang g j z) ^ 2 ≤ (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := by
  have hsub : ∀ θ ∈ Set.uIcc (0:ℝ) (π/2), (z, θ) ∈ Work.Spaces.nbhU := by
    intro θ hθ
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ π/2)] at hθ
    exact ⟨hz, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hcontG : ContinuousOn (fun θ => Work.Spaces.DzIter j g z θ) (Set.uIcc (0:ℝ) (π/2)) :=
    ((contDiffOn_uncurry_DzIter_nbhU hsm j).continuousOn).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun θ hθ => hsub θ hθ)
  have hcontK : ContinuousOn (fun θ => Ktheta θ) (Set.uIcc (0:ℝ) (π/2)) := by
    unfold Ktheta
    exact ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)).continuousOn
  have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt 0 (π / 2)
    (by positivity : (0:ℝ) ≤ π/2) hcontK hcontG
  have hQ : Qang g j z = ∫ θ in (0:ℝ)..(π/2), Ktheta θ * Work.Spaces.DzIter j g z θ := by
    rw [Qang, integral_Iθ_eq_interval]
  have hK : (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2)
      = ∫ θ in (0:ℝ)..(π/2), Ktheta θ ^ 2 := integral_Iθ_eq_interval _
  have hG : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2)
      = ∫ θ in (0:ℝ)..(π/2), (Work.Spaces.DzIter j g z θ) ^ 2 := integral_Iθ_eq_interval _
  rw [hQ, hK, hG]
  have hsq : (∫ θ in (0:ℝ)..(π/2), Ktheta θ * Work.Spaces.DzIter j g z θ) ^ 2
      = |∫ θ in (0:ℝ)..(π/2), Ktheta θ * Work.Spaces.DzIter j g z θ| ^ 2 := by
    rw [sq_abs]
  rw [hsq]
  refine le_trans (pow_le_pow_left₀ (abs_nonneg _) hcs 2) ?_
  have hA : 0 ≤ ∫ θ in (0:ℝ)..(π/2), Ktheta θ ^ 2 :=
    intervalIntegral.integral_nonneg (by positivity)
      (fun u _ => sq_nonneg (Ktheta u))
  have hB : 0 ≤ ∫ θ in (0:ℝ)..(π/2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    intervalIntegral.integral_nonneg (by positivity)
      (fun u _ => sq_nonneg (Work.Spaces.DzIter j g z u))
  rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]

/-- The `H^k`-integrand of the radial function `(z,θ) ↦ u z`: only the pure `D_z` sum
survives, and the weight `w z / sin(2θ)^{η/2}` squares to `(w z)² sin(2θ)^{-η}`. -/
theorem HkIntegrand_rad (α : ℝ) (k : ℕ) (u : ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => u z) z θ
      = (∑ i ∈ Finset.range (k + 1), (DzdIter i u z) ^ 2) * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem hθ
  have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Real.sin (2 * θ) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    norm_num
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => u z) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) = 0 := by
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
    split_ifs with h
    · rw [mixed_rad_eq_zero u h.1]
      ring
    · rfl
  rw [Work.Spaces.HkIntegrand, h2, add_zero]
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [DzIter_rad]
  have hthis : ((DzdIter i u z) * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      = (DzdIter i u z) ^ 2 * (((Work.Spaces.w z) ^ 2) / (Real.sin (2 * θ)
          ^ (Work.Spaces.eta / 2)) ^ 2) := by
    rw [mul_pow, div_pow]
  rw [hthis, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
  ring

/-- The `H^k`-norm of a radial function is the product of `∫_θ sin(2θ)^{-η}` with the
`z`-integral of `∑_i (D_z^i u)² w²`. -/
theorem HkSq_rad (α : ℝ) (k : ℕ) (u : ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => u z)
      = (∫ z in Work.Spaces.Iz,
            ∑ i ∈ Finset.range (k + 1), (DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  rw [Work.Spaces.HkSq]
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => u z) z θ)
        = (∑ i ∈ Finset.range (k + 1), (DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    intro z
    simp only [Work.Spaces.Iθ]
    rw [setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => by rw [HkIntegrand_rad α k u z hθ, Finset.sum_mul])]
    rw [MeasureTheory.integral_const_mul, ← Finset.sum_mul]
  rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => u z) z θ)
      = ∫ z in Work.Spaces.Iz, (∑ i ∈ Finset.range (k + 1),
            (DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      from setIntegral_congr_fun measurableSet_Ici (fun z _ => hinner z)]
  rw [MeasureTheory.integral_mul_const]


end Work.Elliptic

namespace Work.Elliptic

/-- The elementary consequences of `L₁₂(g)(0) = 0` and the integrability of `L12dens g`:
the value formula, the decay at infinity, and continuity on `[0,1]`. -/
theorem L12_values (g : ℝ → ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0))
    (h0 : Work.Elliptic.L12 g 0 = 0) :
    (∀ z : ℝ, 0 ≤ z →
        Work.Elliptic.L12 g z = - ∫ s in (0)..z, Work.Elliptic.L12dens g s)
      ∧ Filter.Tendsto (fun z => Work.Elliptic.L12 g z) Filter.atTop (nhds 0)
      ∧ ContinuousOn (fun z => Work.Elliptic.L12 g z) (Set.Icc 0 1) := by
  have hval : ∀ z : ℝ, 0 ≤ z →
      Work.Elliptic.L12 g z = - ∫ s in (0)..z, Work.Elliptic.L12dens g s := by
    intro z hz
    have h1 : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi z) :=
      hint.mono_set (Set.Ioi_subset_Ioi hz)
    have hadd := intervalIntegral.integral_interval_add_Ioi (f := Work.Elliptic.L12dens g)
      (a := (0:ℝ)) (b := z) hint h1
    have hz0 : (∫ s in Set.Ioi (0:ℝ), Work.Elliptic.L12dens g s) = 0 := h0
    simp only [Work.Elliptic.L12] at hz0 ⊢
    linarith
  refine ⟨hval, ?_, ?_⟩
  · have hanti := MeasureTheory.tendsto_setIntegral_of_antitone (μ := volume)
      (f := Work.Elliptic.L12dens g) (s := fun z : ℝ => Set.Ioi z)
      (fun z => measurableSet_Ioi) (fun a b hab => Set.Ioi_subset_Ioi hab) ⟨0, hint⟩
    have hempty : (⋂ z : ℝ, Set.Ioi z) = (∅ : Set ℝ) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨x, lt_irrefl x⟩
    rw [hempty, MeasureTheory.setIntegral_empty] at hanti
    simpa only [Work.Elliptic.L12] using hanti
  · have hii : IntervalIntegrable (Work.Elliptic.L12dens g) volume (0:ℝ) 1 := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact hint.mono_set (Set.Ioc_subset_Ioi_self)
    have hprim : ContinuousOn (fun z => ∫ s in (0)..z, Work.Elliptic.L12dens g s)
        (Set.Icc (0:ℝ) 1) := by
      have h := intervalIntegral.continuousOn_primitive_interval' hii (Set.left_mem_uIcc (a := (0:ℝ)) (b := 1))
      simpa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using h
    refine ContinuousOn.congr (s := Set.Icc (0:ℝ) 1)
      (f := fun z => - ∫ s in (0)..z, Work.Elliptic.L12dens g s)
      (g := fun z => Work.Elliptic.L12 g z) hprim.neg ?_
    intro z hz
    exact hval z hz.1

end Work.Elliptic

namespace Work.Elliptic

/-- `volume` restricted to the open half-line and to `Iz` agree. -/
theorem restrict_Ioi_eq_restrict_Iz :
    volume.restrict (Set.Ioi (0:ℝ)) = volume.restrict Work.Spaces.Iz := by
  rw [show Work.Spaces.Iz = Set.Ici (0:ℝ) from rfl]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0:ℝ)))

end Work.Elliptic
