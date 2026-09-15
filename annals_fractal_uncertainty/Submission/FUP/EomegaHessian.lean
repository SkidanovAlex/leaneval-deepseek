import Submission.FUP.PSHExtension
import Submission.Commons.Analysis.Calculus.iteratedFDeriv_two_norm_apply
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_apply_add
import Submission.Commons.MeasureTheory.Integral.integral_iteratedFDeriv_two_apply_eq_zero
import Submission.Commons.Analysis.Calculus.contDiffOn_two_Eomega_diag
import Submission.Commons.Analysis.Calculus.iteratedFDeriv_two_integral_add_smul

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Real RealInnerProductSpace Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

namespace Submission.FUP

/-!
# The Hessian of the extension `U(x,y) = Eω(x,y) + C‖y‖`

This module finishes the proof of Cohen's `prop:Ew_is_psh`.  `Submission.FUP.PSHExtension`
reduces the proposition to the single inequality `hHess` (positive semidefiniteness of the
Hessian of `UWeight ω C` in the `(Re, Im)`-coordinates), and here that inequality is proved
from

* the explicit formula for the second derivatives of the Poisson extension
  (`HasPhiE_second`, the two-fold differentiation under the integral sign),
* the vanishing of the line integrals `∫ t, D²ω(x + t•y)[ζ, y]`
  (`integral_iteratedFDeriv_two_apply_eq_zero`), and
* hypothesis (ii) of `prop:Ew_is_psh`, applied after the substitution `u = t/‖y‖`.
-/

/-! ## The Poisson integral as a function on `ℝᵈ × ℝᵈ` -/

/-- The Poisson extension of `ω` as a function of the pair `(x,y)`, i.e.
`Φ(x,y) = ∫_ℝ ω(x + u y)/(1+u²) du`. -/
noncomputable def PhiE (ω : ℝᵈ → ℝ) : ℝᵈ × ℝᵈ → ℝ :=
  fun p => ∫ u : ℝ, ω (p.1 + u • p.2) * (1 + u ^ 2)⁻¹

lemma Eomega_diag_eq_PhiE (ω : ℝᵈ → ℝ) :
    (fun p : ℝᵈ × ℝᵈ => Eomega ω p.1 p.2) = fun p => (1 / π) * PhiE ω p := rfl

lemma UWeight_eq_add (ω : ℝᵈ → ℝ) (C : ℝ) :
    UWeight ω C
      = (fun p : ℝᵈ × ℝᵈ => (1 / π) * PhiE ω p) + (fun p : ℝᵈ × ℝᵈ => C * ‖p.2‖) := by
  funext p
  show Eomega ω p.1 p.2 + C * ‖p.2‖ = (1 / π) * PhiE ω p + C * ‖p.2‖
  rfl

/-- `PhiE ω` is `C²` off the boundary `y = 0`. -/
lemma contDiffAt_two_PhiE {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω)
    {x y : ℝᵈ} (hy : y ≠ 0) : ContDiffAt ℝ 2 (PhiE ω) (x, y) :=
  (Commons.Analysis.Calculus.contDiffOn_two_Eomega_diag (d := d) hω hc).contDiffAt
    ((isOpen_ne.preimage continuous_snd).mem_nhds (by simpa using hy))

/-- **Two-fold differentiation under the integral sign for the Poisson extension:**
`(D²Φ)(x,y)[(V,W),(V,W)] = ∫_ℝ (D²ω(x+uy))[V+uW, V+uW]/(1+u²) du`. -/
def HasPhiE_second (ω : ℝᵈ → ℝ) : Prop :=
  ContDiff ℝ 2 ω → HasCompactSupport ω → ∀ (x y V W : ℝᵈ), y ≠ 0 →
    (iteratedFDeriv ℝ 2 (PhiE ω) (x, y)) ![(V, W), (V, W)]
      = ∫ u : ℝ,
          (iteratedFDeriv ℝ 2 ω (x + u • y)) (fun _ : Fin 2 => (V + u • W)) * (1 + u^2)⁻¹

/-- The scaled version of `HasPhiE_second`. -/
lemma iteratedFDeriv_two_const_mul_PhiE {ω : ℝᵈ → ℝ} (hP : HasPhiE_second ω)
    (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω) (x y V W : ℝᵈ) (hy : y ≠ 0) :
    (iteratedFDeriv ℝ 2 (fun p : ℝᵈ × ℝᵈ => (1 / π) * PhiE ω p) (x, y)) ![(V, W), (V, W)]
      = (1 / π) * ∫ u : ℝ,
          (iteratedFDeriv ℝ 2 ω (x + u • y)) (fun _ : Fin 2 => (V + u • W)) * (1 + u^2)⁻¹ := by
  have hcd : ContDiffAt ℝ 2 (PhiE ω) (x, y) := contDiffAt_two_PhiE hω hc hy
  have hsmul : (fun p : ℝᵈ × ℝᵈ => (1 / π) * PhiE ω p) = (1 / π) • PhiE ω := by
    funext p; rw [Pi.smul_apply, smul_eq_mul]
  rw [hsmul, iteratedFDeriv_const_smul_apply (a := (1 / π : ℝ)) hcd, smul_apply, smul_eq_mul,
    hP hω hc x y V W hy]

/-! ## The second derivative of `y ↦ C‖y‖` -/

/-- **Second derivative of `p ↦ C‖p.2‖`.** -/
lemma iteratedFDeriv_two_snd_mul_norm (C : ℝ) (x y V₁ W₁ V₂ W₂ : ℝᵈ) (hy : y ≠ 0) :
    (iteratedFDeriv ℝ 2 (fun p : ℝᵈ × ℝᵈ => C * ‖p.2‖) (x, y)) ![(V₁, W₁), (V₂, W₂)]
      = C * (iteratedFDeriv ℝ 2 (fun z : ℝᵈ => ‖z‖) y) ![W₁, W₂] := by
  set s : Set ℝᵈ := {z : ℝᵈ | z ≠ 0} with hs
  have hsopen : IsOpen s := isOpen_ne
  have hfun : (fun p : ℝᵈ × ℝᵈ => C * ‖p.2‖)
      = (fun z : ℝᵈ => C * ‖z‖) ∘ (ContinuousLinearMap.snd ℝ ℝᵈ ℝᵈ) := by
    funext p; rfl
  have hcont : ContDiffOn ℝ 2 (fun z : ℝᵈ => C * ‖z‖) s :=
    contDiffOn_const.mul (ContDiffOn.norm ℝ contDiffOn_id (fun z hz => hz))
  have hpre : (ContinuousLinearMap.snd ℝ ℝᵈ ℝᵈ) ⁻¹' s = {p : ℝᵈ × ℝᵈ | p.2 ≠ 0} := by
    ext p; simp [s]
  have hpreopen : IsOpen ((ContinuousLinearMap.snd ℝ ℝᵈ ℝᵈ) ⁻¹' s) := by
    rw [hpre]; exact isOpen_ne.preimage continuous_snd
  have hmem : (ContinuousLinearMap.snd ℝ ℝᵈ ℝᵈ) (x, y) ∈ s := by simp [s, hy]
  have hsnd : (ContinuousLinearMap.snd ℝ ℝᵈ ℝᵈ) (x, y) = y := rfl
  have hcr := ContinuousLinearMap.iteratedFDerivWithin_comp_right
    (ContinuousLinearMap.snd ℝ ℝᵈ ℝᵈ) hcont hsopen.uniqueDiffOn hpreopen.uniqueDiffOn
    hmem (i := 2) (le_refl 2)
  rw [hsnd] at hcr
  have h1 : iteratedFDerivWithin ℝ 2
        ((fun z : ℝᵈ => C * ‖z‖) ∘ (ContinuousLinearMap.snd ℝ ℝᵈ ℝᵈ))
        ((ContinuousLinearMap.snd ℝ ℝᵈ ℝᵈ) ⁻¹' s) (x, y)
      = iteratedFDeriv ℝ 2 ((fun z : ℝᵈ => C * ‖z‖) ∘ (ContinuousLinearMap.snd ℝ ℝᵈ ℝᵈ))
        (x, y) :=
    iteratedFDerivWithin_of_isOpen 2 hpreopen (by rw [hpre]; exact hy)
  have h2 : iteratedFDerivWithin ℝ 2 (fun z : ℝᵈ => C * ‖z‖) s y
      = iteratedFDeriv ℝ 2 (fun z : ℝᵈ => C * ‖z‖) y :=
    iteratedFDerivWithin_of_isOpen 2 hsopen (by simp [s, hy])
  have hmain : iteratedFDeriv ℝ 2 (fun p : ℝᵈ × ℝᵈ => C * ‖p.2‖) (x, y)
      = (iteratedFDeriv ℝ 2 (fun z : ℝᵈ => C * ‖z‖) y).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.snd ℝ ℝᵈ ℝᵈ) := by
    rw [hfun, ← h1, hcr, h2]
  rw [hmain, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hvec : (fun i : Fin 2 => (ContinuousLinearMap.snd ℝ ℝᵈ ℝᵈ) (![(V₁, W₁), (V₂, W₂)] i))
      = ![W₁, W₂] := by
    funext i; fin_cases i <;> rfl
  rw [hvec]
  have hnorm : ContDiffAt ℝ 2 (fun z : ℝᵈ => ‖z‖) y := contDiffAt_norm ℝ hy
  rw [show (fun z : ℝᵈ => C * ‖z‖) = C • (fun z : ℝᵈ => ‖z‖) from by
    funext z; rw [Pi.smul_apply, smul_eq_mul]]
  rw [iteratedFDeriv_const_smul_apply hnorm, smul_apply, smul_eq_mul]

/-! ## The line Hessian `u ↦ D²ω(x + u y)` and the unit direction -/

/-- The unit vector in the direction of `y` (junk `0` if `y = 0`). -/
noncomputable def unitDir (y : ℝᵈ) : ℝᵈ := ‖y‖⁻¹ • y

lemma norm_unitDir {y : ℝᵈ} (hy : y ≠ 0) : ‖unitDir y‖ = 1 := by
  rw [unitDir, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg y)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]

/-- The Hessian of `ω` along the line `u ↦ x + u y`, as a family of bilinear forms. -/
noncomputable def lineBilin (ω : ℝᵈ → ℝ) (x y : ℝᵈ) : ℝ → (ℝᵈ →ₗ[ℝ] ℝᵈ →ₗ[ℝ] ℝ) :=
  fun u => bilinearIteratedFDerivTwo ℝ ω (x + u • y)

lemma lineBilin_apply (ω : ℝᵈ → ℝ) (x y : ℝᵈ) (u : ℝ) (a b : ℝᵈ) :
    lineBilin ω x y u a b = (iteratedFDeriv ℝ 2 ω (x + u • y)) ![a, b] :=
  bilinearIteratedFDerivTwo_eq_iteratedFDeriv ω (x + u • y) a b

lemma lineBilin_symm {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω) (x y : ℝᵈ) (u : ℝ) (a b : ℝᵈ) :
    lineBilin ω x y u a b = lineBilin ω x y u b a := by
  rw [lineBilin_apply, lineBilin_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  exact (hω.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq a b

/-- The constant-`Fin 2` vector is `![a,a]`. -/
lemma fun_const_fin2 {α : Type*} (a : α) : (fun _ : Fin 2 => a) = ![a, a] := by
  funext i; fin_cases i <;> rfl

/-- Expansion of the Hessian along the pair `(a + tb, -b + ta)`. -/
lemma lineBilin_pair_expand {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω) (x y : ℝᵈ) (u : ℝ)
    (a b : ℝᵈ) (t : ℝ) :
    lineBilin ω x y u (a + t • b) (a + t • b)
        + lineBilin ω x y u (-b + t • a) (-b + t • a)
      = (1 + t ^ 2) * (lineBilin ω x y u a a + lineBilin ω x y u b b) := by
  have hsym := lineBilin_symm hω x y u a b
  simp only [map_add, map_neg, map_smul, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hsym]
  ring

/-- Expansion of the Hessian along `a = p + αy`. -/
lemma lineBilin_expand {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω) (x y : ℝᵈ) (u : ℝ) (p : ℝᵈ)
    (α : ℝ) :
    lineBilin ω x y u (p + α • y) (p + α • y)
      = lineBilin ω x y u p p + 2 * α * lineBilin ω x y u p y
        + α ^ 2 * lineBilin ω x y u y y := by
  have hsym := lineBilin_symm hω x y u p y
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hsym]
  ring

/-! ## Compact support and integrability of the line Hessian -/

private lemma hasCompactSupport_iteratedFDeriv_two_apply {ω : ℝᵈ → ℝ} (hc : HasCompactSupport ω)
    (a b : ℝᵈ) :
    HasCompactSupport (fun z : ℝᵈ => (iteratedFDeriv ℝ 2 ω z) ![a, b]) :=
  (hc.iteratedFDeriv 2).comp_left
    (g := fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℝᵈ) ℝ => L ![a, b]) (by simp)

private lemma continuous_iteratedFDeriv_two_apply {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω)
    (a b : ℝᵈ) :
    Continuous (fun z : ℝᵈ => (iteratedFDeriv ℝ 2 ω z) ![a, b]) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝᵈ) ℝ ![a, b]).continuous.comp
    (hω.continuous_iteratedFDeriv (m := 2) (by norm_num))

private lemma hasCompactSupport_comp_line_ne {F : ℝᵈ → ℝ} (hF : HasCompactSupport F)
    {x y : ℝᵈ} (hy : y ≠ 0) : HasCompactSupport (fun t : ℝ => F (x + t • y)) := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝᵈ)).mp hF.isBounded
  refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℝ) ((r + ‖x‖) / ‖y‖ + 1))
    (isCompact_closedBall 0 _) ?_
  intro t ht
  have hnorm_y : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have ht' : (r + ‖x‖) / ‖y‖ + 1 < dist t (0 : ℝ) := not_le.mp ht
  have ht'' : ((r + ‖x‖) / ‖y‖) < |t| := by
    have : dist t (0 : ℝ) = |t| := by rw [Real.dist_eq, sub_zero]
    rw [this] at ht'; linarith
  have hmul : r + ‖x‖ < |t| * ‖y‖ := by
    have h2 : ((r + ‖x‖) / ‖y‖) * ‖y‖ < |t| * ‖y‖ :=
      mul_lt_mul_of_pos_right ht'' hnorm_y
    rwa [div_mul_cancel₀ _ (ne_of_gt hnorm_y)] at h2
  have hsub : (x + t • y) - x = t • y := by abel
  have h1 : ‖t • y‖ - ‖x‖ ≤ ‖x + t • y‖ := by
    have h2 := norm_sub_le (x + t • y) x
    rw [hsub] at h2
    linarith
  rw [norm_smul, Real.norm_eq_abs] at h1
  have hbig : r < ‖x + t • y‖ := by linarith
  exact image_eq_zero_of_notMem_tsupport fun hmem => by
    have hle : dist (x + t • y) 0 ≤ r := Metric.mem_closedBall.mp (hr hmem)
    rw [dist_eq_norm, sub_zero] at hle
    linarith

lemma hasCompactSupport_lineBilin {ω : ℝᵈ → ℝ} (hc : HasCompactSupport ω)
    (x y a b : ℝᵈ) (hy : y ≠ 0) :
    HasCompactSupport (fun u : ℝ => lineBilin ω x y u a b) := by
  have hfun : (fun u : ℝ => lineBilin ω x y u a b)
      = fun u : ℝ => (iteratedFDeriv ℝ 2 ω (x + u • y)) ![a, b] := by
    funext u; rw [lineBilin_apply]
  rw [hfun]
  exact hasCompactSupport_comp_line_ne (hasCompactSupport_iteratedFDeriv_two_apply hc a b) hy

lemma continuous_lineBilin {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω) (x y a b : ℝᵈ) :
    Continuous (fun u : ℝ => lineBilin ω x y u a b) := by
  have hfun : (fun u : ℝ => lineBilin ω x y u a b)
      = fun u : ℝ => (iteratedFDeriv ℝ 2 ω (x + u • y)) ![a, b] := by
    funext u; rw [lineBilin_apply]
  rw [hfun]
  exact (continuous_iteratedFDeriv_two_apply hω a b).comp (by fun_prop)

lemma integrable_lineBilin {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω)
    (x y a b : ℝᵈ) (hy : y ≠ 0) :
    Integrable (fun u : ℝ => lineBilin ω x y u a b) :=
  (continuous_lineBilin hω x y a b).integrable_of_hasCompactSupport
    (hasCompactSupport_lineBilin hc x y a b hy)

lemma continuous_inv_one_add_sq_aux : Continuous (fun u : ℝ => (1 + u ^ 2)⁻¹) :=
  (by fun_prop : Continuous fun u : ℝ => 1 + u ^ 2).inv₀ (fun u => by positivity)

lemma integrable_lineBilin_inv {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω)
    (x y a b : ℝᵈ) (hy : y ≠ 0) :
    Integrable (fun u : ℝ => lineBilin ω x y u a b * (1 + u ^ 2)⁻¹) :=
  ((continuous_lineBilin hω x y a b).mul continuous_inv_one_add_sq_aux).integrable_of_hasCompactSupport
    ((hasCompactSupport_lineBilin hc x y a b hy).mul_right)

/-! ## Vanishing of the line integrals and the substitution `u ↦ t/‖y‖` -/

/-- `∫_ℝ D²ω(x + u y)[ζ, y] du = 0`. -/
lemma integral_lineBilin_y_eq_zero {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω)
    (hc : HasCompactSupport ω) (x y ζ : ℝᵈ) :
    ∫ u : ℝ, lineBilin ω x y u ζ y = 0 := by
  have hfun : (fun u : ℝ => lineBilin ω x y u ζ y)
      = fun u : ℝ => (iteratedFDeriv ℝ 2 ω (x + u • y)) ![ζ, y] := by
    funext u; rw [lineBilin_apply]
  rw [hfun]
  exact Commons.MeasureTheory.Integral.integral_iteratedFDeriv_two_apply_eq_zero hω hc x y ζ

/-- **Change of variables on a line.** -/
lemma integral_comp_line_scale (f : ℝᵈ → ℝ) (x y : ℝᵈ) (hy : y ≠ 0) :
    (∫ u : ℝ, f (x + u • y)) = ‖y‖⁻¹ * ∫ t : ℝ, f (x + t • unitDir y) := by
  have hc : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have h1 : ∀ u : ℝ, f (x + u • y) = f (x + (u * ‖y‖) • unitDir y) := by
    intro u
    congr 1
    rw [unitDir, smul_smul, mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), mul_one]
  calc (∫ u : ℝ, f (x + u • y))
      = ∫ u : ℝ, f (x + (u * ‖y‖) • unitDir y) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        exact h1 u
    _ = |‖y‖⁻¹| • ∫ t : ℝ, f (x + t • unitDir y) :=
        Measure.integral_comp_mul_right (fun t : ℝ => f (x + t • unitDir y)) ‖y‖
    _ = ‖y‖⁻¹ * ∫ t : ℝ, f (x + t • unitDir y) := by
        rw [abs_of_pos (inv_pos.mpr hc), smul_eq_mul]

lemma integral_lineBilin_scale {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω)
    (hc : HasCompactSupport ω) (x y a b : ℝᵈ) (hy : y ≠ 0) :
    (∫ u : ℝ, lineBilin ω x y u a b)
      = ‖y‖⁻¹ * ∫ t : ℝ, lineBilin ω x (unitDir y) t a b := by
  have h1 : (fun u : ℝ => lineBilin ω x y u a b)
      = fun u : ℝ => (fun z : ℝᵈ => (iteratedFDeriv ℝ 2 ω z) ![a, b]) (x + u • y) := by
    funext u; rw [lineBilin_apply]
  rw [h1, integral_comp_line_scale (fun z : ℝᵈ => (iteratedFDeriv ℝ 2 ω z) ![a, b]) x y hy]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  show (iteratedFDeriv ℝ 2 ω (x + t • unitDir y)) ![a, b] = lineBilin ω x (unitDir y) t a b
  rw [← lineBilin_apply]

/-- **The line integral of `D²ω` at an orthogonal unit vector.** -/
lemma integral_lineBilin_scale_unit {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω)
    (hc : HasCompactSupport ω) (x y p : ℝᵈ) (hy : y ≠ 0) :
    (∫ u : ℝ, lineBilin ω x y u p p)
      = ‖y‖⁻¹ * (‖p‖ ^ 2 * ∫ t : ℝ,
          lineBilin ω x (unitDir y) t (unitDir p) (unitDir p)) := by
  rw [integral_lineBilin_scale hω hc x y p p hy]
  congr 1
  by_cases hp : p = 0
  · simp [hp]
  · have hp0 : (0 : ℝ) < ‖p‖ := norm_pos_iff.mpr hp
    have hp_eq : p = ‖p‖ • unitDir p := by
      rw [unitDir, smul_smul, mul_inv_cancel₀ (ne_of_gt hp0), one_smul]
    have hcongr : (fun t : ℝ => lineBilin ω x (unitDir y) t p p)
        = fun t : ℝ => ‖p‖ ^ 2 * lineBilin ω x (unitDir y) t (unitDir p) (unitDir p) := by
      funext t
      conv_lhs => rw [hp_eq]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hcongr, MeasureTheory.integral_const_mul]

/-! ## The perp decomposition -/

/-- The component of `v` orthogonal to `y`. -/
noncomputable def perpComp (y v : ℝᵈ) : ℝᵈ := v - (inner ℝ y v / ‖y‖ ^ 2) • y

lemma perpComp_add (y v : ℝᵈ) : perpComp y v + (inner ℝ y v / ‖y‖ ^ 2) • y = v := by
  rw [perpComp]; abel

lemma inner_perpComp (y v : ℝᵈ) : inner ℝ y (perpComp y v) = 0 := by
  rw [perpComp, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  by_cases hy : y = 0
  · simp [hy]
  · field_simp
    ring

lemma norm_sq_perpComp (y v : ℝᵈ) :
    ‖perpComp y v‖ ^ 2 = ‖v‖ ^ 2 - (inner ℝ y v) ^ 2 / ‖y‖ ^ 2 := by
  have h1 : ‖perpComp y v‖ ^ 2
      = ‖v‖ ^ 2 - 2 * (inner ℝ y v) ^ 2 / ‖y‖ ^ 2 + (inner ℝ y v) ^ 2 / ‖y‖ ^ 2 := by
    rw [perpComp, norm_sub_sq_real, real_inner_smul_right, real_inner_comm v y, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    by_cases hy : y = 0
    · simp [hy]
    · have hy0 : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)
      field_simp
  rw [h1]; ring

lemma inner_unitDir (y p : ℝᵈ) :
    inner ℝ (unitDir y) (unitDir p) = (‖y‖⁻¹ * ‖p‖⁻¹) * inner ℝ y p := by
  rw [unitDir, unitDir, real_inner_smul_left, real_inner_smul_right]
  ring

/-! ## The affine family `u ↦ D²ω(x + u y)[V + uW, V + uW]` -/

lemma continuous_iteratedFDeriv_two_apply_family {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω)
    {α : Type*} [TopologicalSpace α] (φ ψ χ : α → ℝᵈ)
    (hφ : Continuous φ) (hψ : Continuous ψ) (hχ : Continuous χ) :
    Continuous (fun s : α => (iteratedFDeriv ℝ 2 ω (φ s)) ![ψ s, χ s]) := by
  have hD2 : Continuous fun z : ℝᵈ => fderiv ℝ (fderiv ℝ ω) z := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ ω) := by
      have := hω.fderiv_right (m := (1 : ℕ∞)) (by norm_num); simpa using this
    exact h1.continuous_fderiv (by norm_num)
  have hA : Continuous fun s : α => fderiv ℝ (fderiv ℝ ω) (φ s) := hD2.comp hφ
  have hB : Continuous fun s : α => (fderiv ℝ (fderiv ℝ ω) (φ s)) (ψ s) := hA.clm_apply hψ
  have hC : Continuous fun s : α => ((fderiv ℝ (fderiv ℝ ω) (φ s)) (ψ s)) (χ s) :=
    hB.clm_apply hχ
  have hconv : (fun s : α => (iteratedFDeriv ℝ 2 ω (φ s)) ![ψ s, χ s])
      = fun s : α => ((fderiv ℝ (fderiv ℝ ω) (φ s)) (ψ s)) (χ s) := by
    funext s
    rw [iteratedFDeriv_two_apply]
    simp
  rw [hconv]; exact hC

lemma hasCompactSupport_lineBilin_affine {ω : ℝᵈ → ℝ} (hc : HasCompactSupport ω)
    (x y V W : ℝᵈ) (hy : y ≠ 0) :
    HasCompactSupport (fun u : ℝ => lineBilin ω x y u (V + u • W) (V + u • W)) := by
  have hcs : HasCompactSupport (fun z : ℝᵈ => iteratedFDeriv ℝ 2 ω z) := hc.iteratedFDeriv 2
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝᵈ)).mp hcs.isBounded
  have hnorm_y : 0 < ‖y‖ := norm_pos_iff.mpr hy
  refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℝ) ((r + ‖x‖) / ‖y‖ + 1))
    (isCompact_closedBall 0 _) ?_
  intro u hu
  have hu' : (r + ‖x‖) / ‖y‖ + 1 < dist u (0 : ℝ) := not_le.mp hu
  have hu'' : ((r + ‖x‖) / ‖y‖) < |u| := by
    have : dist u (0 : ℝ) = |u| := by rw [Real.dist_eq, sub_zero]
    rw [this] at hu'; linarith
  have hmul : r + ‖x‖ < |u| * ‖y‖ := by
    have h2 : ((r + ‖x‖) / ‖y‖) * ‖y‖ < |u| * ‖y‖ :=
      mul_lt_mul_of_pos_right hu'' hnorm_y
    rwa [div_mul_cancel₀ _ (ne_of_gt hnorm_y)] at h2
  have hsub : (x + u • y) - x = u • y := by abel
  have h1 : ‖u • y‖ - ‖x‖ ≤ ‖x + u • y‖ := by
    have h2 := norm_sub_le (x + u • y) x
    rw [hsub] at h2; linarith
  rw [norm_smul, Real.norm_eq_abs] at h1
  have hbig : r < ‖x + u • y‖ := by linarith
  have hzero : (iteratedFDeriv ℝ 2 ω (x + u • y)) = 0 := by
    by_contra hne
    have hmem : x + u • y ∈ tsupport (fun z : ℝᵈ => iteratedFDeriv ℝ 2 ω z) :=
      subset_tsupport _ (by simpa [Function.mem_support] using hne)
    have hb := hr hmem
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hb
    linarith
  rw [lineBilin_apply, hzero]
  simp

lemma integrable_lineBilin_affine_inv {ω : ℝᵈ → ℝ} (hω : ContDiff ℝ 2 ω)
    (hc : HasCompactSupport ω) (x y V W : ℝᵈ) (hy : y ≠ 0) :
    Integrable (fun u : ℝ => lineBilin ω x y u (V + u • W) (V + u • W) * (1 + u ^ 2)⁻¹) := by
  have hcont : Continuous (fun u : ℝ => lineBilin ω x y u (V + u • W) (V + u • W)) := by
    have hfun : (fun u : ℝ => lineBilin ω x y u (V + u • W) (V + u • W))
        = fun u : ℝ => (iteratedFDeriv ℝ 2 ω (x + u • y)) ![V + u • W, V + u • W] := by
      funext u; rw [lineBilin_apply]
    rw [hfun]
    exact continuous_iteratedFDeriv_two_apply_family hω (fun u : ℝ => x + u • y)
      (fun u : ℝ => V + u • W) (fun u : ℝ => V + u • W)
      (by fun_prop) (by fun_prop) (by fun_prop)
  exact (hcont.mul continuous_inv_one_add_sq_aux).integrable_of_hasCompactSupport
    ((hasCompactSupport_lineBilin_affine hc x y V W hy).mul_right)

/-! ## The lower bound from hypothesis (ii) -/

/-- **The key lower bound of §3.**  Hypothesis (ii) of `prop:Ew_is_psh` bounds the average of
the Hessian of `ω` along every line from below; integrating that against the Poisson weight and
using the vanishing of the `y`-component gives the bound
`(1/π)∫_ℝ D²ω(x+uy)[a,a] du ≥ -C₂‖a^⊥‖²/‖y‖`. -/
theorem PhiE_line_bound {ω : ℝᵈ → ℝ} {C₂ : ℝ}
    (hcond : ∀ (x yhat vhat : ℝᵈ), ‖yhat‖ = 1 → ‖vhat‖ = 1 → inner ℝ yhat vhat = 0 →
      -C₂ ≤ (1 / π) * ∫ t : ℝ,
        ((iteratedFDeriv ℝ 2 ω (x + t • yhat)) (fun _ : Fin 2 => vhat)))
    (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω)
    (x y : ℝᵈ) (hy : y ≠ 0) (a : ℝᵈ) :
    -(C₂ * ‖perpComp y a‖ ^ 2) / ‖y‖ ≤ (1 / π) * ∫ u : ℝ, lineBilin ω x y u a a := by
  have hypos : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set α : ℝ := inner ℝ y a / ‖y‖ ^ 2 with hαdef
  have hα' : perpComp y a + α • y = a := by rw [hαdef]; exact perpComp_add y a
  -- Step 1: the component of `a` along `y` integrates to zero
  have hdecomp : (∫ u : ℝ, lineBilin ω x y u a a)
      = ∫ u : ℝ, lineBilin ω x y u (perpComp y a) (perpComp y a) := by
    have hcongr : (fun u : ℝ => lineBilin ω x y u a a)
        = fun u : ℝ => (lineBilin ω x y u (perpComp y a) (perpComp y a)
            + 2 * α * lineBilin ω x y u (perpComp y a) y)
            + α ^ 2 * lineBilin ω x y u y y := by
      funext u
      conv_lhs => rw [← hα']
      rw [lineBilin_expand hω x y u (perpComp y a) α]
    have hI1 : Integrable (fun u : ℝ => lineBilin ω x y u (perpComp y a) (perpComp y a)
        + 2 * α * lineBilin ω x y u (perpComp y a) y) :=
      (integrable_lineBilin hω hc x y (perpComp y a) (perpComp y a) hy).add
        ((integrable_lineBilin hω hc x y (perpComp y a) y hy).const_mul (2 * α))
    have hI2 : Integrable (fun u : ℝ => α ^ 2 * lineBilin ω x y u y y) :=
      (integrable_lineBilin hω hc x y y y hy).const_mul (α ^ 2)
    have hIA : Integrable (fun u : ℝ => lineBilin ω x y u (perpComp y a) (perpComp y a)) :=
      integrable_lineBilin hω hc x y (perpComp y a) (perpComp y a) hy
    have hIB : Integrable (fun u : ℝ => 2 * α * lineBilin ω x y u (perpComp y a) y) :=
      (integrable_lineBilin hω hc x y (perpComp y a) y hy).const_mul (2 * α)
    rw [hcongr]
    rw [MeasureTheory.integral_add hI1 hI2]
    rw [MeasureTheory.integral_add hIA hIB]
    rw [MeasureTheory.integral_const_mul (2 * α)
        (fun u => lineBilin ω x y u (perpComp y a) y),
      MeasureTheory.integral_const_mul (α ^ 2) (fun u => lineBilin ω x y u y y),
      integral_lineBilin_y_eq_zero hω hc x y (perpComp y a),
      integral_lineBilin_y_eq_zero hω hc x y y]
    ring
  rw [hdecomp]
  by_cases hp : perpComp y a = 0
  · simp [hp]
  · have hp0 : (0 : ℝ) < ‖perpComp y a‖ := norm_pos_iff.mpr hp
    have hinner : inner ℝ (unitDir y) (unitDir (perpComp y a)) = 0 := by
      rw [inner_unitDir, inner_perpComp, mul_zero]
    have hcond' := hcond x (unitDir y) (unitDir (perpComp y a)) (norm_unitDir hy)
      (norm_unitDir hp) hinner
    have hcond'' : -C₂ ≤ (1 / π) * ∫ t : ℝ,
        lineBilin ω x (unitDir y) t (unitDir (perpComp y a)) (unitDir (perpComp y a)) := by
      have hcongr : (fun t : ℝ => (iteratedFDeriv ℝ 2 ω (x + t • unitDir y))
            (fun _ : Fin 2 => unitDir (perpComp y a)))
          = fun t : ℝ => lineBilin ω x (unitDir y) t (unitDir (perpComp y a))
              (unitDir (perpComp y a)) := by
        funext t
        have hvec : (fun _ : Fin 2 => unitDir (perpComp y a))
            = ![unitDir (perpComp y a), unitDir (perpComp y a)] := fun_const_fin2 _
        rw [hvec, ← lineBilin_apply]
      rwa [hcongr] at hcond'
    rw [integral_lineBilin_scale_unit hω hc x y (perpComp y a) hy]
    set K : ℝ := ∫ t : ℝ, lineBilin ω x (unitDir y) t (unitDir (perpComp y a))
      (unitDir (perpComp y a)) with hKdef
    have hK : π * (-C₂) ≤ K := by
      calc π * (-C₂) ≤ π * ((1 / π) * K) := mul_le_mul_of_nonneg_left hcond'' (le_of_lt hpi)
        _ = K := by
              rw [← mul_assoc, show π * (1 / π) = 1 from by field_simp, one_mul]
    have hkey : (1 / π) * (‖y‖⁻¹ * (‖perpComp y a‖ ^ 2 * K))
          - (-(C₂ * ‖perpComp y a‖ ^ 2) / ‖y‖)
        = ‖perpComp y a‖ ^ 2 * (K - π * (-C₂)) / (π * ‖y‖) := by
      field_simp
    rw [← sub_nonneg, hkey]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by positivity)

end Submission.FUP

/-! ## The Hessian of `UWeight` -/

namespace Submission.FUP

/-- **`prop:Ew_is_psh`, the Hessian inequality.**  Under condition (ii) of `prop:Ew_is_psh`,
the Hessian of `U = Eω + C‖Im·‖` in the `(Re,Im)`-coordinates is positive semidefinite. -/
theorem UWeight_hessian_nonneg_of_Eformula (hP : ∀ (ω : ℝᵈ → ℝ), HasPhiE_second ω)
    {ω : ℝᵈ → ℝ} {C₂ C : ℝ} (hC₂C : C₂ ≤ C)
    (hcond : ∀ (x yhat vhat : ℝᵈ), ‖yhat‖ = 1 → ‖vhat‖ = 1 → inner ℝ yhat vhat = 0 →
      -C₂ ≤ (1 / π) * ∫ t : ℝ,
        ((iteratedFDeriv ℝ 2 ω (x + t • yhat)) (fun _ : Fin 2 => vhat)))
    (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω) :
    ∀ (x y v₁ v₂ : ℝᵈ), y ≠ 0 →
      0 ≤ (iteratedFDeriv ℝ 2 (UWeight ω C) (x, y)) ![(v₁, v₂), (v₁, v₂)]
        + (iteratedFDeriv ℝ 2 (UWeight ω C) (x, y)) ![(-v₂, v₁), (-v₂, v₁)] := by
  intro x y v₁ v₂ hy
  have hyn : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hcdE : ContDiffAt ℝ 2 (fun p : ℝᵈ × ℝᵈ => (1 / π) * PhiE ω p) (x, y) := by
    have hsm : (fun p : ℝᵈ × ℝᵈ => (1 / π) * PhiE ω p) = (1 / π) • PhiE ω := by
      funext p; rw [Pi.smul_apply, smul_eq_mul]
    rw [hsm]
    exact (contDiffAt_two_PhiE hω hc hy).const_smul (1 / π)
  have hcdN : ContDiffAt ℝ 2 (fun p : ℝᵈ × ℝᵈ => C * ‖p.2‖) (x, y) := by
    have h1 : ContDiffAt ℝ 2 (fun p : ℝᵈ × ℝᵈ => ‖p.2‖) (x, y) :=
      (contDiffAt_norm ℝ hy).comp (x, y)
        ((ContinuousLinearMap.snd ℝ ℝᵈ ℝᵈ).contDiff.contDiffAt)
    rw [show (fun p : ℝᵈ × ℝᵈ => C * ‖p.2‖) = C • (fun p : ℝᵈ × ℝᵈ => ‖p.2‖)
      from by funext p; rw [Pi.smul_apply, smul_eq_mul]]
    exact h1.const_smul C
  have hsplit : ∀ (V W : ℝᵈ),
      (iteratedFDeriv ℝ 2 (UWeight ω C) (x, y)) ![(V, W), (V, W)]
        = (iteratedFDeriv ℝ 2 (fun p : ℝᵈ × ℝᵈ => (1 / π) * PhiE ω p) (x, y))
            ![(V, W), (V, W)]
        + (iteratedFDeriv ℝ 2 (fun p : ℝᵈ × ℝᵈ => C * ‖p.2‖) (x, y)) ![(V, W), (V, W)] := by
    intro V W
    rw [UWeight_eq_add]
    exact Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_apply_add hcdE hcdN
  have hEeval : ∀ (V W : ℝᵈ),
      (iteratedFDeriv ℝ 2 (fun p : ℝᵈ × ℝᵈ => (1 / π) * PhiE ω p) (x, y)) ![(V, W), (V, W)]
        = (1 / π) * ∫ u : ℝ,
            lineBilin ω x y u (V + u • W) (V + u • W) * (1 + u^2)⁻¹ := by
    intro V W
    rw [iteratedFDeriv_two_const_mul_PhiE (hP ω) hω hc x y V W hy]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    show (iteratedFDeriv ℝ 2 ω (x + u • y)) (fun _ : Fin 2 => (V + u • W)) * (1 + u ^ 2)⁻¹
        = lineBilin ω x y u (V + u • W) (V + u • W) * (1 + u ^ 2)⁻¹
    have hvec : (fun _ : Fin 2 => (V + u • W)) = ![(V + u • W), (V + u • W)] :=
      fun_const_fin2 _
    rw [hvec, ← lineBilin_apply]
  have hNeval : ∀ (V W : ℝᵈ),
      (iteratedFDeriv ℝ 2 (fun p : ℝᵈ × ℝᵈ => C * ‖p.2‖) (x, y)) ![(V, W), (V, W)]
        = C * (iteratedFDeriv ℝ 2 (fun z : ℝᵈ => ‖z‖) y) ![W, W] := fun V W =>
    iteratedFDeriv_two_snd_mul_norm C x y V W V W hy
  -- the sum of the two `E`-terms
  have hsumE :
      (∫ u : ℝ, lineBilin ω x y u (v₁ + u • v₂) (v₁ + u • v₂) * (1 + u^2)⁻¹)
        + (∫ u : ℝ, lineBilin ω x y u (-v₂ + u • v₁) (-v₂ + u • v₁) * (1 + u^2)⁻¹)
      = (∫ u : ℝ, lineBilin ω x y u v₁ v₁) + (∫ u : ℝ, lineBilin ω x y u v₂ v₂) := by
    have hI1 := integrable_lineBilin_affine_inv hω hc x y v₁ v₂ hy
    have hI2 := integrable_lineBilin_affine_inv hω hc x y (-v₂) v₁ hy
    have hJ1 := integrable_lineBilin hω hc x y v₁ v₁ hy
    have hJ2 := integrable_lineBilin hω hc x y v₂ v₂ hy
    rw [← MeasureTheory.integral_add hI1 hI2]
    rw [← MeasureTheory.integral_add hJ1 hJ2]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    show lineBilin ω x y u (v₁ + u • v₂) (v₁ + u • v₂) * (1 + u ^ 2)⁻¹
        + lineBilin ω x y u (-v₂ + u • v₁) (-v₂ + u • v₁) * (1 + u ^ 2)⁻¹
      = lineBilin ω x y u v₁ v₁ + lineBilin ω x y u v₂ v₂
    have hpair := lineBilin_pair_expand hω x y u v₁ v₂ u
    have h2 : (1 + u ^ 2) * (lineBilin ω x y u v₁ v₁ + lineBilin ω x y u v₂ v₂)
          * (1 + u ^ 2)⁻¹ = lineBilin ω x y u v₁ v₁ + lineBilin ω x y u v₂ v₂ := by
      have hu2 : (1 + u ^ 2 : ℝ) ≠ 0 := by positivity
      field_simp
    rw [← add_mul, hpair, h2]
  have hQE : (iteratedFDeriv ℝ 2 (fun p : ℝᵈ × ℝᵈ => (1 / π) * PhiE ω p) (x, y))
          ![(v₁, v₂), (v₁, v₂)]
        + (iteratedFDeriv ℝ 2 (fun p : ℝᵈ × ℝᵈ => (1 / π) * PhiE ω p) (x, y))
          ![(-v₂, v₁), (-v₂, v₁)]
      = (1 / π) * ((∫ u : ℝ, lineBilin ω x y u v₁ v₁)
          + (∫ u : ℝ, lineBilin ω x y u v₂ v₂)) := by
    rw [hEeval v₁ v₂, hEeval (-v₂) v₁, ← mul_add, hsumE]
  have hQN : (iteratedFDeriv ℝ 2 (fun p : ℝᵈ × ℝᵈ => C * ‖p.2‖) (x, y))
          ![(v₁, v₂), (v₁, v₂)]
        + (iteratedFDeriv ℝ 2 (fun p : ℝᵈ × ℝᵈ => C * ‖p.2‖) (x, y))
          ![(-v₂, v₁), (-v₂, v₁)]
      = C * (‖perpComp y v₁‖ ^ 2 + ‖perpComp y v₂‖ ^ 2) / ‖y‖ := by
    rw [hNeval v₁ v₂, hNeval (-v₂) v₁,
      Commons.Analysis.Calculus.iteratedFDeriv_two_norm_apply y v₂ hy,
      Commons.Analysis.Calculus.iteratedFDeriv_two_norm_apply y v₁ hy]
    rw [norm_sq_perpComp y v₁, norm_sq_perpComp y v₂]
    have hyne : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    field_simp
    ring
  have hQexpand : (iteratedFDeriv ℝ 2 (UWeight ω C) (x, y)) ![(v₁, v₂), (v₁, v₂)]
        + (iteratedFDeriv ℝ 2 (UWeight ω C) (x, y)) ![(-v₂, v₁), (-v₂, v₁)]
      = ((iteratedFDeriv ℝ 2 (fun p : ℝᵈ × ℝᵈ => (1 / π) * PhiE ω p) (x, y))
            ![(v₁, v₂), (v₁, v₂)]
          + (iteratedFDeriv ℝ 2 (fun p : ℝᵈ × ℝᵈ => (1 / π) * PhiE ω p) (x, y))
            ![(-v₂, v₁), (-v₂, v₁)])
        + ((iteratedFDeriv ℝ 2 (fun p : ℝᵈ × ℝᵈ => C * ‖p.2‖) (x, y))
            ![(v₁, v₂), (v₁, v₂)]
          + (iteratedFDeriv ℝ 2 (fun p : ℝᵈ × ℝᵈ => C * ‖p.2‖) (x, y))
            ![(-v₂, v₁), (-v₂, v₁)]) := by
    rw [hsplit v₁ v₂, hsplit (-v₂) v₁]
    ring
  rw [hQexpand, hQE, hQN]
  have hb1 := PhiE_line_bound hcond hω hc x y hy v₁
  have hb2 := PhiE_line_bound hcond hω hc x y hy v₂
  have hcomb : -(C₂ * (‖perpComp y v₁‖ ^ 2 + ‖perpComp y v₂‖ ^ 2)) / ‖y‖
      ≤ (1 / π) * ((∫ u : ℝ, lineBilin ω x y u v₁ v₁)
          + (∫ u : ℝ, lineBilin ω x y u v₂ v₂)) := by
    have hrw : (1 / π) * ((∫ u : ℝ, lineBilin ω x y u v₁ v₁)
          + (∫ u : ℝ, lineBilin ω x y u v₂ v₂))
        = (1 / π) * (∫ u : ℝ, lineBilin ω x y u v₁ v₁)
          + (1 / π) * (∫ u : ℝ, lineBilin ω x y u v₂ v₂) := by ring
    rw [hrw]
    have hs : -(C₂ * (‖perpComp y v₁‖ ^ 2 + ‖perpComp y v₂‖ ^ 2)) / ‖y‖
        = -(C₂ * ‖perpComp y v₁‖ ^ 2) / ‖y‖ + -(C₂ * ‖perpComp y v₂‖ ^ 2) / ‖y‖ := by
      rw [← add_div]
      congr 1
      ring
    rw [hs]
    linarith
  have hDnn : (0 : ℝ) ≤ ‖perpComp y v₁‖ ^ 2 + ‖perpComp y v₂‖ ^ 2 := by positivity
  have hfin : (0 : ℝ) ≤ -(C₂ * (‖perpComp y v₁‖ ^ 2 + ‖perpComp y v₂‖ ^ 2)) / ‖y‖
      + C * (‖perpComp y v₁‖ ^ 2 + ‖perpComp y v₂‖ ^ 2) / ‖y‖ := by
    rw [← add_div]
    refine div_nonneg ?_ (by positivity)
    have hA : -(C₂ * (‖perpComp y v₁‖ ^ 2 + ‖perpComp y v₂‖ ^ 2))
        + C * (‖perpComp y v₁‖ ^ 2 + ‖perpComp y v₂‖ ^ 2)
        = (C - C₂) * (‖perpComp y v₁‖ ^ 2 + ‖perpComp y v₂‖ ^ 2) := by ring
    rw [hA]
    exact mul_nonneg (sub_nonneg.mpr hC₂C) hDnn
  linarith

end Submission.FUP

namespace Submission.FUP

/-- The two-fold differentiation under the integral sign, from the shared commons. -/
lemma hasPhiE_second_all : ∀ (ω : ℝᵈ → ℝ), HasPhiE_second ω := fun ω hω hc x y V W hy => by
  have h := Commons.Analysis.Calculus.iteratedFDeriv_two_integral_add_smul (d := d) hω hc x y V W hy
  have hvec : (fun _ : Fin 2 => (V, W)) = ![(V, W), (V, W)] := fun_const_fin2 _
  rw [hvec] at h
  exact h

/-- **The Hessian inequality of `prop:Ew_is_psh`.** -/
theorem UWeight_hessian_nonneg {ω : ℝᵈ → ℝ} {C₂ C : ℝ} (hC₂C : C₂ ≤ C)
    (hcond : ∀ (x yhat vhat : ℝᵈ), ‖yhat‖ = 1 → ‖vhat‖ = 1 → inner ℝ yhat vhat = 0 →
      -C₂ ≤ (1 / π) * ∫ t : ℝ,
        ((iteratedFDeriv ℝ 2 ω (x + t • yhat)) (fun _ : Fin 2 => vhat)))
    (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω) :
    ∀ (x y v₁ v₂ : ℝᵈ), y ≠ 0 →
      0 ≤ (iteratedFDeriv ℝ 2 (UWeight ω C) (x, y)) ![(v₁, v₂), (v₁, v₂)]
        + (iteratedFDeriv ℝ 2 (UWeight ω C) (x, y)) ![(-v₂, v₁), (-v₂, v₁)] :=
  UWeight_hessian_nonneg_of_Eformula hasPhiE_second_all hC₂C hcond hω hc

/-- **Cohen's `prop:Ew_is_psh`** — no longer a black box. -/
theorem exact_psh_extension_statement_proof (d : ℕ) :
    exact_psh_extension_statement (d := d) :=
  exact_psh_extension_statement_of_hessian (d := d) fun ω C₂ C hC₂C hcond hω hc =>
    lineHessian_of_UWeight hω hc fun x y v₁ v₂ hy =>
      UWeight_hessian_nonneg hC₂C hcond hω hc x y v₁ v₂ hy

end Submission.FUP
