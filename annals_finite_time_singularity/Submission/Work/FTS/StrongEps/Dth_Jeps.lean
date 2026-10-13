/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/Dth_Jeps.lean` — E1, the commutation of `J_ε` with `D_θ`

This is the `θ`-half of **E1** of the design (`FTS_HARD_DESIGN.md`, section *(B)*), the
companion of `Commute.lean`'s `Dz_Jeps`:

* `hasDerivAt_integral_Jeps_th` — differentiating the `p`-integral form of `J_ε f` in the
  angle `θ` (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`).  The kernel is supported in
  the ball of radius `ε` and the `θ`-shifts `θ ↦ thShift θ p₂` of a *compact* sub-interval of
  `(0, π/2)` stay in a *compact* sub-interval of `(0, π/2)`, which supplies the domination;
* **`Dth_Jeps`** — `D_θ (J_ε f) = J_ε (D_θ f)` at every point of the open quadrant.  The
  identity is *exact*: on the shifted point
  `sin(2θ) · ∂_θ (thShift θ p₂) = sin (2 · thShift θ p₂)` (`sin_mul_deriv_thShift`), i.e. the
  shift is the translation `ζ ↦ ζ - p₂` of the log coordinate `ζ = log tan θ`, so the weight
  `sin (2θ)` of `D_θ` is carried along by the shift.

The auxiliary bookkeeping (the compact `θ`-region `Kth'` of the shift, the monotonicity of
`thShift`, the bound on `∂_θ (thShift · p)`) is proved here.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Commute

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {f : Fn}

/-! ## The compact `θ`-region of the shift

For a base angle `θ ∈ (0, π/2)` the shifts `thShift x q` with `x` near `θ` (say
`x ∈ (θ/2, (θ+π/2)/2)`) and `|q| ≤ ε` stay in the compact interval `Kth' θ ε`, strictly
inside `(0, π/2)`.  This is what makes both `pth f` and `∂_θ(thShift · q)` bounded. -/

/-- The support of the shift in `z` is `Kz` (`Kernel.lean`); its `θ`-analogue is
`Kth' θ ε`, the interval swept out by `thShift x q` for `x ∈ [θ/2, (θ+π/2)/2]` and
`|q| ≤ ε`. -/
def Kth' (θ ε : ℝ) : Set ℝ := Set.Icc (thShift (θ / 2) ε) (thShift ((θ + π / 2) / 2) (-ε))

theorem isCompact_Kth' (θ ε : ℝ) : IsCompact (Kth' θ ε) := isCompact_Icc

/-- `thShift` is monotone in its first variable on `(0, π/2)`
(the shift `θ ↦ arctan (tan θ · e^{-p})` of `tan`). -/
theorem thShift_mono_theta {θ₁ θ₂ p : ℝ} (h₁ : θ₁ ∈ Set.Ioo 0 (π / 2))
    (h₂ : θ₂ ∈ Set.Ioo 0 (π / 2)) (h : θ₁ ≤ θ₂) : thShift θ₁ p ≤ thShift θ₂ p := by
  rcases lt_or_eq_of_le h with hlt | heq
  · have ht : Real.tan θ₁ * Real.exp (-p) ≤ Real.tan θ₂ * Real.exp (-p) :=
      mul_le_mul_of_nonneg_right
        (le_of_lt (Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [h₁.1, Real.pi_pos])
          h₂.2 hlt))
        (Real.exp_pos _).le
    exact Real.arctan_mono ht
  · simp [heq]

theorem mem_Ioo_half {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : θ / 2 ∈ Set.Ioo 0 (π / 2) :=
  ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem mem_Ioo_halfpi {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (θ + π / 2) / 2 ∈ Set.Ioo 0 (π / 2) :=
  ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩

/-- The shifted angle belongs to the compact region `Kth' θ ε`. -/
theorem thShift_mem_Kth' {θ x q ε : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hx : x ∈ Set.Ioo (θ / 2) ((θ + π / 2) / 2)) (hq : |q| ≤ ε) :
    thShift x q ∈ Kth' θ ε := by
  obtain ⟨hq1, hq2⟩ := abs_le.mp hq
  have hx2 : x ∈ Set.Ioo 0 (π / 2) :=
    ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, hθ.2, Real.pi_pos]⟩
  exact ⟨le_trans (thShift_mono_theta (mem_Ioo_half hθ) hx2 hx.1.le) (thShift_anti hx2 hq2),
    le_trans (thShift_anti hx2 hq1) (thShift_mono_theta hx2 (mem_Ioo_halfpi hθ) hx.2.le)⟩

/-- `Kth' θ ε` lies strictly inside the open quadrant in the `θ`-variable. -/
theorem Kth'_subset {θ ε : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Kth' θ ε ⊆ Set.Ioo 0 (π / 2) := by
  intro _y hy
  exact ⟨lt_of_lt_of_le (thShift_mem (mem_Ioo_half hθ)).1 hy.1,
    lt_of_le_of_lt hy.2 (thShift_mem (mem_Ioo_halfpi hθ)).2⟩

/-- The product region of the two shifts is contained in the open quadrant. -/
theorem Kz_prod_Kth'_subset_Quad {z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Kz z ε ×ˢ Kth' θ ε ⊆ Quad :=
  fun _y hy => ⟨Kz_subset_pos hz hε hy.1, Kth'_subset hθ hy.2⟩

/-! ## The derivative of the `θ`-shift -/

/-- **The bound on `∂_θ (thShift · q)`** on the compact region: since
`∂_θ (thShift · q) = (1 + (tan θ e^{-q})²)^{-1} · (cos θ)^{-2} e^{-q}`, it is dominated by
`e^{ε} / cos((θ+π/2)/2)²` there. -/
theorem deriv_thShift_bound {θ ε : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ∀ x ∈ Set.Ioo (θ / 2) ((θ + π / 2) / 2), ∀ q ∈ Set.Icc (-ε) ε,
      ‖deriv (fun θ' => thShift θ' q) x‖ ≤ Real.exp ε / Real.cos ((θ + π / 2) / 2) ^ 2 := by
  intro x hx q hq
  obtain ⟨hq1, hq2⟩ := hq
  have hx2 : x ∈ Set.Ioo 0 (π / 2) :=
    ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, hθ.2, Real.pi_pos]⟩
  have hcosx : Real.cos x ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx2.1, Real.pi_pos], hx2.2⟩).ne'
  have hd : deriv (fun θ' => thShift θ' q) x
      = (1 / (1 + (Real.tan x * Real.exp (-q)) ^ 2)) * ((1 / Real.cos x ^ 2) * Real.exp (-q)) := by
    have htan : HasDerivAt (fun θ' => Real.tan θ' * Real.exp (-q))
        ((1 / Real.cos x ^ 2) * Real.exp (-q)) x :=
      (Real.hasDerivAt_tan hcosx).mul_const _
    have harct := (Real.hasDerivAt_arctan (Real.tan x * Real.exp (-q))).comp x htan
    simpa only [thShift, Function.comp_def] using harct.deriv
  rw [hd, norm_mul, norm_mul,
    Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (1 + (Real.tan x * Real.exp (-q)) ^ 2)),
    Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / Real.cos x ^ 2),
    Real.norm_of_nonneg (Real.exp_pos _).le]
  have hden : (0:ℝ) < 1 + (Real.tan x * Real.exp (-q)) ^ 2 := by positivity
  have ht_le : 1 / (1 + (Real.tan x * Real.exp (-q)) ^ 2) ≤ 1 := by
    rw [div_le_one hden]
    nlinarith [sq_nonneg (Real.tan x * Real.exp (-q))]
  have hcosC : Real.cos ((θ + π / 2) / 2) ≤ Real.cos x :=
    Real.cos_le_cos_of_nonneg_of_le_pi hx2.1.le (by linarith [hx.2, hθ.2, Real.pi_pos]) hx.2.le
  have hcosCpos : 0 < Real.cos ((θ + π / 2) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hcosxpos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hx2.1, Real.pi_pos], hx2.2⟩
  have hC : (1:ℝ) / Real.cos x ^ 2 ≤ 1 / Real.cos ((θ + π / 2) / 2) ^ 2 := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [hcosC, hcosCpos, hcosxpos]
  have he : Real.exp (-q) ≤ Real.exp ε := Real.exp_le_exp.mpr (by linarith)
  calc (1 / (1 + (Real.tan x * Real.exp (-q)) ^ 2)) * ((1 / Real.cos x ^ 2) * Real.exp (-q))
      ≤ (1 / Real.cos x ^ 2) * Real.exp (-q) :=
        mul_le_of_le_one_left (by positivity) ht_le
    _ ≤ (1 / Real.cos ((θ + π / 2) / 2) ^ 2) * Real.exp ε :=
        mul_le_mul hC he (Real.exp_pos _).le (by positivity)
    _ = Real.exp ε / Real.cos ((θ + π / 2) / 2) ^ 2 := by ring

/-- **Continuity of `q ↦ ∂_θ (thShift · q)`**: it is `sin(2·thShift θ q)/sin(2θ)`. -/
theorem continuous_deriv_thShift {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Continuous fun q => deriv (fun θ' => thShift θ' q) θ := by
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    have h := Real.sin_pos_of_pos_of_lt_pi (x := 2 * θ) (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
    linarith
  have hfun : (fun q => deriv (fun θ' => thShift θ' q) θ)
      = fun q => Real.sin (2 * thShift θ q) / Real.sin (2 * θ) := by
    funext q
    rw [← sin_mul_deriv_thShift hθ q]
    field_simp
  rw [hfun]
  exact (Real.continuous_sin.comp (continuous_const.mul (continuous_thShift θ))).div_const _

/-! ## The `θ`-derivative under the `p`-integral -/

/-- **The dominated-convergence computation of the `θ`-derivative.**  For a profile which is
`C¹` on the open quadrant (with continuous `θ`-derivative there), the `p`-integral form of
`J_ε f` at the radius `z` is differentiable in `θ`, with the integral of the derivative of the
integrand as derivative. -/
theorem hasDerivAt_integral_Jeps_th (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) {f : Fn}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Quad)
    (hdf : ContinuousOn (Function.uncurry (Work.Spaces.pth f)) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' => ∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z p.1) (thShift θ' p.2)
        ∂(volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε)))
      (∫ p : ℝ × ℝ, Jker ρ ε p *
        (Work.Spaces.pth f (zShift z p.1) (thShift θ p.2) *
          deriv (fun θ' => thShift θ' p.2) θ)
        ∂(volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε))) θ := by
  have hx0 : θ ∈ Set.Ioo (θ / 2) ((θ + π / 2) / 2) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hsub : Set.Ioo (θ / 2) ((θ + π / 2) / 2) ⊆ Set.Ioo 0 (π / 2) :=
    fun x hx => ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, hθ.2, Real.pi_pos]⟩
  have hmem : ∀ x ∈ Set.Ioo (θ / 2) ((θ + π / 2) / 2), ∀ p : ℝ × ℝ,
      p ∈ Metric.closedBall (0 : ℝ × ℝ) ε → (zShift z p.1, thShift x p.2) ∈ Quad := by
    intro x hx p hp
    have hp' : max |p.1| |p.2| ≤ ε := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using hp
    exact ⟨Kz_subset_pos hz hε
        (zShift_mem_Kz (self_mem_Ioo_div_two hz) (le_trans (le_max_left _ _) hp')),
      Kth'_subset hθ (thShift_mem_Kth' hθ hx (le_trans (le_max_right _ _) hp'))⟩
  obtain ⟨C, hC⟩ := (isCompact_Kz z ε).prod (isCompact_Kth' θ ε) |>.exists_bound_of_continuousOn
    (hdf.mono (Kz_prod_Kth'_subset_Quad hz hε hθ))
  have hCs : ∀ x ∈ Set.Ioo (θ / 2) ((θ + π / 2) / 2), ∀ p : ℝ × ℝ,
      p ∈ Metric.closedBall (0 : ℝ × ℝ) ε →
        ‖Work.Spaces.pth f (zShift z p.1) (thShift x p.2)‖ ≤ C := by
    intro x hx p hp
    have hp' : max |p.1| |p.2| ≤ ε := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using hp
    exact hC (zShift z p.1, thShift x p.2)
      ⟨zShift_mem_Kz (self_mem_Ioo_div_two hz) (le_trans (le_max_left _ _) hp'),
        thShift_mem_Kth' hθ hx (le_trans (le_max_right _ _) hp')⟩
  have hctrl := continuous_shift_pair z θ
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε)) (𝕜 := ℝ)
    (F := fun x p => Jker ρ ε p * f (zShift z p.1) (thShift x p.2))
    (F' := fun x p => Jker ρ ε p * (Work.Spaces.pth f (zShift z p.1) (thShift x p.2) *
      deriv (fun θ' => thShift θ' p.2) x))
    (bound := fun p => (C * (Real.exp ε / Real.cos ((θ + π / 2) / 2) ^ 2)) * ‖Jker ρ ε p‖)
    (x₀ := θ) (s := Set.Ioo (θ / 2) ((θ + π / 2) / 2)) (isOpen_Ioo.mem_nhds hx0)
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [isOpen_Ioo.mem_nhds hx0] with x hx
    have hctrl' : Continuous fun p : ℝ × ℝ => (zShift z p.1, thShift x p.2) :=
      continuous_shift_pair z x
    have hcont : ContinuousOn (fun p : ℝ × ℝ => f (zShift z p.1) (thShift x p.2))
        (Metric.closedBall 0 ε) :=
      hf.continuousOn.comp hctrl'.continuousOn (fun p hp => hmem x hx p hp)
    exact (integrableOn_Jker_mul_ball hρ hε hcont).aestronglyMeasurable
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => f (zShift z p.1) (thShift θ p.2))
        (Metric.closedBall 0 ε) :=
      hf.continuousOn.comp hctrl.continuousOn (fun p hp => hmem θ hx0 p hp)
    exact integrableOn_Jker_mul_ball hρ hε hcont
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth f (zShift z p.1) (thShift θ p.2) *
        deriv (fun θ' => thShift θ' p.2) θ) (Metric.closedBall 0 ε) :=
      (hdf.comp hctrl.continuousOn (fun p hp => hmem θ hx0 p hp)).mul
        (((continuous_deriv_thShift hθ).comp continuous_snd).continuousOn)
    exact (integrableOn_Jker_mul_ball hρ hε hcont).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_closedBall]
    refine Eventually.of_forall fun a ha x hx => ?_
    have ha' : max |a.1| |a.2| ≤ ε := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using ha
    have ha2 : a.2 ∈ Set.Icc (-ε) ε := by
      rw [Set.mem_Icc]
      exact abs_le.mp (le_trans (le_max_right |a.1| |a.2|) ha')
    have h2 : ‖Work.Spaces.pth f (zShift z a.1) (thShift x a.2)‖ ≤ C := hCs x hx a ha
    have h3 : ‖deriv (fun θ' => thShift θ' a.2) x‖
        ≤ Real.exp ε / Real.cos ((θ + π / 2) / 2) ^ 2 := deriv_thShift_bound hθ x hx a.2 ha2
    rw [norm_mul, norm_mul]
    calc ‖Jker ρ ε a‖ * (‖Work.Spaces.pth f (zShift z a.1) (thShift x a.2)‖ *
            ‖deriv (fun θ' => thShift θ' a.2) x‖)
        ≤ ‖Jker ρ ε a‖ * (C * (Real.exp ε / Real.cos ((θ + π / 2) / 2) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (norm_nonneg _) (le_trans (norm_nonneg _) h2))
            (norm_nonneg _)
      _ = (C * (Real.exp ε / Real.cos ((θ + π / 2) / 2) ^ 2)) * ‖Jker ρ ε a‖ := by ring
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => ‖Jker ρ ε p‖) (Metric.closedBall 0 ε) :=
      (Jker_continuous hρ ε).norm.continuousOn
    exact ((hcont.integrableOn_compact (isCompact_closedBall (0 : ℝ × ℝ) ε)).const_mul _)
  · refine Eventually.of_forall fun a x hx => ?_
    have hquad : (zShift z a.1, thShift x a.2) ∈ Quad :=
      ⟨zShift_pos hz, thShift_mem (hsub hx)⟩
    have hd_on : DifferentiableOn ℝ (Function.uncurry f) Quad := hf.differentiableOn (by norm_num)
    have hd_at : DifferentiableAt ℝ (Function.uncurry f) (zShift z a.1, thShift x a.2) :=
      hd_on.differentiableAt (isOpen_Quad.mem_nhds hquad)
    have hpr : DifferentiableAt ℝ (fun y : ℝ => (zShift z a.1, y)) (thShift x a.2) := by fun_prop
    have hslice : HasDerivAt (fun y : ℝ => f (zShift z a.1) y)
        (Work.Spaces.pth f (zShift z a.1) (thShift x a.2)) (thShift x a.2) := by
      have h := (hd_at.comp (thShift x a.2) hpr).hasDerivAt
      simpa only [Function.comp_def, Function.uncurry, Work.Spaces.pth] using h
    have hcosx : Real.cos x ≠ 0 :=
      ((Real.cos_pos_of_mem_Ioo ⟨by linarith [(hsub hx).1, Real.pi_pos], (hsub hx).2⟩)).ne'
    have hdtan : HasDerivAt (fun y : ℝ => Real.tan y * Real.exp (-a.2))
        ((1 / Real.cos x ^ 2) * Real.exp (-a.2)) x := (Real.hasDerivAt_tan hcosx).mul_const _
    have hdarc : HasDerivAt (fun y : ℝ => thShift y a.2)
        ((1 / (1 + (Real.tan x * Real.exp (-a.2)) ^ 2)) *
          ((1 / Real.cos x ^ 2) * Real.exp (-a.2))) x := by
      have h := (Real.hasDerivAt_arctan (Real.tan x * Real.exp (-a.2))).comp x hdtan
      simpa only [thShift, Function.comp_def] using h
    have hx1 : HasDerivAt (fun y : ℝ => thShift y a.2) (deriv (fun θ' => thShift θ' a.2) x) x :=
      hdarc.congr_deriv hdarc.deriv.symm
    exact (hslice.comp x hx1).const_mul (Jker ρ ε a)

/-- **`E1`, `θ`-half: `J_ε` commutes with `∂_θ` under the integral** (the `p`-integral form). -/
theorem Jeps_deriv_th (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) {f : Fn}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Quad)
    (hdf : ContinuousOn (Function.uncurry (Work.Spaces.pth f)) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    deriv (fun θ' => Jeps ρ ε f z θ') θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p *
          (Work.Spaces.pth f (zShift z p.1) (thShift θ p.2) *
            deriv (fun θ' => thShift θ' p.2) θ) := by
  have hd := hasDerivAt_integral_Jeps_th hρ hε hf hdf hz hθ
  have hballF : (fun θ' => ∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z p.1) (thShift θ' p.2)
        ∂(volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε)))
      = fun θ' => ∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z p.1) (thShift θ' p.2) := by
    funext θ'
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (s := Metric.closedBall (0 : ℝ × ℝ) ε)
      (f := fun p : ℝ × ℝ => Jker ρ ε p * f (zShift z p.1) (thShift θ' p.2))
      (fun p hp => by rw [Jker_eq_zero_of_not_mem hρ hε hp, zero_mul])
  have hballG : (∫ p : ℝ × ℝ, Jker ρ ε p *
        (Work.Spaces.pth f (zShift z p.1) (thShift θ p.2) *
          deriv (fun θ' => thShift θ' p.2) θ))
      = ∫ p : ℝ × ℝ, Jker ρ ε p *
        (Work.Spaces.pth f (zShift z p.1) (thShift θ p.2) *
          deriv (fun θ' => thShift θ' p.2) θ)
        ∂(volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε)) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (s := Metric.closedBall (0 : ℝ × ℝ) ε)
      (f := fun p : ℝ × ℝ => Jker ρ ε p *
        (Work.Spaces.pth f (zShift z p.1) (thShift θ p.2) *
          deriv (fun θ' => thShift θ' p.2) θ))
      (fun p hp => by rw [Jker_eq_zero_of_not_mem hρ hε hp, zero_mul])).symm
  have hev : (fun θ' => Jeps ρ ε f z θ')
      =ᶠ[𝓝 θ] fun θ' => ∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z p.1) (thShift θ' p.2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact Jeps_eq_integral ρ ε f hz hθ'
  rw [hballF] at hd
  rw [hev.deriv_eq, hd.deriv]
  exact hballG.symm

/-- **`E1`, `θ`-half, `D_θ`-form: `D_θ (J_ε f) = J_ε (D_θ f)` on the open quadrant.** -/
theorem Dth_Jeps (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ 1 (Function.uncurry f) Quad)
    (hdf : ContinuousOn (Function.uncurry (Work.Spaces.pth f)) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth (Jeps ρ ε f) z θ = Jeps ρ ε (Work.Spaces.Dth f) z θ := by
  have hd : deriv (fun θ' => (Jeps ρ ε f) z θ') θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p *
          (Work.Spaces.pth f (zShift z p.1) (thShift θ p.2) *
            deriv (fun θ' => thShift θ' p.2) θ) :=
    Jeps_deriv_th hρ hε hf hdf hz hθ
  have hJ : Jeps ρ ε (Work.Spaces.Dth f) z θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p *
          (Real.sin (2 * thShift θ p.2) *
            Work.Spaces.pth f (zShift z p.1) (thShift θ p.2)) := by
    have hD : Work.Spaces.Dth f
        = fun z' θ' => Real.sin (2 * θ') * Work.Spaces.pth f z' θ' := rfl
    rw [hD, Jeps_eq_integral ρ ε _ hz hθ]
  rw [hJ]
  show Real.sin (2 * θ) * deriv (fun θ' => (Jeps ρ ε f) z θ') θ = _
  rw [hd]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  have hsin := sin_mul_deriv_thShift hθ p.2
  simp only [Work.Spaces.pth]
  calc Real.sin (2 * θ) * (Jker ρ ε p * (deriv (fun θ' => f (zShift z p.1) θ') (thShift θ p.2) *
          deriv (fun θ' => thShift θ' p.2) θ))
      = Jker ρ ε p * (deriv (fun θ' => f (zShift z p.1) θ') (thShift θ p.2) *
          (Real.sin (2 * θ) * deriv (fun θ' => thShift θ' p.2) θ)) := by ring
    _ = Jker ρ ε p * (deriv (fun θ' => f (zShift z p.1) θ') (thShift θ p.2) *
          Real.sin (2 * thShift θ p.2)) := by rw [hsin]
    _ = Jker ρ ε p * (Real.sin (2 * thShift θ p.2) *
          deriv (fun θ' => f (zShift z p.1) θ') (thShift θ p.2)) := by ring

end Work.FTS.StrongEps
