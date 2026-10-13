/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/Kernel.lean` — the mollifier kernel in the log coordinates

`Jeps ρ ε` is, in the log coordinates `s = log z`, `ζ = log tan θ`, the convolution with the
rescaled kernel `Jker ρ ε p = ε^{-2} ρ(p/ε)`:

  `Jeps ρ ε f z θ = ∫ p, Jker ρ ε p * (logPull f) (s - p₁, ζ - p₂)`

(`Jeps_eq_integral`, `logPull_shift` of `Basic.lean`).  This module collects the facts about the
kernel and the two shifts that every analytic step of the `E1` chapter uses:

* the support of `Jker ρ ε` is contained in the closed ball of radius `ε`
  (`Jker_ne_zero_support`), so every `p`-integral is an integral over a compact ball and every
  integrand is continuous on it (`integrableOn_Jker_mul_ball`);
* the two shifts map a compact sub-region of the quadrant into a compact sub-region
  (`zShift_mem_Kz`, `thShift_mem_Kth`), which is what makes the dominated-convergence arguments
  of `Commute.lean` work;
* `sin(2θ)·∂_θ(thShift θ p) = sin(2·thShift θ p)` (`sin_mul_deriv_thShift`), the `θ`-half of the
  commutation of `J_ε` with `D_θ`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Weights

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 400000

variable {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {f : Fn}

/-! ## The two shift regions -/

/-- The `z`-range of the shift, over `x ∈ (z/2, 2z)` and `|p| ≤ ε`. -/
def Kz (z ε : ℝ) : Set ℝ := Set.Icc (z / 2 * Real.exp (-ε)) (2 * z * Real.exp ε)

/-- The `θ`-range of the shift, over `|p| ≤ ε` (the shift is antitone in `p`). -/
def Kth (θ ε : ℝ) : Set ℝ := Set.Icc (thShift θ ε) (thShift θ (-ε))

theorem isCompact_Kz (z ε : ℝ) : IsCompact (Kz z ε) := isCompact_Icc

theorem isCompact_Kth (θ ε : ℝ) : IsCompact (Kth θ ε) := isCompact_Icc

theorem zShift_mem_Kz {z x p ε : ℝ} (hx : x ∈ Set.Ioo (z / 2) (2 * z)) (hp : |p| ≤ ε) :
    zShift x p ∈ Kz z ε := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  have hxpos : 0 < x := by linarith
  have hzpos : 0 < z := by linarith
  have hexp : Real.exp (-ε) ≤ Real.exp (-p) := Real.exp_le_exp.mpr (by linarith)
  have hexp' : Real.exp (-p) ≤ Real.exp ε := Real.exp_le_exp.mpr (by linarith)
  show z / 2 * Real.exp (-ε) ≤ zShift x p ∧ zShift x p ≤ 2 * z * Real.exp ε
  constructor
  · have h := mul_le_mul (show z / 2 ≤ x by linarith) hexp (Real.exp_pos _).le (le_of_lt hxpos)
    simpa only [zShift] using h
  · have h := mul_le_mul (le_of_lt hx2) hexp' (Real.exp_pos _).le (by linarith : (0:ℝ) ≤ 2 * z)
    simpa only [zShift] using h

theorem thShift_anti {θ p q : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hpq : p ≤ q) :
    thShift θ q ≤ thShift θ p := by
  have ht : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
  have h : Real.tan θ * Real.exp (-q) ≤ Real.tan θ * Real.exp (-p) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) ht.le
  exact Real.arctan_strictMono.monotone h

theorem thShift_mem_Kth {θ p ε : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hp : |p| ≤ ε) :
    thShift θ p ∈ Kth θ ε := by
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  exact ⟨thShift_anti hθ hp2, thShift_anti hθ (by linarith)⟩

/-- The shifted point stays in the open quadrant. -/
theorem mem_Quad_shift {z θ x p₁ p₂ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hx : x ∈ Set.Ioo (z / 2) (2 * z)) :
    (zShift x p₁, thShift θ p₂) ∈ Quad :=
  ⟨zShift_pos (by linarith [hx.1, hz]), thShift_mem hθ⟩

/-- The map `p ↦ (zShift x p.1, thShift θ p.2)` sends the ball of radius `ε` into the compact
region `Kz z ε ×ˢ Kth θ ε`, for every `x ∈ (z/2, 2z)`. -/
theorem mapsTo_ball_region {z θ x ε : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hx : x ∈ Set.Ioo (z / 2) (2 * z)) :
    MapsTo (fun p : ℝ × ℝ => (zShift x p.1, thShift θ p.2)) (Metric.closedBall 0 ε)
      (Kz z ε ×ˢ Kth θ ε) := by
  intro p hp
  have hp' : max |p.1| |p.2| ≤ ε := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using hp
  exact ⟨zShift_mem_Kz hx (le_trans (le_max_left _ _) hp'),
    thShift_mem_Kth hθ (le_trans (le_max_right _ _) hp')⟩

theorem Kz_subset_pos {z ε : ℝ} (hz : 0 < z) (hε : 0 < ε) :
    Kz z ε ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  exact lt_of_lt_of_le (by positivity) hx.1

theorem Kth_subset {θ ε : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Kth θ ε ⊆ Set.Ioo 0 (π / 2) :=
  fun x hx => ⟨lt_of_lt_of_le (thShift_mem hθ).1 hx.1,
    lt_of_le_of_lt hx.2 (thShift_mem hθ).2⟩

/-- The compact region of the shifts is contained in the open quadrant. -/
theorem Kz_prod_Kth_subset_Quad {z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Kz z ε ×ˢ Kth θ ε ⊆ Quad := by
  intro y hy
  exact ⟨Kz_subset_pos hz hε hy.1, Kth_subset hθ hy.2⟩

theorem continuous_zShift (z : ℝ) : Continuous fun p : ℝ => zShift z p := by
  simp only [zShift]; fun_prop

theorem continuous_thShift (θ : ℝ) : Continuous fun p : ℝ => thShift θ p := by
  simp only [thShift]; fun_prop

/-- The shifted point of a fixed base point, as a continuous function of the shift. -/
theorem continuous_shift_pair (z θ : ℝ) :
    Continuous fun p : ℝ × ℝ => (zShift z p.1, thShift θ p.2) := by
  simp only [zShift, thShift]
  fun_prop

/-- A base point lies in its own symmetric region. -/
theorem self_mem_Ioo_div_two {z : ℝ} (hz : 0 < z) : z ∈ Set.Ioo (z / 2) (2 * z) :=
  Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩

/-! ## The kernel -/

theorem Jker_ne_zero_support (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ}
    (hp : Jker ρ ε p ≠ 0) : p.1 ^ 2 + p.2 ^ 2 ≤ ε ^ 2 := by
  have h1 : (ε⁻¹ • p).1 ^ 2 + (ε⁻¹ • p).2 ^ 2 ≤ 1 :=
    hρ.support (ε⁻¹ • p) (fun hzero => hp (by simp [Jker, hzero]))
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1
  have h2 : ε ^ 2 * ε⁻¹ ^ 2 = 1 := by field_simp
  nlinarith [h1, h2, sq_nonneg (ε⁻¹ * p.1), sq_nonneg (ε⁻¹ * p.2), sq_nonneg ε,
    sq_nonneg ε⁻¹, sq_nonneg (ε * ε⁻¹ * p.1), sq_nonneg (ε * ε⁻¹ * p.2)]

theorem Jker_continuous (hρ : IsMollKernel ρ) (ε : ℝ) : Continuous (Jker ρ ε) :=
  continuous_const.mul (hρ.cont.comp (continuous_const_smul _))

theorem Jker_smooth (hρ : IsSmoothKernel ρ) (ε : ℝ) {n : ℕ} : ContDiff ℝ n (Jker ρ ε) := by
  have h1 : ContDiff ℝ n fun p : ℝ × ℝ => ε⁻¹ • p := contDiff_const_smul _
  exact contDiff_const.mul ((hρ.smooth n).comp h1)

theorem Jker_hasCompactSupport (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (Jker ρ ε) := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ × ℝ) ε) isClosed_closure
    (closure_minimal ?_ Metric.isClosed_closedBall)
  intro p hp
  have h := Jker_ne_zero_support hρ hε hp
  have h1 : p.1 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.2]
  have h2 : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1]
  have ha : |p.1| ≤ ε := by
    rw [sq_le_sq] at h1
    rwa [abs_of_nonneg hε.le] at h1
  have hb : |p.2| ≤ ε := by
    rw [sq_le_sq] at h2
    rwa [abs_of_nonneg hε.le] at h2
  rw [Metric.mem_closedBall, dist_zero_right]
  exact max_le ha hb

theorem Jker_integrable (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (Jker ρ ε) :=
  (Jker_continuous hρ ε).integrable_of_hasCompactSupport (Jker_hasCompactSupport hρ hε)

/-- The kernel vanishes off the ball of radius `ε`. -/
theorem Jker_eq_zero_of_not_mem (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ}
    (hp : p ∉ Metric.closedBall 0 ε) : Jker ρ ε p = 0 := by
  by_contra h
  have h' := Jker_ne_zero_support hρ hε h
  have h1 : p.1 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.2]
  have h2 : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1]
  have ha : |p.1| ≤ ε := by rw [sq_le_sq] at h1; rwa [abs_of_nonneg hε.le] at h1
  have hb : |p.2| ≤ ε := by rw [sq_le_sq] at h2; rwa [abs_of_nonneg hε.le] at h2
  refine hp ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact max_le ha hb

/-- **The basic integrability fact**: on the compact ball of radius `ε`, the product of the
kernel with a function that is continuous there is integrable. -/
theorem integrableOn_Jker_mul_ball (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {A : ℝ × ℝ → ℝ} (hA : ContinuousOn A (Metric.closedBall 0 ε)) :
    IntegrableOn (fun p => Jker ρ ε p * A p) (Metric.closedBall 0 ε) :=
  ((Jker_continuous hρ ε).continuousOn.mul hA).integrableOn_compact
    (isCompact_closedBall (0 : ℝ × ℝ) ε)

/-- The associated bound: the product is dominated by `C` times the kernel norm on the ball. -/
theorem exists_bound_Jker_mul_ball (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {A : ℝ × ℝ → ℝ} (hA : ContinuousOn A (Metric.closedBall 0 ε)) :
    ∃ C : ℝ, ∀ p ∈ Metric.closedBall (0 : ℝ × ℝ) ε, ‖A p‖ ≤ C :=
  (isCompact_closedBall (0 : ℝ × ℝ) ε).exists_bound_of_continuousOn hA

/-! ## Two elementary trigonometric facts used by the commutation -/

/-- `sin (2 arctan u) = 2u/(1+u²)`. -/
theorem sin_two_mul_arctan (u : ℝ) : Real.sin (2 * Real.arctan u) = 2 * u / (1 + u ^ 2) := by
  have hpos : 0 < √(1 + u ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

/-- **The `θ`-half of the commutation**: `sin(2θ) ∂_θ(thShift θ p) = sin (2·thShift θ p)`, i.e.
`D_θ` of the shifted point is the shifted point's own `sin(2·)`. -/
theorem sin_mul_deriv_thShift {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) (p : ℝ) :
    Real.sin (2 * θ) * deriv (fun θ' => thShift θ' p) θ
      = Real.sin (2 * thShift θ p) := by
  have hlt : -(π / 2) < θ := by linarith [hθ.1, Real.pi_pos]
  have hcos : Real.cos θ ≠ 0 := by
    have hp := Real.cos_arctan_pos (Real.tan θ)
    rw [Real.arctan_tan hlt hθ.2] at hp
    exact hp.ne'
  have ht : HasDerivAt (fun θ' => Real.tan θ' * Real.exp (-p))
      ((1 / Real.cos θ ^ 2) * Real.exp (-p)) θ :=
    (Real.hasDerivAt_tan hcos).mul_const _
  have harct := (Real.hasDerivAt_arctan (Real.tan θ * Real.exp (-p))).comp θ ht
  have hd : deriv (fun θ' => thShift θ' p) θ
      = (1 / (1 + (Real.tan θ * Real.exp (-p)) ^ 2))
          * ((1 / Real.cos θ ^ 2) * Real.exp (-p)) := by
    simpa only [thShift, Function.comp_def] using harct.deriv
  rw [hd]
  have h1 : Real.sin (2 * θ) = 2 * Real.tan θ * Real.cos θ ^ 2 := by
    rw [Real.sin_two_mul, Real.tan_eq_sin_div_cos]
    field_simp
  rw [h1, show thShift θ p = Real.arctan (Real.tan θ * Real.exp (-p)) from rfl,
    sin_two_mul_arctan]
  field_simp

end Work.FTS.StrongEps
