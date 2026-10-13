import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.Nonlinear.Open.Row19Prep.gam_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The radial half `2z²/(1+z)³` of the projector coefficient. -/
def bcoefRad (z : ℝ) : ℝ := 2 * z ^ 2 / (1 + z) ^ 3

/-- The angular half `Γ(θ)/c(α)`. -/
def gamCoefAng (α θ : ℝ) : ℝ := Work.Spaces.Gam α θ / Work.Spaces.c α

lemma bcoefRad_eq (z : ℝ) : bcoefRad z = 2 * z ^ 2 / (1 + z) ^ 3 := rfl
lemma gamCoefAng_eq (α θ : ℝ) : gamCoefAng α θ = Work.Spaces.Gam α θ / Work.Spaces.c α := rfl

/-! ## A. Smoothness on the open quadrant -/

lemma contDiffOn_gamCoefAng (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => gamCoefAng α θ) (Set.Ioo 0 (π / 2)) := by
  have h : (fun θ : ℝ => gamCoefAng α θ)
      = fun θ : ℝ => Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹ := by
    funext θ; rw [gamCoefAng_eq]; ring
  rw [h]
  exact (Work.FTS.Nonlinear.Open.Row19Prep.contDiffOn_Gam α).mul contDiffOn_const

lemma contDiffOn_bcoefRad :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => bcoefRad z) (Set.Ioi 0) := by
  have h : (fun z : ℝ => bcoefRad z) = fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3 := by
    funext z; rw [bcoefRad_eq]
  rw [h]
  refine ContDiffOn.div ?_ ?_ ?_
  · exact contDiffOn_const.mul (contDiffOn_id.pow 2)
  · exact (contDiffOn_const.add contDiffOn_id).pow 3
  · intro z hz
    have hz1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    positivity

lemma smoothOpen_prod (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => gamCoefAng α θ * bcoefRad z) :=
  Work.FTS.Nonlinear.Open.Row19Prep.smoothOpen_mul
    (Work.FTS.Nonlinear.Open.Row19Prep.smoothOpen_theta_only (contDiffOn_gamCoefAng α))
    (Work.FTS.Nonlinear.Open.Row19Prep.smoothOpen_z_only contDiffOn_bcoefRad)

/-! ## B. Decomposition of the mixed operators on a product `g θ * φ z` -/

lemma DzIter_ang_rad (i : ℕ) (φ : ℝ → ℝ) (g : ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => g θ * φ z)
      = fun z θ => g θ * (Work.Spaces.Zop^[i] φ) z := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ, ih, Function.iterate_succ_apply']
      funext z θ
      show z * deriv (fun z' => g θ * (Work.Spaces.Zop^[i] φ) z') z
          = g θ * (Work.Spaces.Zop (Work.Spaces.Zop^[i] φ) z)
      simp only [Work.Spaces.Zop]
      rw [Work.Spaces.deriv_const_mul']
      ring

lemma dthU_iter_const_mul (i : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    Work.Spaces.dthU^[i] (fun θ => c * f θ) = fun θ => c * (Work.Spaces.dthU^[i] f) θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      funext θ
      simp only [Work.Spaces.dthU_apply]
      rw [Work.Spaces.deriv_const_mul']
      ring

lemma DthIter_ang_rad (i : ℕ) (φ : ℝ → ℝ) (g : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => g θ * φ z)
      = fun z θ => (Work.Spaces.dthU^[i] g) θ * φ z := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Function.iterate_succ_apply']
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => (Work.Spaces.dthU^[i] g) θ' * φ z) θ
          = (Work.Spaces.dthU (Work.Spaces.dthU^[i] g) θ) * φ z
      simp only [Work.Spaces.dthU_apply]
      rw [Work.Spaces.deriv_mul_const']
      ring

lemma mixed_ang_rad (j i : ℕ) (φ : ℝ → ℝ) (g : ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => g θ * φ z)
      = fun z θ => (Work.Spaces.dthU^[i] g) θ * (Work.Spaces.Zop^[j] φ) z := by
  rw [Work.Spaces.mixed, DthIter_ang_rad]
  exact DzIter_ang_rad j φ (Work.Spaces.dthU^[i] g)

/-! ## C. The two weight-square identities -/

lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

lemma div_sin_eta_sq (a : ℝ) {θ : ℝ} (hs : 0 ≤ Real.sin (2 * θ)) :
    (a / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = a ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have heta : (Work.Spaces.eta / 2) ≠ 0 := by rw [Work.Spaces.eta]; norm_num
  have heta' : -(Work.Spaces.eta) ≠ 0 := by rw [Work.Spaces.eta]; norm_num
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, Real.zero_rpow heta, div_zero, Real.zero_rpow heta', zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    ring
  · have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_mul_natCast h.le (Work.Spaces.eta / 2) 2]
      congr 1
      ring
    rw [div_eq_mul_inv, mul_pow, inv_pow, h1, Real.rpow_neg h.le (Work.Spaces.eta)]

lemma Wt_sq_of_nonneg {α z θ : ℝ} (hα : 0 < α) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hgam : Work.Spaces.gam α ≠ 0 := by
    rw [Work.Spaces.gam]; intro h; linarith
  have hgam2 : -(Work.Spaces.gam α / 2) ≠ 0 := by
    intro h
    apply hgam
    linarith
  have hgam' : -(Work.Spaces.gam α) ≠ 0 := neg_ne_zero.mpr hgam
  have hWt : Work.Spaces.Wt α z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
  rw [hWt, mul_pow]
  congr 1
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, Real.zero_rpow hgam2, Real.zero_rpow hgam', zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  · have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [← Real.rpow_mul_natCast h.le (-(Work.Spaces.gam α / 2)) 2]
      congr 1
      ring
    rw [h1]

/-! ## D. Pointwise angular bounds -/

/-- `radTB` dominates all the `tBound (i-1) 0` for `i ≤ 4`. -/
def radTB : ℝ := ∑ j ∈ Finset.range 3, Work.Spaces.tBound j 0

lemma radTB_nonneg : 0 ≤ radTB :=
  Finset.sum_nonneg fun j _ => Work.Spaces.tBound_nonneg j 0

lemma tBound_le_radTB {i : ℕ} (hi1 : 1 ≤ i) (hi3 : i ≤ 3) :
    Work.Spaces.tBound (i - 1) 0 ≤ radTB :=
  Finset.single_le_sum (f := fun j : ℕ => Work.Spaces.tBound j 0)
    (fun j _ => Work.Spaces.tBound_nonneg j 0)
    (Finset.mem_range.mpr (by omega))

lemma c_pos {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : 0 < Work.Spaces.c α := by
  have h := (Work.Spaces.c_bounds α hα hα1).1
  linarith

lemma gamCoefAng_nonneg {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ gamCoefAng α θ :=
  div_nonneg (Work.Spaces.Gam_bounds α θ hα hθ).1 (le_of_lt (c_pos hα hα1))

lemma gamCoefAng_le_ten {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) : gamCoefAng α θ ≤ 10 := by
  rw [gamCoefAng_eq, div_le_iff₀ (c_pos hα hα1)]
  have h1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
  have h2 : (1 : ℝ) ≤ 10 * Work.Spaces.c α := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  linarith

lemma gamCoefAng_abs_le_ten {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) : |gamCoefAng α θ| ≤ 10 := by
  rw [abs_of_nonneg (gamCoefAng_nonneg hα hα1 hθ)]
  exact gamCoefAng_le_ten hα hα1 hθ

lemma gamCoefAng_sq_le {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) : (gamCoefAng α θ) ^ 2 ≤ 100 := by
  have h1 : gamCoefAng α θ ≤ 10 := gamCoefAng_le_ten hα hα1 hθ
  have h2 : 0 ≤ gamCoefAng α θ := gamCoefAng_nonneg hα hα1 hθ
  nlinarith

lemma gamCoefAng_sq_le_gam_sq {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (gamCoefAng α θ) ^ 2 ≤ 100 * (Work.Spaces.Gam α θ) ^ 2 := by
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hcpos : 0 < Work.Spaces.c α := c_pos hα hα1
  have hcle : 10 * (Work.Spaces.c α)⁻¹ ≤ 100 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    have h1 : (Work.Spaces.c α)⁻¹ ≤ 10 := by
      rw [inv_le_iff_one_le_mul₀ hcpos]
      linarith
    linarith
  have h1 : gamCoefAng α θ ≤ 10 * Work.Spaces.Gam α θ := by
    rw [gamCoefAng_eq, div_le_iff₀ hcpos]
    have : Work.Spaces.Gam α θ * 1 ≤ Work.Spaces.Gam α θ * (10 * Work.Spaces.c α) := by
      have h2 : (1 : ℝ) ≤ 10 * Work.Spaces.c α := by
        have h := (Work.Spaces.c_bounds α hα hα1).1; linarith
      exact mul_le_mul_of_nonneg_left h2 hG0
    linarith
  have h2 : 0 ≤ gamCoefAng α θ := gamCoefAng_nonneg hα hα1 hθ
  have h3 : 0 ≤ 10 * Work.Spaces.Gam α θ := by positivity
  nlinarith [sq_nonneg (gamCoefAng α θ), sq_nonneg (Work.Spaces.Gam α θ), mul_nonneg h2 h3]

/-- `dthU^i` of the angular coefficient is dominated by `α·radTB·(Γ/c)`. -/
lemma dthU_gamCoefAng_le {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) {i : ℕ} (hi1 : 1 ≤ i) (hi3 : i ≤ 3) :
    |Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ| ≤ α * radTB * gamCoefAng α θ := by
  have hdec : (fun θ : ℝ => gamCoefAng α θ)
      = fun θ : ℝ => (Work.Spaces.c α)⁻¹ * Work.Spaces.Gam α θ := by
    funext t; rw [gamCoefAng_eq]; ring
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hcpos : 0 < Work.Spaces.c α := c_pos hα hα1
  have hbase := Work.Spaces.dthU_Gam_le i hi1 α hα hα1 θ hθ
  rw [hdec, dthU_iter_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hcpos)]
  have h1 : (Work.Spaces.c α)⁻¹ * |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ (Work.Spaces.c α)⁻¹ * (α * Work.Spaces.tBound (i - 1) 0 * Work.Spaces.Gam α θ) :=
    mul_le_mul_of_nonneg_left hbase (le_of_lt (inv_pos.mpr hcpos))
  calc (Work.Spaces.c α)⁻¹ * |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ (Work.Spaces.c α)⁻¹ * (α * Work.Spaces.tBound (i - 1) 0 * Work.Spaces.Gam α θ) := h1
    _ = α * Work.Spaces.tBound (i - 1) 0 * (Work.Spaces.Gam α θ / Work.Spaces.c α) := by
          rw [div_eq_mul_inv]; ring
    _ ≤ α * radTB * (Work.Spaces.Gam α θ / Work.Spaces.c α) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (tBound_le_radTB hi1 hi3) (le_of_lt hα))
            (div_nonneg hG0 (le_of_lt hcpos))
    _ = α * radTB * gamCoefAng α θ := by rw [gamCoefAng_eq]

lemma dthU_gamCoefAng_sq_le {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) {i : ℕ} (hi1 : 1 ≤ i) (hi3 : i ≤ 3) :
    (Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ) ^ 2
      ≤ 100 * radTB ^ 2 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2) := by
  have h1 : |Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ| ≤ α * radTB * gamCoefAng α θ :=
    dthU_gamCoefAng_le hα hα1 hθ hi1 hi3
  have h2 : 0 ≤ α * radTB * gamCoefAng α θ :=
    mul_nonneg (mul_nonneg (le_of_lt hα) radTB_nonneg) (gamCoefAng_nonneg hα hα1 hθ)
  have h3 : (Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ) ^ 2
      ≤ (α * radTB * gamCoefAng α θ) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg h2]
    exact h1
  refine h3.trans ?_
  have h4 : (gamCoefAng α θ) ^ 2 ≤ 100 * (Work.Spaces.Gam α θ) ^ 2 := gamCoefAng_sq_le_gam_sq hα hα1 hθ
  have h5 : 0 ≤ (α * radTB) ^ 2 := sq_nonneg _
  calc (α * radTB * gamCoefAng α θ) ^ 2 = (α * radTB) ^ 2 * (gamCoefAng α θ) ^ 2 := by ring
    _ ≤ (α * radTB) ^ 2 * (100 * (Work.Spaces.Gam α θ) ^ 2) := mul_le_mul_of_nonneg_left h4 h5
    _ = 100 * radTB ^ 2 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2) := by ring


end Work.FTS.StrongPersist.L3Aux
