import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.AeMom.Defs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.AeMom.SmoothSlices
import Submission.Work.FTS.EllipticEst.AeMom.Repair.ShiftAeRepair
import Submission.Work.FTS.EllipticEst.H2W.sinRpowWeightDerivs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeSlotOneAe.Interp

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The four functions of the cross-slot identity

`A = z²∂_z²Ψ`, `A' = z²∂_z²(D_zΨ)`, `B = ∂_θ²Ψ`, `H = ∂_θ²(D_zΨ) - ∂_θ²Ψ`. -/

/-- `A = z² ∂_z²Ψ`, the radial-second-derivative datum of the A-slot. -/
def Az (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-- `A' = z² ∂_z²(D_zΨ)`; pointwise equal to `z ∂_z A` on the open quadrant. -/
def A1z (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ

/-- `B = ∂_θ²Ψ`. -/
def Bz (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.pthIter 2 Ψ z θ

/-- `H = ∂_θ²(D_zΨ) - ∂_θ²Ψ`; the `B' - B` whose square is the `B`-side of the slot. -/
def Hz (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
    - Work.Spaces.pthIter 2 Ψ z θ

/-- `ρ(z) = 1 - 4/(1+z)`. -/
def rhoZ (z : ℝ) : ℝ := 1 - 4 / (1 + z)

/-- `σ(θ) = sin(2θ)^{2-γ}`, `γ = gam α`: the angular weight of the `Tk`-slot. -/
def sigA (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)

/-! ## Facts about `ρ` and the radial weight -/

theorem rhoZ_apply {z : ℝ} (hz : 0 ≤ z) : rhoZ z = (z - 3) / (1 + z) := by
  have h1 : (1 + z) ≠ 0 := by positivity
  rw [rhoZ]
  field_simp
  ring

theorem rhoZ_abs_le {z : ℝ} (hz : 0 ≤ z) : |rhoZ z| ≤ 3 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : |z - 3| ≤ 3 * (1 + z) := by
    by_cases h : z ≤ 3
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [rhoZ_apply hz, abs_div, abs_of_pos h1, div_le_iff₀ h1]
  linarith

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

/-! ## Facts about `σ` -/

theorem sigA_eq_gam (α θ : ℝ) :
    sigA α θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 2)) := by
  rw [sigA]; congr 1; ring

theorem sigA_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sigA α θ := by
  rw [sigA]
  exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
    by linarith [hθ.2, Real.pi_pos]⟩) _

theorem sigA_pos {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < sigA α θ := by
  rw [sigA]
  exact Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _

theorem sigA_le_one {α : ℝ} (hα : α ≤ 1 / 4) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    sigA α θ ≤ 1 := by
  rw [sigA]
  refine Real.rpow_le_one (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
    by linarith [hθ.2, Real.pi_pos]⟩) (Real.sin_le_one _) ?_
  simp only [Work.Spaces.gam]; linarith

/-- `σ = sin(2θ)^{2-γ} ≤ sin(2θ)^{-η}` on `Iθ`: the `γ`-weight of the `Tk`-slot is dominated
by the `η`-weight of the `ℋ^k`-norm. -/
theorem sigA_le_sEta {α : ℝ} (hα : α ≤ 1 / 4) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    sigA α θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have h0 : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
    by linarith [hθ.2, Real.pi_pos]⟩
  rcases eq_or_lt_of_le h0 with h | h
  · have h1 : 2 - Work.Spaces.gam α ≠ 0 := by
      simp only [Work.Spaces.gam]; intro hc; linarith
    have h2 : -(Work.Spaces.eta) ≠ 0 := by simp only [Work.Spaces.eta]; norm_num
    rw [sigA, ← h, Real.zero_rpow h1, Real.zero_rpow h2]
  · refine Real.rpow_le_rpow_of_exponent_ge h (Real.sin_le_one _) ?_
    simp only [Work.Spaces.eta, Work.Spaces.gam]; linarith

/-- First derivative of `σ` on the open interval. -/
theorem sigA_deriv_of_mem {α : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (sigA α) θ = -2 * (Work.Spaces.gam α - 2) * Real.cos (2 * θ)
      * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) := by
  have hs : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have hfun : sigA α = fun t : ℝ => (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α - 2)) := by
    funext t; exact sigA_eq_gam α t
  rw [hfun, Work.FTS.EllipticEst.H2W.SinRpowWeight.sinRpowDerivOfNe
    (Work.Spaces.gam α - 2) θ hs]
  congr 1
  ring_nf

/-- Second derivative of `σ` on the open interval. -/
theorem sigA_deriv2_of_mem {α : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (deriv (sigA α)) θ
      = 4 * (Work.Spaces.gam α - 2) * (Work.Spaces.gam α - 1)
          * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        + 4 * (Work.Spaces.gam α - 2) * sigA α θ := by
  have hs : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have hev : deriv (sigA α) =ᶠ[𝓝 θ] fun t : ℝ => -2 * (Work.Spaces.gam α - 2)
      * Real.cos (2 * t) * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α - 2) - 1) := by
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
    rw [sigA_deriv_of_mem ht]
    congr 1
    ring_nf
  rw [Filter.EventuallyEq.deriv_eq hev,
    Work.FTS.EllipticEst.H2W.SinRpowWeight.sinRpowDerivDerivOfNe
      (Work.Spaces.gam α - 2) θ hs, sigA_eq_gam α θ]
  congr 3 <;> ring_nf

/-- `σ'' ≤ 0` on the open interval (for `0 < γ < 2`). -/
theorem sigA_deriv2_nonpos {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (deriv (sigA α)) θ ≤ 0 := by
  have h1 : Work.Spaces.gam α - 2 < 0 := by simp only [Work.Spaces.gam]; linarith
  have h2 : 0 < Work.Spaces.gam α - 1 := by simp only [Work.Spaces.gam]; linarith
  rw [sigA_deriv2_of_mem hθ]
  have h3 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
      by linarith [hθ.2, Real.pi_pos]⟩) _
  have h4 : 0 ≤ sigA α θ := (sigA_pos hθ).le
  have h5 : 0 ≤ (Real.cos (2 * θ)) ^ 2 := sq_nonneg _
  have hb : 0 ≤ (Work.Spaces.gam α - 1) * (Real.cos (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (mul_nonneg h2.le h5) h3
  have hc : 4 * (Work.Spaces.gam α - 2) ≤ 0 := by linarith
  have hA : 4 * (Work.Spaces.gam α - 2) * (Work.Spaces.gam α - 1) * (Real.cos (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ 0 := by
    have := mul_nonpos_of_nonpos_of_nonneg hc hb
    nlinarith [this]
  have hB : 4 * (Work.Spaces.gam α - 2) * sigA α θ ≤ 0 := by
    have := mul_nonpos_of_nonpos_of_nonneg hc h4
    nlinarith [this]
  linarith

end Work.FTS.EllipticEst.AeSlotOneAe.Interp
