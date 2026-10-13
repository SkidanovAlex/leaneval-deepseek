import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.FTS.EllipticEst.Lop_iter_sin_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Radial profiles vs. their `sin (2θ)`-multiples: the algebraic identities

Part 1 of the proof of `Work.FTS.EllSol.PkgK5.radialHkNorm_le_sinMul`: the one-variable
iterates `RIter j Λ` of the radial operator `D_z = z ∂_z`, the identity
`D_z^j (Λ · B θ) = (RIter j Λ) · B`, and the corresponding angular identities.
-/

namespace Work.FTS.EllSol.PkgK5

namespace Radial

/-! ## The one-dimensional radial operator `D_z = z ∂_z` -/

/-- The one-dimensional operator `h ↦ z ∂_z h`. -/
def RDz (h : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv h z

/-- The `j`-fold iterate of `RDz`. -/
def RIter (j : ℕ) (h : ℝ → ℝ) : ℝ → ℝ := RDz^[j] h

@[simp] theorem RIter_zero (h : ℝ → ℝ) : RIter 0 h = h := rfl

theorem RIter_succ (j : ℕ) (h : ℝ → ℝ) :
    RIter (j + 1) h = fun z => z * deriv (RIter j h) z := by
  rw [show RIter (j + 1) h = RDz (RIter j h) from Function.iterate_succ_apply' RDz j h]
  rfl

theorem RIter_succ_apply (j : ℕ) (h : ℝ → ℝ) (z : ℝ) :
    RIter (j + 1) h z = z * deriv (RIter j h) z := by
  rw [RIter_succ]

theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- `sin(2·)^p` is measurable. -/
theorem measurable_sin2_rpow (p : ℝ) : Measurable (fun θ : ℝ => Real.sin (2 * θ) ^ p) := by
  fun_prop

/-! ### Smoothness of the radial iterates -/

/-- The iterates `RIter j Λ` of a smooth `Λ` are smooth on `(0,∞)`. -/
theorem contDiffOn_RIter (Λ : ℝ → ℝ) (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) :
    ∀ j n : ℕ, ContDiffOn ℝ n (RIter j Λ) (Set.Ioi 0) := by
  intro j
  induction j with
  | zero => intro n; simpa using hΛ n
  | succ j ih =>
    intro n
    have h1 : ContDiffOn ℝ (n + 1) (RIter j Λ) (Set.Ioi 0) := ih (n + 1)
    have h2 : ContDiffOn ℝ n (deriv (RIter j Λ)) (Set.Ioi 0) :=
      h1.deriv_of_isOpen isOpen_Ioi (by simp)
    have h3 : ContDiffOn ℝ n (fun z : ℝ => z) (Set.Ioi 0) := contDiff_id.contDiffOn
    rw [RIter_succ]
    exact h3.mul h2

/-- Differentiability of the radial iterates at a positive point. -/
theorem differentiableAt_RIter (Λ : ℝ → ℝ) (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0))
    (j : ℕ) {z : ℝ} (hz : 0 < z) : DifferentiableAt ℝ (RIter j Λ) z :=
  ((contDiffOn_RIter Λ hΛ j 1).differentiableOn (by simp)).differentiableAt
    (isOpen_Ioi.mem_nhds hz)

theorem continuousOn_RIter (Λ : ℝ → ℝ) (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0))
    (j : ℕ) : ContinuousOn (RIter j Λ) (Set.Ioi 0) :=
  (contDiffOn_RIter Λ hΛ j 0).continuousOn

theorem continuousOn_w : ContinuousOn Work.Spaces.w (Set.Ioi 0) := by
  show ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · exact continuousOn_id.pow 2
  · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)

/-! ### The iterates of `D_z` on a `θ`-dependent product -/

/-- On the open half-line, `D_z^j` of the *radial* function `(z,θ) ↦ Λ z` is the one-variable
iterate `RIter j Λ` (evaluated at `z`), independently of `θ`. -/
theorem DzIter_radial (Λ : ℝ → ℝ) (j : ℕ) :
    ∀ {z : ℝ}, 0 < z → ∀ θ : ℝ,
      Work.Spaces.DzIter j (fun z θ => Λ z) z θ = RIter j Λ z := by
  induction j with
  | zero => intro z hz θ; rfl
  | succ j ih =>
    intro z hz θ
    have hev : (fun z' => Work.Spaces.DzIter j (fun z θ => Λ z) z' θ)
        =ᶠ[𝓝 z] RIter j Λ := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact ih hz' θ
    have hder : deriv (fun z' => Work.Spaces.DzIter j (fun z θ => Λ z) z' θ) z
        = deriv (RIter j Λ) z := hev.deriv_eq
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    rw [hder, RIter_succ_apply]

/-- On the open half-line, `D_z^j` of a function of the form `(z,θ) ↦ Λ z · B θ` is
`(RIter j Λ z) · B θ`: `D_z` only sees the `z`-dependence. -/
theorem DzIter_mul_theta (Λ : ℝ → ℝ) (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0))
    (B : ℝ → ℝ) (j : ℕ) :
    ∀ {z : ℝ}, 0 < z → ∀ θ : ℝ,
      Work.Spaces.DzIter j (fun z θ => Λ z * B θ) z θ = RIter j Λ z * B θ := by
  induction j with
  | zero => intro z hz θ; rfl
  | succ j ih =>
    intro z hz θ
    have hev : (fun z' => Work.Spaces.DzIter j (fun z θ => Λ z * B θ) z' θ)
        =ᶠ[𝓝 z] (fun z' => RIter j Λ z' * B θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact ih hz' θ
    have hder : deriv (fun z' => Work.Spaces.DzIter j (fun z θ => Λ z * B θ) z' θ) z
        = deriv (fun z' => RIter j Λ z' * B θ) z := hev.deriv_eq
    have hdm : deriv (fun z' => RIter j Λ z' * B θ) z = deriv (RIter j Λ) z * B θ :=
      deriv_mul_const (differentiableAt_RIter Λ hΛ j hz) (B θ)
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, hder, hdm,
      RIter_succ_apply]
    ring

end Radial

end Work.FTS.EllSol.PkgK5
