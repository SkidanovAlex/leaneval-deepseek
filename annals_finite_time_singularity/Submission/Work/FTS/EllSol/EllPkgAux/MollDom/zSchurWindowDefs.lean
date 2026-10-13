/-
# `zSchurWindowDefs` — vocabulary for the window estimate `zSchur_pth_window`

The target `Work.FTS.EllSol.EllPkgAux.MollDom.zSchur_pth_window` bounds the weighted `L²`-norm

  `∫_{Iθ} σ_η(s) · (zSchur δ (fun w => ∂_θG(w,s)) z)²`

of the logarithmic Schur transform of the angular derivative of a trace-class datum by the
*windowed* slice energy

  `∫_t 1_{|log z - t| ≤ δ} · (∫_{Iθ} σ_η(s) (∂_θG(e^t,s))²)`.

The proof has two analytic inputs, both packaged here:

* the pointwise majorant `thSliceMajorant G z` for the angular derivative of the slice
  `s ↦ G z s` (valid for every `s ∈ (0, π/2)`, from the fundamental theorem of calculus
  between `s` and the landmark angle `π/4`), and
* the boundedness/support of the kernel `sKerd δ = deriv (sKer δ)` (`exists_sKerd_bound`).

The two analytic lemmas about `thSliceMajorant` live in the sibling modules
`pth_slice_sq_le_majorant` and `win_majorant_integrable`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_deriv_le
import Submission.Work.FTS.EllSol.PkgK5.i0TraceMoll.AuxDz.sKerd_eq_zero_of_le_abs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option autoImplicit false

/-! ## The angular weight `σ_η` at the two endpoints -/

theorem thEta_zero : Work.FTS.EllipticEst.thEta 0 = 0 := by
  rw [Work.FTS.EllipticEst.thEta, show (2 : ℝ) * 0 = 0 by norm_num, Real.sin_zero]
  exact Real.zero_rpow (by norm_num [Work.Spaces.eta])

theorem thEta_pi_half : Work.FTS.EllipticEst.thEta (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.thEta, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  exact Real.zero_rpow (by norm_num [Work.Spaces.eta])

theorem measurable_thEta : Measurable Work.FTS.EllipticEst.thEta :=
  Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id))
    (-(Work.Spaces.eta))

/-! ## The pointwise majorant of the angular derivative of a slice -/

/-- **The pointwise majorant of `∂_θG(z, ·)`.**  For a trace-class datum `G` and `z > 0`, the
angular derivative of the slice satisfies

  `|∂_θG(z,s)| ≤ |∂_θG(z,π/4)| + √(∫_{Iθ} (∂_θ²G(z,θ))² σ_η θ) · √(π/4)`

for every `s ∈ (0, π/2)` (fundamental theorem of calculus from the landmark angle `π/4`
together with the interval Cauchy–Schwarz bound); `thSliceMajorant G z` is the square of that
bound.  The proofs are `pth_slice_sq_le_majorant` (the pointwise bound) and
`win_majorant_integrable` (its integrability along the logarithmic window). -/
def thSliceMajorant (G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (|Work.Spaces.pth G z (Real.pi / 4)|
    + Real.sqrt (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      * Real.sqrt (Real.pi / 4)) ^ 2

theorem thSliceMajorant_nonneg (G : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ thSliceMajorant G z :=
  sq_nonneg _

/-! ## The kernel `sKerd δ` is bounded and supported in `[-δ, δ]` -/

/-- **Bound and support of the derivative kernel.**  For `δ > 0` the continuous kernel
`sKerd δ = deriv (sKer δ)` (whose support is contained in `(-δ, δ)`) is bounded on all of `ℝ`
by some `M ≥ 0`. -/
theorem exists_sKerd_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ u : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd δ u| ≤ M) ∧
      (∀ u : ℝ, δ < |u| → Work.FTS.EllSol.EllPkgAux.sKerd δ u = 0) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -δ) (b := δ)).exists_bound_of_continuousOn
    (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd δ).continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_, ?_⟩
  · intro u
    by_cases hu : u ∈ Set.Icc (-δ) δ
    · have h := hC u hu
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_max_left _ _)
    · have hlt : δ < |u| := by
        rw [Set.mem_Icc, not_and_or] at hu
        rcases hu with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have hz : Work.FTS.EllSol.EllPkgAux.sKerd δ u = 0 :=
        Work.FTS.EllSol.PkgK5.i0TraceMoll.AuxDz.sKerd_eq_zero_of_le_abs hδ (le_of_lt hlt)
      rw [hz, abs_zero]
      exact le_max_right _ _
  · intro u hu
    exact Work.FTS.EllSol.PkgK5.i0TraceMoll.AuxDz.sKerd_eq_zero_of_le_abs hδ (le_of_lt hu)

end Work.FTS.EllSol.EllPkgAux.MollDom
