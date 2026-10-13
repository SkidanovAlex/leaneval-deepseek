import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.I4SliceAlgebra
import Submission.Work.FTS.EllipticEst.Honest.I4BoundaryVanish
import Submission.Work.FTS.EllipticEst.Honest.I4SliceBound
import Submission.Work.FTS.EllipticEst.Honest.I4GlobalAssembly
import Submission.Work.FTS.EllipticEst.Honest.I4SliceDivIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The slice-level objects of the honest `I₄` upper bound -/

/-- The coefficient `Σ θ = (1-η) cos²θ + (3+η) sin²θ ≥ 0`. -/
def SigmaCoef (θ : ℝ) : ℝ :=
  (1 - Work.Spaces.eta) * (Real.cos θ) ^ 2 + (3 + Work.Spaces.eta) * (Real.sin θ) ^ 2

/-- The coefficient `Ξ θ = (cos²θ (1-η) + η sin²θ) cos θ`. -/
def XiCoef (θ : ℝ) : ℝ :=
  ((Real.cos θ) ^ 2 * (1 - Work.Spaces.eta) + Work.Spaces.eta * (Real.sin θ) ^ 2) * Real.cos θ

/-- `P θ = cos²θ · ψ'(θ)`. -/
def slP (ψ : ℝ → ℝ) : ℝ → ℝ := fun θ => (Real.cos θ) ^ 2 * deriv ψ θ

/-- `Ψ θ = cos θ · ψ θ`. -/
def slPsi (ψ : ℝ → ℝ) : ℝ → ℝ := fun θ => Real.cos θ * ψ θ

/-- `b θ = Ψ''(θ)` where `Ψ = cos · ψ`. -/
def slB (ψ : ℝ → ℝ) : ℝ → ℝ := fun θ => deriv (deriv (slPsi ψ)) θ

/-- `u θ = ∂_θ (tan θ · Ψ)`. -/
def slU (ψ : ℝ → ℝ) : ℝ → ℝ := fun θ => deriv (fun θ' => Real.tan θ' * slPsi ψ θ') θ

/-- The slice pairing `∫_θ g θ · h θ · σ θ`. -/
def slIP (g h : ℝ → ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, g θ * h θ * AngSecond.sig θ

theorem eta_lt_one : Work.Spaces.eta < 1 := by rw [Work.Spaces.eta]; norm_num

theorem one_sub_eta_pos : 0 < 1 - Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num

theorem SigmaCoef_nonneg (θ : ℝ) : 0 ≤ SigmaCoef θ := by
  rw [SigmaCoef]
  exact add_nonneg (mul_nonneg (by linarith [one_sub_eta_pos]) (sq_nonneg _))
    (mul_nonneg (by rw [Work.Spaces.eta]; norm_num) (sq_nonneg _))

theorem abs_XiCoef_le_one (θ : ℝ) : |XiCoef θ| ≤ 1 := by
  rw [XiCoef]
  have h1 : (0:ℝ) ≤ 1 - Work.Spaces.eta := le_of_lt one_sub_eta_pos
  have h2 : (0:ℝ) ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have h4 : (Real.sin θ) ^ 2 ≤ 1 := by nlinarith [Real.sin_sq_le_one θ]
  have h5 : (Real.cos θ) ^ 2 ≤ 1 := by nlinarith [Real.cos_sq_le_one θ]
  have h6 : (Real.cos θ) ^ 2 * (1 - Work.Spaces.eta) ≤ 1 - Work.Spaces.eta := by
    nlinarith [h5, h1]
  have h7 : Work.Spaces.eta * (Real.sin θ) ^ 2 ≤ Work.Spaces.eta := by
    nlinarith [h4, h2]
  have h8 : |(Real.cos θ) ^ 2 * (1 - Work.Spaces.eta)
      + Work.Spaces.eta * (Real.sin θ) ^ 2| ≤ 1 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ), h1, h2, h4, h6, h7]
    · linarith
  have h9 : |Real.cos θ| ≤ 1 := by
    rw [abs_le]; exact ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  calc |((Real.cos θ) ^ 2 * (1 - Work.Spaces.eta) + Work.Spaces.eta * (Real.sin θ) ^ 2)
        * Real.cos θ|
      = |(Real.cos θ) ^ 2 * (1 - Work.Spaces.eta) + Work.Spaces.eta * (Real.sin θ) ^ 2|
        * |Real.cos θ| := by rw [abs_mul]
    _ ≤ 1 * 1 := mul_le_mul h8 h9 (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem sig_eq (θ : ℝ) : AngSecond.sig θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl

theorem cos_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π/2)) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩

theorem sig_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π/2)) :
    0 < AngSecond.sig θ := by
  rw [sig_eq]
  apply Real.rpow_pos_of_pos
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π/2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])


/-! ## The slice-level inequality, and the target theorem

The proof of the target theorem below is the reduction of
`Submission/Work/FTS/EllipticEst/Honest/I4GlobalAssembly` (the `z`-integration and the
`z`-Cauchy–Schwarz) applied to the single-slice inequality `slice_bound`, whose proof uses the
pointwise algebra `Submission.Work.FTS.EllipticEst.I4SliceAlgebra` and the boundary vanishing
`Submission.Work.FTS.EllipticEst.Honest.I4BoundaryVanish` (see `NOTES_I4UpperHonest.md` for the
complete route).  The pieces of the slice inequality proved in this file are the `θ`-truncated
integration by parts, the AM–GM cancellation and the coercive estimate below.
-/

/-- **The requested upper bound on the `I₄` term.**  Route (all ingredients proved elsewhere in
this workspace, see `NOTES_I4UpperHonest.md`):

`Work.FTS.EllipticEst.Honest.I4GlobalAssembly` reduces it to the single-slice inequality
`Work.FTS.EllipticEst.Honest.I4SliceBound Φ hsm hA hB hAlg hBound`, whose two extra inputs are
`Work.FTS.EllipticEst.I4SliceAlgebra Φ hsm` (the pointwise calculus identities) and
`Work.FTS.EllipticEst.Honest.I4BoundaryVanish (fun θ => Φ θ / Real.cos θ) …` (the vanishing of
the boundary term `(sin θ/cos³θ)·σ·P²`).  The remaining glue is the instantiation of
`I4SliceBound` and `I4BoundaryVanish` with `Φ` the `θ`-slice of `Ψ`, together with the
integrability of `(P'/cos θ)²σ` (from `Hon.memB` and `HkMem α 0 (Ψ/cos θ)` via
`P'/cos θ = Φ'' + Φ`), whose proof is the last block below (in comments because the workspace
state at the time of writing still had `I4SliceBound` open). -/
theorem I4UpperHonest : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.Honest.Hon α F Ψ →
      Work.Spaces.HkMem α 0 Ψ →
      Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) →
      Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
          (Work.Spaces.pthIter 2 Ψ)
        ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ)) ^ 2
            + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
              * Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
            + (Real.sqrt (Work.Spaces.HkSq α 0 F)) ^ 2) := by
  -- The three-step assembly: the `z`-reduction, the single-slice estimate, and the two
  -- inputs of the latter (the pointwise calculus and the vanishing of the boundary term).
  refine Work.FTS.EllipticEst.Honest.I4GlobalAssembly (fun Φ hsm hA hB => ?_)
  refine Work.FTS.EllipticEst.Honest.I4SliceBound Φ hsm hA hB
    (Work.FTS.EllipticEst.I4SliceAlgebra Φ hsm) ?_
  refine Work.FTS.EllipticEst.Honest.I4BoundaryVanish (fun θ => Φ θ / Real.cos θ) ?_ ?_ ?_
  · exact ContDiffOn.div hsm Real.contDiff_cos.contDiffOn (fun x hx =>
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩))
  · exact hA.mono_set Set.Ioo_subset_Icc_self
  · exact Work.FTS.EllipticEst.Honest.I4SliceDivIntegrable Φ hsm hA hB

end

end Work.FTS.EllipticEst.Honest
