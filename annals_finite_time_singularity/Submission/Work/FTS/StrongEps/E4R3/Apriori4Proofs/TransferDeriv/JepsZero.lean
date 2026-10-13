import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

/-! ## The degenerate values of the `ε`-scheme

These are the boundary cases in which a quantity of the transfer estimate is *identically* zero:
the mollifier at scale `ε = 0` (where the rescaled kernel `Jker` collapses, since `(0:ℝ)⁻¹ = 0`),
the projected zero profile, and the `ℋ⁴`/`ℋ⁶`-sizes of the zero profile.  They are used to
discharge the degenerate branches of the transfer/defect estimates (the `ε → 0` and `g ≡ 0`
cases). -/

/-- The `L₁₂`-operator of the fundamental model vanishes on the zero profile.  (This is the
`L₁₂(0)(0) = 0` instance; it is proved here by unfolding, so that this module needs no import of
the Galerkin vocabulary.) -/
theorem l12_zero : Work.Construction.L12 (0 : Work.FTS.Galerkin.Fn) 0 = 0 := by
  simp [Work.Construction.L12, Work.FM.L12, Work.FM.L12dens]

/-- The kernel of `Jeps` at scale `ε = 0` vanishes identically, because `(0:ℝ)⁻¹ = 0`. -/
theorem jker_zero (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    Work.FTS.StrongEps.Jker ρ 0 p = 0 := by
  simp [Work.FTS.StrongEps.Jker]

theorem JepsZero (ρ : ℝ × ℝ → ℝ) (f : Work.FTS.Galerkin.Fn) :
    Work.FTS.StrongEps.Jeps ρ 0 f = 0 ∧ Work.FTS.StrongEps.Pz (0 : Work.FTS.Galerkin.Fn) = 0 ∧
      (∀ α : ℝ, Work.Spaces.HkNorm α 4 (0 : Work.FTS.Galerkin.Fn) = 0) ∧
      (∀ α : ℝ, Work.FTS.StrongGlobal.Xn6 α (0 : Work.FTS.Galerkin.Fn) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `ε = 0`: the integrand of `Jeps` is `0 · ρ (0 • p) · ·  = 0`.
    funext z θ
    simp only [Work.FTS.StrongEps.Jeps]
    split <;> simp
  · -- `Pz` subtracts a multiple of `bump`; on the zero profile the multiple is `0`.
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply]
    simp only [Pi.zero_apply, l12_zero, zero_div, zero_mul, sub_zero]
  · intro α
    exact Work.FTS.EllipticEst.HkNorm_zero α 4
  · intro α
    exact Work.FTS.EllipticEst.HkNorm_zero α 6

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
