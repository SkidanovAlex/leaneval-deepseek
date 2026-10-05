import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPV.VBasic

/-!
# B5: injectivity of the collar level parametrisation modulo `2π`

The collar point at level `σ ≥ 0` is `levelPt (Γc τ σ t) σ (Ac τ σ t)`.  The invariant `K₀` of
the `K₀`-flow and of the `2π`-shift `Tk` reads `-1-σ` there, so the level is determined by the
point; the reduced coordinate `uproj` reads `Γc τ σ t` there and is also invariant under `Tk`,
so the parameter is determined mod `2π` by the injectivity of the level curve `Γc τ σ ·`.

Both invariants are the content of `Work.RPV.VBasic`; the geometric input is the `hemb` field of
`Work.RPB.B5.LagData`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

theorem collar_levelPt_inj (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ σ' t t' : ℝ, 0 ≤ σ → 0 ≤ σ' → ∀ k : ℤ,
      Work.RPV.levelPt (D.Γc τ σ' t') σ' (D.Ac τ σ' t')
        = Work.RPV.Tk k (Work.RPV.levelPt (D.Γc τ σ t) σ (D.Ac τ σ t)) →
      σ = σ' ∧ ∃ m : ℤ, t' = t + 2 * Real.pi * m := by
  intro τ hτ σ σ' t t' hσ hσ' k h
  -- `K₀` is invariant under `Tk` and equals `-1-σ` on the level `σ`: hence `σ = σ'`.
  have hK : Work.RPV.K0 (Work.RPV.levelPt (D.Γc τ σ' t') σ' (D.Ac τ σ' t'))
      = Work.RPV.K0 (Work.RPV.Tk k (Work.RPV.levelPt (D.Γc τ σ t) σ (D.Ac τ σ t))) := by
    rw [h]
  rw [Work.RPV.K0_levelPt, Work.RPV.K0_Tk, Work.RPV.K0_levelPt] at hK
  have hσσ : σ = σ' := by linarith
  -- `uproj` is invariant under `Tk` and equals the reduced coordinate on the level: hence the
  -- reduced coordinates of the two collar points agree.
  have hu : D.Γc τ σ t = D.Γc τ σ t' := by
    have h1 := congrArg Work.RPV.uproj h
    rw [Work.RPV.uproj_levelPt, Work.RPV.uproj_Tk, Work.RPV.uproj_levelPt] at h1
    rw [← hσσ] at h1
    exact h1.symm
  -- the embedded level curve is injective modulo `2π`
  obtain ⟨-, hinj⟩ := D.hemb τ hτ σ hσ
  obtain ⟨m, hm⟩ := hinj t t' hu
  exact ⟨hσσ, m, hm⟩

end Work.RPB.B5
