import Mathlib
import Submission.Work.Mostow.flatActBasic
import Submission.Work.Mostow.finite_nearStab

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-- A `ξ`-stabilising element of level one whose flat displacement is at most `T` displaces the base
point `0` by at most `arccosh (1 + T²/2)`. -/
theorem hdist_zero_le_of_flatAct_le {n : ℕ} {ξ : E n} (hξ : ξ ∈ Sph n) {g : PO n 1}
    (h0 : lev ξ (g • (0 : E n)) = 1) {T : ℝ}
    (hT : ‖flatAct ξ g (0 : E n)‖ ≤ T) :
    hdist (0 : E n) (g • (0 : E n)) ≤ Real.arcosh (1 + T ^ 2 / 2) := by
  have h1 : hdist (0 : E n) (g • (0 : E n))
      = Real.arcosh (1 + ‖flatAct ξ g (0 : E n)‖ ^ 2 / 2) := by
    rw [hdist_zero_eq_yc (u := g • (0 : E n)) hξ h0, ← flatAct_zero_eq_yc hξ (g := g)]
  rw [h1]
  refine (Real.arcosh_le_arcosh (by positivity) (by positivity)).mpr ?_
  have h2 : ‖flatAct ξ g (0 : E n)‖ ^ 2 ≤ T ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hT 2
  linarith

theorem flatActNearStab {n : ℕ} (hA : Work.Mostow.POBasic n) (hI : Work.Mostow.HypIsoData n)
    {Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)} {ξ : Submission.Mostow.E n}
    (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hdisc : IsDiscrete (SetLike.coe Γ))
    (hlev : ∀ γ : Γ,
      Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.lev ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)
        • (0 : Submission.Mostow.E n)) = 1)
    (T : ℝ) :
    {γ : Γ | Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
      ‖Work.Mostow.flatAct ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1))
        (0 : Submission.Mostow.E n)‖ ≤ T}.Finite := by
  refine (finite_nearStab hA hI hdisc (Real.arcosh (1 + T ^ 2 / 2))).subset ?_
  intro γ hγ
  exact hdist_zero_le_of_flatAct_le hξ (hlev γ hγ.1) hγ.2

end Work.Mostow
