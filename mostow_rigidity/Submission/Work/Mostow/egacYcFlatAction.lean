import Mathlib
import Submission.Work.Mostow.stabFlatActionCanon
import Submission.Work.Mostow.horoSpec
import Submission.Work.Mostow.hptOf_yc

/-!
# The flat action of an element fixing a boundary point and all horosphere levels

If `γ : PO n 1` fixes `ξ ∈ Sph n` on the boundary and does not move the horosphere levels at `ξ`
(`lev ξ (γ • u) = lev ξ u` for every `u`), then `γ` preserves every horosphere of `ξ` and acts on
the flat coordinate `yc ξ ·` of every one of them by the *canonical* affine map
`y ↦ flatLin ξ (LambdaMat γ) y + flatTrans ξ (LambdaMat γ)`.

This is `Work.Mostow.stabFlatActionCanon` with its hypothesis
`busemann ξ (γ • 0) = 0` deduced from the level hypothesis: `busemann ξ u = log (lev ξ u)`,
`lev ξ 0 = 1`, and `lev ξ (γ • 0) = lev ξ 0 = 1` by the hypothesis at `u = 0`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-- The normalised flat coordinate at `ξ` lies in the hyperplane `ξ^⊥`. -/
private lemma egac_inner_yc {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) :
    inner ℝ (yc ξ u) ξ = 0 := by
  have hξ1 : inner ℝ ξ ξ = (1 : ℝ) := inner_self_of_mem_Sph hξ
  have hw : inner ℝ (wc ξ u) ξ = 0 := by
    rw [wc, inner_sub_left, real_inner_smul_left, hξ1, mul_one, sub_self]
  rw [yc, real_inner_smul_left, hw, mul_zero]

theorem egacYcFlatAction (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) {ξ : Submission.Mostow.E n}
    (hξ : ξ ∈ Submission.Mostow.Sph n) {γ : LeanEval.Geometry.MostowRigidity.PO n 1}
    (hγbd : Submission.Mostow.bd γ ξ = ξ)
    (hlev : ∀ u : Submission.Mostow.E n, Work.Mostow.lev ξ (γ • u) = Work.Mostow.lev ξ u) :
    ∀ u : Submission.Mostow.E n, Work.Mostow.yc ξ (γ • u) =
      Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat γ) (Work.Mostow.yc ξ u)
        + Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat γ) := by
  -- the level hypothesis at `u = 0` says `lev ξ (γ • 0) = 1`, hence the Busemann cocycle vanishes
  have hβ : busemann ξ (γ • (0 : E n)) = 0 := by
    have h := hlev (0 : E n)
    have h0 : lev ξ (0 : E n) = (1 : ℝ) := by simp [lev, tpart]
    rw [h0] at h
    have hlog : busemann ξ (γ • (0 : E n)) = Real.log (lev ξ (γ • (0 : E n))) := rfl
    rw [hlog, h, Real.log_one]
  obtain ⟨-, -, -, hmain⟩ := stabFlatActionCanon n hA hI ξ hξ γ hγbd hβ
  intro u
  have h := hmain (yc ξ u) (lev ξ u) (egac_inner_yc hξ u) (lev_pos ξ hξ u)
  rw [hptOf_yc_lev hξ u] at h
  exact h.2

end

end Work.Mostow
