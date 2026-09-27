import Mathlib
import Submission.Work.Mostow.cuspHoroDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.horSpec
import Submission.Work.Mostow.flatActBasic
import Submission.Work.Mostow.stabFlatAction

namespace Work.Mostow.cuspHoro

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-- The pointwise form of the flat action: for `γ` fixing `ξ` and preserving the levels `lev ξ ·`,
the normalised flat coordinate `yc ξ (γ • u)` at *any* horospherical level is given by the same
affine map of `ξ^⊥` as at level one, namely `flatAct ξ γ`. -/
theorem yc_smul_eq_flatAct {n : ℕ} (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (ξ : Submission.Mostow.E n)
    (hξ : ξ ∈ Submission.Mostow.Sph n) (γ : LeanEval.Geometry.MostowRigidity.PO n 1)
    (hγ : Submission.Mostow.bd γ ξ = ξ)
    (hlev : ∀ u : Submission.Mostow.E n, Work.Mostow.lev ξ (γ • u) = Work.Mostow.lev ξ u)
    (u : Submission.Mostow.E n) :
    Work.Mostow.yc ξ (γ • u) = Work.Mostow.flatAct ξ γ (Work.Mostow.yc ξ u) := by
  have hzero : Work.Mostow.lev ξ (0 : Submission.Mostow.E n) = 1 := by
    simp [Work.Mostow.lev, Submission.Mostow.tpart]
  have hβ : Submission.Mostow.busemann ξ (γ • (0 : Submission.Mostow.E n)) = 0 := by
    have h1 : Work.Mostow.lev ξ (γ • (0 : Submission.Mostow.E n)) = 1 := by
      rw [hlev (0 : Submission.Mostow.E n)]; exact hzero
    have h3 : Real.log (Work.Mostow.lev ξ (γ • (0 : Submission.Mostow.E n))) = 0 := by
      rw [h1, Real.log_one]
    rwa [Work.Mostow.lev_eq_exp hξ, Real.log_exp] at h3
  obtain ⟨A, v, hv, hAperp, hAnorm, hpt⟩ :=
    Work.Mostow.stabFlatAction n hA hI ξ hξ γ hγ hβ
  have hfa : ∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 →
      Work.Mostow.flatAct ξ γ y = A y + v := by
    intro y hy
    rw [Work.Mostow.flatAct, Work.Mostow.horoPt_eq_hptOf]
    exact (hpt y 1 hy one_pos).2
  have hD : 0 < Work.Mostow.lev ξ u := Work.Mostow.lev_pos ξ hξ u
  have hy : inner ℝ (Work.Mostow.yc ξ u) ξ = 0 := Work.Mostow.yc_inner_orth hξ
  have hu : Work.Mostow.hptOf ξ (Work.Mostow.yc ξ u) (Work.Mostow.lev ξ u) = u :=
    Work.Mostow.hptOf_yc ξ hξ (Work.Mostow.lev ξ u) hD u rfl
  have h1 : Work.Mostow.yc ξ (γ • u) = A (Work.Mostow.yc ξ u) + v := by
    have h := (hpt (Work.Mostow.yc ξ u) (Work.Mostow.lev ξ u) hy hD).2
    rwa [hu] at h
  have h2 : Work.Mostow.flatAct ξ γ (Work.Mostow.yc ξ u) = A (Work.Mostow.yc ξ u) + v :=
    hfa (Work.Mostow.yc ξ u) hy
  rw [h1, h2]

theorem flatDispEqLevOne {n : ℕ} (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n) (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (γ : Γ) (hγ : Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ) (hlev : ∀ u : Submission.Mostow.E n, Work.Mostow.lev ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) = Work.Mostow.lev ξ u) : Work.Mostow.flatDisp ξ (γ : LeanEval.Geometry.MostowRigidity.PO n 1) = sInf {r : ℝ | ∃ y : Submission.Mostow.E n, inner ℝ y ξ = 0 ∧ r = ‖y - Work.Mostow.flatAct ξ (γ : LeanEval.Geometry.MostowRigidity.PO n 1) y‖} := by
  have hkey : ∀ u : Submission.Mostow.E n,
      Work.Mostow.yc ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u)
        = Work.Mostow.flatAct ξ (γ : LeanEval.Geometry.MostowRigidity.PO n 1)
            (Work.Mostow.yc ξ u) :=
    fun u => yc_smul_eq_flatAct hA hI ξ hξ (γ : LeanEval.Geometry.MostowRigidity.PO n 1) hγ hlev u
  have hfa1 : ∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 →
      Work.Mostow.flatAct ξ (γ : LeanEval.Geometry.MostowRigidity.PO n 1) y
        = Work.Mostow.yc ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1)
            • Work.Mostow.horoPt ξ y) := fun y _ => rfl
  have hset : Set.range (fun u : Submission.Mostow.E n =>
        ‖Work.Mostow.yc ξ u - Work.Mostow.yc ξ
          ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u)‖)
      = {r : ℝ | ∃ y : Submission.Mostow.E n, inner ℝ y ξ = 0 ∧
          r = ‖y - Work.Mostow.flatAct ξ (γ : LeanEval.Geometry.MostowRigidity.PO n 1) y‖} := by
    ext r
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨Work.Mostow.yc ξ u, Work.Mostow.yc_inner_orth hξ, ?_⟩
      show ‖Work.Mostow.yc ξ u - Work.Mostow.yc ξ
            ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u)‖
          = ‖Work.Mostow.yc ξ u - Work.Mostow.flatAct ξ
              (γ : LeanEval.Geometry.MostowRigidity.PO n 1) (Work.Mostow.yc ξ u)‖
      rw [hkey u]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨Work.Mostow.horoPt ξ y, ?_⟩
      show ‖Work.Mostow.yc ξ (Work.Mostow.horoPt ξ y) - Work.Mostow.yc ξ
              ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.horoPt ξ y)‖
          = ‖y - Work.Mostow.flatAct ξ (γ : LeanEval.Geometry.MostowRigidity.PO n 1) y‖
      rw [Work.Mostow.yc_horoPt hξ y hy, hfa1 y hy]
  rw [Work.Mostow.flatDisp, Work.Mostow.flatDispSet, hset]

end Work.Mostow.cuspHoro
