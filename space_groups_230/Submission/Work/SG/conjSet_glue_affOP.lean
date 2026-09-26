import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.affEquiv_facts
import Submission.Work.SG.sgSet_basic

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

/-- The conjugation of a set of affine maps by `φ` (both orders of `φ` and `φ⁻¹`), phrased with
the `AffFacts.conjAct` name so that the group-action lemmas apply. -/
private lemma conjSet_eq_conjAct (φ : AffineGroup 3) (S : Set (AffineGroup 3)) :
    conjSet φ S = AffFacts.conjAct φ S := rfl

/-- Gluing conjugacies to lattice-normalised data: if `ψ` carries the affine image of `G` onto the
normal form `sgSet P τ`, `ψ'` carries that of `G'` onto `sgSet P' τ'`, and `θ` (of positive
determinant) carries `sgSet P τ` onto `sgSet P' τ'`, then `G` and `G'` are orientation-preserving
affinely equivalent, via `ψ'⁻¹ * θ * ψ` (whose determinant is positive). -/
theorem conjSet_glue_affOP {G G' : Subgroup (EuclideanIsom 3)}
    {P P' : Set IMat} {τ τ' : IMat → Fin 3 → ℝ} {ψ ψ' θ : AffineGroup 3}
    (hψ : conjSet ψ (affImage G) = sgSet P τ)
    (hψ' : conjSet ψ' (affImage G') = sgSet P' τ')
    (hθ : conjSet θ (sgSet P τ) = sgSet P' τ')
    (hψpos : 0 < (ψ.linear.det : ℝ)) (hψ'pos : 0 < (ψ'.linear.det : ℝ))
    (hθpos : 0 < (θ.linear.det : ℝ)) :
    AffOPEquivalent G G' := by
  have hψc : AffFacts.conjAct ψ (AffFacts.affImage G) = sgSet P τ := hψ
  have hψ'c : AffFacts.conjAct ψ' (AffFacts.affImage G') = sgSet P' τ' := hψ'
  have hθc : AffFacts.conjAct θ (sgSet P τ) = sgSet P' τ' := hθ
  have hinv : ∀ (φ : AffineGroup 3) (S : Set (AffineGroup 3)),
      AffFacts.conjAct φ⁻¹ (AffFacts.conjAct φ S) = S :=
    fun φ S => (sgSet_basic).2.2.1 φ S
  have hcomp := (conjAct_action 3).2
  refine ⟨ψ'⁻¹ * θ * ψ, ?_, ?_⟩
  · rw [AffFacts.det_mul, AffFacts.det_mul, AffFacts.det_inv]
    exact mul_pos (mul_pos (inv_pos.mpr hψ'pos) hθpos) hψpos
  · have key : AffFacts.conjAct (ψ'⁻¹ * θ * ψ) (AffFacts.affImage G) = AffFacts.affImage G' := by
      have h1 : AffFacts.conjAct (ψ'⁻¹ * θ * ψ) (AffFacts.affImage G)
          = AffFacts.conjAct ψ'⁻¹
              (AffFacts.conjAct θ (AffFacts.conjAct ψ (AffFacts.affImage G))) := by
        rw [mul_assoc, hcomp, hcomp]
      rw [h1, hψc, hθc, ← hψ'c, hinv]
    rw [← conjAct_affImage_eq 3 (ψ'⁻¹ * θ * ψ) G]
    exact key

end Work.SG
