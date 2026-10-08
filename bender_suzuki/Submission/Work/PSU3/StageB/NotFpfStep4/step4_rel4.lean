import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageB.ThetaOmegaAux
import Submission.Work.PSU3.StageB.NotFpfStep4.etaAction_semilinear
import Submission.Work.PSU3.StageB.NotFpfStep4.bar_fcan_step4_3
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_rel4_aux
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_rel4_left
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_rel4_right

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep4

/-- Arithmetic endgame of relation (4): multiplying the relation
`q·(c⁻¹·Y) = (c²)⁻¹·Z + c⁻¹·W` (with `c ≠ 0`) by `c` gives `q·Y = c⁻¹·Z + W`. -/
lemma field_arith {K : Type} [Field K] (c q Y Z W : K) (hc : c ≠ 0)
    (h : q * (c⁻¹ * Y) = (c^2)⁻¹ * Z + c⁻¹ * W) : q * Y = c⁻¹ * Z + W := by
  have h1 : c * (q * (c⁻¹ * Y)) = q * Y := by
    field_simp
  have h2 : c * ((c^2)⁻¹ * Z + c⁻¹ * W) = c⁻¹ * Z + W := by
    field_simp
  have h3 := congrArg (fun t => c * t) h
  rw [h1, h2] at h3
  exact h3

theorem step4_rel4 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω * Work.PSU3.StageB.zcQF fr α))
    (hsq : ω * ω = Work.PSU3.StageB.zcQF fr α)
    {η : G} (hηV : η ∈ Submission.Blueprint.centD H t)
    (hh : (Work.PSU3.StageB.hcan hS.split ω : G) = (fr.ζ : G) ^ 3 * η⁻¹)
    (hcentζ : η * (fr.ζ : G) = (fr.ζ : G) * η)
    (hηN : ∀ d : fr.KW, ∃ e : fr.KW, (e : G) = η⁻¹ * (d : G) * η)
    (hη1 : ∃ s : ↥Q, (s : G) ∉ fr.Q0 ∧ Multiplicative.toAdd (fr.bar s) = 1 ∧
      ((Work.PSU3.StageB.qconj hS.split
          (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ :
            ↥(Submission.Blueprint.twoPoint H t)) s * s⁻¹ : ↥Q) : G) ∈ fr.Q0)
    (a : ↥(Work.PSU3.StageB.FX n)) :
    (Work.PSU3.StageB.fval a) ^ 2 *
        Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
          (ω * Work.PSU3.StageB.sconjF fr a))) =
      ((fr.κ fr.ζ : Work.PSU3.E n))⁻¹ *
        Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.qconj hS.split
          (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ :
            ↥(Submission.Blueprint.twoPoint H t))
          (Work.PSU3.StageB.fcan hS.split (ω * Work.PSU3.StageB.sconjF fr a))))
      + Multiplicative.toAdd (fr.bar ω) := by
  have hL := step4_rel4_left hS fr hω hf hsq a
  have hR := step4_rel4_right hS fr hω hf hsq hηV hh hcentζ a
  exact field_arith (fr.κ fr.ζ : Work.PSU3.E n) ((Work.PSU3.StageB.fval a) ^ 2)
    (Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
      (ω * Work.PSU3.StageB.sconjF fr a))))
    (Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.qconj hS.split
      (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ :
        ↥(Submission.Blueprint.twoPoint H t))
      (Work.PSU3.StageB.fcan hS.split (ω * Work.PSU3.StageB.sconjF fr a)))))
    (Multiplicative.toAdd (fr.bar ω)) (Units.ne_zero _) (hL.symm.trans hR)

end Work.PSU3.StageB.NotFpfStep4
