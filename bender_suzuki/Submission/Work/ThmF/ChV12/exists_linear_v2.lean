import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.chi_on_D
import Submission.Work.ThmF.ChV12.exists_phi_of_chi
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem exists_linear_v2 {G : Type} [Group G] [Fintype G] (hFT : FeitThompsonProp) (H Q : Subgroup G) (t : G) (hS : Situation G) (h : IsSplitRankOne H Q t) (hV : centD H t ≠ ⊥) (hKcyc : IsCyclic ↥(Ksub H t)) (hKset : (Ksub H t : Set G) = Kset H t) : ∃ lam : H → ℂ, lam ∈ Work.CharCore.Irr H ∧ lam 1 = 1 ∧ lam ≠ (fun _ : H => (1 : ℂ)) ∧ (∀ x : H, (x : G) ∈ Q → lam x = 1) ∧ (∀ x : H, (x : G) ∈ Kset H t → lam x = 1) := by
  classical
  obtain ⟨χ, hχne, hχK⟩ := chi_on_D hFT h hV hKset
  obtain ⟨φ, hφne, hφQ, hφK⟩ := exists_phi_of_chi h χ hχne hχK
  obtain ⟨lam, hlam, hlamval⟩ := Work.CharCore.exists_irr_of_monoidHom φ
  refine ⟨lam, hlam, ?_, ?_, ?_, ?_⟩
  · rw [hlamval 1]; simp
  · intro hcon
    apply hφne
    apply MonoidHom.ext
    intro x
    apply Units.ext
    change ((φ x : ℂˣ) : ℂ) = ((1 : ℂˣ) : ℂ)
    rw [← hlamval x]
    simp [hcon]
  · intro x hx
    rw [hlamval x, hφQ x hx]; simp
  · intro x hx
    rw [hlamval x, hφK x hx]; simp

end Work.ThmF.ChV12
