import Submission.Work.Step7Comm.Defs
import Submission.Work.ThmF.Prove.sigLemma2c

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Step7Comm.isPGroup_two_CQ_of_mem_SigCQ`

Step (7), first move: if `1 ≠ w ∈ Σ ⊓ C_G(C_Q(P))` then §2 Lemma 2 (c) (`sigLemma2c`) makes
`Q ⊓ C_G(w)` a `2`-group, and since `w` centralises `C_Q(P)` the same holds for `C_Q(P)`; moreover
`f = o(st) ∈ {3,5}`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.Step7Comm

variable {G : Type} [Group G] [Finite G]

/-- **Step (7)**: `C_Q(P)` is a `2`-group and `f = o(st) ∈ {3,5}` for `1 ≠ w ∈ Σ ⊓ C_G(C_Q(P))`. -/
theorem isPGroup_two_CQ_of_mem_SigCQ {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hC4 : ChIIFourProp) (hnil : Group.IsNilpotent ↥Q)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (hQ0 : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ Nat.card P) {w : G}
    (hw : w ∈ SigCQ H t Q P) (hw1 : w ≠ 1) :
    IsPGroup 2 ↥(Work.ThmF.ChV3.CQ Q P) ∧
      (orderOf (s * t) = 3 ∨ orderOf (s * t) = 5) := by
  obtain ⟨hwSig, hwCQ⟩ := Subgroup.mem_inf.mp hw
  obtain ⟨hQ2, hf⟩ :=
    Work.ThmF.Prove.sigLemma2c hC4 hnil c hQ0 (w := w) hwSig hw1
  have hle : Work.ThmF.ChV3.CQ Q P ≤ Q ⊓ Subgroup.centralizer ({w} : Set G) := by
    refine le_inf inf_le_left ?_
    intro y hy
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (Subgroup.mem_centralizer_iff.mp hwCQ y hy).symm
  exact ⟨hQ2.to_le hle, hf⟩

end Work.Step7Comm
