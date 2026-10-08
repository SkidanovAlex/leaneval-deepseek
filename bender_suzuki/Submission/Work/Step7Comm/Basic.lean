import Submission.Work.Step7Comm.Defs
import Submission.Work.ThmF.ChV3.step1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Step7Comm.Basic` — how `Q₀sub H` centralises `W`

`W = C_V(K)` coincides with `C_D(Inv H)` (Ch. II §4 Prop. 4, `W_eq_inf_centralizer_involutions`).
Since `Q₀sub H = ⟨Inv H ∪ {1}⟩`, every element of `W` centralises `Q₀sub H`.  This is the input
`Q₀ ≤ C_G(X)` used both in the §2 Lemma 2 (c) recursion (`sigLemma2c`) and in the construction of
the four-group in `C_G(⟨w⟩)` that §2 Lemma 2 (c) needs at `P' = ⟨w⟩`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.Step7Comm

variable {G : Type} [Group G] [Finite G]

/-- An element of `W = C_V(K)` centralises every involution of `H` (Ch. II §4 Prop. 4). -/
theorem mem_centralizer_involutions_of_mem_W {H Q : Subgroup G} {t s r w : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (hC4 : ChIIFourProp) (hw : w ∈ Work.ThmF.W H t) :
    w ∈ Subgroup.centralizer (involutions (H : Set G)) := by
  rw [Work.ThmF.ChV3.W_eq_inf_centralizer_involutions c.sit hC4 c.split] at hw
  exact (Subgroup.mem_inf.mp hw).2

/-- `Q₀sub H ≤ C_G(w)` for `w ∈ W`. -/
theorem Q0sub_le_centralizer_singleton_of_mem_W {H Q : Subgroup G} {t s r w : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) (hC4 : ChIIFourProp)
    (hw : w ∈ Work.ThmF.W H t) : Work.ThmF.Q0sub H ≤ Subgroup.centralizer ({w} : Set G) := by
  have hwC := mem_centralizer_involutions_of_mem_W c hC4 hw
  rw [Work.ThmF.Q0sub, Work.ThmF.Q0]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rcases hx with hx | rfl
  · refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.mp hwC x hx).symm
  · exact Subgroup.one_mem _

/-- `Q₀sub H ≤ C_G(⟨w⟩)` for `w ∈ W`. -/
theorem Q0sub_le_centralizer_zpowers_of_mem_W {H Q : Subgroup G} {t s r w : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) (hC4 : ChIIFourProp)
    (hw : w ∈ Work.ThmF.W H t) :
    Work.ThmF.Q0sub H ≤
      Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
  have hwC := Q0sub_le_centralizer_singleton_of_mem_W c hC4 hw
  intro x hx
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hxc : Commute x w :=
    (Subgroup.mem_centralizer_iff.mp (hwC hx) w (Set.mem_singleton w)).symm
  exact ((hxc.zpow_right n).eq).symm

end Work.Step7Comm
