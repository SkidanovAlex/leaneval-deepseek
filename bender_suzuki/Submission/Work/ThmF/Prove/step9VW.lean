import Mathlib
import Submission.Work.ThmF.ChV3.Chain15
import Submission.Work.ThmF.Prove.step9WV

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ThmF.Prove

open scoped commutatorElement

/-- **Step (9): `V/W` is abelian** (Peterfalvi II Ch. V §3).

Let `V, W, P ≤ G` with `V ≤ N_G(W)` (so `W ◁ V`), `W ⊔ P = V`, and `P` abelian.  Then every
commutator `a b a⁻¹ b⁻¹` of elements of `V` lies in `W`, i.e. `[V, V] ≤ W`.

The point is that `V/W` is a quotient of `P` (indeed `W ⊔ P = V` and `W ◁ V` give
`V/W = P W / W`, the image of the abelian group `P`), hence abelian.  Formally we apply
`Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top` inside the group `↥V`:  there
`N := W.subgroupOf V` is normal (`Subgroup.normal_subgroupOf_of_le_normalizer`), `H := P.subgroupOf V`
is commutative (inherited from `P`), and `N ⊔ H = ⊤` (from `W ⊔ P = V`). -/
theorem step9VW {G : Type} [Group G] {V W P : Subgroup G}
    (hWV : V ≤ Subgroup.normalizer (W : Set G))
    (hsup : W ⊔ P = V)
    (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) :
    ∀ a ∈ V, ∀ b ∈ V, a * b * a⁻¹ * b⁻¹ ∈ W := by
  have hWleV : W ≤ V := by rw [← hsup]; exact le_sup_left
  have hPleV : P ≤ V := by rw [← hsup]; exact le_sup_right
  -- `W.subgroupOf V` is normal in `↥V`
  haveI hNnormal : (W.subgroupOf V).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hWV
  -- `W.subgroupOf V ⊔ P.subgroupOf V = ⊤` in `↥V`
  have hHN : (W.subgroupOf V) ⊔ (P.subgroupOf V) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hWleV hPleV, hsup, Subgroup.subgroupOf_eq_top.mpr le_rfl]
  -- `P.subgroupOf V` is commutative
  have hHcomm : IsMulCommutative ↥(P.subgroupOf V) :=
    IsMulCommutative.of_comm (fun a b => by
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hPab (a.val : G) (Subgroup.mem_subgroupOf.mp a.2) (b.val : G)
        (Subgroup.mem_subgroupOf.mp b.2))
  have hcomm : _root_.commutator ↥V ≤ W.subgroupOf V :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hHN hHcomm
  intro a ha b hb
  have h : ⁅(⟨a, ha⟩ : ↥V), (⟨b, hb⟩ : ↥V)⁆ ∈ W.subgroupOf V :=
    (Subgroup.commutator_le.mp hcomm) _ trivial _ trivial
  rw [Subgroup.mem_subgroupOf] at h
  simpa [commutatorElement_def] using h

end Work.ThmF.Prove
