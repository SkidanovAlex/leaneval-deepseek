import Submission.Work.Hering.Step3.centralizer_isPGroup
import Submission.Work.Hering.Step4.card_four_false
import Submission.Work.Hering.Step5.card_eight
import Submission.Work.Hering.Step6.actsAsAut
import Submission.Work.Hering.V.card_eq_two_pow
import Submission.Work.Hering.V.four_le_card
import Submission.Work.Hering.V.exists_subgroup_card_four
import Submission.Work.Hering.V.ExponentTwo

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The reduction of Hering's theorem (Peterfalvi I Ch. IV §2)

`Work.Hering.hering_of_noReducedConfig_of`: a minimal group of even order acting doubly
transitively on its involutions with 2-rank `≥ 2` yields the reduced configuration
`Work.Hering.ReducedConfig`. Hence `HeringProp` follows from the hard core
`NoReducedConfigProp`.

The proof follows Peterfalvi I §2 (pp. 191–193), Steps 1–5:
`V = Inv(G) ∪ {1}` is elementary abelian of order `2^m ≥ 4`; Step 3 gives that `C_G(U)` is a
2-group for every `U ≤ V` of order `4`; Step 4 rules out `m = 2`; Step 5 gives `|V| = 8`; and
then `V ⊴ G`, `Inv(G) = V#`, `C_G(V)` a 2-group and `G/C_G(V) ≅ Aut(V)` are the clauses of
`ReducedConfig`.
-/

set_option autoImplicit false

namespace Work.Hering

open LeanEval.GroupTheory.Defs

/-- **The reduction §2 of Peterfalvi I Ch. IV.** A minimal counterexample to Hering's theorem
gives the reduced configuration. -/
theorem hering_of_noReducedConfig_of (hNoRed : NoReducedConfigProp)
    (hAppII5 : AppII5Prop) (hWagner : WagnerProp) (hAppVII : AppVIIProp) :
    ∀ (G : Type) [Group G] [Finite G], Even (Nat.card G) → DTInv G → ¬ HasFourGroup G := by
  have key : ∀ n, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → Even (Nat.card G) →
      DTInv G → ¬ HasFourGroup G := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G _ _ hcard _hEven hDT h4
      -- (E2): the induction hypothesis
      have hE2 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
          Even (Nat.card F) → DTInv F → ¬ HasFourGroup F := by
        intro F _ _ hlt
        exact ih (Nat.card F) (by rw [← hcard]; exact hlt) F rfl
      -- Step 3
      have hC : ∀ U : Subgroup G, U ≤ invSubgroup hDT h4 → Nat.card U = 4 →
          IsPGroup 2 ↥(Subgroup.centralizer (U : Set G)) :=
        fun U hU hUc => Step3.centralizer_isPGroup hAppII5 hDT h4 hE2 hU hUc
      obtain ⟨m, hm⟩ := V.card_eq_two_pow hDT h4
      have hV4 : 4 ≤ Nat.card ↥(invSubgroup hDT h4) := V.four_le_card hDT h4
      -- Steps 4 and 5: `|V| = 8`
      have hV8 : Nat.card ↥(invSubgroup hDT h4) = 8 := by
        rcases Nat.lt_or_ge m 3 with hm3 | hm3
        · have hm2 : m = 2 := by
            have h4le : 4 ≤ 2 ^ m := by rw [← hm]; exact hV4
            have h2m : 2 ≤ m := by
              by_contra h
              push_neg at h
              interval_cases m <;> norm_num at h4le
            omega
          exact (Step4.card_four_false (hDT := hDT) (h4 := h4) hC (by rw [hm, hm2]; norm_num)).elim
        · have h8 : 8 ≤ Nat.card ↥(invSubgroup hDT h4) := by
            rw [hm]
            calc 8 = 2 ^ 3 := by norm_num
              _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
          exact Step5.card_eight (hDT := hDT) (h4 := h4) hWagner hAppVII hC h8
      -- the reduced configuration
      refine hNoRed G ⟨invSubgroup hDT h4, invSubgroup_normal hDT h4, hV8, ?_, ?_, ?_, ?_⟩
      · intro x hx
        exact pow_two_eq_one_of_mem_invSubgroup hDT h4 hx
      · intro x hx
        exact involutions_subset_invSubgroup hDT h4 hx
      · obtain ⟨U, hU, hUc⟩ := V.exists_subgroup_card_four (hDT := hDT) (h4 := h4) hV8
        have hle : Subgroup.centralizer ((invSubgroup hDT h4 : Set G)) ≤
            Subgroup.centralizer (U : Set G) :=
          Subgroup.centralizer_le (fun x hx => hU hx)
        exact (hC U hU hUc).to_le hle
      · exact Step6.actsAsAut (hDT := hDT) (h4 := h4) hWagner hV8
  intro G _ _ hEven hDT h4
  exact key (Nat.card G) G rfl hEven hDT h4

end Work.Hering
