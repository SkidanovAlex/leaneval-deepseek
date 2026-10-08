import Submission.Work.ASM.DAG

/-!
# ASM: the challenge statement, in the challenge's own words

This file records that the assembly of `Submission.Work.ASM.Assembly` produces the *exact*
statement of `Challenge.lean`, once the other areas' `Prop`s are supplied.  (`Challenge.lean`
writes the conclusion with the notation `PSL(2, GaloisField p k)`, which is how the statement
below is written too.)
-/

open scoped MatrixGroups

namespace Work.GW2

/-- The challenge statement of `Challenge.lean`, derived from the areas' `Prop`s. -/
theorem gorenstein_walter_of_props (hFT : FeitThompsonProp) (hN : NonSimpleStepProp)
    (h210 : Thm210Prop) (h1 : Case1FalseProp) (h2 : Case2FalseProp)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G)
    (_hdih : ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    ∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
      Nonempty (G ≃* PSL(2, GaloisField p k)) :=
  gorenstein_walter_of_areas hN (simpleStep_of_bender hFT h210 h1 h2) G hnonab P _hdih

end Work.GW2
