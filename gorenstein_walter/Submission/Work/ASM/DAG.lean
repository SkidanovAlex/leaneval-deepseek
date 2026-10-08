import Submission.Work.ASM.Assembly
import Submission.Work.ASM.FT

/-!
# ASM: the full DAG wiring

This file mirrors `GW2.gorenstein_walter_of_areas` of `_design_gw/Contracts2.lean`: *every* area
deliverable of the blueprint appears as an explicit hypothesis, and the only mathematics proved
here is the ASM assembly (`gw_of_DGroupTheorem`, `dGroupTheorem_of_steps`,
`simpleStep_of_bender`).

It is the template for the final assembly: a caller supplies the areas' theorems (each an
instance of the corresponding `Prop` of `Work.GW2`) and Feit–Thompson (`feitThompsonProp`, or
`T.ft` for the toolkit), and gets the challenge statement.
-/

open scoped MatrixGroups
open Subgroup

namespace Work.GW2

set_option linter.unusedVariables false in
/-- The assembled challenge statement, with every area of the blueprint as an explicit input. -/
theorem gorenstein_walter_of_all_areas (hFT : FeitThompsonProp)
    -- RED (GW Prop. 9 replacement)
    (hNonSimple : NonSimpleStepProp)
    -- CORE2B: Bender's Theorem 2.10
    (hThm210 : Thm210Prop)
    -- CORE3 / CORE4: the two eliminations
    (hCase1 : Case1FalseProp) (hCase2 : Case2FalseProp)
    -- the remaining area deliverables of the blueprint (consumed by the CORE areas)
    (hBGA : BGThmAProp) (hBGB : BGThmBProp) (hBGC : BGThmCProp)
    (hBSWZass : BSWZassProp) (hZassOdd : ZassOddProp) (hA7Rec : A7RecProp)
    (hPStable : PStableProp) (hZJA : ZJAProp) (hZJB : ZJBProp) (hLemma23 : Lemma23Prop)
    (hLemma22 : Lemma22Prop) (hThm26 : Thm26Prop) (hLemma27 : Lemma27Prop)
    (hLemma28 : Lemma28Prop) (hLemma29 : Lemma29Prop)
    (T : LocalToolkit)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G) (hdih : ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    ∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
      Nonempty (G ≃* PSL(2, GaloisField p k)) :=
  gorenstein_walter_of_areas hNonSimple (simpleStep_of_bender hFT hThm210 hCase1 hCase2)
    G hnonab P hdih

end Work.GW2
