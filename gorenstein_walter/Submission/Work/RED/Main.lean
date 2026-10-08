import Submission.Work.RED.Basic

/-!
# RED: the non-simple step (Bender 1981, blueprint §4)

`nonSimpleStep_of_facts` proves `NonSimpleStepProp` from the bundled external facts
`RedFacts`, the case-B2 analysis (delegated as `dShape_of_oddCore_eq_bot`), and the
toolkit Props `InvolutionFusionProp`, `CentralizerSplitProp`, `AutL2Prop`, `AutA7Prop`.
-/

namespace Work.RED.GW2

open Subgroup

/-- Case B1 of blueprint §4: if `O(G) ≠ 1`, apply the induction hypothesis to `G ⧸ O(G)`. -/
theorem dShape_of_oddCore_ne_bot (F : RedFacts) {G : Type} [Group G] [Finite G]
    (hdih : DihOrCycSylow G) (hsmall : SmallerDGroups G) (hO : oddCore G ≠ ⊥) :
    DShape (G ⧸ oddCore G) := by
  have hcard : Nat.card (G ⧸ oddCore G) < Nat.card G := F.odd.card_quotient_lt G hO
  have hoddO : Odd (Nat.card (oddCore G)) := F.odd.odd G
  have hdihq : DihOrCycSylow (G ⧸ oddCore G) := F.quotSylow G hoddO hdih
  have h1 : IsDGroup (G ⧸ oddCore G) := hsmall (G ⧸ oddCore G) hcard hdihq
  have hEq : oddCore (G ⧸ oddCore G) = ⊥ := F.odd.quotient_eq_bot G
  exact (DShape.quotientBot_iff (G ⧸ oddCore G)).mp
    (DShape.of_mulEquiv h1 (QuotientGroup.quotientMulEquivOfEq hEq))

/-- RED reduced to the case `O(G) = 1` (the delegated analysis `dShape_of_oddCore_eq_bot`). -/
theorem nonSimpleStep_of_facts (F : RedFacts)
    (hB2 : ∀ (G : Type) [Group G] [Finite G], DihOrCycSylow G → SmallerDGroups G →
      oddCore G = ⊥ → ¬ (IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a) →
      ∀ {n : ℕ} [NeZero n] {P : Sylow 2 G},
      (↥(P : Subgroup G) ≃* DihedralGroup n) → 2 ≤ n → DShape G)
    (hfus : InvolutionFusionProp) (hsplit : CentralizerSplitProp)
    (hautL2 : AutL2Prop) (hautA7 : AutA7Prop) :
    NonSimpleStepProp := by
  intro G _ _ hdih hsmall hnotsimple
  change DShape (G ⧸ oddCore G)
  by_cases hcyc : ∃ P : Sylow 2 G, IsCyclic ↥(P : Subgroup G)
  · obtain ⟨P, hP⟩ := hcyc
    exact Or.inl (F.csq G P hP)
  · push_neg at hcyc
    obtain ⟨P₀, -⟩ := (IsPGroup.of_bot (p := 2) (G := G)).exists_le_sylow
    rcases hdih P₀ with hc | ⟨n, ⟨e⟩⟩
    · exact absurd hc (hcyc P₀)
    · haveI : IsCyclic (DihedralGroup 1) := (DihedralGroup.isCyclic_iff (n := 1)).mpr rfl
      have hn1 : n ≠ 1 := by
        intro h1
        subst h1
        exact hcyc P₀ (isCyclic_of_mulEquiv (G := DihedralGroup 1)
          (H := ↥(P₀ : Subgroup G)) e.symm)
      haveI : NeZero n := neZero_of_mulEquiv_dihedral e
      have hn2 : 2 ≤ n := by
        have : n ≠ 0 := NeZero.out
        omega
      by_cases hO : oddCore G = ⊥
      · refine DShape.of_mulEquiv (hB2 G hdih hsmall hO hnotsimple e hn2) ?_
        exact (((QuotientGroup.quotientMulEquivOfEq hO.symm).symm.trans
          QuotientGroup.quotientBot).symm)
      · exact dShape_of_oddCore_ne_bot F hdih hsmall hO

end Work.RED.GW2
