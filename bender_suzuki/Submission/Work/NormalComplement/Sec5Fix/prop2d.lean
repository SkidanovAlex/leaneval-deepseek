import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec5_setup
import Submission.Work.NormalComplement.sec5_prop1
import Submission.Work.NormalComplement.sec5_clause_d

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.Sec5Fix

open Classical
open scoped Pointwise

/-- **Peterfalvi I Ch. III §5 Proposition 2 (d)**: with `M = Mset u t` (an abelian subgroup, whose
elements are inverted by `t` and centralise `ut`) and `f = orderOf (u * t) ∈ {3,5}`, the `f'`-core
`O_{f'}(M) = pPrimeCoreSub f M` is nontrivial and `P` acts fixed-point-freely on it.

This is the `Sec5Fix` restatement of the design's `sec5_prop2d`; the mathematical content is
assembled in `Work.NormalComplement.sec5_clause_d` from the §5 datum `sec5_setup`, the bound
`7 ≤ p` (`sec5_prop1`), the abelianness/oddness of `M` (`msetAbelianOdd`), the cyclic subgroup
`T` with `6 ≤ |T|` (`benderLift`, from `BenderModelFacts2Prop` (2°)) and the `N_G(P)`-inversion
fact `ngpInverted` (App. III (2),(4) applied to `N_G(P)/P`). -/
theorem prop2d (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hC : Submission.Blueprint.ThmCProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop)
    (hBC : Work.NormalComplement.Design.BurnsideClassProp)
    (hBP : Work.NormalComplement.BenderPrelimProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    (hf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5)
    (M : Subgroup G) (hM : (M : Set G) = Work.NormalComplement.Design.Mset u t) :
    Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M ≠ ⊥ ∧
      Work.NormalComplement.Design.FpfOn P
        (Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Set G) := by
  -- the Bender-group datum of §5 Prop. 2 (a), from Ch. II §4 Prop. 3 (`sec5_setup`)
  obtain ⟨hun, ub, hub, hdatb⟩ := sec5_setup (G := G) hFT hC4 hP3 h
  obtain ⟨w, hw, huniq'⟩ := hun
  have huniq : ∀ y : G, y ∈ H → orderOf y = 2 →
      y ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) → y = w :=
    fun y h1 h2 h3 => huniq' y ⟨h1, h2, h3⟩
  -- that datum, moved to the given involution `u` (`u = ub` by uniqueness)
  have hbd : ∀ v : G, v ∈ H → orderOf v = 2 →
      v ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) →
      (let C : Subgroup G := Subgroup.centralizer (A : Set G)
       let F₀ : Subgroup G := (Submission.Blueprint.oddResidual ↥C).map C.subtype
       ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (φ : F₀ →* Y) (HY : Subgroup Y),
         Function.Surjective φ ∧ φ.ker = Subgroup.center ↥F₀ ∧
         LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y ∧
         LeanEval.GroupTheory.Defs.IsStronglyEmbedded HY ∧
         Submission.Blueprint.IsZassenhaus HY ∧
         (Submission.Blueprint.involutions (HY : Set Y)).ncard = 2 ^ p - 1 ∧
         ∃ (hu0 : v ∈ F₀) (ht0 : t ∈ F₀),
           φ ⟨v, hu0⟩ ∈ HY ∧ orderOf (φ ⟨v, hu0⟩) = 2 ∧ φ ⟨t, ht0⟩ ∉ HY ∧
           orderOf (φ ⟨t, ht0⟩) = 2 ∧
           ∀ x : F₀, (x : G) ∈ H → φ x ∈ HY) := by
    intro v hv1 hv2 hv3
    have hveq : ub = v :=
      (huniq ub hub.1 hub.2.1 hub.2.2).trans ((huniq v hv1 hv2 hv3).symm)
    subst hveq
    exact hdatb
  have hp7 : 7 ≤ p := sec5_prop1 (G := G) hFT hC4 hBP hBC h
  exact sec5_clause_d (G := G) hFT hA hC hC4 hP3 hIII hMF2 hCor1 hBC hBP h u hu M hM
    hp7 hf (hbd u hu.1 hu.2.1 hu.2.2)

end Work.NormalComplement.Sec5Fix
