import Submission.Work.RED.Basic
import Submission.Work.RED.Main
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.RED.DihedralFacts
import Submission.Work.RED.MinimalNormalFacts
import Submission.Work.RED.OddCoreFacts
import Submission.Work.RED.CharSimpleNotSolvable
import Submission.Work.RED.DihOrCycSubgroup
import Submission.Work.RED.DihOrCycIso
import Submission.Work.RED.QuotientSylowDihedral
import Submission.Work.RED.le_center_of_card_eq_two
import Submission.Work.RED.CyclicSylowQuotient
import Submission.Work.RED.odd_card_centralizer_of_four_subgroup
import Submission.Work.RED.exists_fourGroup_of_dihOrCyc_nonsolvable
import Submission.Work.RED.centralizer_eq_of_normal_fourGroup
import Submission.Work.RED.not_isSolvable_of_minimalNormalIn
import Submission.Work.RED.oddCore_of_minimalNormalIn_eq_bot
import Submission.Work.RED.minimalNormalIn_eq_of_contained
import Submission.Work.RED.dShape_of_oddCore_eq_bot

/-!
# RED: the deliverable

`Work.RED.GW2.nonSimpleStep` proves `NonSimpleStepProp` (blueprint §4, replacing GW 1965
Prop. 9) from the toolkit Props `FeitThompsonProp`, `InvolutionFusionProp`,
`CentralizerSplitProp`, `AutL2Prop` and `AutA7Prop`, assembling the external facts into
`RedFacts` from the individual modules of this area.
-/

namespace Work.RED.GW2

open Subgroup

/-- The external facts of the RED reduction, assembled from the modules of this area. -/
theorem redFacts (hft : FeitThompsonProp) : RedFacts := by
  have hdi := Work.RED.DihedralFacts
  have hminf := Work.RED.MinimalNormalFacts
  have hodd := Work.RED.OddCoreFacts
  have hcsq : ∀ (G : Type) [Group G] [Finite G] (P : Sylow 2 G),
      IsCyclic ↥(P : Subgroup G) → IsPGroup 2 (G ⧸ oddCore G) :=
    fun G _ _ P hP => Work.RED.CyclicSylowQuotient G P hP
  have hdcs : ∀ {G : Type} [Group G] [Finite G] (K : Subgroup G),
      DihOrCycSylow G → DihOrCycSylow ↥K :=
    fun {G} _ _ K h => Work.RED.DihOrCycSubgroup Work.RED.DihedralSubgroup K h
  have hdiiso : ∀ {G H : Type} [Group G] [Finite G] [Group H] [Finite H],
      DihOrCycSylow G → G ≃* H → DihOrCycSylow H :=
    fun {G H} _ _ _ _ h e => Work.RED.DihOrCycIso Work.RED.DihedralSubgroup h e
  have hquot : ∀ (G : Type) [Group G] [Finite G], Odd (Nat.card (oddCore G)) →
      DihOrCycSylow G → DihOrCycSylow (G ⧸ oddCore G) :=
    fun G _ _ hoddO h => Work.RED.QuotientSylowDihedral hoddO h
  have hcent2 : ∀ {G : Type} [Group G] (N : Subgroup G), N.Normal → Nat.card N = 2 →
      N ≤ Subgroup.center G :=
    fun {G} _ N hNn hcard => Work.RED.le_center_of_card_eq_two N hNn hcard
  have hcent4 : ∀ {G : Type} [Group G] [Finite G] (N : Subgroup G), N.Normal →
      Subgroup.center ↥N = ⊥ →
      ∀ {n : ℕ} [NeZero n] {P : Sylow 2 G}, (↥(P : Subgroup G) ≃* DihedralGroup n) → 2 ≤ n →
      (∃ V : Subgroup G, V ≤ N ∧ IsFourGroup V) →
      Odd (Nat.card (Subgroup.centralizer (N : Set G))) :=
    fun {G} _ _ N hNn hZ n _ P e hn hV =>
      Work.RED.odd_card_centralizer_of_four_subgroup hdi N hNn hZ e hn hV
  have hv4 : ∀ (N : Type) [Group N] [Finite N], DihOrCycSylow N → oddCore N = ⊥ →
      ¬ Group.IsSolvable N → ∃ V : Subgroup N, IsFourGroup V :=
    fun N _ _ h hO hsol =>
      Work.RED.exists_fourGroup_of_dihOrCyc_nonsolvable hdi hcsq h hO hsol
  have hfourNorm : ∀ {G : Type} [Group G] [Finite G] {N : Subgroup G}, N.Normal →
      IsFourGroup N → oddCore G = ⊥ →
      ∀ {n : ℕ} [NeZero n] {P : Sylow 2 G}, (↥(P : Subgroup G) ≃* DihedralGroup n) → 2 ≤ n →
      Subgroup.centralizer (N : Set G) = N :=
    fun {G} _ _ {N} hNn hN4 hO n _ P e hn =>
      Work.RED.centralizer_eq_of_normal_fourGroup hdi hodd (N := N) hNn hN4 hO e hn
  have hnotSol : ∀ {G : Type} [Group G] [Finite G] {N K : Subgroup G}, IsMinimalNormal N →
      IsMinimalNormalIn N K → ¬ IsMulCommutative K → ¬ Group.IsSolvable ↥K :=
    fun {G} _ _ {N K} hN hK hnab =>
      Work.RED.not_isSolvable_of_minimalNormalIn hminf hN hK hnab
  have hoddCoreK : ∀ {G : Type} [Group G] [Finite G] {N K : Subgroup G}, IsMinimalNormal N →
      IsMinimalNormalIn N K → ¬ Group.IsSolvable ↥K → oddCore ↥K = ⊥ :=
    fun {G} _ _ {N K} hN hK hsol =>
      Work.RED.oddCore_of_minimalNormalIn_eq_bot hminf hodd hft hN hK hsol
  have heqOfContained : ∀ {G : Type} [Group G] [Finite G] (N K : Subgroup G),
      IsMinimalNormal N → IsMinimalNormalIn N K →
      (∃ V : Subgroup G, V ≤ K ∧ IsFourGroup V) →
      ∀ {n : ℕ} [NeZero n] {P : Sylow 2 G}, (↥(P : Subgroup G) ≃* DihedralGroup n) → 2 ≤ n →
      K = N :=
    fun {G} _ _ N K hN hK hV n _ P e hn =>
      Work.RED.minimalNormalIn_eq_of_contained hminf hdi N K hN hK hV e hn
  exact
    { dihedralSubgroup := Work.RED.DihedralSubgroup
      dih := hdi
      min := hminf
      odd := hodd
      ft := hft
      csq := hcsq
      dcs := hdcs
      diiso := hdiiso
      quotSylow := hquot
      cent2 := hcent2
      cent4 := hcent4
      v4 := hv4
      fourNorm := hfourNorm
      notSol := hnotSol
      oddCoreK := hoddCoreK
      eqOfContained := heqOfContained }

/-- **The deliverable of area RED**: the non-simple step, from the toolkit Props. -/
theorem nonSimpleStep (hft : FeitThompsonProp) (hfus : InvolutionFusionProp)
    (hsplit : CentralizerSplitProp) (hautL2 : AutL2Prop) (hautA7 : AutA7Prop) :
    NonSimpleStepProp := by
  have hB2 : ∀ (G : Type) [Group G] [Finite G], DihOrCycSylow G → SmallerDGroups G →
      oddCore G = ⊥ → ¬ (IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a) →
      ∀ {n : ℕ} [NeZero n] {P : Sylow 2 G},
      (↥(P : Subgroup G) ≃* DihedralGroup n) → 2 ≤ n → DShape G := by
    intro G _ _ hdih hsmall hO hns n _ P e hn
    exact Work.RED.dShape_of_oddCore_eq_bot (redFacts hft) hfus hsplit hautL2 hautA7
      hdih hsmall hO hns e hn
  exact nonSimpleStep_of_facts (redFacts hft) hB2 hfus hsplit hautL2 hautA7

/-- The deliverable in the shape used by the assembly: the whole local toolkit. -/
theorem nonSimpleStep_of_toolkit (T : LocalToolkit) : NonSimpleStepProp :=
  nonSimpleStep T.ft T.fus T.split T.autL2 T.autA7

end Work.RED.GW2
