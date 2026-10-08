import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2
import Submission.Work.ThreePoints.Sec2b
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThreePoints.oddCore_le_of_stronglyEmbedded
import Submission.Work.ThreePoints.sup_centralizer_eq_of_fourGroup
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThreePoints.ThmC.Crux
import Submission.Work.ThreePoints.ThmC.hAexists
import Submission.Work.ThreePoints.ThmC.app4
import Submission.Work.ThreePoints.ThmC.app3_1
import Submission.Work.ThreePoints.ThmC.ch1_sec6_prop2
import Submission.Work.ThreePoints.ThmC.ch2_sec2_lem1
import Submission.Work.ThreePoints.ThmC.ch2_sec2_lem3

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThreePoints

/-! ## The four numbered results consumed by `ThmC.hAexists`, in the exact shape it asks for -/

private theorem app4_form :
    ∀ (M : Type) [Group M] [Finite M] {p : ℕ}, p.Prime → p ≠ 2 → Group.IsSolvable M →
      ∀ {P X : Subgroup M}, IsPGroup p P →
        (∀ x : M, x ∈ Subgroup.centralizer (P : Set M) → orderOf x = p → x ∈ P) →
        Nat.Coprime (Nat.card X) p → P ≤ Subgroup.normalizer (X : Set M) →
        X ≤ Submission.Blueprint.pPrimeCore p M := by
  intro M _ _ p hp hpodd hsolv P X hP hC hXp hPX
  exact ThmC.app4 hp hpodd hsolv hP hC hXp hPX

private theorem hlem1_form {G : Type} [Group G] [Finite G] {H : Subgroup G} :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded H → Submission.Blueprint.IsTwoTransitiveOn H →
    Submission.Blueprint.BrauerSuzukiProp → Submission.Blueprint.FeitThompsonProp →
    ∀ {g u : G}, g ∉ H → u ∈ Submission.Blueprint.involutions (H : Set G) →
    ∀ {p : ℕ} {P : Subgroup G}, p.Prime → p ≠ 2 →
    ThmC.IsSylowOf p P (Submission.Blueprint.twoPoint H g ⊓
      Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H g)) →
    u ∈ Subgroup.normalizer (P : Set G) →
    ThmC.IsMaxP3 H p P ∧
    (Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set G))
        (Submission.Blueprint.fixedPts H P) ∧
      ∀ g₁ : G, P ≤ Submission.Blueprint.conj g₁ H →
        LeanEval.GroupTheory.Defs.IsStronglyEmbedded
          ((Subgroup.normalizer (P : Set G) ⊓ Submission.Blueprint.conj g₁ H).subgroupOf
            (Subgroup.normalizer (P : Set G)))) ∧
    (¬ Submission.Blueprint.HasFourGroup (Subgroup.normalizer (P : Set G)) →
      ThmC.IsSylowOf p P (Submission.Blueprint.twoPoint H g)) ∧
    (¬ ThmC.IsSylowOf p P
        (P ⊔ (Subgroup.centralizer (P : Set G) ⊓ Submission.Blueprint.twoPoint H g)) →
      ∀ x ∈ P, u * x = x * u) := by
  intro hH h2t hBrSz hFT g u hg hu p P hp hpodd hP huP
  exact ThmC.ch2_sec2_lem1 hH h2t hBrSz hFT hg hu hp hpodd hP huP

private theorem hlem3_form {F : Type} [Group F] [Finite F] :
    Submission.Blueprint.FeitThompsonProp → Submission.Blueprint.GlaubermanZJProp →
    Submission.Blueprint.HasFourGroup F → ∀ {H : Subgroup F},
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded H →
    (∀ u v : F, u ∈ Submission.Blueprint.involutions (H : Set F) →
      v ∈ Submission.Blueprint.involutions (H : Set F) →
      u * v * u⁻¹ * v⁻¹ ∈ Submission.Blueprint.oddCore F) →
    ∀ {t : F}, orderOf t = 2 → t ∉ H → ∀ {p : ℕ} {R : Subgroup F}, p.Prime → p ≠ 2 →
    ThmC.IsSylowOf p R (Submission.Blueprint.twoPoint H t) →
    Submission.Blueprint.pPrimeCore p (Submission.Blueprint.twoPoint H t) = ⊥ →
    (∃ Q : Subgroup F, Q ≤ Submission.Blueprint.twoPoint H t ∧ IsPGroup p Q ∧
      ∃ u ∈ Submission.Blueprint.involutions (H : Set F),
        u ∈ Subgroup.normalizer (Q : Set F) ∧ ¬ ∀ x ∈ Q, u * x = x * u) →
    Submission.Blueprint.involutions (H : Set F) ⊆
      (Subgroup.normalizer (Submission.Blueprint.ZJ R : Set F) : Set F) := by
  intro hFT hZJ hfour H hH hcomm t ht htH p R hp hpodd hR hOp' hP
  exact ThmC.ch2_sec2_lem3 hFT hZJ hfour hH hcomm ht htH hp hpodd hR hOp' hP

private theorem hsec6_form {G : Type} [Group G] [Finite G] {H : Subgroup G} :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded H → Submission.Blueprint.FeitThompsonProp →
    Submission.Blueprint.ThmAProp → Submission.Blueprint.BrauerSuzukiProp →
    Submission.Blueprint.HasFourGroup G →
    ∀ {p : ℕ} {P : Subgroup G}, p.Prime → p ≠ 2 → ThmC.IsMaxP3 H p P → P ≤ H →
    ∀ {u : G}, u ∈ Submission.Blueprint.involutions (H : Set G) →
    u ∈ Subgroup.normalizer (P : Set G) → (∃ x ∈ P, u * x ≠ x * u) →
    ∃ s : G, orderOf s = 2 ∧ s ∉ H ∧ ∀ ω : G ⧸ H, s • ω = ω →
      ThmC.pPrimeCoreSub p (H ⊓ Submission.Blueprint.conj s H) ≤
        ThmC.pPrimeCoreSub p (MulAction.stabilizer G ω ⊓ H ⊓ Submission.Blueprint.conj s H) := by
  intro hH hFT hA hBrSz hfour p P hp hpodd hP hPH u hu huP hnc
  exact ThmC.ch1_sec6_prop2 hH hFT hA hBrSz hfour hp hpodd hP hPH hu huP hnc

/-- The blueprint's `ThmCProp` (Peterfalvi I Ch. II p. 163).

The proof is Peterfalvi's.  `ThmC.Crux.thmC_of_A` reduces Theorem C to the existence, for
`u ∈ Inv(H)` not centralising `D ∩ D^u` (`D = H ∩ H^t`, `t ∈ Inv(G∖H)`), of a nontrivial `u`- and
`t`-invariant normal subgroup `A` of `D`; that existence is `ThmC.hAexists`, the conclusion of
Ch. II §3 Steps 1–3 (pp. 166–168).  `hAexists` consumes Appendix IV (`ThmC.app4`), Ch. II §2
Lemma 1 (`ThmC.ch2_sec2_lem1`) and Lemma 3 (`ThmC.ch2_sec2_lem3`), and Ch. I §6 Prop. 2
(`ThmC.ch1_sec6_prop2`) — each of them a complete, axiom-clean module of this workspace — and
the four private wrappers above adapt their binder order to the one `hAexists` was stated with. -/
theorem thmC (hFT : Submission.Blueprint.FeitThompsonProp) (hA : Submission.Blueprint.ThmAProp)
    (hZJ : Submission.Blueprint.GlaubermanZJProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hMod : Submission.Blueprint.ModelFactsProp) : Submission.Blueprint.ThmCProp :=
  ThmC.thmC_of_A hFT hA hZJ hBrSz hMod
    (ThmC.hAexists hFT hA hZJ hBrSz app4_form hlem1_form hlem3_form hsec6_form)

end Work.ThreePoints
