import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.Case2EightQfacts

namespace Work.CORE4.CtxN9InfAux

/-- **Bender 1981, §4 (8) case 2 (p. 226): the elementary facts about `Q = Ω₁(Z₂(O_p(U)))`.**

In the §4 configuration (`BenderCtx G`, `Case2Ctx B`), for an odd prime `p`, a subgroup `P ≤ F` of
order `p` and the `(p,p)`-subgroup `A ≤ F ⊔ K` containing `P` (`Case2EightObj`), if moreover the
case-2 hypotheses `A ≤ Q`, `Z(Q) < A`, `A < Q`, `|Q : A| = p` hold (with `Q := Qsub p B`), then:
`|Q| = p ^ 3`, `|Z(Q)| = p`, `Z(Q) ≤ A`, `Q ≤ F(U)`, `U` normalises `Q`, `A ⊴ Q`, and commutators
of `Q` with `A` lie in `Z(Q)`. -/
theorem QsubCase2Facts (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj h.D p P A →
          A ≤ Work.CORE4.Qsub p B → Work.CORE4.centerIn (Work.CORE4.Qsub p B) < A →
            A < Work.CORE4.Qsub p B → A.relIndex (Work.CORE4.Qsub p B) = p →
            (Nat.card ↥(Work.CORE4.Qsub p B) = p ^ 3 ∧
             Nat.card ↥(Work.CORE4.centerIn (Work.CORE4.Qsub p B)) = p ∧
             Work.CORE4.centerIn (Work.CORE4.Qsub p B) ≤ A ∧
             Work.CORE4.Qsub p B ≤ Work.GW2.fittingIn B.U ∧
             B.U ≤ Subgroup.normalizer (Work.CORE4.Qsub p B : Set G) ∧
             (A.subgroupOf (Work.CORE4.Qsub p B)).Normal ∧
             (∀ a ∈ A, ∀ y ∈ Work.CORE4.Qsub p B,
                y * a * y⁻¹ * a⁻¹ ∈ Work.CORE4.centerIn (Work.CORE4.Qsub p B))) := by sorry

end Work.CORE4.CtxN9InfAux
