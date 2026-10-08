import Mathlib
import Submission.Work.AppXIField.Defs
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.ChV3.Prove.Sig_sup_P_le_normalizer_CQ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIField.Main

/-- General form of the conjugation action: if `S ≤ N_G(A)` then conjugation gives a monoid
homomorphism `S →* MulAut A` whose value on `w` and `a` is `w a w⁻¹`.

This is the abstract content of `sig_conjAction_cq`; the only group-theoretic input needed is
`S ≤ N_G(A)`, which for `S = Σ` and `A = C_Q(P)` is `Sig_sup_P_le_normalizer_CQ`. -/
theorem conjAction_of_le_normalizer {G : Type} [Group G] {S A : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (A : Set G)) :
    ∃ φ : ↥S →* MulAut ↥A,
      ∀ (w : ↥S) (a : ↥A),
        ((φ w a : ↥A) : G) = (w : G) * (a : G) * (w : G)⁻¹ := by
  refine ⟨A.normalizerMonoidHom.comp (Subgroup.inclusion hS), fun w a => ?_⟩
  show ((Subgroup.inclusion hS w • a : ↥A) : G) = (w : G) * (a : G) * (w : G)⁻¹
  have h : ((Subgroup.inclusion hS w • a : ↥A) : G)
      = ((Subgroup.inclusion hS w : G)) * (a : G)
          * ((Subgroup.inclusion hS w : G))⁻¹ := rfl
  rw [h, Subgroup.coe_inclusion]

theorem sig_conjAction_cq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    ∃ φ : ↥(Work.ThmF.ChV3.Sig H t P) →* MulAut ↥(Work.ThmF.ChV3.CQ Q P),
      ∀ (w : ↥(Work.ThmF.ChV3.Sig H t P)) (a : ↥(Work.ThmF.ChV3.CQ Q P)),
        ((φ w a : ↥(Work.ThmF.ChV3.CQ Q P)) : G) = (w : G) * (a : G) * (w : G)⁻¹ :=
  conjAction_of_le_normalizer
    (le_sup_left.trans (Work.ThmF.ChV3.Prove.Sig_sup_P_le_normalizer_CQ c))

end Work.AppXIField.Main
