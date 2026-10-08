import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- The conjugation action of the normalizer `N_G(Q)` on `Q`, `g ↦ (x ↦ g x g⁻¹)`,
written on underlying elements of `G`. -/
theorem normalizerMonoidHom_apply_coe {G : Type} [Group G] (Q : Subgroup G)
    (g : ↥(Subgroup.normalizer (Q : Set G))) (x : ↥Q) :
    (((Subgroup.normalizerMonoidHom Q) g) x : G) = (g : G) * (x : G) * (g : G)⁻¹ := by
  show ((g • x : ↥Q) : G) = _
  rfl

/-- Since `H ≤ N_G(Q)`, the two-point stabiliser `D = twoPoint H t = H ∩ H^t ≤ H ≤ N_G(Q)`
acts on `Q` by conjugation, giving a homomorphism `twoPoint H t →* MulAut Q` whose action
on underlying elements is `x ↦ d x d⁻¹`. -/
theorem exists_conjAction {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t) :
    ∃ φ : ↥(Submission.Blueprint.twoPoint H t) →* MulAut ↥Q,
      ∀ (d : ↥(Submission.Blueprint.twoPoint H t)) (x : ↥Q),
        ((φ d x : ↥Q) : G) = (d : G) * (x : G) * (d : G)⁻¹ := by
  have htp : Submission.Blueprint.twoPoint H t ≤ Subgroup.normalizer (Q : Set G) :=
    fun d hd => hsplit.normal (Subgroup.mem_inf.mp hd).1
  refine ⟨(Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion htp), ?_⟩
  intro d x
  show (((Subgroup.normalizerMonoidHom Q) (Subgroup.inclusion htp d)) x : G) = _
  rw [normalizerMonoidHom_apply_coe, Subgroup.coe_inclusion]

end Work.ZassenhausSuzuki
