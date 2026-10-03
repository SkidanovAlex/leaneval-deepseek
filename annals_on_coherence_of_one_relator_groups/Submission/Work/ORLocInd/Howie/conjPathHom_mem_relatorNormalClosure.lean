import Mathlib
import Submission.Work.ORLocInd.Howie.TietzeSupport
import Submission.Work.ORLocInd.Howie.mem_relatorNormalClosure_conj

namespace Work.ORLocInd.Howie

variable {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- Moving a conjugate of the relator `R` by `B` across the path `A`: conjugating `B · R · B⁻¹`
by `A` is the same as conjugating the relator by the composite path `A · B`.  Both sides are the
reduced path representing the element `A · B · R · B⁻¹ · A⁻¹` of `F(Γ)`. -/
theorem pmul_conj_comp_path {a b v : V} (A : Quiver.Path a b) (B : Quiver.Path b v)
    (R : Quiver.Path v v) :
    pmul (pmul A (pmul B (pmul R B.reverse))) A.reverse
      = pmul (pmul (A.comp B) R) (A.comp B).reverse := by
  rw [Quiver.Path.reverse_comp]
  rw [← pmul_assoc A B (pmul R B.reverse)]
  change pmul (pmul (red (A.comp B)) (pmul R B.reverse)) A.reverse
    = pmul (pmul (A.comp B) R) (B.reverse.comp A.reverse)
  rw [pmul_red_left (A.comp B) (pmul R B.reverse)]
  rw [← pmul_assoc (A.comp B) R B.reverse]
  rw [pmul_assoc (pmul (A.comp B) R) B.reverse A.reverse]
  change pmul (pmul (A.comp B) R) (red (B.reverse.comp A.reverse))
    = pmul (pmul (A.comp B) R) (B.reverse.comp A.reverse)
  rw [pmul_red_right (pmul (A.comp B) R) (B.reverse.comp A.reverse)]

theorem conjPathHom_mem_relatorNormalClosure {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V] (P : Work.ORLocInd.Howie.Presentation V) {a b : V}
    (δ : Quiver.Path a b) {x : Work.ORLocInd.Howie.VertexGroup b}
    (hx : x ∈ P.relatorNormalClosure b) :
    Work.ORLocInd.Howie.conjPathHom δ x ∈ P.relatorNormalClosure a := by
  -- `conjPathHom δ` maps every conjugate of a relator at `b` to a conjugate of a relator at `a`,
  -- hence carries `relatorSet b` into `relatorNormalClosure a`; as `conjPathHom δ` is a
  -- homomorphism, that subgroup's preimage is normal and contains `relatorSet b`, so it contains
  -- the normal closure.
  have hle : P.relatorNormalClosure b ≤ (P.relatorNormalClosure a).comap (conjPathHom δ) :=
    Subgroup.normalClosure_le_normal (fun y hy => ?_)
  · exact Subgroup.mem_comap.mp (hle hx)
  · simp only [Presentation.relatorSet, Set.mem_ofPred_eq] at hy
    obtain ⟨i, δ', -, rfl⟩ := hy
    have key : ∀ (i : P.ι) (δ' : Quiver.Path b (P.base i)),
        conjPathHom δ (⟨pmul δ' (pmul (P.path i) δ'.reverse), pmul_isReduced _ _⟩ : VertexGroup b)
          ∈ P.relatorNormalClosure a := by
      intro i δ'
      have h := mem_relatorNormalClosure_conj P a i (δ.comp δ')
      have hEq : conjPathHom δ
            (⟨pmul δ' (pmul (P.path i) δ'.reverse), pmul_isReduced _ _⟩ : VertexGroup b)
          = (⟨pmul (pmul (δ.comp δ') (P.path i)) (δ.comp δ').reverse,
              pmul_isReduced _ _⟩ : VertexGroup a) := by
        apply Subtype.ext
        show pmul (pmul δ (pmul δ' (pmul (P.path i) δ'.reverse))) δ.reverse = _
        exact pmul_conj_comp_path δ δ' (P.path i)
      rw [hEq]
      exact h
    exact key i δ'

end Work.ORLocInd.Howie
