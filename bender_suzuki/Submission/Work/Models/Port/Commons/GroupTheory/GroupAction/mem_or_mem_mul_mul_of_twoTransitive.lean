import Mathlib
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.stabilizer_transitive_on_complement

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.GroupAction

/-- In a 2-transitive action, the stabilizer of a point is transitive on the
complement of that point.  Consequently, any element `g` of `G` either fixes
`a`, or can be written as `m * w * m'` with `m`, `m'` fixing `a`, for any `w`
that moves `a`. -/
theorem mem_or_mem_mul_mul_of_twoTransitive {G α : Type*} [Group G] [MulAction G α]
    [MulAction.IsMultiplyPretransitive G α 2] (a : α) (w : G) (hw : w • a ≠ a) :
    ∀ g : G, g • a = a ∨ ∃ m m' : G, m • a = a ∧ m' • a = a ∧ g = m * w * m' := by
  intro g
  by_cases hga : g • a = a
  · exact Or.inl hga
  · right
    -- Pick `m` fixing `a` with `m • (w • a) = g • a`.
    obtain ⟨m, hma, hmw⟩ :=
      stabilizer_transitive_on_complement (G := G) a (w • a) (g • a) hw hga
    refine ⟨m, (m * w)⁻¹ * g, hma, ?_, ?_⟩
    · -- `(m * w)⁻¹ * g` fixes `a`.
      have key : (m * w) • a = g • a := by rw [mul_smul]; exact hmw
      show ((m * w)⁻¹ * g) • a = a
      rw [mul_smul, ← key, inv_smul_smul]
    · -- `g = m * w * ((m * w)⁻¹ * g)`.
      group

end Commons.GroupTheory.GroupAction
