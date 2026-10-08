import Mathlib
import Submission.Work.Clifford.autChar_mem_Irr
import Submission.Work.Clifford.Orbit

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.conjFun_mem_Irr`

The set `Work.Clifford.Irr N` of irreducible complex characters of a normal subgroup `N ⊴ G`
is stable under the conjugation action of `G` on functions `N → ℂ`: if `θ` is irreducible
then so is `θ^g`, `θ^g(x) = θ (g * x * g⁻¹)`.

The proof is a reduction to `Work.Clifford.autChar_mem_Irr`: because `N` is normal,
`n ↦ g * n * g⁻¹` is an automorphism `conjMulEquiv N g` of `N`, and
`conjFun N g θ = autChar (conjMulEquiv N g).symm θ`, since
`(conjMulEquiv N g).symm.symm = conjMulEquiv N g`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Classical

namespace Work.Clifford

universe u

variable {G : Type u} [Group G] [Fintype G]
variable {N : Subgroup G} [N.Normal]

/-- Conjugation by `g : G` as a multiplicative equivalence of a normal subgroup `N ⊴ G`:
`n ↦ g * n * g⁻¹`, with inverse `n ↦ g⁻¹ * n * g`. -/
def conjMulEquiv (N : Subgroup G) [hN : N.Normal] (g : G) : N ≃* N where
  toFun n := ⟨g * (n : G) * g⁻¹, hN.conj_mem (n : G) n.2 g⟩
  invFun n := ⟨g⁻¹ * (n : G) * g, hN.conj_mem' (n : G) n.2 g⟩
  left_inv n := by ext; group
  right_inv n := by ext; group
  map_mul' n m := by ext; simp only [Subgroup.coe_mul]; group

/-- The conjugate `θ^g` of a function on a normal subgroup is the twist of `θ` by the
automorphism `conjMulEquiv N g`: `conjFun N g θ = autChar (conjMulEquiv N g).symm θ`. -/
theorem conjFun_eq_autChar (g : G) (θ : N → ℂ) :
    conjFun N g θ = autChar (conjMulEquiv N g).symm θ := by
  ext n
  simp only [conjFun, autChar]
  exact congrArg θ (Subtype.ext rfl)

theorem conjFun_mem_Irr {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    (g : G) {θ : N → ℂ} (hθ : θ ∈ Work.Clifford.Irr N) :
    Work.Clifford.conjFun N g θ ∈ Work.Clifford.Irr N := by
  rw [conjFun_eq_autChar]
  exact autChar_mem_Irr (conjMulEquiv N g).symm hθ

end Work.Clifford
