import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.EquivFin

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis

theorem exists_fin_monomial_sum {ι : Type} [Fintype ι] (a b : ι → ℕ) (c : ι → ℝ) :
    ∃ (m : ℕ) (p q : Fin m → ℕ) (c' : Fin m → ℝ),
      ∀ z θ : ℝ, (∑ k, c' k * z ^ (p k) * θ ^ (q k)) = ∑ i, c i * z ^ (a i) * θ ^ (b i) := by
  classical
  refine ⟨Fintype.card ι, fun k => a ((Fintype.equivFin ι).symm k),
    fun k => b ((Fintype.equivFin ι).symm k),
    fun k => c ((Fintype.equivFin ι).symm k), ?_⟩
  intro z θ
  exact Fintype.sum_equiv (Fintype.equivFin ι).symm _ _ (fun k => rfl)

end Work.FTS.GalBasis
