import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.Lat.span_pair_lattice

/-!
# Hadamard bound for the ℤ-span of two independent integer vectors

The covolume `detL` of the rank-`2` lattice `span_ℤ {v 0, v 1}` spanned by two `ℤ`-linearly
independent integer vectors is at most the product `‖v 0‖ ‖v 1‖` of their Euclidean norms.

This is the Hadamard bound `detL = √(det Gram) = √(‖v 0‖²‖v 1‖² - ⟨v 0, v 1⟩²) ≤ ‖v 0‖ ‖v 1‖`,
obtained from `Work.HP.Lat.detL_span_range_le`, which says exactly this for the family
`![v 0, v 1]`; here the argument is a family `v : Fin 2 → ι → ℤ`, which is `![v 0, v 1]`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.MDEstimates

theorem detL_span_fin2_le {ι : Type*} [Fintype ι] (v : Fin 2 → (ι → ℤ))
    (hv : LinearIndependent ℤ v) :
    Work.HP.detL (Submodule.span ℤ (Set.range v)) ≤
      Work.HP.eNorm (v 0) * Work.HP.eNorm (v 1) := by
  classical
  -- `v` is the pair `![v 0, v 1]`.
  have hv' : ![v 0, v 1] = v := by
    funext i
    fin_cases i <;> simp
  have hrange : Set.range v = Set.range ![v 0, v 1] := by rw [hv']
  rw [hrange]
  exact Work.HP.Lat.detL_span_range_le (v 0) (v 1) (by rwa [hv'])

end Work.HP.MDEstimates
