import Mathlib
import Submission.Commons.Combinatorics.Transference.poly_lemma_abstract

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- The dual function is homogeneous of degree `2^d - 1`:
`𝒟(c·F) = c^{2^d - 1}·𝒟F`. -/
theorem davg_smul {p : ℕ} [Fact p.Prime] {d : ℕ} (c : ℝ) (F : ZMod p → ℝ) :
    davg d (fun x => c * F x) = fun x => c ^ (2 ^ d - 1) * davg d F x := by
  have hcard : ((Finset.univ.erase (0 : Fin d → Bool)) : Finset (Fin d → Bool)).card
      = 2 ^ d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool]
  funext x
  rw [davg, davg]
  have h1 : (∑ h : Fin d → ZMod p, ∏ ω ∈ Finset.univ.erase (0 : Fin d → Bool),
        c * F (x + ∑ i, (if ω i then h i else 0)))
      = c ^ (2 ^ d - 1) * ∑ h : Fin d → ZMod p,
          ∏ ω ∈ Finset.univ.erase (0 : Fin d → Bool),
            F (x + ∑ i, (if ω i then h i else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
  rw [h1]
  ring

end Commons.Combinatorics.Transference
