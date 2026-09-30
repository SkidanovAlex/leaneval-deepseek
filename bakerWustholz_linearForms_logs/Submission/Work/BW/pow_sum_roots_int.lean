import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- The sum of the `m`-th powers of the complex roots of a monic integer polynomial is an
integer (a power sum of the roots, i.e. a symmetric function of the roots with integer
coefficients).  This is proved by evaluating the symmetric-polynomial identity
`Polynomial.leadingCoeff_pow_natDegree_smul_sum_map_aroots_aeval_mem_range_algebraMap`
at the roots: since `P` is monic, the sum of `q.aeval` over the roots lies in the base ring
`ℤ` for any `q : ℤ[X]`, and taking `q = X ^ m` gives the claim. -/
theorem pow_sum_roots_int (P : Polynomial ℤ) (hP : P.Monic) (m : ℕ) :
    ∃ c : ℤ, ((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ m)).sum = (c : ℂ) := by
  have hsplit : (P.map (algebraMap ℤ ℂ)).Splits := IsAlgClosed.splits _
  have h :=
    Polynomial.leadingCoeff_pow_natDegree_smul_sum_map_aroots_aeval_mem_range_algebraMap
      (R := ℤ) (A := ℂ) P (Polynomial.X ^ m) hsplit
  rw [hP.leadingCoeff, one_pow, one_smul] at h
  have h' : ((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ m)).sum
      ∈ Set.range (algebraMap ℤ ℂ) := by
    simpa [Polynomial.aroots_def, Polynomial.aeval_X] using h
  obtain ⟨c, hc⟩ := h'
  exact ⟨c, hc.symm⟩

end Work.BW
