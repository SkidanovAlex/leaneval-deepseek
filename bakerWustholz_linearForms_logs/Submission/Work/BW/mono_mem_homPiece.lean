import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.subgroup_rayDegAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

/-- The multidegree weight of the `i`-th factor is the basis vector `eᵢ = Finsupp.single i 1`
(both `X_{i0}` and `X_{i1}` have weight `eᵢ`), and the `i`-th coordinate of `d` is `d i`, so `d`
is the `ℕ`-linear combination `∑ᵢ dᵢ · eᵢ`. -/
private lemma sum_smul_single_eq (N : ℕ) (d : Fin (N + 1) →₀ ℕ) :
    (∑ i : Fin (N + 1), d i • (Finsupp.single i 1 : Fin (N + 1) →₀ ℕ)) = d := by
  ext j
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Finsupp.single_eq_of_ne ?_]
    · simp
    · exact fun h => hij h.symm
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The monomial `∏ᵢ X_{i,1}^{bᵢ}X_{i,0}^{dᵢ-bᵢ}` is multihomogeneous of multidegree `d` whenever `bᵢ ≤ dᵢ` for all `i` (each factor is weighted homogeneous of weight `bᵢ·eᵢ + (dᵢ-bᵢ)·eᵢ = dᵢ·eᵢ`). -/
theorem mono_mem_homPiece (N : ℕ) (d : Fin (N + 1) →₀ ℕ) (b : Fin (N + 1) → ℕ)
    (hb : ∀ i, b i ≤ d i) : mono N d b ∈ homPiece N d := by
  rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
  -- Each factor `X_{i,1}^{bᵢ} · X_{i,0}^{dᵢ-bᵢ}` has multidegree `(bᵢ + (dᵢ - bᵢ)) · eᵢ = dᵢ · eᵢ`.
  have hprod : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      ((∏ i : Fin (N + 1),
        MvPolynomial.X (i,1) ^ (b i) * MvPolynomial.X (i,0) ^ (d i - b i)) : MR N)
      (∑ i : Fin (N + 1), d i • (Finsupp.single i 1 : Fin (N + 1) →₀ ℕ)) :=
    MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
      (fun i : Fin (N + 1) =>
        (MvPolynomial.X (i,1) ^ (b i) * MvPolynomial.X (i,0) ^ (d i - b i) : MR N))
      (fun i : Fin (N + 1) => d i • (Finsupp.single i 1 : Fin (N + 1) →₀ ℕ))
      (by
        intro i _
        have hX1 : MvPolynomial.IsWeightedHomogeneous (mdeg N)
            ((MvPolynomial.X (i,1) : MR N) ^ (b i))
            (b i • (Finsupp.single i 1 : Fin (N + 1) →₀ ℕ)) := by
          simpa [mdeg] using
            (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (mdeg N) (i,1)).pow (b i)
        have hX0 : MvPolynomial.IsWeightedHomogeneous (mdeg N)
            ((MvPolynomial.X (i,0) : MR N) ^ (d i - b i))
            ((d i - b i) • (Finsupp.single i 1 : Fin (N + 1) →₀ ℕ)) := by
          simpa [mdeg] using
            (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (mdeg N) (i,0)).pow (d i - b i)
        have h := hX1.mul hX0
        rw [← add_nsmul, Nat.add_sub_of_le (hb i)] at h
        exact h)
  rw [sum_smul_single_eq] at hprod
  simpa [mono] using hprod

end Work.BW
