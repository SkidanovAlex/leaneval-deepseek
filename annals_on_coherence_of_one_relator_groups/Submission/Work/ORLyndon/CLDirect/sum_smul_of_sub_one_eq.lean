import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs

namespace Work.ORLyndon.CLDirect

open MonoidAlgebra

section Aux

variable {X : Type*} {K : Type*} [Field K]

/-- Additivity of the fundamental-identity functional `E ↦ E.sum (fun x d => d * (of x - 1))`. -/
private theorem foxVecSum_add (E F : X →₀ MonoidAlgebra K (FreeGroup X)) :
    (E + F).sum (fun x d => d * (MonoidAlgebra.of K (FreeGroup X) (FreeGroup.of x) - 1)) =
      E.sum (fun x d => d * (MonoidAlgebra.of K (FreeGroup X) (FreeGroup.of x) - 1)) +
      F.sum (fun x d => d * (MonoidAlgebra.of K (FreeGroup X) (FreeGroup.of x) - 1)) := by
  rw [Finsupp.sum_add_index'
      (h := fun x d => d * (MonoidAlgebra.of K (FreeGroup X) (FreeGroup.of x) - 1))
      (fun i => by rw [zero_mul]) (fun i b1 b2 => by rw [add_mul])]

/-- `K`-homogeneity of the fundamental-identity functional `E ↦ E.sum (fun x d => d * (of x - 1))`. -/
private theorem foxVecSum_smul (E : X →₀ MonoidAlgebra K (FreeGroup X)) (b : K) :
    (b • E).sum (fun x d => d * (MonoidAlgebra.of K (FreeGroup X) (FreeGroup.of x) - 1)) =
      b • E.sum (fun x d => d * (MonoidAlgebra.of K (FreeGroup X) (FreeGroup.of x) - 1)) := by
  rw [Finsupp.sum_smul_index' (g := E) (b := b)
      (h := fun x d => d * (MonoidAlgebra.of K (FreeGroup X) (FreeGroup.of x) - 1))
      (fun i => by rw [zero_mul])]
  rw [Finsupp.smul_sum]
  congr 1
  funext x c
  rw [smul_mul_assoc]

end Aux

/-- The fundamental-identity expansion of `Σ c_i (ρ_i - 1)`. Sketch: rewrite each `of (ρ i) - 1` with `← Work.ORLyndon.Fox.fundamental_identity (ρ i)`; the map `E ↦ E.sum (fun x d => d * (of x - 1))` is additive and `K`-homogeneous (`Finsupp.sum_finset_sum_index`, `Finsupp.sum_smul_index'`, `smul_mul_assoc`, `Finsupp.smul_sum`), zero terms by `zero_mul`. -/
theorem sum_smul_of_sub_one_eq {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (ι : Type) [Fintype ι] (ρ : ι → FreeGroup X) (c : ι → K) :
    (∑ i, c i • (MonoidAlgebra.of K (FreeGroup X) (ρ i) - 1)) =
      (∑ i, c i • Work.ORLyndon.foxFD (K := K) (ρ i)).sum
        (fun x d => d * (MonoidAlgebra.of K (FreeGroup X) (FreeGroup.of x) - 1)) := by
  classical
  have key : ∀ s : Finset ι,
      (s.sum fun i => c i • Work.ORLyndon.foxFD (K := K) (ρ i)).sum
        (fun x d => d * (MonoidAlgebra.of K (FreeGroup X) (FreeGroup.of x) - 1)) =
      s.sum fun i => c i • (MonoidAlgebra.of K (FreeGroup X) (ρ i) - 1) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [foxVecSum_add, foxVecSum_smul, ih, Work.ORLyndon.Fox.fundamental_identity]
  exact (key Finset.univ).symm

end Work.ORLyndon.CLDirect
