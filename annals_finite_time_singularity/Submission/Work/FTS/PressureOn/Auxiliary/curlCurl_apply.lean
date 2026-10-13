import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

/-- The coordinate form of the identity.  `A i k` is the vector `S i k` of the main statement,
written in coordinates, so that `crossProduct` (which acts on `Fin 3 → ℝ`) applies directly.

For a tensor symmetric in its first two indices the `j`-th component of the "trace"
`∑ᵢ A i i` equals the trace `∑ᵢ (A i j) i` minus the `j`-th component of the double curl
`∑_k e_k × (∑_i e_i × A i k)`. -/
theorem curlCurl_core (A : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (h : ∀ i k l : Fin 3, A i k l = A k i l) (j : Fin 3) :
    (∑ i : Fin 3, A i i j)
      = (∑ i : Fin 3, A i j i)
        - ∑ k : Fin 3, crossProduct (Pi.single k (1 : ℝ) : Fin 3 → ℝ)
            (fun l : Fin 3 => ∑ i : Fin 3,
              crossProduct (Pi.single i (1 : ℝ) : Fin 3 → ℝ) (A i k) l) j := by
  fin_cases j <;>
    simp only [Fin.sum_univ_three] <;>
    simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Pi.single_eq_same, Pi.single_eq_of_ne] <;>
    (try ring_nf) <;>
    simp only [h 1 0, h 2 0, h 2 1] <;>
    ring

theorem curlCurl_apply (S : Fin 3 → Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hsymm : ∀ i k l : Fin 3, (S i k) l = (S k i) l) (j : Fin 3) :
    (∑ i : Fin 3, (S i i) j)
      = (∑ i : Fin 3, (S i j) i)
        - ∑ k : Fin 3, (crossProduct (WithLp.ofLp (FiniteTimeSingularity.e k))
            (fun l : Fin 3 => ∑ i : Fin 3,
              crossProduct (WithLp.ofLp (FiniteTimeSingularity.e i))
                (WithLp.ofLp (S i k)) l)) j :=
  curlCurl_core (fun i k l => (S i k).ofLp l) hsymm j

end Work.FTS.PressureOn.Auxiliary
