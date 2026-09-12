import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators
open scoped RealInnerProductSpace

namespace Commons.Analysis.InnerProductSpace

lemma orthonormalBasis_normSq_sum_smul {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (s : Finset ι) (c : ι → ℝ) :
    ‖s.sum (fun i => c i • (b i : E))‖ ^ 2 = s.sum (fun i => (c i) ^ 2) := by
  classical
  calc
    ‖s.sum (fun i => c i • (b i : E))‖ ^ 2
        = inner ℝ (s.sum (fun i => c i • (b i : E))) (s.sum (fun i => c i • (b i : E))) := by
            rw [← real_inner_self_eq_norm_sq]
    _ = inner ℝ (∑ i ∈ s, c i • (b i : E)) (∑ i ∈ s, c i • (b i : E)) := by rfl
    _ = ∑ i ∈ s, c i * c i := Orthonormal.inner_sum b.orthonormal c c s
    _ = s.sum (fun i => (c i) ^ 2) := by
        simp [pow_two]

end Commons.Analysis.InnerProductSpace