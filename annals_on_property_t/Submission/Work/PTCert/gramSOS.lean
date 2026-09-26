import Mathlib
import Submission.Work.PTCert.Math
import Submission.Work.RouteB.StarStructure
import Submission.Helpers

/-!
# (Q1) Gram forms of positive semidefinite matrices are sums of hermitian squares

`GramSOS` (declared in `Submission/Work/PTCert/Math.lean`) states: for a group `G`, a finite
family `f : ι → G` and a positive semidefinite matrix `U : Matrix ι ι ℝ`, the element

  `gramForm f U = Σ_{i,j} U i j • of ((f i)⁻¹ * f j)`

of the group ring `ℝG` is a sum of hermitian squares.

## Proof

`U ⪰ 0` gives `U = Σ_k vecMulVec (v k) (v k)`, i.e. `U i j = Σ_k v k i * v k j`
(`Matrix.posSemidef_iff_eq_sum_vecMulVec`).  With the "seed"

  `ξ k = Σ_i v k i • of (f i)`,

`star` acts on a real linear combination of `of`'s by inverting the group elements
(`star_sum_smul_of` below), so

  `star (ξ k) * ξ k = Σ_i Σ_j (v k i * v k j) • of ((f i)⁻¹ * f j)`

(`star_smul_of_mul_sum_smul_of`: bilinearity and `map_mul`).  Reordering the triple sum with
`Finset.sum_comm`/`Finset.sum_smul` telescopes the sum over `k` back into `U i j`, so

  `gramForm f U = Σ_k star (ξ k) * ξ k`,

a sum of hermitian squares by `isSOS_of_fintype`.
-/

namespace Work.PTCert

open Submission.PTCert Submission.RouteB Submission.Helpers

open scoped BigOperators

variable {G : Type*} [Group G]

/-- `star` of a real linear combination of group elements inverts the group elements. -/
lemma star_sum_smul_of {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → G) :
    star (∑ i ∈ s, c i • MonoidAlgebra.of ℝ G (f i))
      = ∑ i ∈ s, c i • MonoidAlgebra.of ℝ G ((f i)⁻¹) := by
  rw [_root_.star_sum]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [Submission.Helpers.star_smul, Submission.Helpers.star_of])

/-- Bilinearity of the product in the group ring, for real linear combinations of group
elements: the `of`'s multiply by `map_mul`, and the scalars by `smul_mul_smul`. -/
lemma sum_smul_of_mul_sum_smul_of {ι : Type*} (s t : Finset ι) (c d : ι → ℝ) (f : ι → G) :
    (∑ i ∈ s, c i • MonoidAlgebra.of ℝ G ((f i)⁻¹)) *
        (∑ j ∈ t, d j • MonoidAlgebra.of ℝ G (f j))
      = ∑ i ∈ s, ∑ j ∈ t, (c i * d j) • MonoidAlgebra.of ℝ G ((f i)⁻¹ * f j) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_mul_smul, ← map_mul]

/-- **(Q1) Gram forms of PSD matrices are sums of hermitian squares.** -/
theorem gramSOS : GramSOS := by
  intro G _ _ ι _ f U hU
  classical
  -- `U` is a Gram matrix
  obtain ⟨n, v, hv⟩ := (Matrix.posSemidef_iff_eq_sum_vecMulVec (𝕜 := ℝ)).1 hU
  have hUV : ∀ i j, U i j = ∑ k : Fin n, v k i * v k j := by
    intro i j
    have h := congrFun (congrFun hv i) j
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using h
  -- the seeds `ξ k = Σ_i v k i • of (f i)`
  have hstar : ∀ k : Fin n, star (∑ i, v k i • MonoidAlgebra.of ℝ G (f i))
      = ∑ i, v k i • MonoidAlgebra.of ℝ G ((f i)⁻¹) := fun k => by
    rw [_root_.star_sum]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [Submission.Helpers.star_smul, Submission.Helpers.star_of])
  have hterm : ∀ k : Fin n,
      star (∑ i, v k i • MonoidAlgebra.of ℝ G (f i))
          * (∑ i, v k i • MonoidAlgebra.of ℝ G (f i))
      = ∑ i, ∑ j, (v k i * v k j) • MonoidAlgebra.of ℝ G ((f i)⁻¹ * f j) := fun k => by
    rw [hstar k, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_mul_smul, ← map_mul]
  -- expand `gramForm`
  have hU' : gramForm f U
      = ∑ i, ∑ j, (∑ k : Fin n, v k i * v k j) • MonoidAlgebra.of ℝ G ((f i)⁻¹ * f j) := by
    simp only [gramForm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hUV i j]
  -- reorder the triple sum
  have h2 : (∑ k : Fin n, ∑ i, ∑ j, (v k i * v k j) • MonoidAlgebra.of ℝ G ((f i)⁻¹ * f j))
      = ∑ i, ∑ j, (∑ k : Fin n, v k i * v k j) • MonoidAlgebra.of ℝ G ((f i)⁻¹ * f j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_smul]
  rw [hU', ← h2, ← Finset.sum_congr rfl (fun k _ => hterm k)]
  exact isSOS_of_fintype _

end Work.PTCert
