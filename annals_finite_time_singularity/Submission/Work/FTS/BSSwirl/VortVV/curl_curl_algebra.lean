import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.FTS.BSSwirl.CrossAux
import Submission.Work.FTS.PressureOn.Auxiliary.curlCurl_apply

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity

namespace Work.FTS.BSSwirl.VortVV

/-! ## The vector triple product identity for `crossR3`

The proof of `curl_curl_algebra` below is the algebraic identity
`∑ᵢ eᵢ × (∑ⱼ eⱼ × B eᵢ eⱼ) = ∑_k (∑ᵢ ⟪eᵢ, B e_k eᵢ⟫) e_k - ∑_k B e_k e_k`
for a symmetric bilinear `B` and an orthonormal basis `e`.  It rests on the vector triple
product formula `a × (b × c) = ⟪a,c⟫ b - ⟪b,a⟫ c`, the additivity of `×` in its last argument,
and the orthonormality of the basis. -/

/-- **The vector triple product formula** for the cross product `crossR3` of `ℝ³`:
`a × (b × c) = ⟪a,c⟫ b - ⟪b,a⟫ c`. -/
private lemma crossR3_crossR3 (a b c : Work.FTS.BSSwirl.R3) :
    Work.FTS.BSSwirl.crossR3 a (Work.FTS.BSSwirl.crossR3 b c)
      = (inner ℝ a c) • b - (inner ℝ b a) • c := by
  apply PiLp.ext; intro k
  simp only [Work.FTS.BSSwirl.crossR3_ofLp, WithLp.ofLp_sub, WithLp.ofLp_smul]
  rw [Work.FTS.BSSwirl.inner_eq_dot, Work.FTS.BSSwirl.inner_eq_dot]
  simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
    congr_fun (cross_cross_eq_smul_sub_smul' a.ofLp b.ofLp c.ofLp) k

/-- The cross product `crossR3` is additive in its second argument. -/
private lemma crossR3_sum (a : Work.FTS.BSSwirl.R3) (f : Fin 3 → Work.FTS.BSSwirl.R3) :
    Work.FTS.BSSwirl.crossR3 a (∑ j : Fin 3, f j)
      = ∑ j : Fin 3, Work.FTS.BSSwirl.crossR3 a (f j) :=
  map_sum (Work.FTS.BSSwirl.crossBilin a) f Finset.univ

/-- The standard basis `FiniteTimeSingularity.e` of `ℝ³` is orthonormal. -/
private lemma inner_e_e (i j : Fin 3) :
    inner ℝ (e i) (e j) = if i = j then 1 else 0 := by
  rw [show e i = EuclideanSpace.single i 1 from rfl, show e j = EuclideanSpace.single j 1 from rfl]
  rw [EuclideanSpace.inner_single_left, PiLp.single_apply]
  simp

/-- Orthonormality of the standard basis, in the form in which it resolves a vector `X i` out of
the sum `∑ j, ⟪e_j, e_i⟫ • X j`. -/
private lemma sum_inner_e_smul (X : Fin 3 → Work.FTS.BSSwirl.R3) (i : Fin 3) :
    (∑ j : Fin 3, (inner ℝ (e j) (e i)) • X j) = X i := by
  rw [Finset.sum_eq_single i]
  · rw [show inner ℝ (e i) (e i) = 1 from by simpa using inner_e_e i i]
    exact one_smul ℝ (X i)
  · intro j _ hj
    rw [show inner ℝ (e j) (e i) = 0 from by rw [inner_e_e j i]; simp [hj]]
    exact zero_smul ℝ (X j)
  · intro h; exact absurd (Finset.mem_univ i) h

theorem curl_curl_algebra
    (B : Work.FTS.BSSwirl.R3 →L[ℝ] Work.FTS.BSSwirl.R3 →L[ℝ] Work.FTS.BSSwirl.R3)
    (hB : ∀ u v, B u v = B v u) :
    (∑ i : Fin 3, Work.FTS.BSSwirl.crossR3 (FiniteTimeSingularity.e i)
        (∑ j : Fin 3, Work.FTS.BSSwirl.crossR3 (FiniteTimeSingularity.e j)
          (B (FiniteTimeSingularity.e i) (FiniteTimeSingularity.e j))))
      = (∑ k : Fin 3, (∑ i : Fin 3, inner ℝ (FiniteTimeSingularity.e i)
            (B (FiniteTimeSingularity.e k) (FiniteTimeSingularity.e i)))
              • FiniteTimeSingularity.e k)
        - ∑ k : Fin 3, B (FiniteTimeSingularity.e k) (FiniteTimeSingularity.e k) := by
  -- The value at a fixed `i` of the outer term: expand the inner cross product with the vector
  -- triple product formula and use orthonormality to kill the diagonal part.
  have key : ∀ i : Fin 3,
      Work.FTS.BSSwirl.crossR3 (e i)
        (∑ j : Fin 3, Work.FTS.BSSwirl.crossR3 (e j) (B (e i) (e j)))
        = (∑ j : Fin 3, (inner ℝ (e i) (B (e i) (e j))) • e j) - B (e i) (e i) := by
    intro i
    calc Work.FTS.BSSwirl.crossR3 (e i)
          (∑ j : Fin 3, Work.FTS.BSSwirl.crossR3 (e j) (B (e i) (e j)))
        = ∑ j : Fin 3, Work.FTS.BSSwirl.crossR3 (e i)
            (Work.FTS.BSSwirl.crossR3 (e j) (B (e i) (e j))) := crossR3_sum _ _
      _ = ∑ j : Fin 3, ((inner ℝ (e i) (B (e i) (e j))) • e j
            - (inner ℝ (e j) (e i)) • B (e i) (e j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [crossR3_crossR3]
      _ = (∑ j : Fin 3, (inner ℝ (e i) (B (e i) (e j))) • e j)
            - ∑ j : Fin 3, (inner ℝ (e j) (e i)) • B (e i) (e j) :=
          Finset.sum_sub_distrib _ _
      _ = (∑ j : Fin 3, (inner ℝ (e i) (B (e i) (e j))) • e j) - B (e i) (e i) := by
          rw [sum_inner_e_smul (fun j => B (e i) (e j)) i]
  -- Reassembling: interchange the two sums and use the symmetry of `B`.
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3, (inner ℝ (e i) (B (e i) (e j))) • e j)
      = ∑ k : Fin 3, (∑ i : Fin 3, inner ℝ (e i) (B (e k) (e i))) • e k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB (e i) (e j)]
  calc (∑ i : Fin 3, Work.FTS.BSSwirl.crossR3 (e i)
          (∑ j : Fin 3, Work.FTS.BSSwirl.crossR3 (e j) (B (e i) (e j))))
      = ∑ i : Fin 3, ((∑ j : Fin 3, (inner ℝ (e i) (B (e i) (e j))) • e j)
            - B (e i) (e i)) := Finset.sum_congr rfl fun i _ => key i
    _ = (∑ i : Fin 3, ∑ j : Fin 3, (inner ℝ (e i) (B (e i) (e j))) • e j)
          - ∑ i : Fin 3, B (e i) (e i) := Finset.sum_sub_distrib _ _
    _ = (∑ k : Fin 3, (∑ i : Fin 3, inner ℝ (e i) (B (e k) (e i))) • e k)
          - ∑ k : Fin 3, B (e k) (e k) := by rw [hsum]

end Work.FTS.BSSwirl.VortVV
