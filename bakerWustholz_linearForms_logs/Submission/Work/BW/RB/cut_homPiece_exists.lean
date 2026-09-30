import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.RB

open MvPolynomial

/-- The monomial `∏ᵢ X_{i0}^{cᵢ}` is multihomogeneous of multidegree `∑ᵢ cᵢ • eᵢ`. -/
private lemma prod_X0_isWeightedHomogeneous {N : ℕ} (c : Fin (N + 1) → ℕ) :
    MvPolynomial.IsWeightedHomogeneous (mdeg N)
      (∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (c i))
      (∑ i : Fin (N + 1), c i • mdeg N (i, 0)) :=
  MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun i : Fin (N + 1) => (MvPolynomial.X (i, 0) : MR N) ^ (c i))
    (fun i : Fin (N + 1) => c i • mdeg N (i, 0))
    (fun i _ => (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (mdeg N) (i, 0)).pow (c i))

/-- Evaluating the multidegrees `c i • e_i` at a coordinate `j` returns `c j`. -/
private lemma sum_smul_mdeg_apply {N : ℕ} (c : Fin (N + 1) → ℕ) (j : Fin (N + 1)) :
    (∑ i : Fin (N + 1), c i • mdeg N (i, 0)) j = c j := by
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, mdeg, Finsupp.single_apply, smul_ite, smul_zero]
  simp

theorem cut_homPiece_exists {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (r s : Ideal (MR N)) (hr : r.IsPrime) (hsm : MultiHom N s) (hlt : r < s)
    (havr : ∀ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ∉ r) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ P : MR N, P ∈ homPiece N (k • D) ∧ P ∈ s ∧ P ∉ r := by
  classical
  -- Step 1: `s` is strictly larger than `r`, so `s` has an element outside `r`.
  have hsle : ¬ s ≤ r := (lt_iff_le_not_ge.mp hlt).2
  obtain ⟨Q, hQs, hQr⟩ : ∃ Q : MR N, Q ∈ s ∧ Q ∉ r := by
    by_contra h
    refine hsle (fun x hx => ?_)
    by_contra hxr
    exact h ⟨x, hx, hxr⟩
  -- Step 2: since `s` is multihomogeneous, one multihomogeneous component of `Q` is in `s \ r`.
  have hcomp : ∃ d : Fin (N + 1) →₀ ℕ,
      MvPolynomial.weightedHomogeneousComponent (mdeg N) d Q ∉ r := by
    by_contra h
    have hall : ∀ d : Fin (N + 1) →₀ ℕ,
        MvPolynomial.weightedHomogeneousComponent (mdeg N) d Q ∈ r := by
      intro d
      by_contra hd
      exact h ⟨d, hd⟩
    have hsupp : Function.support
        (fun m => MvPolynomial.weightedHomogeneousComponent (mdeg N) m Q) ⊆
        ↑(Q.support.image (fun e => Finsupp.weight (mdeg N) e)) := by
      intro m hm
      rw [Function.mem_support] at hm
      by_contra hmem
      refine hm (MvPolynomial.weightedHomogeneousComponent_eq_zero' m Q ?_)
      intro e he hwe
      exact hmem (Finset.mem_image.mpr ⟨e, he, hwe⟩)
    have hsum : (∑ᶠ m, MvPolynomial.weightedHomogeneousComponent (mdeg N) m Q) ∈ r := by
      rw [finsum_eq_sum_of_support_subset
        (fun m => MvPolynomial.weightedHomogeneousComponent (mdeg N) m Q) hsupp]
      exact Ideal.sum_mem r (fun m _ => hall m)
    rw [MvPolynomial.sum_weightedHomogeneousComponent] at hsum
    exact hQr hsum
  obtain ⟨d0, hd0notr⟩ := hcomp
  have hd0s : MvPolynomial.weightedHomogeneousComponent (mdeg N) d0 Q ∈ s := hsm Q hQs d0
  have hd0hom : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      (MvPolynomial.weightedHomogeneousComponent (mdeg N) d0 Q) d0 :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous (w := mdeg N) d0 Q
  -- Step 3: choose the ray degree `k` and the correcting monomial.
  set k : ℕ := 1 + ∑ i : Fin (N + 1), d0 i with hk
  have hk1 : 1 ≤ k := by omega
  have hd0le : ∀ i, d0 i ≤ k := by
    intro i
    have h1 : d0 i ≤ ∑ j : Fin (N + 1), d0 j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hkD : ∀ i, d0 i ≤ k * D i := by
    intro i
    refine le_trans (hd0le i) ?_
    simpa [Nat.mul_one] using Nat.mul_le_mul_left k (hD i)
  set a : Fin (N + 1) → ℕ := fun i => k * D i - d0 i with ha
  set M : MR N := ∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (a i) with hM
  have hMhom : MvPolynomial.IsWeightedHomogeneous (mdeg N) M
      (∑ i : Fin (N + 1), a i • mdeg N (i, 0)) := by
    rw [hM]
    exact prod_X0_isWeightedHomogeneous a
  have hsum_eq : d0 + (∑ i : Fin (N + 1), a i • mdeg N (i, 0)) = k • D := by
    ext j
    have h1 : (∑ i : Fin (N + 1), a i • mdeg N (i, 0)) j = k * D j - d0 j := by
      rw [sum_smul_mdeg_apply a j, ha]
    rw [Finsupp.add_apply, h1, Finsupp.smul_apply]
    simp only [nsmul_eq_mul, Nat.cast_id]
    exact Nat.add_sub_cancel' (hkD j)
  have hPhom : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      (MvPolynomial.weightedHomogeneousComponent (mdeg N) d0 Q * M) (k • D) := by
    have h := hd0hom.mul hMhom
    rwa [hsum_eq] at h
  -- Step 4: the monomial `M` is not in `r` (its factors `X_{i0}` are not, `r` is prime).
  have hMnotr : M ∉ r := by
    intro hmem
    rw [hM] at hmem
    rw [hr.prod_mem_iff] at hmem
    obtain ⟨i, -, hi⟩ := hmem
    exact (fun hx => havr i (hr.mem_of_pow_mem (a i) hx)) hi
  refine ⟨k, hk1, MvPolynomial.weightedHomogeneousComponent (mdeg N) d0 Q * M, ?_, ?_, ?_⟩
  · rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact hPhom
  · have h := Ideal.mul_mem_left s M hd0s
    rwa [mul_comm] at h
  · intro hmem
    rcases hr.mem_or_mem hmem with h | h
    · exact hd0notr h
    · exact hMnotr h

end Work.BW.RB
