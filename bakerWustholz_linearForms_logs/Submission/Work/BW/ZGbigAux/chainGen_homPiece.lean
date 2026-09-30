import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.transl_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Every generator of Philippon's chain ideal `I_r` is multihomogeneous of multidegree `D`

`chainGen w θ D P A B` is the set of generators `τ_{sγ} δ^t P^h` (`s ≤ A`, `|t| ≤ B`) of
Philippon's ideal `I_r` (BW §5.1).  This file proves `chainGen_homPiece`: each of these generators
lies in the multidegree-`fsD D` piece `homPiece N (fsD D)` of the homogeneous coordinate ring
`MR N` of `(P¹)^{N+1}`, i.e. every generator is multihomogeneous of the *single* multidegree `D`.

The three ingredients are

* `homog_mem_homPiece`: the homogenisation `P^h` of `P` to multidegree `D` is multihomogeneous of
  multidegree `D`, as soon as `degreeOf i P ≤ D i` for all `i` (so that the truncated subtractions
  `D i - s i` really complete the exponent `s i` to `D i`);
* `applyH_mem_homPiece`: the iterated invariant derivations `δ^t = ∏_k (derH (w k))^{t k}`
  preserve every multidegree piece.  This is where the `G_a`-direction `X_{0,0} ∂_{0,1}` needs
  care: `derH v` is a sum of terms `X_{i,0} ∂_{i,1}` and `X_{i+1,1} ∂_{i+1,1}`, i.e. of a
  derivative that drops the weight `e_i` of the factor `i` followed by the multiplication by a
  variable of exactly that weight, so the multidegree is restored;
* `transl_basic` (already in the library): the translation `τ_{sγ}` preserves every multidegree
  piece.
-/

namespace Work.BW.ZGbigAux

/-- A right fold of maps preserving a set stays in the set. -/
private lemma foldr_mem {N : ℕ} {α : Type*} (f : α → MR N → MR N) (S : Set (MR N))
    (hf : ∀ a, ∀ x ∈ S, f a x ∈ S) (l : List α) {x : MR N} (hx : x ∈ S) :
    l.foldr f x ∈ S := by
  induction l with
  | nil => exact hx
  | cons a l ih => rw [List.foldr_cons]; exact hf a _ ih

/-- The multidegree `a • eᵢ + b • eᵢ` is `(a+b) • eᵢ`. -/
private lemma smul_single_add {N : ℕ} (i : Fin (N + 1)) (a b : ℕ) :
    a • (Finsupp.single i 1 : Fin (N + 1) →₀ ℕ) + b • Finsupp.single i 1
      = Finsupp.single i (a + b) := by
  rw [← add_smul, Finsupp.smul_single]
  simp

/-- Pointwise application of `fsD`. -/
private lemma fsD_apply {N : ℕ} (D : Fin (N + 1) → ℕ) (j : Fin (N + 1)) :
    (fsD D) j = D j :=
  congrFun (Finsupp.coe_equivFunOnFinite_symm D) j

/-- `fsD D` is the sum of the single multidegrees `D i • eᵢ`. -/
private lemma sum_single_fsD {N : ℕ} (D : Fin (N + 1) → ℕ) :
    (∑ i : Fin (N + 1), Finsupp.single i (D i)) = fsD D := by
  apply Finsupp.ext
  intro j
  rw [fsD_apply, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single j]
  · rw [Finsupp.single_eq_same]
  · intro b _ hb
    rw [Finsupp.single_eq_of_ne (Ne.symm hb)]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The homogenisation of `P` to multidegree `D` is multihomogeneous of multidegree `D` (only
true when `P` is of multidegree `≤ D`). -/
private lemma homog_mem_homPiece {N : ℕ} (D : Fin (N + 1) → ℕ)
    (P : MvPolynomial (Fin (N + 1)) ℂ) (hdeg : ∀ i, P.degreeOf i ≤ D i) :
    homog D P ∈ homPiece N (fsD D) := by
  rw [← sum_single_fsD D, homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule, homog]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ ?_
  intro s hs
  refine MvPolynomial.IsWeightedHomogeneous.C_mul ?_ _
  refine MvPolynomial.IsWeightedHomogeneous.prod _ _ _ ?_
  intro i _
  have hs' : s i ≤ D i := (MvPolynomial.degreeOf_le_iff.mp (hdeg i)) s hs
  have h1 : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      ((MvPolynomial.X ((i : Fin (N + 1)), (1 : Fin 2)) : MR N) ^ (s i))
      (s i • (Finsupp.single i 1 : Fin (N + 1) →₀ ℕ)) := by
    simpa [mdeg] using
      ((MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (mdeg N)
        ((i : Fin (N + 1)), (1 : Fin 2))).pow (s i))
  have h0 : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      ((MvPolynomial.X ((i : Fin (N + 1)), (0 : Fin 2)) : MR N) ^ (D i - s i))
      ((D i - s i) • (Finsupp.single i 1 : Fin (N + 1) →₀ ℕ)) := by
    simpa [mdeg] using
      ((MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (mdeg N)
        ((i : Fin (N + 1)), (0 : Fin 2))).pow (D i - s i))
  have hwt : s i • (Finsupp.single i 1 : Fin (N + 1) →₀ ℕ)
      + (D i - s i) • Finsupp.single i 1 = Finsupp.single i (D i) := by
    rw [smul_single_add, Nat.add_sub_cancel' hs']
  have h := h1.mul h0
  rwa [hwt] at h

/-- `X_{0,0} ∂/∂X_{0,1}` maps a monomial to a monomial of the same multidegree: the two variables
of the `0`-th `P¹` factor carry the same weight, so the derivative `∂/∂X_{0,1}` drops the weight
`e_0` and the multiplication by `X_{0,0}` adds it back. -/
private lemma X00_pderiv01_monomial_isWH {N : ℕ} (m : (Fin (N + 1) × Fin 2) →₀ ℕ) (c : ℂ) :
    MvPolynomial.IsWeightedHomogeneous (mdeg N)
      (MvPolynomial.X ((0 : Fin (N + 1)), (0 : Fin 2)) *
        MvPolynomial.pderiv ((0 : Fin (N + 1)), (1 : Fin 2)) (MvPolynomial.monomial m c))
      (Finsupp.weight (mdeg N) m) := by
  by_cases h : m ((0 : Fin (N + 1)), (1 : Fin 2)) = 0
  · rw [MvPolynomial.pderiv_monomial, h, Nat.cast_zero, mul_zero,
      MvPolynomial.monomial_zero, mul_zero]
    exact MvPolynomial.isWeightedHomogeneous_zero ℂ (mdeg N) _
  · have hX : MvPolynomial.X ((0 : Fin (N + 1)), (0 : Fin 2)) =
        MvPolynomial.monomial (Finsupp.single ((0 : Fin (N + 1)), (0 : Fin 2)) 1) (1 : ℂ) := by
      simpa using (MvPolynomial.X_pow_eq_monomial (R := ℂ)
        (n := ((0 : Fin (N + 1)), (0 : Fin 2))) (e := 1))
    rw [MvPolynomial.pderiv_monomial, hX, MvPolynomial.monomial_mul_monomial, one_mul]
    refine MvPolynomial.isWeightedHomogeneous_monomial _ _ _ ?_
    have hwe : Finsupp.weight (mdeg N) (Finsupp.single ((0 : Fin (N + 1)), (0 : Fin 2)) 1) =
        Finsupp.weight (mdeg N) (Finsupp.single ((0 : Fin (N + 1)), (1 : Fin 2)) 1) := by
      rw [Finsupp.weight_single, Finsupp.weight_single]
      simp [mdeg]
    have h1 : Finsupp.weight (mdeg N)
          (m - Finsupp.single ((0 : Fin (N + 1)), (1 : Fin 2)) 1)
        + Finsupp.weight (mdeg N) (Finsupp.single ((0 : Fin (N + 1)), (1 : Fin 2)) 1)
        = Finsupp.weight (mdeg N) m := by
      rw [← map_add, Finsupp.sub_add_single_one_cancel h]
    rw [map_add, hwe, add_comm (Finsupp.weight (mdeg N)
      (Finsupp.single ((0 : Fin (N + 1)), (1 : Fin 2)) 1)), h1]

/-- `derH` is additive. -/
private lemma derH_add {N : ℕ} (v : Fin (N + 1) → ℂ) (a b : MR N) :
    derH v (a + b) = derH v a + derH v b := by
  simp only [derH, map_add, mul_add, Finset.sum_add_distrib]
  abel

/-- The invariant derivation `derH v` preserves every multidegree piece. -/
private lemma derH_mem_homPiece {N : ℕ} (v : Fin (N + 1) → ℂ) {d : Fin (N + 1) →₀ ℕ}
    {F : MR N} (hF : F ∈ homPiece N d) : derH v F ∈ homPiece N d := by
  rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule] at hF ⊢
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
    rw [show derH v (0 : MR N) = 0 from by simp [derH]]
    exact MvPolynomial.isWeightedHomogeneous_zero ℂ (mdeg N) d
  | add p q hp hq ihp ihq =>
    rw [derH_add]
    exact ihp.add ihq
  | monomial m c hm =>
    rw [← hm]
    simp only [derH, mul_assoc]
    refine MvPolynomial.IsWeightedHomogeneous.add ?_ ?_
    · refine MvPolynomial.IsWeightedHomogeneous.C_mul ?_ _
      exact X00_pderiv01_monomial_isWH m c
    · refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ ?_
      intro i _
      refine MvPolynomial.IsWeightedHomogeneous.C_mul ?_ _
      rw [MvPolynomial.X_mul_pderiv_monomial, MvPolynomial.smul_monomial]
      exact MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl

/-- Iterated `derH` preserves every multidegree piece. -/
private lemma derH_iterate_mem {N : ℕ} (v : Fin (N + 1) → ℂ) (k : ℕ)
    {d : Fin (N + 1) →₀ ℕ} {F : MR N} (hF : F ∈ homPiece N d) :
    (derH v)^[k] F ∈ homPiece N d := by
  induction k with
  | zero => simpa using hF
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact derH_mem_homPiece v ih

/-- `applyH` preserves every multidegree piece. -/
private lemma applyH_mem_homPiece {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (t : Fin q → ℕ)
    {d : Fin (N + 1) →₀ ℕ} {F : MR N} (hF : F ∈ homPiece N d) :
    applyH w t F ∈ homPiece N d := by
  rw [applyH]
  exact foldr_mem (fun m Q => (derH (w m))^[t m] Q) (homPiece N d : Set (MR N))
    (fun m x hx => derH_iterate_mem (w m) (t m) hx) (List.finRange q) hF

/-- Every generator of Philippon's `I_r` is multihomogeneous of multidegree `D`. -/
theorem chainGen_homPiece {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ)
    (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) (hdeg : ∀ i, P.degreeOf i ≤ D i)
    (A B : ℕ) {Q : Work.BW.MR N} (hQ : Q ∈ Work.BW.chainGen w θ D P A B) :
    Q ∈ Work.BW.homPiece N (Work.BW.fsD D) := by
  obtain ⟨s, t, hs, ht, rfl⟩ := hQ
  exact (transl_basic (ptTheta θ s) (ptTheta θ s)).2.2.2.1 (fsD D) _
    (applyH_mem_homPiece w t (homog_mem_homPiece D P hdeg))

end Work.BW.ZGbigAux
