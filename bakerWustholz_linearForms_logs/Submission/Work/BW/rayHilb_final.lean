import Mathlib
import Submission.Work.BW.GradedHilbDefs
import Submission.Work.BW.BWGradedBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Final assembly for the ray Hilbert function

The ray Hilbert function `rayHilb N D I t` is the dimension of the multidegree-`tD` piece of
`MR N ⧸ I`, i.e. the value `hilbIdeal N I (castF (t • D))` of the multigraded Hilbert function.
Once the multigraded Hilbert–Serre theorem (`hilb_serre_poly`) shows that this value is given by
the binomial kernel `kFun N (fun _ => 2) P`, the ray Hilbert function is for large `t` a finite
combination of products of `N+1` linear factors `t ↦ t D_i - v_i + 1`, hence agrees with a
polynomial of degree `≤ N + 1`.

That last step is what this file provides.
-/

namespace Work.BW

open MvPolynomial

/-- The ray Hilbert function is the value of the multigraded Hilbert function of the quotient
`MR N ⧸ I` at `castF (t • D)`. -/
theorem rayHilb_eq_hilbIdeal (N : ℕ) (D : Fin (N + 1) →₀ ℕ) (I : Ideal (MR N)) (t : ℕ) :
    rayHilb N D I t = hilbIdeal N I (castF (t • D)) := by
  rw [rayHilb, hilbIdeal, homPiece_eq_pieceZ]

/-- The multidegree-`(t • D)` value of `kFun N (fun _ => 2) P`, for `t` large enough that
`t D i ≥ v i` for every `v` in the support of `P`, is the polynomial expression
`∑_v P_v ∏_i (t D_i - v_i + 1)`. -/
private theorem kFun_two_eq (N : ℕ) (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (P : MvPolynomial (Fin (N + 1)) ℚ) {t : ℕ}
    (ht : ∀ v ∈ P.support, ∀ i, v i ≤ t) :
    kFun N (fun _ => 2) P (castF (t • D)) =
      ∑ v ∈ P.support, P.coeff v * ∏ i, ((t : ℚ) * (D i : ℚ) - (v i : ℚ) + 1) := by
  rw [kFun]
  refine Finset.sum_congr rfl fun v hv => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hvi : v i ≤ t := ht v hv i
  obtain ⟨c, hc⟩ : ∃ c : ℕ, v i = c := ⟨v i, rfl⟩
  subst hc
  have hle : v i ≤ t * D i := by
    calc v i ≤ t := hvi
      _ = t * 1 := (mul_one t).symm
      _ ≤ t * D i := Nat.mul_le_mul_left t (hD i)
  have harg : (castF (t • D)) i - (v i : ℤ) = ((t * D i - v i : ℕ) : ℤ) := by
    rw [castF_apply, Finsupp.smul_apply, smul_eq_mul]
    push_cast
    omega
  rw [harg]
  have hnn : (0 : ℤ) ≤ ((t * D i - v i : ℕ) : ℤ) := by positivity
  rw [cbeta_pos (by norm_num : (0 : ℕ) < 2) hnn, Int.toNat_natCast]
  have hch : (t * D i - v i + 2 - 1).choose (2 - 1) = t * D i - v i + 1 := by
    rw [show t * D i - v i + 2 - 1 = (t * D i - v i) + 1 by omega, Nat.choose_one_right]
  rw [hch]
  push_cast [Nat.cast_sub hle]
  ring

/-- **Final assembly.** If the ray Hilbert function is given, for all large `t`, by the value of
the binomial kernel `kFun N (fun _ => 2) P`, then it agrees with a polynomial of degree `≤ N+1`
for large `t`. -/
theorem rayHilb_poly_of_kFun {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (I : Ideal (MR N)) (P : MvPolynomial (Fin (N + 1)) ℚ) (B : ℕ)
    (h : ∀ t, B ≤ t →
      ((rayHilb N D I t : ℕ) : ℚ) = kFun N (fun _ => 2) P (castF (t • D))) :
    ∃ q : Polynomial ℚ, IsRayPoly N D I q ∧ q.natDegree ≤ N + 1 := by
  refine ⟨∑ v ∈ P.support, Polynomial.C (P.coeff v) *
      ∏ i, (Polynomial.C ((D i : ℚ)) * Polynomial.X - Polynomial.C ((v i : ℚ)) + 1), ?_, ?_⟩
  · rw [IsRayPoly]
    set B' : ℕ := max B (P.support.sup (fun v => v.sum (fun _ n => n))) with hB'
    filter_upwards [Filter.eventually_atTop.mpr ⟨B', fun t ht => ht⟩] with t ht
    have htB : B ≤ t := by
      rw [hB'] at ht
      exact le_trans (le_max_left _ _) ht
    have htv : ∀ v ∈ P.support, ∀ i, v i ≤ t := by
      intro v hv i
      have h1 : v.sum (fun _ n => n) ≤ B' := by
        rw [hB']
        exact le_trans (Finset.le_sup (f := fun v => v.sum fun _ n => n) hv) (le_max_right _ _)
      have h2 : v i ≤ v.sum (fun _ n => n) :=
        Finsupp.single_eval_le_sum (g := fun n => n) v rfl (fun n => Nat.zero_le n) i
      omega
    rw [h t htB, kFun_two_eq N D hD P htv]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_one]
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  · have hlin : ∀ a b : ℚ,
        (Polynomial.C a * Polynomial.X - Polynomial.C b + 1 : Polynomial ℚ).natDegree ≤ 1 := by
      intro a b
      refine le_trans
        (Polynomial.natDegree_add_le (Polynomial.C a * Polynomial.X - Polynomial.C b) 1)
        (max_le ?_ ?_)
      · refine le_trans
          (Polynomial.natDegree_sub_le (Polynomial.C a * Polynomial.X) (Polynomial.C b))
          (max_le ?_ ?_)
        · refine le_trans (Polynomial.natDegree_mul_le (p := Polynomial.C a) (q := Polynomial.X)) ?_
          rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
        · rw [Polynomial.natDegree_C]; omega
      · rw [Polynomial.natDegree_one]; omega
    refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    refine Finset.sup_le fun v hv => ?_
    refine le_trans
      (Polynomial.natDegree_mul_le (p := Polynomial.C (P.coeff v))
        (q := ∏ i, (Polynomial.C ((D i : ℚ)) * Polynomial.X - Polynomial.C ((v i : ℚ)) + 1))) ?_
    have h1 : (Polynomial.C (P.coeff v)).natDegree ≤ 0 := by rw [Polynomial.natDegree_C]
    have h2 : (∏ i, (Polynomial.C ((D i : ℚ)) * Polynomial.X -
        Polynomial.C ((v i : ℚ)) + 1)).natDegree ≤ ∑ _i : Fin (N + 1), 1 :=
      le_trans (Polynomial.natDegree_prod_le (s := Finset.univ)
        (f := fun i : Fin (N + 1) => Polynomial.C ((D i : ℚ)) * Polynomial.X -
          Polynomial.C ((v i : ℚ)) + 1)) (Finset.sum_le_sum fun i _ => hlin _ _)
    have h3 : (∑ _i : Fin (N + 1), (1 : ℕ)) = N + 1 := by simp
    omega

end Work.BW
