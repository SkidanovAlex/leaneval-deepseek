import Mathlib
import Submission.Work.DSCOH.Shift
import Submission.Work.DSCOH.shift_gradedSMul
import Submission.Work.DSCOH.ShiftToolkit

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The product `∏_{i∈S} Xᵢ` is homogeneous of degree `|S|`. -/
private lemma monomial_mem_homSub (S : Finset (Fin n)) :
    monomial (A := A) S ∈ homSub A n S.card := by
  rw [homSub, MvPolynomial.mem_homogeneousSubmodule]
  unfold monomial Var
  simpa using MvPolynomial.IsHomogeneous.prod (R := A) S (fun i => MvPolynomial.X i)
    (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X A i)

/-- Its `j`-th power is homogeneous of degree `j·|S|`. -/
private lemma monomial_pow_mem_homSub (S : Finset (Fin n)) (j : ℕ) :
    (monomial (A := A) S) ^ j ∈ homSub A n (j * S.card) := by
  rw [homSub, MvPolynomial.mem_homogeneousSubmodule]
  have h1 : (monomial (A := A) S).IsHomogeneous S.card := by
    unfold monomial Var
    simpa using MvPolynomial.IsHomogeneous.prod (R := A) S (fun i => MvPolynomial.X i)
      (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X A i)
  simpa only [mul_comm] using h1.pow j

/-- **Monotonicity of the `k`-th piece of `degZero` for the shifted grading.**

The `k`-th piece `S(-d)_{k·|S|}/X_S^k` of the degree-zero part of the localization of the shift
`S(-d) = shift d` is contained in the `k'`-th piece for every `k' ≥ k`: a generator `m/X_S^k` is
rewritten as `(X_S^{k'-k}·m)/X_S^{k'}`, and `X_S^{k'-k}` is homogeneous of degree `(k'-k)·|S|`,
so that `X_S^{k'-k}·m` sits in `S(-d)_{k'·|S|}`. -/
private lemma map_divPow_toLoc_shift_mono_aux (d : ℕ) (S : Finset (Fin n)) {k k' : ℕ}
    (h : k ≤ k') :
    Submodule.map ((divPow (A := A) (M := Poly A n) S k).comp
        (toLoc (A := A) (M := Poly A n) S))
      (shift (A := A) (n := n) d (k * S.card))
    ≤ Submodule.map ((divPow (A := A) (M := Poly A n) S k').comp
        (toLoc (A := A) (M := Poly A n) S))
      (shift (A := A) (n := n) d (k' * S.card)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k' = k + j := ⟨k' - k, (Nat.add_sub_cancel' h).symm⟩
  haveI : SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d) := shift_gradedSMul d
  rintro y ⟨m, hm, rfl⟩
  refine Submodule.mem_map.mpr ⟨(monomial (A := A) S) ^ j • m, ?_, ?_⟩
  · have hsm := SetLike.GradedSMul.smul_mem (monomial_pow_mem_homSub (A := A) S j) hm
    rwa [show j * S.card +ᵥ (k * S.card) = (k + j) * S.card from by
      rw [show j * S.card +ᵥ (k * S.card) = j * S.card + k * S.card from rfl]; ring] at hsm
  · show divPow (A := A) (M := Poly A n) S (k + j)
        (toLoc (A := A) (M := Poly A n) S ((monomial (A := A) S) ^ j • m)) =
      divPow (A := A) (M := Poly A n) S k (toLoc (A := A) (M := Poly A n) S m)
    simpa only [smul_eq_mul] using divPow_toLoc_smul_monomial_pow (A := A) S k j m

theorem map_divPow_toLoc_shift_mono {A : Type*} [CommRing A] {n : ℕ}
    (d : ℕ) {S : Finset (Fin n)} {k k' : ℕ} (h : k ≤ k') :
    Submodule.map ((divPow (A := A) (n := n) (M := Poly A n) S k).comp
        (toLoc (A := A) (n := n) (M := Poly A n) S))
      (shift (A := A) (n := n) d (k * S.card))
    ≤ Submodule.map ((divPow (A := A) (n := n) (M := Poly A n) S k').comp
        (toLoc (A := A) (n := n) (M := Poly A n) S))
      (shift (A := A) (n := n) d (k' * S.card)) :=
  map_divPow_toLoc_shift_mono_aux (A := A) (n := n) d S h

end Work.DSCOH
