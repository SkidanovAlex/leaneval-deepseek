import Mathlib
import Submission.Vdw.CaseIIIStability
import Submission.Vdw.Counting
import Submission.Commons.Data.Set.ncard_eq_natCard

open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case III: the `(u,c)`-parametrisation of the box and the upper-coefficient box

Every `f ∈ Box n H` is determined by its upper coefficients `u = upperCoeffs n f`
(coefficients of `X^1,…,X^{n-1}`) and its constant coefficient `c = f.coeff 0`:

* `monicOfUpper_eq_self` — `monicOfUpper n (upperCoeffs n f) (f.coeff 0) = f`;
* `monicOfUpper_in_box`, `upperCoeffs_bound`, `coeff0_bound` — the two directions of
  the correspondence;
* `uBox_card` — the upper-coefficient box `{u : Fin (n-1) → ℤ | ∀ j, |u j| ≤ H}` has
  exactly `(2H+1)^(n-1)` elements (needed for the Case-III subcase-(ii) sum over `u`).

These are the counting bridges used by the Case-III assembly to turn counts of
`(u, c)`-pairs into counts of box polynomials.
-/

noncomputable section

namespace Submission.Vdw

/-- The set of box-bounded upper-coefficient vectors of length `n-1`. -/
def upperBox (n H : ℕ) : Set (Fin (n - 1) → ℤ) :=
  {u | ∀ j, |u j| ≤ (H : ℤ)}

/-- Bijection between the upper-coefficient box and the bounded-integer vectors. -/
def upperBoxEquiv (n H : ℕ) : {u : Fin (n - 1) → ℤ // u ∈ upperBox n H} ≃
    (Fin (n - 1) → BddInt H) where
  toFun := fun u j => ⟨u.1 j, u.2 j⟩
  invFun := fun v => ⟨fun j => (v j : ℤ), by intro j; exact (v j).2⟩
  left_inv := by
    intro u
    apply Subtype.ext
    funext j
    rfl
  right_inv := by
    intro v
    funext j
    apply Subtype.ext
    rfl

/-- The upper-coefficient box has exactly `(2H+1)^(n-1)` elements. -/
theorem upperBox_ncard_eq (n H : ℕ) : (upperBox n H).ncard = (2 * H + 1) ^ (n - 1) := by
  classical
  haveI : Fintype {u : Fin (n - 1) → ℤ // u ∈ upperBox n H} :=
    Fintype.ofEquiv (Fin (n - 1) → BddInt H) (upperBoxEquiv n H).symm
  have hb : (upperBox n H).ncard = Nat.card {u : Fin (n - 1) → ℤ // u ∈ upperBox n H} := by
    exact ncard_eq_natCard (upperBox n H)
  calc
    (upperBox n H).ncard = Nat.card {u : Fin (n - 1) → ℤ // u ∈ upperBox n H} := hb
    _ = Nat.card (Fin (n - 1) → BddInt H) := Nat.card_congr (upperBoxEquiv n H)
    _ = (2 * H + 1) ^ (n - 1) := bddVec_card (n - 1) H

/-- `monicOfUpper` applied to the upper coefficients and constant coefficient of
a monic degree-`n` polynomial returns that polynomial. -/
theorem monicOfUpper_eq_self (n : ℕ) (hn : 1 ≤ n) (f : ℤ[X]) (hfmon : f.Monic)
    (hdeg : f.natDegree = n) :
    monicOfUpper n (upperCoeffs n f) (f.coeff 0) = f := by
  classical
  ext k
  by_cases hkn : k < n
  · by_cases hk0 : k = 0
    · subst hk0
      rw [monicOfUpper_coeff_zero n hn (upperCoeffs n f) (f.coeff 0)]
    · have hjk : k - 1 < n - 1 := by omega
      have hi : k = (k - 1 : ℕ) + 1 := by omega
      rw [hi, monicOfUpper_coeff_add_one n (upperCoeffs n f) (f.coeff 0) ⟨k - 1, hjk⟩]
      rfl
  · have hkn' : n ≤ k := le_of_not_gt hkn
    by_cases hk : k = n
    · rw [hk]
      rw [monicOfUpper_coeff_n n hn (upperCoeffs n f) (f.coeff 0)]
      rw [← hdeg]
      exact hfmon.coeff_natDegree.symm
    · have hk' : n < k := lt_of_le_of_ne hkn' (Ne.symm hk)
      rw [monicOfUpper_coeff_gt n hn (upperCoeffs n f) (f.coeff 0) k hk']
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hk')).symm

/-- The upper coefficients of a box polynomial are bounded by `H`. -/
lemma upperCoeffs_bound {n H : ℕ} {f : ℤ[X]} (hf : f ∈ Box n H) (hn : 1 ≤ n)
    (j : Fin (n - 1)) : |upperCoeffs n f j| ≤ (H : ℤ) := by
  have hb := hf.2.2 ((j : ℕ) + 1) (by
    have hj := j.isLt
    omega)
  simpa [upperCoeffs] using hb

/-- The constant coefficient of a box polynomial is bounded by `H`. -/
lemma coeff0_bound {n H : ℕ} {f : ℤ[X]} (hf : f ∈ Box n H) (hn : 1 ≤ n) :
    |f.coeff 0| ≤ (H : ℤ) := by
  exact hf.2.2 0 (by omega)

/-- `monicOfUpper n u c` lies in the box when `u` and `c` are bounded. -/
theorem monicOfUpper_in_box (n H : ℕ) (hn : 1 ≤ n) (u : Fin (n - 1) → ℤ)
    (hu : u ∈ upperBox n H) (c : ℤ) (hc : |c| ≤ (H : ℤ)) :
    monicOfUpper n u c ∈ Box n H := by
  classical
  obtain ⟨hmon, hdeg⟩ := monicOfUpper_monic_natDegree n hn u c
  refine ⟨hmon, ?_, ?_⟩
  · rw [Polynomial.degree_eq_natDegree (Polynomial.Monic.ne_zero hmon), hdeg]
  · intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [monicOfUpper_coeff_zero n hn u c]
      exact hc
    · have hi1 : 1 ≤ i := by omega
      have hj : i - 1 < n - 1 := by omega
      have hiadd : i = (i - 1 : ℕ) + 1 := by omega
      rw [hiadd]
      rw [monicOfUpper_coeff_add_one n u c ⟨i - 1, hj⟩]
      exact hu ⟨i - 1, hj⟩

/-- Reconstructing a box polynomial from its own upper coefficients and constant
term gives a box polynomial (combination of `monicOfUpper_eq_self` and
`monicOfUpper_in_box`). -/
theorem box_poly_of_upper_coeffs {n H : ℕ} {f : ℤ[X]} (hf : f ∈ Box n H)
    (hn : 1 ≤ n) (u : Fin (n - 1) → ℤ) (hu : u = upperCoeffs n f) (c : ℤ)
    (hc : c = f.coeff 0) :
    monicOfUpper n u c ∈ Box n H := by
  subst u
  subst c
  have hnd : f.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hf.2.1
  rw [monicOfUpper_eq_self n hn f hf.1 hnd]
  exact hf

end Submission.Vdw
