/-
Area DSCOH — auxiliary lemmas for `Work.DSCOH.locAt_monomial_basis`.

These are the pieces of `Submission.Work.DSCOH.locAt_monomial_basis` that were requested from
colleagues in parallel (`lmb_*`); this file contains an independent, self-contained proof of the
same statements under `lmbA_*` names, so that the main theorem does not depend on the state of the
parallel development.
-/
import Mathlib
import Submission.Work.DSCOH.Basic
import Submission.Work.DSCOH.Shift
import Submission.Work.DSCOH.ShiftToolkit
import Submission.Work.DSCOH.LocBasisDefs
import Submission.Work.DSCOH.lmb_isRegular_subS

open MvPolynomial

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-! ## Monomials are multiplicative in the index set -/

lemma monomial_union {S T : Finset (Fin n)} (h : Disjoint S T) :
    monomial (A := A) (S ∪ T) = monomial (A := A) S * monomial (A := A) T := by
  simp only [monomial, Var]
  rw [Finset.prod_union h]

/-! ## The total degree of a monomial in the support of a homogeneous polynomial -/

lemma lmbA_support_degree {e : ℕ} {m : Poly A n} (hm : m ∈ homSub A n e) {v : Fin n →₀ ℕ}
    (hv : v ∈ m.support) : (∑ i, v i) = e := by
  have hc : m.coeff v ≠ 0 := MvPolynomial.mem_support_iff.mp hv
  have hh : m.IsHomogeneous e := (MvPolynomial.mem_homogeneousSubmodule e m).mp hm
  by_contra hne
  exact hc (hh.coeff_eq_zero (by rwa [Finsupp.degree_eq_sum]))

/-! ## The localization map is injective on `X_S`-powers -/

lemma lmbA_mk_den_eq_zero {S : Finset (Fin n)} {k : ℕ} {m : Poly A n}
    (h : LocalizedModule.mk m (den (A := A) S k) = 0) : m = 0 := by
  have h' : LocalizedModule.mk m (den (A := A) S k) =
      LocalizedModule.mk (0 : Poly A n) (den (A := A) S k) := by
    rw [h, LocalizedModule.zero_mk]
  rw [LocalizedModule.mk_eq] at h'
  obtain ⟨u, hu⟩ := h'
  simp only [smul_zero] at hu
  have hreg : IsRegular ((u : Poly A n) * ((den (A := A) S k : subS (A := A) S) : Poly A n)) :=
    (lmb_isRegular_subS S u).mul (by
      rw [den_coe]
      exact (isRegular_prod_X (R := A) (σ := Fin n) S).pow k)
  exact hreg.left.mul_left_eq_zero_iff.mp (by rw [mul_assoc]; exact hu)

/-! ## The exponent shift by a variable -/

lemma aux_eIdx_shift (S : Finset (Fin n)) {k : ℕ} {β : Fin n → ℤ} (hk : Adm S k β) (i : Fin n) :
    eIdx S k (fun j => if j = i then β j + 1 else β j) =
      eIdx S k β + fun j => if j = i then 1 else 0 := by
  funext j
  by_cases hji : j = i
  · simp only [Pi.add_apply, eIdx, hji, ite_true]
    have h1 : (0 : ℤ) ≤ β i + (if i ∈ S then (k : ℤ) else 0) := by
      have := hk i; linarith
    rw [show β i + 1 + (if i ∈ S then (k : ℤ) else 0)
        = (β i + (if i ∈ S then (k : ℤ) else 0)) + 1 by ring,
      Int.toNat_add h1 (by norm_num), Int.toNat_one]
  · simp only [Pi.add_apply, eIdx, hji, ite_false, add_zero]

lemma lmbA_bAt_X_smul (S : Finset (Fin n)) {k : ℕ} {β : Fin n → ℤ} (hk : Adm S k β) (i : Fin n) :
    (MvPolynomial.X i : Poly A n) • bAt (A := A) (n := n) S β k =
      bAt (A := A) (n := n) S (fun j => if j = i then β j + 1 else β j) k := by
  rw [bAt_eq_mk, bAt_eq_mk, LocalizedModule.smul'_mk]
  congr 1
  rw [smul_eq_mul, aux_eIdx_shift S hk i, xpow_add, xpow_single]
  ring

/-! ## Restriction to a bigger chart -/

lemma aux_eIdx_diff (S T : Finset (Fin n)) (hST : S ⊆ T) {k : ℕ} {β : Fin n → ℤ}
    (hk : Adm S k β) :
    eIdx T k β = eIdx S k β + fun j => if j ∈ T \ S then k else 0 := by
  funext j
  have hβj : ∀ (h : j ∉ S), (0 : ℤ) ≤ β j := fun h => hk.idx j h
  by_cases hjS : j ∈ S
  · rw [Pi.add_apply, eIdx, eIdx, ite_eq_left (hST hjS), ite_eq_left hjS,
      ite_eq_right (by simp [Finset.mem_sdiff, hjS]), add_zero]
  · by_cases hjT : j ∈ T
    · rw [Pi.add_apply, eIdx, eIdx, ite_eq_left hjT, ite_eq_right (by simpa using hjS),
        ite_eq_left (Finset.mem_sdiff.mpr ⟨hjT, hjS⟩), add_zero]
      have h1 : (0 : ℤ) ≤ β j := hβj hjS
      have h2 : (0 : ℤ) ≤ β j + (k : ℤ) := by linarith
      apply Nat.cast_injective (R := ℤ)
      push_cast
      rw [Int.toNat_of_nonneg h2, Int.toNat_of_nonneg h1]
    · rw [Pi.add_apply, eIdx, eIdx, ite_eq_right (by simpa using hjT),
        ite_eq_right (by simpa using hjS),
        ite_eq_right (by simp [Finset.mem_sdiff, hjT]), add_zero, add_zero]

lemma aux_poly_resAt (S T : Finset (Fin n)) (h : S ⊆ T) {k : ℕ} {β : Fin n → ℤ}
    (hk : Adm S k β) :
    monomial (A := A) T ^ k * xpow (A := A) (eIdx S k β)
      = monomial (A := A) S ^ k * xpow (A := A) (eIdx T k β) := by
  have hT : monomial (A := A) T = monomial (A := A) S * monomial (A := A) (T \ S) := by
    rw [← monomial_union (Finset.disjoint_sdiff), Finset.union_sdiff_of_subset h]
  rw [hT, mul_pow, aux_eIdx_diff S T h hk, xpow_add, xpow_ite]
  ring

lemma lmbA_bAt_resAt (S T : Finset (Fin n)) (h : S ⊆ T) {k : ℕ} {β : Fin n → ℤ}
    (hk : Adm S k β) :
    resAt (M := Poly A n) h (bAt (A := A) (n := n) S β k) =
      bAt (A := A) (n := n) T β k := by
  rw [bAt_eq_mk, bAt_eq_mk, resAt_mk]
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul, smul_eq_mul, den_coe]
  exact aux_poly_resAt S T h hk

end Work.DSCOH
