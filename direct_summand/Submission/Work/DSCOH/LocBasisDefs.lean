/-
Area DSCOH — the monomial `A`-basis of the chart localization `locAt S`.

This file contains the *vocabulary* for the theorem `Work.DSCOH.locAt_monomial_basis`: the index
set `Idx S` of the basis (integer exponent vectors, non-negative outside `S`), the admissibility
predicate `Adm S k β` for the denominator exponent `k`, the explicit fraction
`bAt S β k = (∏ i, Xᵢ^{βᵢ + k·[i∈S]}) / X_S^k`, the canonical choice `KIdx S β` of an admissible
denominator exponent, and the basis element `bloc S β`.

This file is meant as a *frozen interface*: it is `sorry`-free and the rest of the development
(the theorem `locAt_monomial_basis` and the lemmas proved for it in parallel) imports it.
-/
import Mathlib
import Submission.Work.DSCOH.Basic
import Submission.Work.DSCOH.Shift
import Submission.Work.DSCOH.ShiftToolkit

open MvPolynomial

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-! ## The index set and admissible exponent vectors -/

/-- Index set of the monomial `A`-basis of `locAt S`: exponent vectors `β : Fin n → ℤ` which are
non-negative outside `S`. -/
abbrev Idx (S : Finset (Fin n)) := {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i}

/-- `β` is admissible for the denominator exponent `k` when `β i + k ≥ 0` for `i ∈ S` and
`β i ≥ 0` for `i ∉ S`. This is exactly the condition making the exponent vector `eIdx S k β`
the "expected" one. -/
def Adm (S : Finset (Fin n)) (k : ℕ) (β : Fin n → ℤ) : Prop :=
  ∀ i, -(β i) ≤ if i ∈ S then (k : ℤ) else 0

lemma Adm.idx {S : Finset (Fin n)} {k : ℕ} {β : Fin n → ℤ} (h : Adm S k β) :
    ∀ i, i ∉ S → 0 ≤ β i := by
  intro i hi
  have h' := h i
  rw [ite_eq_right (by simpa using hi)] at h'
  linarith

lemma Adm.mono {S T : Finset (Fin n)} {k : ℕ} {β : Fin n → ℤ} (h : Adm S k β) (hST : S ⊆ T) :
    Adm T k β := by
  intro i
  by_cases hiT : i ∈ T
  · rw [ite_eq_left hiT]
    by_cases hiS : i ∈ S
    · have h' := h i
      rw [ite_eq_left hiS] at h'
      exact h'
    · have h' := h i
      rw [ite_eq_right (by simpa using hiS)] at h'
      linarith
  · rw [ite_eq_right (by simpa using hiT)]
    by_cases hiS : i ∈ S
    · exact absurd (hST hiS) hiT
    · have h' := h i
      rw [ite_eq_right (by simpa using hiS)] at h'
      exact h'

lemma Adm.of_le {S : Finset (Fin n)} {k k' : ℕ} {β : Fin n → ℤ} (h : Adm S k β) (hkk : k ≤ k') :
    Adm S k' β := by
  intro i
  have h' := h i
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi] at h' ⊢
    have : (k : ℤ) ≤ (k' : ℤ) := by exact_mod_cast hkk
    linarith
  · rw [ite_eq_right (by simpa using hi)] at h' ⊢
    exact h'

/-! ## The exponent vector of the explicit fraction -/

/-- The exponent vector `∏ i, Xᵢ^{βᵢ + (k if i ∈ S)}` of the numerator of the fraction
`bAt S β k`. -/
noncomputable def eIdx (S : Finset (Fin n)) (k : ℕ) (β : Fin n → ℤ) : Fin n → ℕ :=
  fun i => (β i + (if i ∈ S then (k : ℤ) else 0)).toNat

lemma Adm.cast_eIdx {S : Finset (Fin n)} {k : ℕ} {β : Fin n → ℤ} (h : Adm S k β) (i : Fin n) :
    ((eIdx S k β i : ℕ) : ℤ) = β i + (if i ∈ S then (k : ℤ) else 0) :=
  Int.toNat_of_nonneg (by have := h i; linarith)

lemma eIdx_sub (S : Finset (Fin n)) (k : ℕ) (α : Fin n → ℕ) :
    eIdx S k (fun i => (α i : ℤ) - (if i ∈ S then (k : ℤ) else 0)) = α := by
  funext i
  by_cases hi : i ∈ S
  · simp only [eIdx, hi, ite_true, sub_add_cancel, Int.toNat_natCast]
  · simp only [eIdx, hi, ite_false, sub_zero, add_zero, Int.toNat_natCast]

lemma Adm.sub (S : Finset (Fin n)) (k : ℕ) (α : Fin n → ℕ) :
    Adm S k (fun i => (α i : ℤ) - (if i ∈ S then (k : ℤ) else 0)) := by
  intro i
  by_cases hi : i ∈ S
  · simp only [hi, ite_true]
    have : (0 : ℤ) ≤ (α i : ℤ) := Int.natCast_nonneg _
    linarith
  · simp only [hi, ite_false, sub_zero]
    have : (0 : ℤ) ≤ (α i : ℤ) := Int.natCast_nonneg _
    linarith

/-- The index vector of `Idx S` attached to a `ℕ`-valued exponent vector and a denominator
exponent `k`. -/
noncomputable def subIdx (S : Finset (Fin n)) (k : ℕ) (α : Fin n → ℕ) : Idx S :=
  ⟨fun i => (α i : ℤ) - (if i ∈ S then (k : ℤ) else 0), (Adm.sub S k α).idx⟩

lemma subIdx_val (S : Finset (Fin n)) (k : ℕ) (α : Fin n → ℕ) :
    (subIdx S k α).1 = fun i => (α i : ℤ) - (if i ∈ S then (k : ℤ) else 0) := rfl

/-! ## The explicit fraction `bAt S β k` -/

/-- The explicit fraction `(∏ i, Xᵢ^{βᵢ + k·[i∈S]}) / X_S^k` in the chart localization at `S`. -/
noncomputable def bAt (S : Finset (Fin n)) (β : Fin n → ℤ) (k : ℕ) :
    locAt (A := A) (M := Poly A n) S :=
  divPow (A := A) (M := Poly A n) S k
    (toLoc (A := A) (M := Poly A n) S (xpow (A := A) (n := n) (eIdx S k β)))

lemma bAt_eq_mk (S : Finset (Fin n)) (β : Fin n → ℤ) (k : ℕ) :
    bAt (A := A) (n := n) S β k =
      LocalizedModule.mk (xpow (A := A) (eIdx S k β)) (den (A := A) S k) :=
  divPow_toLoc_eq_mk (A := A) S k (xpow (A := A) (eIdx S k β))

lemma bAt_sub_eq_mk (S : Finset (Fin n)) (k : ℕ) (α : Fin n → ℕ) :
    bAt (A := A) (n := n) S (fun i => (α i : ℤ) - (if i ∈ S then (k : ℤ) else 0)) k =
      LocalizedModule.mk (xpow (A := A) α) (den (A := A) S k) := by
  rw [bAt_eq_mk, eIdx_sub]

/-! ## The monomial lemmas used to manipulate `bAt` -/

lemma xpow_ite (S : Finset (Fin n)) (j : ℕ) :
    xpow (A := A) (fun i => if i ∈ S then j else 0) = monomial (A := A) S ^ j := by
  simp only [xpow, monomial, Var, ← Finset.prod_pow]
  exact (Finset.prod_subset (s₁ := S) (s₂ := Finset.univ) (Finset.subset_univ S)
    (f := fun i => (MvPolynomial.X i : Poly A n) ^ (if i ∈ S then j else 0))
    (fun x _ hx => by rw [ite_eq_right (by simpa using hx), pow_zero])).symm.trans
    (Finset.prod_congr rfl (fun i hi => by rw [ite_eq_left hi]))

lemma xpow_single (i : Fin n) :
    xpow (A := A) (fun j => if j = i then 1 else 0) = (MvPolynomial.X i : Poly A n) := by
  rw [xpow, ← Finset.prod_subset (s₁ := {i}) (s₂ := Finset.univ) (by simp)
    (f := fun j => (MvPolynomial.X j : Poly A n) ^ (if j = i then 1 else 0))
    (fun x _ hx => by rw [ite_eq_right (by simpa using hx), pow_zero])]
  simp

lemma xpow_eIdx_add {S : Finset (Fin n)} {k : ℕ} {β : Fin n → ℤ} (h : Adm S k β) (j : ℕ) :
    xpow (A := A) (eIdx S (k + j) β) =
      monomial (A := A) S ^ j * xpow (A := A) (eIdx S k β) := by
  have hfun : eIdx S (k + j) β = eIdx S k β + fun i => if i ∈ S then j else 0 := by
    funext i
    by_cases hi : i ∈ S
    · simp only [eIdx, Pi.add_apply, hi, ite_true]
      rw [show β i + ((k + j : ℕ) : ℤ) = (β i + (k : ℤ)) + (j : ℤ) by push_cast; ring]
      have h1 : (0 : ℤ) ≤ β i + (k : ℤ) := by have := h i; rw [ite_eq_left hi] at this; linarith
      rw [Int.toNat_add h1 (Int.natCast_nonneg j), Int.toNat_natCast]
    · simp only [eIdx, Pi.add_apply, hi, ite_false, add_zero]
  rw [hfun, xpow_add, xpow_ite, mul_comm]

lemma bAt_add {S : Finset (Fin n)} {k : ℕ} {β : Fin n → ℤ} (h : Adm S k β) (j : ℕ) :
    bAt (A := A) (n := n) S β (k + j) = bAt (A := A) (n := n) S β k := by
  unfold bAt
  rw [xpow_eIdx_add h j]
  exact divPow_toLoc_smul_monomial_pow (A := A) S k j _

lemma bAt_eq_of_le {S : Finset (Fin n)} {k k' : ℕ} {β : Fin n → ℤ} (h : Adm S k β) (hkk : k ≤ k') :
    bAt (A := A) (n := n) S β k' = bAt (A := A) (n := n) S β k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkk
  exact bAt_add h j

lemma bAt_eq {S : Finset (Fin n)} {k k' : ℕ} {β : Fin n → ℤ} (h : Adm S k β) (h' : Adm S k' β) :
    bAt (A := A) (n := n) S β k = bAt (A := A) (n := n) S β k' := by
  rcases le_total k k' with hle | hle
  · exact (bAt_eq_of_le h hle).symm
  · exact bAt_eq_of_le h' hle

/-! ## The canonical basis element `bloc S β` -/

/-- The canonical admissible denominator exponent of `β`. -/
noncomputable def KIdx (S : Finset (Fin n)) (β : Fin n → ℤ) : ℕ :=
  ∑ i ∈ S, (-(β i)).toNat

lemma le_KIdx (S : Finset (Fin n)) (β : Fin n → ℤ) {i : Fin n} (hi : i ∈ S) :
    -(β i) ≤ (KIdx S β : ℤ) := by
  have h1 : (-(β i)).toNat ≤ KIdx S β :=
    Finset.single_le_sum (f := fun j => (-(β j)).toNat) (fun j _ => Nat.zero_le _) hi
  have h2 : (((-(β i)).toNat : ℕ) : ℤ) ≤ (KIdx S β : ℤ) := by exact_mod_cast h1
  rcases le_total (β i) 0 with hb | hb
  · rwa [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -(β i))] at h2
  · have : -(β i) ≤ 0 := by omega
    linarith

lemma Adm.KIdx {S : Finset (Fin n)} {β : Fin n → ℤ} (hβ : ∀ i, i ∉ S → 0 ≤ β i) :
    Adm S (KIdx S β) β := by
  intro i
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi]
    exact le_KIdx S β hi
  · rw [ite_eq_right (by simpa using hi)]
    have := hβ i hi
    linarith

/-- The monomial basis element of `locAt S` attached to `β : Idx S`. -/
noncomputable def bloc (S : Finset (Fin n)) (β : Idx S) : locAt (A := A) (M := Poly A n) S :=
  bAt (A := A) (n := n) S β.1 (KIdx S β.1)

lemma bloc_eq_bAt {S : Finset (Fin n)} (β : Idx S) {k : ℕ} (h : Adm S k β.1) :
    bloc (A := A) (n := n) S β = bAt (A := A) (n := n) S β.1 k :=
  bAt_eq (Adm.KIdx β.2) h

lemma bloc_subIdx (S : Finset (Fin n)) (k : ℕ) (α : Fin n → ℕ) :
    bloc (A := A) (n := n) S (subIdx S k α) =
      LocalizedModule.mk (xpow (A := A) α) (den (A := A) S k) := by
  rw [bloc, bAt_eq (Adm.KIdx (subIdx S k α).2) (Adm.sub S k α)]
  exact bAt_sub_eq_mk (A := A) (n := n) S k α

end Work.DSCOH
