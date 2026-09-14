import ChallengeDeps

open vanDerWaerdenConjecture
open Function Polynomial Filter Asymptotics

set_option autoImplicit false

/-!
# Counting box for van der Waerden's conjecture

The set of monic integer polynomials of degree `n` with all non-leading
coefficients bounded in absolute value by `H`, and the subset of "bad"
polynomials (Galois group smaller than the full symmetric group) counted by
`E n H`.  We prove that the box contains exactly `(2H+1)^n` polynomials.
-/

namespace Submission.Vdw

open Polynomial

/-- Monic integer polynomials of degree `n` with `|coeff i| ≤ H` for all `i < n`. -/
def Box (n H : ℕ) : Set ℤ[X] :=
  {p : ℤ[X] | p.Monic ∧ p.degree = n ∧ ∀ i < n, |p.coeff i| ≤ H}

/-- The "bad" polynomials counted by `E n H`. -/
def Bad (n H : ℕ) : Set ℤ[X] :=
  {p : ℤ[X] | p.Monic ∧ p.degree = n ∧ (∀ i < n, |p.coeff i| ≤ H) ∧
    Nat.card (p.map (algebraMap ℤ ℚ)).Gal < n.factorial}

@[simp]
theorem E_eq_ncard_bad (n H : ℕ) : E n H = (Bad n H).ncard := by
  rfl

theorem Bad_subset_Box (n H : ℕ) : Bad n H ⊆ Box n H := by
  intro p hp
  exact ⟨hp.1, hp.2.1, hp.2.2.1⟩

/-- Integers with absolute value at most `H`, as a type. -/
abbrev BddInt (H : ℕ) := {z : ℤ // |z| ≤ H}

/-- Bounded coefficient vectors of length `n`. -/
abbrev BddVec (n H : ℕ) := (i : Fin n) → BddInt H

noncomputable section

/-- `z ↦ z + H` viewed as an element of `Fin (2H+1)`. -/
def bddIntToFin (H : ℕ) (z : BddInt H) : Fin (2 * H + 1) :=
  ⟨(z.1 + (H : ℤ)).toNat, by
    have hz := z.2
    rw [abs_le] at hz
    have h0 : 0 ≤ z.1 + (H : ℤ) := by omega
    have h1 : z.1 + (H : ℤ) < ((2 * H + 1 : ℕ) : ℤ) := by omega
    exact (Int.toNat_lt h0).2 h1⟩

/-- `k ↦ k - H` is a bounded integer when `k < 2H + 1`. -/
def bddFinToInt (H : ℕ) (k : Fin (2 * H + 1)) : BddInt H :=
  ⟨(k : ℤ) - (H : ℤ), by
    rw [abs_le]
    have hk : (k : ℕ) ≤ 2 * H := by omega
    omega⟩

/-- The integers of absolute value `≤ H` are in bijection with `Fin (2H+1)`. -/
def bddIntEquivFin (H : ℕ) : BddInt H ≃ Fin (2 * H + 1) where
  toFun := bddIntToFin H
  invFun := bddFinToInt H
  left_inv z := by
    apply Subtype.ext
    dsimp [bddFinToInt, bddIntToFin]
    have h0 : 0 ≤ z.1 + (H : ℤ) := by
      have hz := z.2
      rw [abs_le] at hz
      omega
    rw [Int.toNat_of_nonneg h0]
    omega
  right_inv k := by
    apply Fin.ext
    dsimp [bddFinToInt, bddIntToFin]
    have hmain : ((k : ℤ) - (H : ℤ) + (H : ℤ)) = (k : ℤ) := by omega
    rw [hmain]
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le (k : ℕ)
    exact_mod_cast (Int.toNat_of_nonneg hk0)

@[simp]
theorem bddInt_card (H : ℕ) : Nat.card (BddInt H) = 2 * H + 1 := by
  rw [← Nat.card_fin (2 * H + 1)]
  exact Nat.card_congr (bddIntEquivFin H)

noncomputable instance bddIntFintype (H : ℕ) : Fintype (BddInt H) :=
  Fintype.ofEquiv (Fin (2 * H + 1)) (bddIntEquivFin H).symm

noncomputable instance bddVecFintype (n H : ℕ) : Fintype (BddVec n H) :=
  inferInstance

@[simp]
theorem bddVec_card (n H : ℕ) : Nat.card (BddVec n H) = (2 * H + 1) ^ n := by
  rw [Nat.card_pi]
  simp only [Finset.prod_const, Finset.card_fin, bddInt_card]

/-- Coefficient vector of a polynomial in the box. -/
def coeffVec {n H : ℕ} (p : ↥(Box n H)) : BddVec n H :=
  fun i => ⟨p.1.coeff i.1, p.2.2.2 i.1 i.2⟩

/-- The coefficient-vector map is injective on the box. -/
theorem coeffVec_injective (n H : ℕ) :
    Function.Injective (coeffVec : ↥(Box n H) → BddVec n H) := by
  intro p q hpq
  apply Subtype.ext
  have hpdeg : p.1.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some p.2.2.1
  have hqdeg : q.1.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some q.2.2.1
  have hsumP : ∀ i < n, p.1.coeff i = q.1.coeff i := by
    intro i hi
    have := congrArg (fun v : BddVec n H => (v ⟨i, hi⟩ : BddInt H).1) hpq
    simpa [coeffVec] using this
  calc
    p.1 = X ^ p.1.natDegree + ∑ x ∈ Finset.range p.1.natDegree, C (p.1.coeff x) * X ^ x :=
      p.2.1.as_sum
    _ = X ^ n + ∑ x ∈ Finset.range n, C (p.1.coeff x) * X ^ x := by rw [hpdeg]
    _ = X ^ n + ∑ x ∈ Finset.range n, C (q.1.coeff x) * X ^ x := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      rw [hsumP x (Finset.mem_range.mp hx)]
    _ = X ^ q.1.natDegree + ∑ x ∈ Finset.range q.1.natDegree, C (q.1.coeff x) * X ^ x := by
      rw [hqdeg]
    _ = q.1 := q.2.1.as_sum.symm

noncomputable instance boxFintype (n H : ℕ) : Fintype (↥(Box n H)) :=
  Fintype.ofInjective coeffVec (coeffVec_injective n H)

/-- The box is finite. -/
theorem box_finite (n H : ℕ) : (Box n H).Finite := by
  exact Set.toFinite (Box n H)

/-- A general lemma: for a set with a `Fintype`, `ncard` is `Nat.card` of the
subtype. -/
theorem ncard_eq_natCard {α : Type*} (s : Set α) [Fintype ↥s] : s.ncard = Nat.card s := by
  rw [Nat.card_eq_fintype_card, Set.ncard_eq_toFinset_card' s, Set.toFinset_card]

/-- At most `(2H+1)^n` monic degree-`n` polynomials have all non-leading
coefficients bounded by `H`. -/
theorem Box_ncard_le (n H : ℕ) : (Box n H).ncard ≤ (2 * H + 1) ^ n := by
  rw [ncard_eq_natCard (Box n H)]
  calc
    Nat.card (↥(Box n H)) ≤ Nat.card (BddVec n H) :=
      Nat.card_le_card_of_injective coeffVec (coeffVec_injective n H)
    _ = (2 * H + 1) ^ n := bddVec_card n H

/-- `E n H` is bounded by the total number of polynomials in the box. -/
theorem E_le_box_card (n H : ℕ) : E n H ≤ (2 * H + 1) ^ n := by
  rw [E_eq_ncard_bad]
  exact le_trans (Set.ncard_le_ncard (Bad_subset_Box n H)) (Box_ncard_le n H)

/-- Coefficients of a finite power-of-`X` sum. -/
lemma coeff_sum_fin (n : ℕ) (c : Fin n → ℤ) (j : ℕ) :
    (∑ i : Fin n, C (c i) * X ^ (i : ℕ)).coeff j =
      if h : j < n then c ⟨j, h⟩ else 0 := by
  by_cases hj : j < n
  · simp [hj]
    rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro b hb hbne
      have hbne' : b.val ≠ j := by
        intro h
        apply hbne
        ext
        exact h
      rw [if_neg (by intro h; exact hbne' h.symm)]
    · intro hb
      simp at hb
  · have hjge : n ≤ j := by omega
    simp [hj]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : i.val ≠ j := by omega
    rw [if_neg (by intro h; exact hne h.symm)]

/-- The polynomial with coefficient vector `v`: `X^n + ∑_{i<n} v_i X^i`. -/
noncomputable def polyOfVec (n H : ℕ) (v : BddVec n H) : ℤ[X] :=
  X ^ n + ∑ i : Fin n, C (v i).1 * X ^ (i : ℕ)

lemma coeff_polyOfVec_lt (n H : ℕ) (v : BddVec n H) {j : ℕ} (hj : j < n) :
    (polyOfVec n H v).coeff j = (v ⟨j, hj⟩).1 := by
  rw [polyOfVec, Polynomial.coeff_add, Polynomial.coeff_X_pow, coeff_sum_fin]
  simp [hj, ne_of_lt hj]

lemma coeff_polyOfVec_n (n H : ℕ) (v : BddVec n H) :
    (polyOfVec n H v).coeff n = 1 := by
  rw [polyOfVec, Polynomial.coeff_add, Polynomial.coeff_X_pow, coeff_sum_fin]
  simp

lemma coeff_polyOfVec_gt (n H : ℕ) (v : BddVec n H) {j : ℕ} (hj : n < j) :
    (polyOfVec n H v).coeff j = 0 := by
  rw [polyOfVec, Polynomial.coeff_add, Polynomial.coeff_X_pow, coeff_sum_fin]
  have hjn : ¬ j < n := by omega
  rw [dif_neg hjn]
  rw [if_neg (ne_of_gt hj)]
  simp

lemma polyOfVec_natDegree (n H : ℕ) (v : BddVec n H) : (polyOfVec n H v).natDegree = n := by
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact coeff_polyOfVec_gt n H v hN
  · by_contra h
    have hlt : (polyOfVec n H v).natDegree < n := by omega
    have hc0 : (polyOfVec n H v).coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    have hc1 : (polyOfVec n H v).coeff n = 1 := coeff_polyOfVec_n n H v
    rw [hc1] at hc0
    norm_num at hc0

lemma polyOfVec_monic (n H : ℕ) (v : BddVec n H) : (polyOfVec n H v).Monic := by
  rw [Polynomial.Monic.def]
  rw [← Polynomial.coeff_natDegree]
  rw [polyOfVec_natDegree]
  exact coeff_polyOfVec_n n H v

/-- `polyOfVec` produces a polynomial in the box. -/
theorem polyOfVec_mem_box (n H : ℕ) (v : BddVec n H) : polyOfVec n H v ∈ Box n H := by
  refine ⟨polyOfVec_monic n H v, ?_, ?_⟩
  · rw [Polynomial.degree_eq_natDegree]
    · exact_mod_cast polyOfVec_natDegree n H v
    · exact Polynomial.Monic.ne_zero (polyOfVec_monic n H v)
  · intro i hi
    rw [coeff_polyOfVec_lt n H v hi]
    exact (v ⟨i, hi⟩).2

/-- `polyOfVec` as a map into the box. -/
noncomputable def polyOfVecBox (n H : ℕ) (v : BddVec n H) : ↥(Box n H) :=
  ⟨polyOfVec n H v, polyOfVec_mem_box n H v⟩

/-- The polynomial-with-given-coefficients map is injective. -/
theorem polyOfVec_injective (n H : ℕ) :
    Function.Injective (polyOfVecBox n H) := by
  intro v w h
  have hp := congrArg Subtype.val h
  apply _root_.funext
  intro i
  have hc := congrArg (fun p : ℤ[X] => p.coeff i.1) hp
  change (polyOfVec n H v).coeff i.1 = (polyOfVec n H w).coeff i.1 at hc
  rw [coeff_polyOfVec_lt n H v i.2] at hc
  rw [coeff_polyOfVec_lt n H w i.2] at hc
  exact Subtype.ext hc

/-- Exact count of the box: `(2H+1)^n`. -/
theorem Box_ncard_eq (n H : ℕ) : (Box n H).ncard = (2 * H + 1) ^ n := by
  rw [ncard_eq_natCard (Box n H)]
  apply le_antisymm
  · calc
      Nat.card (↥(Box n H)) ≤ Nat.card (BddVec n H) :=
        Nat.card_le_card_of_injective coeffVec (coeffVec_injective n H)
      _ = (2 * H + 1) ^ n := bddVec_card n H
  · calc
      (2 * H + 1) ^ n = Nat.card (BddVec n H) := (bddVec_card n H).symm
      _ ≤ Nat.card (↥(Box n H)) := Nat.card_le_card_of_injective (polyOfVecBox n H)
        (polyOfVec_injective n H)

end

end Submission.Vdw
