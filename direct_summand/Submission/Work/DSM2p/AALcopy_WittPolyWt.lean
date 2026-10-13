-- Redirected copy of `Submission.Work.DSM2p.WittPolyWt` (imports re-pointed to the `AALvaln` vocabulary layer so that
-- `area_AAL_proved.lean` can import the result without an import cycle).  The original
-- file is untouched; this copy is generated mechanically.
import Mathlib
import Submission.Work.DSM2p.AALcopy_approx_defs

/-!
# Weights of Witt addition / multiplication polynomials

This file owns the *integrality* gadget on which the sup-norm (digit-bound) calculus of
`Work.DSM2p.witt_step_rec` rests.

## The weight

For a variable type `σ` and a "height" `ρ : σ → ℕ`, the *weight* of a monomial
`m : σ →₀ ℕ` is `monWt ρ m = ∑ x, m x * ρ x`, and `WtLe ρ P N` says that every monomial
occurring in `P` has weight at least `N`.

## Main results

* `WtLe.mul`, `WtLe.add`, `WtLe.pow`, `WtLe.monomial`, `WtLe.sum` — the weight bound is
  compatible with the ring operations.
* `wtLe_rename_wittPolynomial` — the (renamed) Witt polynomial has all monomials of weight
  exactly `p ^ n` for the height `ρ (i, j) = p ^ j`.
* `wtLe_wittStructureRat_add` / `wtLe_wittStructureRat_mul` (and the row-weight variants) — the
  Witt structure polynomials of `X 0 + X 1` and `X 0 * X 1` have monomials of weight `≥ p ^ n`.

The last two are what makes Witt addition and multiplication "integral" for the Gauss norm: a
monomial of degree pattern `(a_{ij})` contributes the factor `∏ β_i^{∑_j a_{ij} p^j}`, and the
weight statement controls the exponent.
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.DSM2p

open WittVector MvPolynomial

section PolyWeight

variable {σ : Type*} {R : Type*} [CommRing R]

/-- The weight of a monomial `m` with respect to a "height" `ρ` on the variables. -/
noncomputable def monWt (ρ : σ → ℕ) (m : σ →₀ ℕ) : ℕ := m.sum (fun x k => k * ρ x)

theorem monWt_add (ρ : σ → ℕ) (m₁ m₂ : σ →₀ ℕ) :
    monWt ρ (m₁ + m₂) = monWt ρ m₁ + monWt ρ m₂ := by
  rw [monWt, monWt, monWt]
  exact Finsupp.sum_add_index' (fun a => by simp) (fun a b₁ b₂ => by simp [add_mul])

theorem monWt_single (ρ : σ → ℕ) (x : σ) (k : ℕ) :
    monWt ρ (Finsupp.single x k) = k * ρ x := by
  rw [monWt, Finsupp.sum_single_index]
  simp

theorem monWt_zero (ρ : σ → ℕ) : monWt ρ 0 = 0 := by
  rw [monWt, Finsupp.sum_zero_index]

/-- `WtLe ρ P N` : every monomial of `P` has weight at least `N`. -/
def WtLe (ρ : σ → ℕ) (P : MvPolynomial σ R) (N : ℕ) : Prop :=
  ∀ m : σ →₀ ℕ, P.coeff m ≠ 0 → N ≤ monWt ρ m

theorem WtLe.mono {ρ : σ → ℕ} {N N' : ℕ} {P : MvPolynomial σ R} (h : N' ≤ N)
    (hP : WtLe ρ P N) : WtLe ρ P N' := fun m hm => le_trans h (hP m hm)

theorem WtLe.zero (ρ : σ → ℕ) : WtLe ρ (0 : MvPolynomial σ R) 0 := by
  intro m hm; exact absurd hm (by simp)

theorem WtLe.triv (ρ : σ → ℕ) (P : MvPolynomial σ R) : WtLe ρ P 0 := fun _ _ => Nat.zero_le _

theorem WtLe.add {ρ : σ → ℕ} {N N' : ℕ} {P Q : MvPolynomial σ R}
    (hP : WtLe ρ P N) (hQ : WtLe ρ Q N') : WtLe ρ (P + Q) (min N N') := by
  classical
  intro m hm
  rw [show (P + Q).coeff m = P.coeff m + Q.coeff m from rfl] at hm
  rcases eq_or_ne (P.coeff m) 0 with h | h
  · rw [h, zero_add] at hm
    exact le_trans (min_le_right N N') (hQ m hm)
  · exact le_trans (min_le_left N N') (hP m h)

theorem WtLe.neg {ρ : σ → ℕ} {N : ℕ} {P : MvPolynomial σ R} (hP : WtLe ρ P N) :
    WtLe ρ (-P) N := by
  intro m hm
  rw [coeff_neg] at hm
  exact hP m (by simpa using hm)

theorem WtLe.sub {ρ : σ → ℕ} {N N' : ℕ} {P Q : MvPolynomial σ R}
    (hP : WtLe ρ P N) (hQ : WtLe ρ Q N') : WtLe ρ (P - Q) (min N N') := by
  rw [sub_eq_add_neg]
  exact WtLe.add hP (WtLe.neg hQ)

theorem WtLe.mul {ρ : σ → ℕ} {N N' : ℕ} {P Q : MvPolynomial σ R}
    (hP : WtLe ρ P N) (hQ : WtLe ρ Q N') : WtLe ρ (P * Q) (N + N') := by
  classical
  intro m hm
  rw [coeff_mul] at hm
  obtain ⟨x, hx, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have h1 : P.coeff x.1 ≠ 0 := fun h => hxne (by rw [h, zero_mul])
  have h2 : Q.coeff x.2 ≠ 0 := fun h => hxne (by rw [h, mul_zero])
  have hxmem := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [← hxmem, monWt_add]
  exact add_le_add (hP x.1 h1) (hQ x.2 h2)

theorem WtLe.C (ρ : σ → ℕ) (c : R) : WtLe ρ (MvPolynomial.C c) 0 := by
  classical
  intro m hm
  rw [coeff_C m c] at hm
  by_cases h : (0 : σ →₀ ℕ) = m
  · subst h; exact Nat.zero_le _
  · rw [ite_eq_right (by simpa using h)] at hm; exact absurd rfl hm

theorem WtLe.monomial (ρ : σ → ℕ) (m : σ →₀ ℕ) (c : R) :
    WtLe ρ (MvPolynomial.monomial m c) (monWt ρ m) := by
  classical
  intro m' hm'
  rw [coeff_monomial m' m c] at hm'
  by_cases h : m = m'
  · subst h; exact le_rfl
  · rw [ite_eq_right h] at hm'; exact absurd rfl hm'

theorem WtLe.pow {ρ : σ → ℕ} {N : ℕ} {P : MvPolynomial σ R} (hP : WtLe ρ P N) (n : ℕ) :
    WtLe ρ (P ^ n) (n * N) := by
  induction n with
  | zero => simpa using (WtLe.C (ρ := ρ) (1 : R) : WtLe ρ (MvPolynomial.C (1 : R)) 0)
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact WtLe.mul ih hP

theorem WtLe.sum {ρ : σ → ℕ} {N : ℕ} {ι : Type*} {s : Finset ι}
    {f : ι → MvPolynomial σ R} (h : ∀ i ∈ s, WtLe ρ (f i) N) :
    WtLe ρ (∑ i ∈ s, f i) N := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; intro m hm; exact absurd hm (by simp)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have h3 := WtLe.add h1 h2
    rwa [min_self] at h3

end PolyWeight

/-! ## The height used below -/

section Main

variable {p : ℕ} [Fact p.Prime]

/-- The height `ρ (i, j) = p ^ j` on `Fin 2 × ℕ`. -/
noncomputable def rho2 : Fin 2 × ℕ → ℕ := fun x => p ^ x.2

/-- The height concentrated on the `i`-th row. -/
noncomputable def rhoRow (i : Fin 2) : Fin 2 × ℕ → ℕ := fun x => if x.1 = i then p ^ x.2 else 0

theorem monWt_rho2_single (b : Fin 2) (i : ℕ) :
    monWt (rho2 (p := p)) (Finsupp.single (b, i) 1) = p ^ i := by
  rw [monWt_single]; simp [rho2]

theorem monWt_rhoRow_single_self (b : Fin 2) (i : ℕ) :
    monWt (rhoRow (p := p) b) (Finsupp.single (b, i) 1) = p ^ i := by
  rw [monWt_single]; simp [rhoRow]

theorem monWt_rhoRow_single_ne {b b' : Fin 2} (h : b ≠ b') (i : ℕ) :
    monWt (rhoRow (p := p) b) (Finsupp.single (b', i) 1) = 0 := by
  rw [monWt_single]
  simp only [rhoRow, if_neg (Ne.symm h), mul_zero]

/-- The renamed `n`-th Witt polynomial, written as an explicit sum of monomials.  All of its
monomials have weight `p ^ n` for the height `ρ (i,j) = p ^ j`. -/
theorem rename_wittPolynomial_eq (R : Type*) [CommRing R] (b : Fin 2) (n : ℕ) :
    rename (fun i : ℕ => (b, i)) (wittPolynomial p R n) =
      ∑ i ∈ Finset.range (n + 1),
        monomial (Finsupp.single (b, i) (p ^ (n - i))) ((p : R) ^ i) := by
  rw [wittPolynomial_eq_sum_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, rename_C, rename_X]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow (MvPolynomial.C : R →+* MvPolynomial (Fin 2 × ℕ) R)]
  rw [C_mul_X_pow_eq_monomial]

theorem wtLe_rename_wittPolynomial (R : Type*) [CommRing R] (ρ : Fin 2 × ℕ → ℕ) (b : Fin 2)
    (n : ℕ) (hρ : ∀ j : ℕ, ρ (b, j) = p ^ j) :
    WtLe ρ (rename (fun i : ℕ => (b, i)) (wittPolynomial p R n)) (p ^ n) := by
  classical
  rw [rename_wittPolynomial_eq R]
  refine WtLe.sum fun j hj => ?_
  rw [Finset.mem_range] at hj
  have h : monWt ρ (Finsupp.single (b, j) (p ^ (n - j))) = p ^ n := by
    rw [monWt_single, hρ, ← pow_add]
    congr 1
    omega
  simpa [h] using WtLe.monomial ρ (Finsupp.single (b, j) (p ^ (n - j))) ((p : R) ^ j)

theorem wtLe_rename_wittPolynomial_rho2 (R : Type*) [CommRing R] (b : Fin 2) (n : ℕ) :
    WtLe (rho2 (p := p)) (rename (fun i : ℕ => (b, i)) (wittPolynomial p R n)) (p ^ n) :=
  wtLe_rename_wittPolynomial R _ b n (fun _ => rfl)

theorem wtLe_rename_wittPolynomial_rhoRow (R : Type*) [CommRing R] (b : Fin 2) (n : ℕ) :
    WtLe (rhoRow (p := p) b) (rename (fun i : ℕ => (b, i)) (wittPolynomial p R n)) (p ^ n) :=
  wtLe_rename_wittPolynomial R _ b n (fun _ => by simp [rhoRow])

end Main

section WittStruct

variable {p : ℕ} [Fact p.Prime]

/-- The `n`-th Witt structure polynomial of `X 0 + X 1`, over `ℚ`. -/
noncomputable def wittAddRat (p : ℕ) [Fact p.Prime] (n : ℕ) : MvPolynomial (Fin 2 × ℕ) ℚ :=
  wittStructureRat p (X 0 + X 1 : MvPolynomial (Fin 2) ℚ) n

/-- The `n`-th Witt structure polynomial of `X 0 * X 1`, over `ℚ`. -/
noncomputable def wittMulRat (p : ℕ) [Fact p.Prime] (n : ℕ) : MvPolynomial (Fin 2 × ℕ) ℚ :=
  wittStructureRat p (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) n

theorem wittAddRat_rec (n : ℕ) :
    wittAddRat p n * MvPolynomial.C ((p : ℚ) ^ n) =
      (bind₁ (fun b : Fin 2 => rename (Prod.mk b) (wittPolynomial p ℚ n))
          (X 0 + X 1 : MvPolynomial (Fin 2) ℚ))
        - ∑ i ∈ Finset.range n, MvPolynomial.C ((p : ℚ) ^ i) * wittAddRat p i ^ (p ^ (n - i)) := by
  rw [wittAddRat, wittStructureRat_rec_aux]
  simp only [wittAddRat]

theorem wittMulRat_rec (n : ℕ) :
    wittMulRat p n * MvPolynomial.C ((p : ℚ) ^ n) =
      (bind₁ (fun b : Fin 2 => rename (Prod.mk b) (wittPolynomial p ℚ n))
          (X 0 * X 1 : MvPolynomial (Fin 2) ℚ))
        - ∑ i ∈ Finset.range n, MvPolynomial.C ((p : ℚ) ^ i) * wittMulRat p i ^ (p ^ (n - i)) := by
  rw [wittMulRat, wittStructureRat_rec_aux]
  simp only [wittMulRat]

theorem qpow_ne_zero (n : ℕ) : ((p : ℚ) ^ n) ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

/-- **The Witt addition polynomial is integral for the Gauss norm.**  Every monomial of the
`n`-th Witt structure polynomial of `X 0 + X 1` has total weight at least `p ^ n`, where the
weight of the variable `X (i,j)` is `p ^ j`. -/
theorem wtLe_wittAddRat (n : ℕ) :
    WtLe (rho2 (p := p)) (wittAddRat p n) (p ^ n) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hB : WtLe (rho2 (p := p))
        (bind₁ (fun b : Fin 2 => rename (Prod.mk b) (wittPolynomial p ℚ n))
          (X 0 + X 1 : MvPolynomial (Fin 2) ℚ)) (p ^ n) := by
      rw [map_add, bind₁_X_right, bind₁_X_right]
      have h0 := wtLe_rename_wittPolynomial_rho2 (p := p) ℚ 0 n
      have h1 := wtLe_rename_wittPolynomial_rho2 (p := p) ℚ 1 n
      have h := WtLe.add h0 h1
      rwa [min_self] at h
    have hT : WtLe (rho2 (p := p))
        (∑ i ∈ Finset.range n, MvPolynomial.C ((p : ℚ) ^ i) * wittAddRat p i ^ (p ^ (n - i)))
        (p ^ n) := by
      refine WtLe.sum fun i hi => ?_
      rw [Finset.mem_range] at hi
      have hSi : WtLe (rho2 (p := p)) (wittAddRat p i) (p ^ i) := ih i hi
      have hpow := WtLe.pow hSi (p ^ (n - i))
      have hC : WtLe (rho2 (p := p)) (MvPolynomial.C ((p : ℚ) ^ i)) 0 := WtLe.C _ _
      have hmul := WtLe.mul hC hpow
      rw [Nat.zero_add, ← pow_add, Nat.sub_add_cancel (le_of_lt hi)] at hmul
      exact hmul
    have hmain : WtLe (rho2 (p := p)) (wittAddRat p n * MvPolynomial.C ((p : ℚ) ^ n))
        (p ^ n) := by
      rw [wittAddRat_rec]
      exact WtLe.mono (le_of_eq (min_self _).symm) (WtLe.sub hB hT)
    intro m hm
    exact hmain m (by rw [mul_comm, coeff_C_mul]; exact mul_ne_zero (qpow_ne_zero n) hm)

/-- **The Witt multiplication polynomial is integral for the Gauss norm**, in the row-wise form
needed for submultiplicativity: every monomial of the `n`-th Witt structure polynomial of
`X 0 * X 1` has weight at least `p ^ n` in any fixed row `i`, where the weight of `X (i,j)` is
`p ^ j`. -/
theorem wtLe_wittMulRat_row (i : Fin 2) (n : ℕ) :
    WtLe (rhoRow (p := p) i) (wittMulRat p n) (p ^ n) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hB : WtLe (rhoRow (p := p) i)
        (bind₁ (fun b : Fin 2 => rename (Prod.mk b) (wittPolynomial p ℚ n))
          (X 0 * X 1 : MvPolynomial (Fin 2) ℚ)) (p ^ n) := by
      rw [map_mul, bind₁_X_right, bind₁_X_right]
      fin_cases i
      · have h0 := wtLe_rename_wittPolynomial_rhoRow (p := p) ℚ 0 n
        have h1 : WtLe (rhoRow (p := p) 0)
            (rename (Prod.mk 1) (wittPolynomial p ℚ n)) 0 := WtLe.triv _ _
        have h := WtLe.mul h0 h1
        rwa [add_zero] at h
      · have h0 : WtLe (rhoRow (p := p) 1)
            (rename (Prod.mk 0) (wittPolynomial p ℚ n)) 0 := WtLe.triv _ _
        have h1 := wtLe_rename_wittPolynomial_rhoRow (p := p) ℚ 1 n
        have h := WtLe.mul h0 h1
        rwa [zero_add] at h
    have hT : WtLe (rhoRow (p := p) i)
        (∑ j ∈ Finset.range n, MvPolynomial.C ((p : ℚ) ^ j) * wittMulRat p j ^ (p ^ (n - j)))
        (p ^ n) := by
      refine WtLe.sum fun j hj => ?_
      rw [Finset.mem_range] at hj
      have hSj : WtLe (rhoRow (p := p) i) (wittMulRat p j) (p ^ j) := ih j hj
      have hpow := WtLe.pow hSj (p ^ (n - j))
      have hC : WtLe (rhoRow (p := p) i) (MvPolynomial.C ((p : ℚ) ^ j)) 0 := WtLe.C _ _
      have hmul := WtLe.mul hC hpow
      rw [Nat.zero_add, ← pow_add, Nat.sub_add_cancel (le_of_lt hj)] at hmul
      exact hmul
    have hmain : WtLe (rhoRow (p := p) i) (wittMulRat p n * MvPolynomial.C ((p : ℚ) ^ n))
        (p ^ n) := by
      rw [wittMulRat_rec]
      exact WtLe.mono (le_of_eq (min_self _).symm) (WtLe.sub hB hT)
    intro m hm
    exact hmain m (by rw [mul_comm, coeff_C_mul]; exact mul_ne_zero (qpow_ne_zero n) hm)

end WittStruct

end Work.DSM2p

namespace Work.DSM2p

section MonWtSum
variable {σ : Type*}

theorem monWt_eq_sum (ρ : σ → ℕ) (m : σ →₀ ℕ) :
    monWt ρ m = ∑ x ∈ m.support, m x * ρ x := rfl

end MonWtSum

end Work.DSM2p
