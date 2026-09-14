import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial
open scoped BigOperators

noncomputable section

namespace Commons.Algebra.MvPolynomial

/-!
# Degree functions and bounding the discriminant

We develop a small theory of "degree functions" on a commutative ring: functions
`δ : R → ℕ` with `δ(a+b) ≤ max (δ a) (δ b)`, `δ(a*b) ≤ δ a + δ b`, `δ 1 = 0`,
which are then used to bound the total degree of discriminants.

The main goal is:
`doubleDiscr_totalDegree_le`: for the double-discriminant `dd` of the monic family
`x^n + a_0 x + ... + a_{n-2} x^{n-1} + t`, one has `dd.totalDegree ≤ (4n-3)(2n-1)`.
-/

/-- A function on a commutative ring behaving like a (total) degree:
additive up to max, subadditive for products, constants have degree 0. -/
structure Degree (R : Type*) [CommRing R] where
  δ : R → ℕ
  δ_zero : δ 0 = 0
  δ_one : δ 1 = 0
  δ_add_le : ∀ {a b : R}, δ (a + b) ≤ max (δ a) (δ b)
  δ_mul_le : ∀ {a b : R}, δ (a * b) ≤ δ a + δ b
  δ_neg_le : ∀ a : R, δ (-a) ≤ δ a

namespace Degree

variable {R : Type*} [CommRing R] (D : Degree R)

lemma δ_nsmul_le (k : ℕ) (a : R) : D.δ (k • a) ≤ D.δ a := by
  induction k with
  | zero => simp [D.δ_zero]
  | succ k ih =>
      calc
        D.δ ((k + 1) • a) = D.δ (k • a + a) := by rw [succ_nsmul a k]
        _ ≤ max (D.δ (k • a)) (D.δ a) := D.δ_add_le
        _ ≤ D.δ a := by exact max_le ih le_rfl

lemma δ_natCast (k : ℕ) : D.δ (k : R) ≤ 0 := by
  calc
    D.δ (k : R) = D.δ (k • (1 : R)) := by simp
    _ ≤ D.δ (1 : R) := D.δ_nsmul_le k 1
    _ = 0 := D.δ_one

lemma δ_sum_le {ι : Type*} (s : Finset ι) (f : ι → R) :
    D.δ (∑ i ∈ s, f i) ≤ s.sup fun i => D.δ (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [D.δ_zero]
  · intro a s has ih
    simp only [Finset.sum_insert has, Finset.sup_insert]
    calc
      D.δ (f a + ∑ x ∈ s, f x) ≤ max (D.δ (f a)) (D.δ (∑ x ∈ s, f x)) := D.δ_add_le
      _ ≤ max (D.δ (f a)) (s.sup fun i => D.δ (f i)) := max_le_max le_rfl ih

lemma δ_prod_le {ι : Type*} (s : Finset ι) (f : ι → R) :
    D.δ (∏ i ∈ s, f i) ≤ ∑ i ∈ s, D.δ (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [D.δ_one]
  · intro a s has ih
    simp only [Finset.prod_insert has, Finset.sum_insert has]
    calc
      D.δ (f a * ∏ x ∈ s, f x) ≤ D.δ (f a) + D.δ (∏ x ∈ s, f x) := D.δ_mul_le
      _ ≤ D.δ (f a) + ∑ x ∈ s, D.δ (f x) := Nat.add_le_add_left ih _

lemma δ_mul_zint_le {a : R} {z : ℤ} (h : z = 1 ∨ z = -1) :
    D.δ (((z : ℤ) : R) * a) ≤ D.δ a := by
  rcases h with rfl | rfl
  · simp
  · simpa using D.δ_neg_le a

lemma δ_det_le {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (K : ℕ)
    (hM : ∀ i j, D.δ (M i j) ≤ K) : D.δ M.det ≤ n * K := by
  classical
  rw [Matrix.det_apply']
  let f : Equiv.Perm (Fin n) → R := fun σ =>
    ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i : Fin n, M (σ i) i
  let g : Equiv.Perm (Fin n) → ℕ := fun σ =>
    ∑ i : Fin n, D.δ (M (σ i) i)
  have hf : ∀ σ, D.δ (f σ) ≤ g σ := by
    intro σ
    dsimp [f, g]
    calc
      D.δ (((Equiv.Perm.sign σ : ℤ) : R) * (∏ i : Fin n, M (σ i) i))
          ≤ D.δ (∏ i : Fin n, M (σ i) i) := by
            apply D.δ_mul_zint_le
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
            · left
              simpa using congrArg (fun u : ℤˣ => (u : ℤ)) h
            · right
              simpa using congrArg (fun u : ℤˣ => (u : ℤ)) h
      _ ≤ ∑ i : Fin n, D.δ (M (σ i) i) := by
            simpa using (D.δ_prod_le (Finset.univ : Finset (Fin n)) (fun i => M (σ i) i))
  calc
    D.δ (∑ σ : Equiv.Perm (Fin n), f σ) ≤
        (Finset.univ.sup fun σ => D.δ (f σ)) := D.δ_sum_le Finset.univ f
    _ ≤ (Finset.univ.sup fun σ => g σ) := by
      refine Finset.sup_le ?_
      intro σ hσ
      exact (hf σ).trans (Finset.le_sup (f := fun σ => g σ) hσ)
    _ ≤ n * K := by
      refine Finset.sup_le ?_
      intro σ hσ
      calc
        g σ = ∑ i : Fin n, D.δ (M (σ i) i) := rfl
        _ ≤ ∑ i : Fin n, K := Finset.sum_le_sum fun i hi => hM (σ i) i
        _ = n * K := by simp

/-- Bound entries of a Sylvester matrix. -/
lemma δ_sylvester_entry_le (u v : R[X]) (m n : ℕ) (K : ℕ)
    (hu : ∀ t, t ≤ m → D.δ (u.coeff t) ≤ K)
    (hv : ∀ t, t ≤ n → D.δ (v.coeff t) ≤ K) :
    ∀ (i : Fin (m + n)) (j : Fin (m + n)), D.δ ((u.sylvester v m n) i j) ≤ K := by
  intro i j
  classical
  rw [Polynomial.sylvester]
  change D.δ (j.addCases
    (fun j₁ : Fin m => if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + n) then v.coeff ((i : ℕ) - (j₁ : ℕ)) else 0)
    (fun j₁ : Fin n => if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + m) then u.coeff ((i : ℕ) - (j₁ : ℕ)) else 0)) ≤ K
  induction j using Fin.addCases with
  | left j₁ =>
      rw [Fin.addCases_left]
      by_cases h : (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + n)
      · have hle : (i : ℕ) - (j₁ : ℕ) ≤ n := by
          have hmem := (Set.mem_Icc.mp h)
          omega
        have hb : D.δ (v.coeff ((i : ℕ) - (j₁ : ℕ))) ≤ K := hv _ hle
        rw [if_pos h]; exact hb
      · rw [if_neg h]; simp [D.δ_zero]
  | right j₁ =>
      rw [Fin.addCases_right]
      by_cases h : (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + m)
      · have hle : (i : ℕ) - (j₁ : ℕ) ≤ m := by
          have hmem := (Set.mem_Icc.mp h)
          omega
        have hb : D.δ (u.coeff ((i : ℕ) - (j₁ : ℕ))) ≤ K := hu _ hle
        rw [if_pos h]; exact hb
      · rw [if_neg h]; simp [D.δ_zero]

/-- The discriminant has bounded degree: if the coefficients of `f` at indices `< 2 natDegree`
have degree ≤ the sup `K`, then `discr f` has degree ≤ `(natDegree - 1 + natDegree) * K`. -/
lemma δ_discr_le (f : R[X]) :
    D.δ (Polynomial.discr f) ≤
      (f.natDegree - 1 + f.natDegree) *
        (Finset.range (2 * f.natDegree)).sup (fun k => D.δ (f.coeff k)) := by
  classical
  by_cases hd : f.natDegree = 0
  · have hf : f = C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd
    rw [hf, Polynomial.discr_C]
    simp [D.δ_one, hd]
  · have hdpos : 0 < f.natDegree := Nat.pos_of_ne_zero hd
    let K := (Finset.range (2 * f.natDegree)).sup fun k => D.δ (f.coeff k)
    have hK : ∀ k, k < 2 * f.natDegree → D.δ (f.coeff k) ≤ K := by
      intro k hk
      exact Finset.le_sup (f := fun k => D.δ (f.coeff k)) (Finset.mem_range.mpr hk)
    have hKder : ∀ t, t + 1 < 2 * f.natDegree → D.δ ((derivative f).coeff t) ≤ K := by
      intro t ht
      calc
        D.δ ((derivative f).coeff t) = D.δ (f.coeff (t + 1) * ((t + 1 : ℕ) : R)) := by
          rw [Polynomial.coeff_derivative]; simp
        _ ≤ D.δ (f.coeff (t + 1)) + D.δ (((t + 1 : ℕ) : R)) := D.δ_mul_le
        _ ≤ K + 0 := Nat.add_le_add (hK (t + 1) ht) (D.δ_natCast (t + 1))
        _ = K := by omega
    have hsign : ∀ e : ℕ, D.δ ((-1 : R) ^ e) ≤ 0 := by
      intro e
      induction e with
      | zero => simp [D.δ_one]
      | succ e ih =>
          calc
            D.δ ((-1 : R) ^ (e + 1)) = D.δ ((-1 : R) ^ e * (-1 : R)) := by rw [pow_succ]
            _ ≤ D.δ ((-1 : R) ^ e) + D.δ (-1 : R) := D.δ_mul_le
            _ ≤ 0 + 0 := Nat.add_le_add ih (by simpa [D.δ_one] using D.δ_neg_le (1 : R))
            _ = 0 := by omega
    have hM : ∀ i j : Fin (f.natDegree - 1 + f.natDegree), D.δ ((Polynomial.sylvesterDeriv f) i j) ≤ K := by
      intro i j
      rw [Polynomial.sylvesterDeriv]
      rw [dif_neg hd]
      by_cases hiv : (i : ℕ) = 2 * f.natDegree - 2
      · have hi : i = (⟨2 * f.natDegree - 2, by omega⟩ : Fin (f.natDegree - 1 + f.natDegree)) := Fin.ext hiv
        rw [hi, Matrix.updateRow_self]
        by_cases hj1 : (j : ℕ) = f.natDegree - 2
        · rw [if_pos hj1]; simp [D.δ_one]
        · by_cases hj2 : (j : ℕ) = 2 * f.natDegree - 2
          · rw [if_neg hj1, if_pos hj2]
            exact le_trans (D.δ_natCast f.natDegree) (Nat.zero_le K)
          · rw [if_neg hj1, if_neg hj2]
            simp [D.δ_zero]
      · have hne : i ≠ (⟨2 * f.natDegree - 2, by omega⟩ : Fin (f.natDegree - 1 + f.natDegree)) := by
          intro h
          apply hiv
          exact congrArg (fun z : Fin (f.natDegree - 1 + f.natDegree) => (z : ℕ)) h
        rw [Matrix.updateRow_ne hne]
        refine D.δ_sylvester_entry_le (derivative f) f (f.natDegree - 1) f.natDegree K ?_ ?_ i j
        · intro t ht
          have ht' : t + 1 < 2 * f.natDegree := by omega
          exact hKder t ht'
        · intro t ht
          have ht' : t < 2 * f.natDegree := by omega
          exact hK t ht'
    calc
      D.δ (Polynomial.discr f) = D.δ ((Polynomial.sylvesterDeriv f).det * (-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2)) := by
        simp [Polynomial.discr]
      _ ≤ D.δ ((Polynomial.sylvesterDeriv f).det) + D.δ ((-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2)) := D.δ_mul_le
      _ ≤ (f.natDegree - 1 + f.natDegree) * K + 0 := by
        exact Nat.add_le_add (D.δ_det_le (Polynomial.sylvesterDeriv f) K hM) (hsign (f.natDegree * (f.natDegree - 1) / 2))
      _ = (f.natDegree - 1 + f.natDegree) * K := by omega
      _ = (f.natDegree - 1 + f.natDegree) * (Finset.range (2 * f.natDegree)).sup
            (fun k => D.δ (f.coeff k)) := by
        simp [K]

/-- A convenient form: if the coefficients of `f` at indices `< 2n` have degree ≤ 1 and
`natDegree f ≤ n`, then `discr f` has degree ≤ `2n-1`. -/
lemma δ_discr_le_of_coeff {f : R[X]} (n : ℕ) (hn : 1 ≤ n)
    (hdeg : f.natDegree ≤ n)
    (hc : ∀ k, k < 2 * n → D.δ (f.coeff k) ≤ 1) :
    D.δ (Polynomial.discr f) ≤ 2 * n - 1 := by
  classical
  have hs1 : (Finset.range (2 * f.natDegree)).sup (fun k => D.δ (f.coeff k)) ≤ 1 := by
    exact (Finset.sup_mono (Finset.range_mono (by omega))).trans
      (Finset.sup_le fun k hk => hc k (Finset.mem_range.mp hk))
  calc
    D.δ (Polynomial.discr f) ≤ (f.natDegree - 1 + f.natDegree) *
        (Finset.range (2 * f.natDegree)).sup (fun k => D.δ (f.coeff k)) := D.δ_discr_le f
    _ ≤ (2 * n - 1) * 1 := by
      exact Nat.mul_le_mul (by omega) hs1
    _ = 2 * n - 1 := by simp

end Degree

/-! ## Concrete degree functions -/

/-- `natDegree` as a degree function on a polynomial ring. -/
def natDegreeDegree (S : Type*) [CommRing S] : Degree (Polynomial S) where
  δ := Polynomial.natDegree
  δ_zero := Polynomial.natDegree_zero
  δ_one := Polynomial.natDegree_one
  δ_add_le := fun {a b} => Polynomial.natDegree_add_le a b
  δ_mul_le := fun {a b} => Polynomial.natDegree_mul_le
  δ_neg_le := fun a => (Polynomial.natDegree_neg a).le

/-- `totalDegree` as a degree function on a multivariate polynomial ring. -/
def totalDegreeDegree (σ : Type*) (F : Type*) [Field F] : Degree (MvPolynomial σ F) where
  δ := MvPolynomial.totalDegree
  δ_zero := MvPolynomial.totalDegree_zero
  δ_one := MvPolynomial.totalDegree_one
  δ_add_le := fun {a b} => MvPolynomial.totalDegree_add a b
  δ_mul_le := fun {a b} => MvPolynomial.totalDegree_mul a b
  δ_neg_le := fun a => (MvPolynomial.totalDegree_neg a).le

/-- The maximum total degree (over the base ring) of the coefficients of a polynomial. -/
def coeffTotalDegree (σ : Type*) (F : Type*) [Field F] (q : Polynomial (MvPolynomial σ F)) : ℕ :=
  q.support.sup fun k => (q.coeff k).totalDegree

namespace CoeffTD
variable {σ : Type*} {F : Type*} [Field F]

lemma coeff_le (q : Polynomial (MvPolynomial σ F)) (k : ℕ) :
    (q.coeff k).totalDegree ≤ coeffTotalDegree σ F q := by
  classical
  by_cases h : q.coeff k = 0
  · simp [coeffTotalDegree, h]
  · exact Finset.le_sup (f := fun k => (q.coeff k).totalDegree) (Polynomial.mem_support_iff.mpr h)

lemma add_le (a b : Polynomial (MvPolynomial σ F)) :
    coeffTotalDegree σ F (a + b) ≤ max (coeffTotalDegree σ F a) (coeffTotalDegree σ F b) := by
  classical
  rw [coeffTotalDegree]
  refine Finset.sup_le ?_
  intro k hk
  calc
    ((a + b).coeff k).totalDegree = (a.coeff k + b.coeff k).totalDegree := by simp
    _ ≤ max ((a.coeff k).totalDegree) ((b.coeff k).totalDegree) := MvPolynomial.totalDegree_add _ _
    _ ≤ max (coeffTotalDegree σ F a) (coeffTotalDegree σ F b) := by
      exact max_le_max (coeff_le a k) (coeff_le b k)

lemma mul_le (a b : Polynomial (MvPolynomial σ F)) :
    coeffTotalDegree σ F (a * b) ≤ coeffTotalDegree σ F a + coeffTotalDegree σ F b := by
  classical
  rw [coeffTotalDegree]
  refine Finset.sup_le ?_
  intro k hk
  calc
    ((a * b).coeff k).totalDegree
        ≤ (Finset.HasAntidiagonal.antidiagonal k).sup (fun x => ((a.coeff x.1 * b.coeff x.2).totalDegree)) := by
          rw [Polynomial.coeff_mul]
          exact MvPolynomial.totalDegree_finsetSum (Finset.HasAntidiagonal.antidiagonal k) (fun x => a.coeff x.1 * b.coeff x.2)
    _ ≤ coeffTotalDegree σ F a + coeffTotalDegree σ F b := by
      refine Finset.sup_le ?_
      intro x hx
      calc
        (a.coeff x.1 * b.coeff x.2).totalDegree
            ≤ (a.coeff x.1).totalDegree + (b.coeff x.2).totalDegree := MvPolynomial.totalDegree_mul _ _
        _ ≤ coeffTotalDegree σ F a + coeffTotalDegree σ F b := Nat.add_le_add (coeff_le a x.1) (coeff_le b x.2)

end CoeffTD

/-- The "coefficient total degree" `g_a`, a degree function on `Polynomial (MvPolynomial σ F)`. -/
def coeffTDegree (σ : Type*) (F : Type*) [Field F] : Degree (Polynomial (MvPolynomial σ F)) where
  δ := coeffTotalDegree σ F
  δ_zero := by
    classical
    simp [coeffTotalDegree]
  δ_one := by
    classical
    unfold coeffTotalDegree
    apply le_antisymm
    · refine Finset.sup_le ?_
      intro k hk
      have hk0 : k = 0 := by
        by_contra h
        have : (1 : Polynomial (MvPolynomial σ F)).coeff k = 0 := by
          rw [Polynomial.coeff_one, if_neg h]
        exact (Polynomial.mem_support_iff.mp hk) this
      subst k
      simp
    · exact Nat.zero_le _
  δ_add_le := fun {a b} => CoeffTD.add_le a b
  δ_mul_le := fun {a b} => CoeffTD.mul_le a b
  δ_neg_le := by
    intro a
    classical
    simp [coeffTotalDegree, MvPolynomial.totalDegree_neg]


/-! ## The concrete family and its double discriminant -/

/-- The family `x^n + Σ_j a_j x^(j+1) + t` over `F[a_0..a_{n-2}]`, with the outer polynomial
variable playing the role of `x` and the inner polynomial variable playing the role of `t`. -/
noncomputable def famPoly {F : Type*} [Field F] (n : ℕ) :
    Polynomial (Polynomial (MvPolynomial (Fin (n - 1)) F)) :=
  Polynomial.X ^ n + (∑ j : Fin (n - 1), Polynomial.C (Polynomial.C (MvPolynomial.X j)) * Polynomial.X ^ ((j : ℕ) + 1)) +
    Polynomial.C (Polynomial.X : Polynomial (MvPolynomial (Fin (n - 1)) F))

/-- First discriminant: a polynomial in `t` with coefficients in `F[a_0..a_{n-2}]`. -/
noncomputable def innerDisc {F : Type*} [Field F] (n : ℕ) :
    Polynomial (MvPolynomial (Fin (n - 1)) F) :=
  Polynomial.discr (famPoly n)

/-- The double discriminant `dd`. -/
noncomputable def ddPoly {F : Type*} [Field F] (n : ℕ) : MvPolynomial (Fin (n - 1)) F :=
  Polynomial.discr (innerDisc n)

/-- Coefficients of the family at indices `< 2n` have small degree, for any degree function
`D` that is small on the elementary building blocks. -/
lemma famPoly_coeff_δ_le {F : Type*} [Field F] {n k : ℕ}
    (D : Degree (Polynomial (MvPolynomial (Fin (n - 1)) F)))
    (h1 : D.δ (1 : Polynomial (MvPolynomial (Fin (n - 1)) F)) ≤ 1)
    (hX : D.δ (Polynomial.X : Polynomial (MvPolynomial (Fin (n - 1)) F)) ≤ 1)
    (hC : ∀ j : Fin (n - 1), D.δ (Polynomial.C (MvPolynomial.X j)) ≤ 1) :
    D.δ ((famPoly n).coeff k) ≤ 1 := by
  classical
  let R1 := Polynomial (MvPolynomial (Fin (n - 1)) F)
  have h1' : D.δ (1 : R1) ≤ 1 := h1
  have hX' : D.δ (Polynomial.X : R1) ≤ 1 := hX
  have hA : D.δ ((Polynomial.X ^ n : Polynomial R1).coeff k) ≤ 1 := by
    rw [Polynomial.coeff_X_pow]
    by_cases h : k = n
    · simp [h, h1']
    · simp [h, D.δ_zero]
  have hB : D.δ ((∑ j : Fin (n - 1),
        Polynomial.C (Polynomial.C (MvPolynomial.X j)) * Polynomial.X ^ ((j : ℕ) + 1) :
        Polynomial R1).coeff k) ≤ 1 := by
    calc
      D.δ ((∑ j : Fin (n - 1),
            (Polynomial.C (Polynomial.C (MvPolynomial.X j)) * Polynomial.X ^ ((j : ℕ) + 1) :
              Polynomial R1)).coeff k)
          = D.δ (∑ j : Fin (n - 1),
              if k = (j : ℕ) + 1 then Polynomial.C (MvPolynomial.X j) else (0 : Polynomial (MvPolynomial (Fin (n - 1)) F))) := by
            simp
      _ ≤ (Finset.univ : Finset (Fin (n - 1))).sup (fun j =>
              D.δ (if k = (j : ℕ) + 1 then Polynomial.C (MvPolynomial.X j) else (0 : Polynomial (MvPolynomial (Fin (n - 1)) F)))) := by
            exact D.δ_sum_le (Finset.univ : Finset (Fin (n - 1))) (fun j =>
              if k = (j : ℕ) + 1 then Polynomial.C (MvPolynomial.X j) else (0 : Polynomial (MvPolynomial (Fin (n - 1)) F)))
      _ ≤ 1 := by
        refine Finset.sup_le ?_
        intro j hj
        by_cases h : k = (j : ℕ) + 1
        · simp [h]; exact hC j
        · simp [h, D.δ_zero]

  have hC' : D.δ ((Polynomial.C (Polynomial.X : Polynomial (MvPolynomial (Fin (n - 1)) F)) :
        Polynomial R1).coeff k) ≤ 1 := by
    rw [Polynomial.coeff_C]
    by_cases h : k = 0
    · simp [h, hX']
    · simp [h, D.δ_zero]
  calc
    D.δ ((famPoly n).coeff k)
        = D.δ (((Polynomial.X ^ n : Polynomial R1).coeff k +
            (∑ j : Fin (n - 1), Polynomial.C (Polynomial.C (MvPolynomial.X j)) * Polynomial.X ^ ((j : ℕ) + 1) :
              Polynomial R1).coeff k) +
            (Polynomial.C (Polynomial.X : Polynomial (MvPolynomial (Fin (n - 1)) F)) :
              Polynomial R1).coeff k) := by
          simp [famPoly, Polynomial.coeff_add]
    _ ≤ max (D.δ (((Polynomial.X ^ n : Polynomial R1).coeff k +
              (∑ j : Fin (n - 1), Polynomial.C (Polynomial.C (MvPolynomial.X j)) * Polynomial.X ^ ((j : ℕ) + 1) :
                Polynomial R1).coeff k)))
            (D.δ ((Polynomial.C (Polynomial.X : Polynomial (MvPolynomial (Fin (n - 1)) F)) :
                Polynomial R1).coeff k)) := D.δ_add_le
    _ ≤ max (max (D.δ ((Polynomial.X ^ n : Polynomial R1).coeff k))
              (D.δ ((∑ j : Fin (n - 1), Polynomial.C (Polynomial.C (MvPolynomial.X j)) * Polynomial.X ^ ((j : ℕ) + 1) :
                Polynomial R1).coeff k)))
            (D.δ ((Polynomial.C (Polynomial.X : Polynomial (MvPolynomial (Fin (n - 1)) F)) :
                Polynomial R1).coeff k)) := by
          exact max_le_max D.δ_add_le le_rfl
    _ ≤ max (max 1 1) 1 := by
          exact max_le_max (max_le_max hA hB) hC'
    _ = 1 := by norm_num


/-- The outer `natDegree` of the family is at most `n`. -/
lemma natDegree_famPoly_le {F : Type*} [Field F] (n : ℕ) (hn : 1 ≤ n) :
    (famPoly (F := F) n).natDegree ≤ n := by
  classical
  rw [Polynomial.natDegree_le_iff_degree_le, Polynomial.degree_le_iff_coeff_zero]
  intro m hm
  have hmn : n < m := by
    exact_mod_cast (WithBot.coe_lt_coe.mp hm)
  let R1 := Polynomial (MvPolynomial (Fin (n - 1)) F)
  have hsum : (∑ j : Fin (n - 1),
        (Polynomial.C (Polynomial.C (MvPolynomial.X j)) * Polynomial.X ^ ((j : ℕ) + 1) :
          Polynomial R1).coeff m) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hne : m ≠ (j : ℕ) + 1 := by omega
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne]
    simp
  calc
    (famPoly n).coeff m
        = (Polynomial.X ^ n : Polynomial R1).coeff m +
          (∑ j : Fin (n - 1),
            Polynomial.C (Polynomial.C (MvPolynomial.X j)) * Polynomial.X ^ ((j : ℕ) + 1) :
            Polynomial R1).coeff m +
          (Polynomial.C (Polynomial.X : Polynomial (MvPolynomial (Fin (n - 1)) F)) :
            Polynomial R1).coeff m := by
          simp [famPoly, Polynomial.coeff_add]
    _ = 0 := by
      rw [Polynomial.coeff_X_pow, if_neg hmn.ne', Polynomial.coeff_C, if_neg (by omega)]
      have hcd : ((∑ j : Fin (n - 1),
            Polynomial.C (Polynomial.C (MvPolynomial.X j)) * Polynomial.X ^ ((j : ℕ) + 1) :
            Polynomial R1).coeff m) =
            ∑ j : Fin (n - 1),
            (Polynomial.C (Polynomial.C (MvPolynomial.X j)) * Polynomial.X ^ ((j : ℕ) + 1) :
              Polynomial R1).coeff m := by
            simp
      rw [hcd, hsum]
      simp



/-! ## Small-degree facts for the elementary building blocks -/

lemma natDeg_one_le {σ : Type*} (F : Type*) [Field F] :
    (natDegreeDegree (MvPolynomial σ F)).δ (1 : Polynomial (MvPolynomial σ F)) ≤ 1 := by
  simp [natDegreeDegree]

lemma natDeg_X_le {σ : Type*} (F : Type*) [Field F] :
    (natDegreeDegree (MvPolynomial σ F)).δ (Polynomial.X : Polynomial (MvPolynomial σ F)) ≤ 1 := by
  simp [natDegreeDegree]

lemma natDeg_C_le {σ : Type*} (F : Type*) [Field F] (a : MvPolynomial σ F) :
    (natDegreeDegree (MvPolynomial σ F)).δ (Polynomial.C a) ≤ 1 := by
  simp [natDegreeDegree]

lemma coeffTDeg_one_le (σ : Type*) {F : Type*} [Field F] :
    (coeffTDegree σ F).δ (1 : Polynomial (MvPolynomial σ F)) ≤ 1 := by
  classical
  change coeffTotalDegree σ F (1 : Polynomial (MvPolynomial σ F)) ≤ 1
  unfold coeffTotalDegree
  refine Finset.sup_le ?_
  intro k hk
  have hk0 : k = 0 := by
    by_contra h
    have : (1 : Polynomial (MvPolynomial σ F)).coeff k = 0 := by
      rw [Polynomial.coeff_one, if_neg h]
    exact (Polynomial.mem_support_iff.mp hk) this
  subst k
  simp

lemma coeffTDeg_X_le (σ : Type*) {F : Type*} [Field F] :
    (coeffTDegree σ F).δ (Polynomial.X : Polynomial (MvPolynomial σ F)) ≤ 1 := by
  classical
  change coeffTotalDegree σ F (Polynomial.X : Polynomial (MvPolynomial σ F)) ≤ 1
  unfold coeffTotalDegree
  refine Finset.sup_le ?_
  intro k hk
  have hk1 : k = 1 := by
    by_contra h
    have : (Polynomial.X : Polynomial (MvPolynomial σ F)).coeff k = 0 := by
      rw [Polynomial.coeff_X, if_neg (by simpa [eq_comm] using h)]
    exact (Polynomial.mem_support_iff.mp hk) this
  subst k
  simp

lemma coeffTDeg_C_X_le {σ : Type*} {F : Type*} [Field F] (j : σ) :
    (coeffTDegree σ F).δ (Polynomial.C (MvPolynomial.X j)) ≤ 1 := by
  classical
  change coeffTotalDegree σ F (Polynomial.C (MvPolynomial.X j) : Polynomial (MvPolynomial σ F)) ≤ 1
  unfold coeffTotalDegree
  refine Finset.sup_le ?_
  intro k hk
  have hk0 : k = 0 := by
    by_contra h
    have : (Polynomial.C (MvPolynomial.X j) : Polynomial (MvPolynomial σ F)).coeff k = 0 := by
      rw [Polynomial.coeff_C, if_neg h]
    exact (Polynomial.mem_support_iff.mp hk) this
  subst k
  simp

/-! ## Bounds on the discriminants -/

/-- The `t`-degree of the first discriminant is at most `2n-1`. -/
lemma innerDisc_natDegree_le {F : Type*} [Field F] (n : ℕ) (hn : 1 ≤ n) :
    (innerDisc (F := F) n).natDegree ≤ 2 * n - 1 := by
  classical
  let Dα : Degree (Polynomial (MvPolynomial (Fin (n - 1)) F)) := natDegreeDegree (MvPolynomial (Fin (n - 1)) F)
  have hdeg : (famPoly (F := F) n).natDegree ≤ n := natDegree_famPoly_le (F := F) n hn
  have hc : ∀ k, k < 2 * n → Dα.δ ((famPoly (F := F) n).coeff k) ≤ 1 := by
    intro k hk
    exact famPoly_coeff_δ_le (n := n) (k := k) Dα
      (natDeg_one_le (F := F))
      (natDeg_X_le (F := F))
      (fun j => natDeg_C_le (F := F) (MvPolynomial.X j))
  have hb := Degree.δ_discr_le_of_coeff Dα n hn hdeg hc
  simpa [innerDisc, Dα, natDegreeDegree] using hb

/-- The coefficients of the first discriminant (in the `t` variable) have total degree
at most `2n-1` over the base variables. -/
lemma innerDisc_coeffTotalDegree_le {F : Type*} [Field F] (n : ℕ) (hn : 1 ≤ n) :
    coeffTotalDegree (Fin (n - 1)) F (innerDisc (F := F) n) ≤ 2 * n - 1 := by
  classical
  let Dβ : Degree (Polynomial (MvPolynomial (Fin (n - 1)) F)) := coeffTDegree (Fin (n - 1)) F
  have hdeg : (famPoly (F := F) n).natDegree ≤ n := natDegree_famPoly_le (F := F) n hn
  have hc : ∀ k, k < 2 * n → Dβ.δ ((famPoly (F := F) n).coeff k) ≤ 1 := by
    intro k hk
    exact famPoly_coeff_δ_le (n := n) (k := k) Dβ
      (coeffTDeg_one_le (Fin (n - 1)) (F := F))
      (coeffTDeg_X_le (Fin (n - 1)) (F := F))
      (fun j => coeffTDeg_C_X_le (F := F) j)
  have hb := Degree.δ_discr_le_of_coeff Dβ n hn hdeg hc
  simpa [innerDisc, Dβ, coeffTDegree] using hb

/-- The main bound on the total degree of the double discriminant. -/
lemma dd_totalDegree_le {F : Type*} [Field F] (n : ℕ) (hn : 1 ≤ n) :
    (ddPoly (F := F) n).totalDegree ≤ (4 * n - 3) * (2 * n - 1) := by
  classical
  have hnd : (innerDisc (F := F) n).natDegree ≤ 2 * n - 1 := innerDisc_natDegree_le (F := F) n hn
  have hct : coeffTotalDegree (Fin (n - 1)) F (innerDisc (F := F) n) ≤ 2 * n - 1 :=
    innerDisc_coeffTotalDegree_le (F := F) n hn
  let Dγ : Degree (MvPolynomial (Fin (n - 1)) F) := totalDegreeDegree (Fin (n - 1)) F
  let inner := innerDisc (F := F) n
  have hnd' : inner.natDegree ≤ 2 * n - 1 := by
    simpa [inner] using hnd
  have hsup : (Finset.range (2 * inner.natDegree)).sup
      (fun k => (inner.coeff k).totalDegree) ≤ coeffTotalDegree (Fin (n - 1)) F inner := by
    refine Finset.sup_le ?_
    intro k hk
    exact CoeffTD.coeff_le inner k
  calc
    (ddPoly (F := F) n).totalDegree = Dγ.δ (Polynomial.discr inner) := by
      simp [ddPoly, inner, Dγ, totalDegreeDegree]
    _ ≤ (inner.natDegree - 1 + inner.natDegree) *
        (Finset.range (2 * inner.natDegree)).sup (fun k => (inner.coeff k).totalDegree) := by
          simpa [Dγ, totalDegreeDegree] using (Degree.δ_discr_le Dγ inner)
    _ ≤ (4 * n - 3) * (2 * n - 1) := by
      have hm : inner.natDegree - 1 + inner.natDegree ≤ 4 * n - 3 := by omega
      exact Nat.mul_le_mul hm (le_trans hsup hct)

/-- The double discriminant of the van der Waerden family has controlled total degree. -/
theorem doubleDiscr_totalDegree_le {F : Type*} [Field F] (n : ℕ) (hn : 1 ≤ n) :
    let P := MvPolynomial (Fin (n - 1)) F
    let fam : (Polynomial P)[X] :=
      X ^ n + (∑ j : Fin (n - 1), Polynomial.C (Polynomial.C (MvPolynomial.X j)) * X ^ ((j : ℕ) + 1)) +
        Polynomial.C (Polynomial.X : Polynomial P)
    let dd : P := Polynomial.discr (Polynomial.discr fam)
    dd.totalDegree ≤ (4 * n - 3) * (2 * n - 1) := by
  dsimp
  exact dd_totalDegree_le (F := F) n hn

end Commons.Algebra.MvPolynomial