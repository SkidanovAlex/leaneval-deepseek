import Mathlib
import Submission.Vdw.DDFamInt
import Submission.Vdw.PolyIndex
import Submission.Commons.FieldTheory.Polynomial.discr_sq_dvd_of_index_ge_two

open Polynomial
open scoped BigOperators

set_option autoImplicit false

/-!
# Case III: from mod-`p` index ≥ 2 to `p | DD(u)` (the per-prime geometric-sieve input)

Bhargava, proof of Theorem 1, Case III: for a bad irreducible `f` and a ramified prime
`p` with `p > n`, Lemma 24 (field version) gives `index(f̄ mod p) ≥ v_p(D_f) ≥ 2`
(`D_f` squarefull).  Case III then needs: for the double discriminant
`DD(u) = Disc_t(Disc_X(f_t))` (`u` the upper coefficients of `f`), the prime `p`
divides `DD(u)` — because `Disc(f)` is a multiple of `p²` "for mod-`p` reasons"
(`discr_sq_dvd_of_index_ge_two`, commons L81), which along the constant-coefficient
fibre is exactly the stability hypothesis of
`DDFamInt.prime_dvd_concDDZ_of_modp_stable`.

This module assembles that chain at the ℤ-polynomial level (no number fields):

* `monicOfUpper n u c` — the monic degree-`n` polynomial with upper coefficients
  `u : Fin (n-1) → ℤ` (coefficient of `X^(j+1)`) and constant term `c` (defined as the
  `t ↦ c`-specialisation of the `ℤ[t]`-family `concFamilyZ`);
* `upperCoeffs n f` — the upper coefficient vector of `f`;
* `concInnerZ_eval_eq_discr` — `P_u(c) = Disc(monicOfUpper n u c)`;
* **`prime_dvd_concDDZ_of_index_ge_two`** — `f` monic degree `n`, prime `p > n` with
  `polyIndex(f̄ mod p) ≥ 2` ⟹ `p | concDDZ n (upperCoeffs n f)`.
-/

noncomputable section

namespace Submission.Vdw

/-- The upper coefficient vector of a polynomial (coefficients of `X^1,…,X^(n-1)`). -/
def upperCoeffs (n : ℕ) (f : ℤ[X]) : Fin (n - 1) → ℤ := fun j => f.coeff ((j : ℕ) + 1)

/-- Substituting the constant coefficient `t ↦ c` in the `ℤ[t]`-family: the monic
degree-`n` polynomial with upper coefficients `u` and constant term `c`. -/
noncomputable def monicOfUpper (n : ℕ) (u : Fin (n - 1) → ℤ) (c : ℤ) : ℤ[X] :=
  Polynomial.map (Polynomial.eval₂RingHom (RingHom.id ℤ) c) (concFamilyZ n u)

/-- Coefficient of `X^(j+1)` in the `ℤ[t]`-family is the constant `C (u j)`. -/
lemma concFamilyZ_coeff_add_one (n : ℕ) (u : Fin (n - 1) → ℤ) (j : Fin (n - 1)) :
    (concFamilyZ n u).coeff ((j : ℕ) + 1) = Polynomial.C (u j) := by
  classical
  unfold concFamilyZ
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  have hX : (X ^ n : (Polynomial ℤ)[X]).coeff ((j : ℕ) + 1) = 0 := by
    rw [Polynomial.coeff_X_pow]
    simp [show (j : ℕ) + 1 ≠ n by
      intro h
      have hjle : (j : ℕ) + 1 ≤ n - 1 := (j : Fin (n - 1)).isLt
      omega]
  have hC : (Polynomial.C (Polynomial.X : Polynomial ℤ) : (Polynomial ℤ)[X]).coeff
      ((j : ℕ) + 1) = 0 := by
    rw [Polynomial.coeff_C]
    simp
  have hsum : (∑ b : Fin (n - 1), Polynomial.C (Polynomial.C (u b)) * X ^ ((b : ℕ) + 1)
      : (Polynomial ℤ)[X]).coeff ((j : ℕ) + 1) = Polynomial.C (u j) := by
    rw [coeff_finset_sum]
    rw [Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul_X_pow]
      rw [if_pos rfl]
    · intro b hb hbne
      rw [Polynomial.coeff_C_mul_X_pow]
      rw [if_neg]
      · intro h
        apply hbne
        ext
        omega
    · intro hmem
      simp at hmem
  rw [hX, hC, hsum]
  simp

/-- Constant term of the `ℤ[t]`-family is the variable `t`. -/
lemma concFamilyZ_coeff_zero (n : ℕ) (hn : 1 ≤ n) (u : Fin (n - 1) → ℤ) :
    (concFamilyZ n u).coeff 0 = (Polynomial.X : Polynomial ℤ) := by
  classical
  unfold concFamilyZ
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  have hX : (X ^ n : (Polynomial ℤ)[X]).coeff 0 = 0 := by
    rw [Polynomial.coeff_X_pow]
    simp [show 0 ≠ n by omega]
  have hC : (Polynomial.C (Polynomial.X : Polynomial ℤ) : (Polynomial ℤ)[X]).coeff 0 =
      Polynomial.X := by simp
  have hsum : (∑ j : Fin (n - 1), Polynomial.C (Polynomial.C (u j)) * X ^ ((j : ℕ) + 1)
      : (Polynomial ℤ)[X]).coeff 0 = 0 := by
    rw [coeff_finset_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Polynomial.coeff_C_mul_X_pow]
    rw [if_neg (by omega : 0 ≠ (j : ℕ) + 1)]
  rw [hX, hC, hsum]
  simp

/-- Constant term of `monicOfUpper` is `c`. -/
lemma monicOfUpper_coeff_zero (n : ℕ) (hn : 1 ≤ n) (u : Fin (n - 1) → ℤ) (c : ℤ) :
    (monicOfUpper n u c).coeff 0 = c := by
  rw [monicOfUpper, Polynomial.coeff_map, concFamilyZ_coeff_zero n hn u]
  simp

/-- Coefficient `X^(j+1)` of `monicOfUpper` is `u j`. -/
lemma monicOfUpper_coeff_add_one (n : ℕ) (u : Fin (n - 1) → ℤ) (c : ℤ) (j : Fin (n - 1)) :
    (monicOfUpper n u c).coeff ((j : ℕ) + 1) = u j := by
  rw [monicOfUpper, Polynomial.coeff_map, concFamilyZ_coeff_add_one n u j]
  simp

/-- Top coefficient of `monicOfUpper` is 1. -/
lemma monicOfUpper_coeff_n (n : ℕ) (hn : 1 ≤ n) (u : Fin (n - 1) → ℤ) (c : ℤ) :
    (monicOfUpper n u c).coeff n = 1 := by
  rw [monicOfUpper, Polynomial.coeff_map, concFamilyZ_coeff_ge n hn n (le_rfl) u]
  simp

/-- Higher coefficients of `monicOfUpper` vanish. -/
lemma monicOfUpper_coeff_gt (n : ℕ) (hn : 1 ≤ n) (u : Fin (n - 1) → ℤ) (c : ℤ) (k : ℕ)
    (hk : n < k) :
    (monicOfUpper n u c).coeff k = 0 := by
  rw [monicOfUpper, Polynomial.coeff_map, concFamilyZ_coeff_ge n hn k (le_of_lt hk) u]
  simp [ne_of_gt hk]

/-- `monicOfUpper` is monic of degree `n`. -/
lemma monicOfUpper_monic_natDegree (n : ℕ) (hn : 1 ≤ n) (u : Fin (n - 1) → ℤ) (c : ℤ) :
    (monicOfUpper n u c).Monic ∧ (monicOfUpper n u c).natDegree = n := by
  classical
  let φ : Polynomial ℤ →+* ℤ := Polynomial.eval₂RingHom (RingHom.id ℤ) c
  have hmon : (concFamilyZ n u).Monic := (concFamilyZ_monic_natDegree n hn u).1
  have hdeg : (monicOfUpper n u c).natDegree = n := by
    dsimp [monicOfUpper]
    rw [hmon.natDegree_map φ]
    exact (concFamilyZ_monic_natDegree n hn u).2
  constructor
  · rw [Monic.def, Polynomial.leadingCoeff, hdeg]
    exact monicOfUpper_coeff_n n hn u c
  · exact hdeg

/-- Substituting the constant coefficient `t ↦ c` commutes with `Disc_X`: the value of
`P_u(t) = Disc_X(f_t)` at `t = c` is the discriminant of the concrete polynomial. -/
lemma concInnerZ_eval_eq_discr (n : ℕ) (hn : 1 ≤ n) (u : Fin (n - 1) → ℤ) (c : ℤ) :
    (concInnerZ n u).eval c = Polynomial.discr (monicOfUpper n u c) := by
  classical
  let φ : Polynomial ℤ →+* ℤ := Polynomial.eval₂RingHom (RingHom.id ℤ) c
  have hmon : (concFamilyZ n u).Monic := (concFamilyZ_monic_natDegree n hn u).1
  have hnd : (Polynomial.map φ (concFamilyZ n u)).natDegree = (concFamilyZ n u).natDegree := by
    exact hmon.natDegree_map φ
  have hcomm := Commons.RingTheory.Polynomial.discr_map_of_natDegree φ hnd
  change φ (Polynomial.discr (concFamilyZ n u)) = Polynomial.discr (monicOfUpper n u c)
  rw [hcomm]
  congr 1

/-- **Case III per prime:** `f` monic degree `n`, prime `p > n`, and the reduction of `f`
mod `p` has index ≥ 2 ⟹ `p | DD(u)` where `u` are the upper coefficients of `f`. -/
theorem prime_dvd_concDDZ_of_index_ge_two (p : ℕ) [Fact (Nat.Prime p)] {n : ℕ}
    (hn3 : 3 ≤ n) (hpgt : n < p) (f : ℤ[X]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hind : 2 ≤ polyIndex (F := ZMod p) (Polynomial.map (Int.castRingHom (ZMod p)) f)) :
    (p : ℤ) ∣ concDDZ n (upperCoeffs n f) := by
  classical
  let u : Fin (n - 1) → ℤ := upperCoeffs n f
  let a₀ : ℤ := f.coeff 0
  have hn1 : 1 ≤ n := by omega
  have hpn : ¬ p ∣ n := by
    intro hpd
    have hpnle : p ≤ n := Nat.le_of_dvd (by omega) hpd
    omega
  have hstab : ∀ d : ℤ, ((p : ℤ) ^ 2) ∣ (concInnerZ n u).eval (a₀ + (p : ℤ) * d) := by
    intro d
    let g : ℤ[X] := monicOfUpper n u (a₀ + (p : ℤ) * d)
    have hgmon : g.Monic := (monicOfUpper_monic_natDegree n hn1 u (a₀ + (p : ℤ) * d)).1
    have hgdeg : g.natDegree = n := (monicOfUpper_monic_natDegree n hn1 u (a₀ + (p : ℤ) * d)).2
    have hcong : ∀ i < n, (g.coeff i : ZMod p) = (f.coeff i : ZMod p) := by
      intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        rw [monicOfUpper_coeff_zero n hn1 u (a₀ + (p : ℤ) * d)]
        dsimp [g, a₀, u, upperCoeffs]
        norm_num
      · have hi1 : 1 ≤ i := by omega
        have hj : i - 1 < n - 1 := by omega
        have hiadd : i = ((i - 1 : ℕ) + 1) := by omega
        rw [hiadd]
        rw [monicOfUpper_coeff_add_one n u (a₀ + (p : ℤ) * d) ⟨i - 1, hj⟩]
        dsimp [g, u, upperCoeffs]
    have hp2dvd : (p : ℤ) ^ 2 ∣ Polynomial.discr g := by
      exact Commons.FieldTheory.Polynomial.discr_sq_dvd_of_index_ge_two p hpgt f hf hdeg
        (by simpa [polyIndex] using hind) g hgmon hgdeg hcong
    have hdisc : Polynomial.discr g = (concInnerZ n u).eval (a₀ + (p : ℤ) * d) := by
      rw [concInnerZ_eval_eq_discr n hn1 u (a₀ + (p : ℤ) * d)]
    rwa [← hdisc]
  exact prime_dvd_concDDZ_of_modp_stable p (Fact.out : Nat.Prime p) (n := n) (hn := hn3) (hpn := hpn)
    u a₀ hstab

end Submission.Vdw
