import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.NatAbs
import Mathlib.RingTheory.Polynomial.Resultant.Basic

open Polynomial

set_option autoImplicit false

namespace Commons.Data.Int.Polynomial

open scoped BigOperators

/-- `natAbs` of a scalar multiple by an integer unit is `natAbs` of the scalar. -/
private lemma natAbs_units_smul (u : ℤˣ) (x : ℤ) : (u • x).natAbs = x.natAbs := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

/-- Crude determinant bound: an `N × N` integer matrix with all entries bounded in
`natAbs` by `B` has `natAbs (det) ≤ N! * B^N`. -/
private lemma det_natAbs_le (N : ℕ) (A : Matrix (Fin N) (Fin N) ℤ) {B : ℕ}
    (h : ∀ i j, (A i j).natAbs ≤ B) : A.det.natAbs ≤ N.factorial * B ^ N := by
  rw [Matrix.det_apply]
  have hsmul (σ : Equiv.Perm (Fin N)) (x : ℤ) : (Equiv.Perm.sign σ • x).natAbs = x.natAbs := by
    exact natAbs_units_smul (Equiv.Perm.sign σ) x
  have hmap (σ : Equiv.Perm (Fin N)) :
      (∏ i : Fin N, A (σ i) i).natAbs = ∏ i : Fin N, (A (σ i) i).natAbs := by
    exact map_prod Int.natAbsHom (fun i : Fin N => A (σ i) i) Finset.univ
  calc
    (∑ σ : Equiv.Perm (Fin N), Equiv.Perm.sign σ • ∏ i : Fin N, A (σ i) i).natAbs
        ≤ ∑ σ : Equiv.Perm (Fin N), (Equiv.Perm.sign σ • ∏ i : Fin N, A (σ i) i).natAbs := by
          simpa using (Int.natAbs_sum_le Finset.univ (fun σ : Equiv.Perm (Fin N) =>
            Equiv.Perm.sign σ • ∏ i : Fin N, A (σ i) i))
    _ = ∑ σ : Equiv.Perm (Fin N), ∏ i : Fin N, (A (σ i) i).natAbs := by
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          rw [hsmul, hmap]
    _ ≤ ∑ _σ : Equiv.Perm (Fin N), ∏ _i : Fin N, B := by
          refine Finset.sum_le_sum ?_
          intro σ hσ
          exact Finset.prod_le_prod' (fun i _ => h _ _)
    _ = N.factorial * B ^ N := by
          simp [Fintype.card_perm]

/-- The entry of a Sylvester matrix in the first `m` columns (the `Fin m` block). -/
private lemma sylvester_apply_castAdd {m n : ℕ} (f g : ℤ[X]) (i : Fin (m + n)) (j₁ : Fin m) :
    ((Polynomial.sylvester f g m n) i (Fin.castAdd n j₁)) =
      if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + n) then g.coeff ((i : ℕ) - (j₁ : ℕ)) else 0 := by
  simp [Polynomial.sylvester, Fin.addCases_left]

/-- The entry of a Sylvester matrix in the last `n` columns (the `Fin n` block). -/
private lemma sylvester_apply_natAdd {m n : ℕ} (f g : ℤ[X]) (i : Fin (m + n)) (j₁ : Fin n) :
    ((Polynomial.sylvester f g m n) i (Fin.natAdd m j₁)) =
      if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + m) then f.coeff ((i : ℕ) - (j₁ : ℕ)) else 0 := by
  simp [Polynomial.sylvester, Fin.addCases_right]

/-- Every entry of a Sylvester matrix is bounded by a common bound `B` for the
`natAbs` of all coefficients of `f` and `g`. -/
private lemma sylvester_entry_natAbs_le {m n : ℕ} {f g : ℤ[X]} {B : ℕ}
    (hf : ∀ k : ℕ, (f.coeff k).natAbs ≤ B) (hg : ∀ k : ℕ, (g.coeff k).natAbs ≤ B) :
    ∀ i j : Fin (m + n), ((Polynomial.sylvester f g m n) i j).natAbs ≤ B := by
  intro i j
  have hlt_or : (j : ℕ) < m ∨ m ≤ (j : ℕ) := lt_or_ge _ _
  rcases hlt_or with hj | hj
  · have hjc : Fin.castAdd n ⟨(j : ℕ), hj⟩ = j := by
      ext; simp
    rw [← hjc]
    rw [sylvester_apply_castAdd]
    split_ifs with h
    · simpa using hg ((i : ℕ) - (j : ℕ))
    · exact Nat.zero_le _
  · have hjc : Fin.natAdd m ⟨(j : ℕ) - m, by omega⟩ = j := by
      ext; simp; omega
    rw [← hjc]
    rw [sylvester_apply_natAdd]
    split_ifs with h
    · simpa using hf ((i : ℕ) - ((j : ℕ) - m))
    · exact Nat.zero_le _

/-- `sylvesterDeriv` is obtained from the Sylvester matrix of `f.derivative` and `f`
by replacing the last row by a row with entries `1`, `f.natDegree` and `0`. -/
private lemma sylvesterDeriv_eq_updateRow {f : ℤ[X]} (hf : 0 < f.natDegree) :
    f.sylvesterDeriv =
      (f.derivative.sylvester f (f.natDegree - 1) f.natDegree).updateRow
        (⟨2 * f.natDegree - 2, by omega⟩ : Fin (f.natDegree - 1 + f.natDegree))
        (fun j : Fin (f.natDegree - 1 + f.natDegree) =>
          if (j : ℕ) = f.natDegree - 2 then (1 : ℤ)
          else if (j : ℕ) = 2 * f.natDegree - 2 then (f.natDegree : ℤ) else 0) := by
  rw [Polynomial.sylvesterDeriv]
  simp [hf.ne']

/-- If a monic polynomial of degree `n` has all coefficients below the leading one
bounded in absolute value by `H`, then every coefficient has `natAbs ≤ H + 1`. -/
private lemma coeff_natAbs_le {n H : ℕ} {f : ℤ[X]} (hfM : f.Monic) (hfdeg : f.natDegree = n)
    (hcoeff : ∀ k < n, |f.coeff k| ≤ (H : ℤ)) : ∀ k, (f.coeff k).natAbs ≤ H + 1 := by
  intro k
  by_cases hk : k < n
  · have h1 : (f.coeff k).natAbs ≤ H := by
      have hc := hcoeff k hk
      rw [Int.abs_eq_natAbs] at hc
      exact_mod_cast hc
    exact Nat.le_trans h1 (Nat.le_succ H)
  · have hkn : n ≤ k := le_of_not_gt hk
    rcases lt_or_eq_of_le hkn with hlt | heq
    · have hzero : f.coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
      simp [hzero]
    · have hc : f.coeff k = 1 := by
        subst k
        rw [← hfdeg, Polynomial.coeff_natDegree]
        exact Polynomial.Monic.leadingCoeff hfM
      simp [hc]

/-- Coefficients of the derivative of a polynomial whose coefficients are all
bounded by `H + 1` have `natAbs ≤ n * (H + 1)`. -/
private lemma deriv_coeff_natAbs_le {n H : ℕ} {f : ℤ[X]} (hfdeg : f.natDegree = n)
    (hfcoeff : ∀ k, (f.coeff k).natAbs ≤ H + 1) :
    ∀ k, (f.derivative.coeff k).natAbs ≤ n * (H + 1) := by
  intro k
  by_cases hk : k + 1 ≤ n
  · have hk1 : (((k : ℤ) + 1).natAbs) = k + 1 := by
      have hcast : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by
        norm_num [Nat.cast_add, Nat.cast_one]
      rw [hcast, Int.natAbs_natCast]
    calc
      (f.derivative.coeff k).natAbs = (f.coeff (k + 1)).natAbs * (k + 1) := by
        rw [Polynomial.coeff_derivative, Int.natAbs_mul, hk1]
      _ ≤ (H + 1) * (k + 1) := by
        exact Nat.mul_le_mul_right (k + 1) (hfcoeff (k + 1))
      _ ≤ (H + 1) * n := by
        exact Nat.mul_le_mul_left (H + 1) hk
      _ = n * (H + 1) := by rw [Nat.mul_comm]
  · have hnlt : n < k + 1 := Nat.lt_of_not_ge hk
    have hzero : f.coeff (k + 1) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
    rw [Polynomial.coeff_derivative, hzero, zero_mul, Int.natAbs_zero]
    exact Nat.zero_le _

/-- The modified bottom row of `sylvesterDeriv` has all entries bounded by `n * (H + 1)`. -/
private lemma row'_natAbs_le {n H : ℕ} {f : ℤ[X]} (hfdeg : f.natDegree = n) (hn : 1 ≤ n) :
    ∀ j : Fin (f.natDegree - 1 + f.natDegree),
      (if (j : ℕ) = f.natDegree - 2 then (1 : ℤ)
       else if (j : ℕ) = 2 * f.natDegree - 2 then (f.natDegree : ℤ) else 0).natAbs ≤ n * (H + 1) := by
  intro j
  by_cases h1 : (j : ℕ) = f.natDegree - 2
  · rw [if_pos h1]
    simp
    have h1le : 1 ≤ H + 1 := by omega
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ n * (H + 1) := Nat.mul_le_mul hn h1le
  · rw [if_neg h1]
    by_cases h2 : (j : ℕ) = 2 * f.natDegree - 2
    · rw [if_pos h2]
      rw [Int.natAbs_natCast]
      rw [hfdeg]
      have h1le : 1 ≤ H + 1 := by omega
      calc
        n = n * 1 := by rw [Nat.mul_one]
        _ ≤ n * (H + 1) := Nat.mul_le_mul_left n h1le
    · rw [if_neg h2]
      simp

/-- Every entry of `sylvesterDeriv` is bounded in `natAbs` by `n * (H + 1)`. -/
private lemma sylvesterDeriv_entry_natAbs_le {n H : ℕ} {f : ℤ[X]} (hfdeg : f.natDegree = n)
    (hf0 : 0 < f.natDegree)
    (hfcoeff : ∀ k, (f.coeff k).natAbs ≤ n * (H + 1))
    (hf'coeff : ∀ k, (f.derivative.coeff k).natAbs ≤ n * (H + 1)) :
    ∀ i j : Fin (f.natDegree - 1 + f.natDegree), (f.sylvesterDeriv i j).natAbs ≤ n * (H + 1) := by
  intro i j
  rw [sylvesterDeriv_eq_updateRow hf0]
  rw [Matrix.updateRow_apply]
  by_cases hii : i = (⟨2 * f.natDegree - 2, by omega⟩ : Fin (f.natDegree - 1 + f.natDegree))
  · simp [hii]
    exact row'_natAbs_le hfdeg (by rw [← hfdeg]; omega) j
  · simp [hii]
    exact sylvester_entry_natAbs_le hf'coeff hfcoeff i j

/-- Crude height bound on the polynomial discriminant of a monic integer
polynomial whose non-leading coefficients are bounded by `H`: needed to cap
the absolute discriminant `D = |Disc(K_f)|` of the number field cut out by a
box polynomial `f` (then `D ≤ |Disc(f)|` by Dedekind), so that the Case-I
squarefull tail sum can run over a finite range `Y < D ≤ Z(H)` with
`log Z = O(log H)` (any polynomial-in-`H` cap suffices: the tail estimate's
polylog factor in `log Z` is absorbed by the exponent margin).  Proof route:
`Polynomial.discr f` is (up to sign) the determinant of the
`(2n−1)×(2n−1)` matrix `f.sylvesterDeriv` (`Polynomial.discr` definition in
`RingTheory/Polynomial/Resultant/Basic.lean`); every entry of that matrix is
bounded in absolute value by `n*(H+1)` (its rows carry coefficients of `f`
and of `f.derivative`, all `≤ n*H`, plus the replaced row with entries in
`{1,…,n}`); expand the determinant as `∑ σ, sign σ • ∏ᵢ M(σ i) i`
(`Matrix.det_apply`) and bound termwise by `max^(2n−1)`, with
`Fintype.card_perm` for the number of permutations `(2n−1)!`.  -/
theorem discr_height_bound (n H : ℕ) (f : ℤ[X]) (hfM : f.Monic)
    (hfdeg : f.natDegree = n) (hcoeff : ∀ k < n, |f.coeff k| ≤ (H : ℤ)) :
    (Polynomial.discr f).natAbs ≤ (2 * n - 1).factorial * (n * (H + 1)) ^ (2 * n - 1) := by
  by_cases hn0 : n = 0
  · have hdeg0 : f.natDegree = 0 := by simpa [hn0] using hfdeg
    have hC : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
    rw [hC, Polynomial.discr_C]
    norm_num [hn0]
  · have hn : 1 ≤ n := by omega
    have hf0 : 0 < f.natDegree := by omega
    have hcoeff1 : ∀ k, (f.coeff k).natAbs ≤ H + 1 := coeff_natAbs_le hfM hfdeg hcoeff
    have hcoeffn : ∀ k, (f.coeff k).natAbs ≤ n * (H + 1) := by
      intro k
      have hHn : H + 1 ≤ n * (H + 1) := by
        calc H + 1 = 1 * (H + 1) := by rw [Nat.one_mul]
             _ ≤ n * (H + 1) := Nat.mul_le_mul_right (H + 1) hn
      exact Nat.le_trans (hcoeff1 k) hHn
    have hderiv : ∀ k, (f.derivative.coeff k).natAbs ≤ n * (H + 1) :=
      deriv_coeff_natAbs_le hfdeg hcoeff1
    have hdiscr : (Polynomial.discr f).natAbs = (f.sylvesterDeriv.det).natAbs := by
      rw [Polynomial.discr]
      simp [Int.natAbs_mul, Int.natAbs_pow]
    have hentry : ∀ i j : Fin (f.natDegree - 1 + f.natDegree),
        (f.sylvesterDeriv i j).natAbs ≤ n * (H + 1) :=
      sylvesterDeriv_entry_natAbs_le hfdeg hf0 hcoeffn hderiv
    have hdet : (f.sylvesterDeriv.det).natAbs ≤
        (f.natDegree - 1 + f.natDegree).factorial * (n * (H + 1)) ^ (f.natDegree - 1 + f.natDegree) := by
      simpa using det_natAbs_le (f.natDegree - 1 + f.natDegree) f.sylvesterDeriv hentry
    calc
      (Polynomial.discr f).natAbs = (f.sylvesterDeriv.det).natAbs := hdiscr
      _ ≤ (f.natDegree - 1 + f.natDegree).factorial * (n * (H + 1)) ^ (f.natDegree - 1 + f.natDegree) := hdet
      _ = (2 * n - 1).factorial * (n * (H + 1)) ^ (2 * n - 1) := by
        have hdim : f.natDegree - 1 + f.natDegree = 2 * n - 1 := by omega
        rw [hdim]

end Commons.Data.Int.Polynomial