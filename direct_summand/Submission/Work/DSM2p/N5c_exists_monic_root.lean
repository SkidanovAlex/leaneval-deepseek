import Mathlib
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.PERFD_T

/-!
# N5c — a monic `p^j`-th root of `F(T)` in `Λ = A[T^{1/p^∞}]` modulo `p`

Node **N5c** of the Česnavičius–Scholze single-polynomial design
(`sources/dsmap/direct_summand_m2p_h2_design.md`, §2).  For a perfectoid `A`, a monic
`F ∈ A[T]` and `j : ℕ`, there is a monic `g ∈ A[T]` with

`g(T^{1/p^j}) ^ (p^j) ≡ F(T)  (mod p)`  in `Λ = Lam1 A p = A[T^{1/p^∞}]`.

## Proof

Write `X = T^{1/p^j}` and `T = T^{1/p^0}`, so `X ^ (p^j) = T`.  Iterating `P.frobSurj`
(`x ≡ y ^ p mod p`) `j` times shows that every element of `A` has a `p^j`-th root modulo
`(p)`.  Choose such a root `c i` of each coefficient `F.coeff i` (and put `c n := 1` at the
leading index, which is legitimate since `F.coeff n = 1` for `n = F.natDegree`), and set

`g := Σ_{i ∈ F.support} C (c i) · X ^ i`.

This is monic: its degree-`n` coefficient is `c n = 1` and all coefficients of degree `> n`
vanish.  Finally, in `Λ` modulo `(p)` the `p^j`-th power map is additive
(`Finset_sum_pow_pow_sub_sum_pow_mem`, iterating the Freshman's dream `sum_pow_sub_mem`),
so

`g(X) ^ (p^j) ≡ Σ_i c_i ^ (p^j) X ^ (i·p^j) = Σ_i c_i ^ (p^j) T ^ i ≡ Σ_i F.coeff i T ^ i
= F(T)  (mod p)`,

because `c_i ^ (p^j) ≡ F.coeff i (mod p)` and `X ^ (p^j) = T`.  For a trivial (`Subsingleton`)
coefficient ring everything is trivial and `g := F` works.
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-- **Iterated Frobenius surjectivity modulo `p`.**  If every element of `A` has a `p`-th root
modulo `(p)` (the `frobSurj` field of `PerfectoidData`), then every element has a `p ^ j`-th root
modulo `(p)`. -/
theorem exists_sub_pow_eq_mem_span_p (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (j : ℕ) (x : A) :
    ∃ y : A, x - y ^ (p ^ j) ∈ Ideal.span {(p : A)} := by
  induction j with
  | zero => exact ⟨x, by simp⟩
  | succ j ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨z, hz⟩ := P.frobSurj y
    refine ⟨z, ?_⟩
    have h1 : y ^ (p ^ j) - z ^ (p ^ (j + 1)) ∈ Ideal.span {(p : A)} := by
      have hzp : z ^ (p ^ (j + 1)) = (z ^ p) ^ (p ^ j) := by rw [pow_succ', pow_mul]
      obtain ⟨w, hw⟩ := sub_dvd_pow_sub_pow y (z ^ p) (p ^ j)
      rw [hzp, hw]
      exact Ideal.mul_mem_right w _ hz
    rw [show x - z ^ (p ^ (j + 1)) =
      (x - y ^ (p ^ j)) + (y ^ (p ^ j) - z ^ (p ^ (j + 1))) from by ring]
    exact Ideal.add_mem _ hy h1

/-- **Iterated Freshman's dream modulo `p`.**  The `p ^ j`-th power of a finite sum differs from
the sum of the `p ^ j`-th powers of the summands by a multiple of `p`. -/
theorem Finset_sum_pow_pow_sub_sum_pow_mem {R : Type*} [CommRing R] {α : Type*} {p : ℕ}
    (hp : p.Prime) (j : ℕ) (s : Finset α) (u : α → R) :
    (∑ i ∈ s, u i) ^ (p ^ j) - ∑ i ∈ s, (u i) ^ (p ^ j) ∈ Ideal.span {(p : R)} := by
  induction j with
  | zero => simp
  | succ j ih =>
    set S : R := ∑ i ∈ s, u i with hS
    set T : R := ∑ i ∈ s, (u i) ^ (p ^ j) with hT
    set z : R := S ^ (p ^ j) - T with hz
    have hzI : z ∈ Ideal.span {(p : R)} := ih
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp T z
    have hS_eq : S ^ (p ^ j) = T + z := by rw [hz]; ring
    have hmain : S ^ (p ^ (j + 1)) = (T + z) ^ p := by rw [Nat.pow_succ, pow_mul, hS_eq]
    have hTp : T ^ p - ∑ i ∈ s, (u i) ^ (p ^ (j + 1)) ∈ Ideal.span {(p : R)} := by
      have h := Finset_sum_pow_sub_sum_pow_mem hp s (fun i => (u i) ^ (p ^ j))
      have hT' : (∑ i ∈ s, (u i) ^ (p ^ j)) ^ p = T ^ p := by rw [hT]
      have hcongr : (∑ i ∈ s, ((u i) ^ (p ^ j)) ^ p) = ∑ i ∈ s, (u i) ^ (p ^ (j + 1)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← pow_mul, Nat.pow_succ]
      rw [hcongr] at h
      rwa [hT'] at h
    have hzpow : z ^ p ∈ Ideal.span {(p : R)} := by
      have h2 : z ^ p = z ^ (p - 1) * z := by rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
      rw [h2]
      exact Ideal.mul_mem_left _ _ hzI
    have hpTzr : (p : R) * T * z * r ∈ Ideal.span {(p : R)} := by
      rw [show (p : R) * T * z * r = (T * z * r) * (p : R) from by ring]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self (p : R))
    have hcomb : S ^ (p ^ (j + 1)) - ∑ i ∈ s, (u i) ^ (p ^ (j + 1))
        = (T ^ p - ∑ i ∈ s, (u i) ^ (p ^ (j + 1))) + z ^ p + (p : R) * T * z * r := by
      rw [hmain, hr]; ring
    rw [hcomb]
    exact Ideal.add_mem _ (Ideal.add_mem _ hTp hzpow) hpTzr

/-- `(T^{1/p^j}) ^ (p^j) = T`, i.e. `(T1 A p j) ^ (p ^ j) = T1 A p 0`. -/
theorem T1_pow_pow (A : Type*) [CommRing A] (p : ℕ) (j : ℕ) :
    (T1 A p j) ^ (p ^ j) = T1 A p 0 := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', pow_mul, T1_pow A p j, ih]

/-- The image of a multiple of `p` under a ring homomorphism is a multiple of `p`. -/
theorem algebraMap_mem_span_p {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (p : ℕ)
    {x : A} (hx : x ∈ Ideal.span {(p : A)}) : f x ∈ Ideal.span {(p : B)} := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  rw [hy, map_mul, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self (p : B))

theorem N5c_exists_monic_root (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) (hF : F.Monic) (j : ℕ) :
    ∃ g : Polynomial A, g.Monic ∧
      (Polynomial.aeval (T1 A p j) g) ^ (p ^ j) - Polynomial.aeval (T1 A p 0) F ∈
        Ideal.span {(p : Lam1 A p)} := by
  classical
  have hp : p.Prime := Fact.out
  rcases subsingleton_or_nontrivial A with hA | hA
  · -- trivial coefficient ring: everything is `0` and `F` is already monic
    haveI := hA
    refine ⟨F, hF, ?_⟩
    haveI : Subsingleton (Lam1 A p) := inferInstance
    have h0 : (Polynomial.aeval (T1 A p j) F) ^ (p ^ j)
        - Polynomial.aeval (T1 A p 0) F = 0 := Subsingleton.elim _ _
    rw [h0]
    exact Ideal.zero_mem _
  · haveI : Nontrivial A := hA
    set n : ℕ := F.natDegree with hn
    -- coefficientwise `p ^ j`-th roots modulo `(p)`
    have hroot : ∀ i : ℕ, ∃ c : A, c ^ (p ^ j) - F.coeff i ∈ Ideal.span {(p : A)} := by
      intro i
      obtain ⟨c, hc⟩ := exists_sub_pow_eq_mem_span_p A p P j (F.coeff i)
      refine ⟨c, ?_⟩
      have hh : c ^ (p ^ j) - F.coeff i = -(F.coeff i - c ^ (p ^ j)) := by ring
      rw [hh]
      exact neg_mem hc
    let c : ℕ → A := fun i => if i = n then 1 else Classical.choose (hroot i)
    have hcn : c n = 1 := by simp [c]
    have hc : ∀ i : ℕ, (c i) ^ (p ^ j) - F.coeff i ∈ Ideal.span {(p : A)} := by
      intro i
      by_cases hi : i = n
      · have hc_n : (c n) ^ (p ^ j) - F.coeff n ∈ Ideal.span {(p : A)} := by
          have hFn : F.coeff n = 1 := by rw [hn, hF.coeff_natDegree]
          rw [hcn, hFn, one_pow]
          have h1 : (1 : A) - 1 = 0 := sub_self 1
          rw [h1]
          exact Ideal.zero_mem _
        rw [hi]
        exact hc_n
      · have hci : c i = Classical.choose (hroot i) := by simp [c, hi]
        rw [hci]
        exact Classical.choose_spec (hroot i)
    set g : Polynomial A := F.support.sum (fun i => Polynomial.monomial i (c i)) with hg
    -- monicity of `g`
    have hmem_n : n ∈ F.support := by
      rw [Polynomial.mem_support_iff, hn, hF.coeff_natDegree]
      exact one_ne_zero
    have hcoeff_n : g.coeff n = 1 := by
      rw [hg, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single n]
      · rw [Polynomial.coeff_monomial, if_pos rfl, hcn]
      · intro i _ hi
        rw [Polynomial.coeff_monomial, if_neg hi]
      · intro hn'
        exact absurd hmem_n hn'
    have hcoeff_gt : ∀ m, n < m → g.coeff m = 0 := by
      intro m hm
      rw [hg, Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Polynomial.coeff_monomial]
      by_cases h : i = m
      · exfalso
        have h1 : F.coeff m ≠ 0 := by
          rw [← h]
          exact (Polynomial.mem_support_iff).mp hi
        have h2 : F.coeff m = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [← hn]; exact hm)
        exact h1 h2
      · rw [if_neg h]
    have hM : g.Monic := by
      have hnle : g.natDegree ≤ n := (Polynomial.natDegree_le_iff_coeff_eq_zero).mpr hcoeff_gt
      have hnd : g.natDegree = n :=
        Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hnle (by rw [hcoeff_n]; exact one_ne_zero)
      show g.leadingCoeff = 1
      rw [Polynomial.leadingCoeff, hnd, hcoeff_n]
    refine ⟨g, hM, ?_⟩
    -- evaluation of `g` and of `F`
    have hFx : F = ∑ i ∈ F.support, Polynomial.monomial i (F.coeff i) := by
      conv_lhs => rw [← Polynomial.sum_monomial_eq F]
      exact Polynomial.sum_def F (fun n a => Polynomial.monomial n a)
    have hXg : Polynomial.aeval (T1 A p j) g
        = ∑ i ∈ F.support, algebraMap A (Lam1 A p) (c i) * (T1 A p j) ^ i := by
      rw [hg, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.aeval_monomial]
    have hTF : Polynomial.aeval (T1 A p 0) F
        = ∑ i ∈ F.support, algebraMap A (Lam1 A p) (F.coeff i) * (T1 A p 0) ^ i := by
      conv_lhs => rw [hFx]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.aeval_monomial]
    have hroot' : ∀ i : ℕ, (algebraMap A (Lam1 A p) (c i)) ^ (p ^ j)
        - algebraMap A (Lam1 A p) (F.coeff i) ∈ Ideal.span {(p : Lam1 A p)} := by
      intro i
      have hmap := algebraMap_mem_span_p (algebraMap A (Lam1 A p)) p (hc i)
      rwa [map_sub, map_pow] at hmap
    -- the three pieces
    have hpow1 : (Polynomial.aeval (T1 A p j) g) ^ (p ^ j)
        - ∑ i ∈ F.support, (algebraMap A (Lam1 A p) (c i)) ^ (p ^ j) * (T1 A p 0) ^ i
        ∈ Ideal.span {(p : Lam1 A p)} := by
      have h1 := Finset_sum_pow_pow_sub_sum_pow_mem hp j F.support
        (fun i => algebraMap A (Lam1 A p) (c i) * (T1 A p j) ^ i)
      have hcongr : (∑ i ∈ F.support,
            (algebraMap A (Lam1 A p) (c i) * (T1 A p j) ^ i) ^ (p ^ j))
          = ∑ i ∈ F.support, (algebraMap A (Lam1 A p) (c i)) ^ (p ^ j) * (T1 A p 0) ^ i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_pow, ← pow_mul, mul_comm i (p ^ j), pow_mul, T1_pow_pow]
      rw [hcongr] at h1
      rw [← hXg] at h1
      exact h1
    have hpow2 : (∑ i ∈ F.support, (algebraMap A (Lam1 A p) (c i)) ^ (p ^ j) * (T1 A p 0) ^ i)
        - ∑ i ∈ F.support, algebraMap A (Lam1 A p) (F.coeff i) * (T1 A p 0) ^ i
        ∈ Ideal.span {(p : Lam1 A p)} := by
      rw [← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun i _ => ?_
      have h1 := Ideal.mul_mem_right ((T1 A p 0) ^ i) _ (hroot' i)
      rwa [sub_mul] at h1
    have hfinal : (Polynomial.aeval (T1 A p j) g) ^ (p ^ j) - Polynomial.aeval (T1 A p 0) F
        = ((Polynomial.aeval (T1 A p j) g) ^ (p ^ j)
            - ∑ i ∈ F.support, (algebraMap A (Lam1 A p) (c i)) ^ (p ^ j) * (T1 A p 0) ^ i)
          + ((∑ i ∈ F.support, (algebraMap A (Lam1 A p) (c i)) ^ (p ^ j) * (T1 A p 0) ^ i)
            - ∑ i ∈ F.support, algebraMap A (Lam1 A p) (F.coeff i) * (T1 A p 0) ^ i)
          + ((∑ i ∈ F.support, algebraMap A (Lam1 A p) (F.coeff i) * (T1 A p 0) ^ i)
            - Polynomial.aeval (T1 A p 0) F) := by
      rw [hTF]; ring
    rw [hfinal]
    refine Ideal.add_mem _ (Ideal.add_mem _ hpow1 hpow2) ?_
    rw [hTF, sub_self]
    exact Ideal.zero_mem _

end Work.DSM2p
