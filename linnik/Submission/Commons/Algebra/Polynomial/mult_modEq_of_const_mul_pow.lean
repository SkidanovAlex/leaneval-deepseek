import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.Polynomial

/-- For a family `a : ι → K` over a finite type, the product `∏ i, (X + C (a i))` has, at the
root `-x`, multiplicity equal to the number of indices `i` with `a i = x`.  Equivalently, the
multiset of roots of the product of the linear factors `X + C (a i)` is the image of the index
set under `i ↦ -a i`, counted with multiplicity. -/
lemma roots_count_prod_X_add_C {K : Type*} [Field K] [DecidableEq K]
    {ι : Type*} [Fintype ι] (a : ι → K) (x : K) :
    (∏ i, (Polynomial.X + Polynomial.C (a i))).roots.count (-x)
      = (Finset.univ.filter (fun i => a i = x)).card := by
  classical
  have hne : (∏ i, (Polynomial.X + Polynomial.C (a i))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (Polynomial.monic_X_add_C (a i)).ne_zero)
  rw [Polynomial.roots_prod (fun i => Polynomial.X + Polynomial.C (a i)) Finset.univ hne]
  simp only [Polynomial.roots_X_add_C]
  rw [Multiset.bind_singleton]
  rw [Multiset.count_map]
  rw [← Finset.filter_val]
  congr 1
  ext i
  simp [eq_comm, neg_inj]

theorem mult_modEq_of_const_mul_pow
    {K : Type*} [Field K] [DecidableEq K] {r m : ℕ} (hm : 2 ≤ m)
    (a b : Fin r → K) {c : K} {Q : Polynomial K}
    (h : (∏ i, (Polynomial.X + Polynomial.C (a i)))
       * (∏ i, (Polynomial.X + Polynomial.C (b i))) ^ (m - 1)
       = Polynomial.C c * Q ^ m) :
    ∀ x : K, (Finset.univ.filter (fun i => a i = x)).card % m
           = (Finset.univ.filter (fun i => b i = x)).card % m := by
  classical
  intro x
  set na : ℕ := (Finset.univ.filter (fun i => a i = x)).card with hna
  set nb : ℕ := (Finset.univ.filter (fun i => b i = x)).card with hnb
  set A : Polynomial K := ∏ i, (Polynomial.X + Polynomial.C (a i)) with hA
  set B : Polynomial K := ∏ i, (Polynomial.X + Polynomial.C (b i)) with hB
  have hA0 : A ≠ 0 := by
    rw [hA]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => (Polynomial.monic_X_add_C (a i)).ne_zero)
  have hB0 : B ≠ 0 := by
    rw [hB]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => (Polynomial.monic_X_add_C (b i)).ne_zero)
  have hAB0 : A * B ^ (m - 1) ≠ 0 := mul_ne_zero hA0 (pow_ne_zero _ hB0)
  have hc : c ≠ 0 := by
    intro hc0
    apply hAB0
    rw [h, hc0, Polynomial.C_0, zero_mul]
  have hL : (A * B ^ (m - 1)).roots = A.roots + (m - 1) • B.roots := by
    rw [Polynomial.roots_mul hAB0, Polynomial.roots_pow]
  have hR : (Polynomial.C c * Q ^ m).roots = m • Q.roots := by
    rw [Polynomial.roots_C_mul (Q ^ m) hc, Polynomial.roots_pow]
  have hmult : A.roots + (m - 1) • B.roots = m • Q.roots := by
    rw [← hL, ← hR, h]
  have hcount := congrArg (fun s : Multiset K => s.count (-x)) hmult
  rw [Multiset.count_add, Multiset.count_nsmul, Multiset.count_nsmul] at hcount
  rw [hA, hB, roots_count_prod_X_add_C, roots_count_prod_X_add_C] at hcount
  rw [← hna, ← hnb] at hcount
  have hm1 : 1 ≤ m := by omega
  have hmb : (m - 1) * nb + nb = m * nb := by
    conv_rhs => rw [show m = (m - 1) + 1 from (Nat.sub_add_cancel hm1).symm]
    rw [Nat.add_mul, one_mul]
  have key : na + m * nb = m * (Q.roots.count (-x)) + nb := by
    rw [← hmb, ← add_assoc, hcount]
  have hmod : na % m = nb % m := by
    have hA2 : (m * nb + na) % m = na % m := Nat.ModEq.modulus_mul_add
    have hB2 : (m * (Q.roots.count (-x)) + nb) % m = nb % m := Nat.ModEq.modulus_mul_add
    have e : m * nb + na = m * (Q.roots.count (-x)) + nb := by
      rw [add_comm (m * nb) na]; exact key
    rw [← hA2, e, hB2]
  exact hmod

end Commons.Algebra.Polynomial