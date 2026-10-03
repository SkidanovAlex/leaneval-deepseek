import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.P231Defs
import Submission.Work.FIArea7.prop232Defs
import Submission.Work.FIArea7.quadEigen_decomp
import Submission.Work.FIArea7.sum_primarySet_mul
import Submission.Work.FIArea7.grossenChar_mul_primarySet
import Submission.Work.FIArea7.jksym_mul_rule_primary
import Submission.Work.FIArea4.GaussMoebiusCore
import Submission.Work.FIArea7.JKSym_mul_eq_zero

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Coprimality of Gaussian integers from coprimality of their norms -/

/-- If the norms of two Gaussian integers are coprime then the Gaussian integers are coprime:
every common divisor `g` has `gnorm g ∣ gnorm e` and `gnorm g ∣ gnorm w`, hence `gnorm g = 1`,
so `g` is a unit and the Bezout identity for the gcd gives `IsCoprime e w`. -/
lemma isCoprime_of_coprime_gnorm {e w : GaussianInt}
    (h : Nat.Coprime (Work.FIPlan.gnorm e) (Work.FIPlan.gnorm w)) : IsCoprime e w := by
  haveI : DecidableEq GaussianInt := Classical.decEq _
  set g : GaussianInt := EuclideanDomain.gcd e w with hg
  have hge : g ∣ e := EuclideanDomain.gcd_dvd_left e w
  have hgw : g ∣ w := EuclideanDomain.gcd_dvd_right e w
  have h1 : Work.FIPlan.gnorm g ∣ Work.FIPlan.gnorm e := Work.FIArea4.gnorm_dvd hge
  have h2 : Work.FIPlan.gnorm g ∣ Work.FIPlan.gnorm w := Work.FIArea4.gnorm_dvd hgw
  have h3 : Work.FIPlan.gnorm g ∣ 1 := by
    have hdiv : Work.FIPlan.gnorm g ∣ Nat.gcd (Work.FIPlan.gnorm e) (Work.FIPlan.gnorm w) :=
      Nat.dvd_gcd h1 h2
    have hg' : Nat.gcd (Work.FIPlan.gnorm e) (Work.FIPlan.gnorm w) = 1 := h
    rw [hg'] at hdiv
    exact hdiv
  have hunit : IsUnit g := by
    rw [← Zsqrtd.norm_eq_one_iff]
    exact Nat.dvd_one.mp h3
  obtain ⟨v, hv⟩ := hunit
  have hbez := EuclideanDomain.gcd_eq_gcd_ab e w
  rw [← hg] at hbez
  have hvg : (e * EuclideanDomain.gcdA e w + w * EuclideanDomain.gcdB e w)
      * ((v⁻¹ : GaussianIntˣ) : GaussianInt) = 1 := by
    rw [← hbez, ← hv]
    exact Units.mul_inv v
  refine ⟨EuclideanDomain.gcdA e w * ((v⁻¹ : GaussianIntˣ) : GaussianInt),
    EuclideanDomain.gcdB e w * ((v⁻¹ : GaussianIntˣ) : GaussianInt), ?_⟩
  rw [← hvg]; ring

/-! ## 2. The three-factor decomposition of the eigenvalue -/

/-- **(23.1), three factorisation**: if `c, m, n` are pairwise coprime then every primary `E` of norm
`cmn` factors uniquely as `E = e·w·z` with `e, w, z` primary of norms `c, m, n`, and the
Grössencharacter is multiplicative on the (automatically coprime) factors.  Hence

  `λ(cmn) = Σ_{e ∈ S(c)} Σ_{w ∈ S(m)} Σ_{z ∈ S(n)} ψ(e)ψ(w)ψ(z)[ewz]`. -/
theorem quadEigen_triple {c m n : ℕ} (hc : 1 ≤ c) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hcm : Nat.Coprime c m) (hcn : Nat.Coprime c n) (hmn : Nat.Coprime m n)
    (k : ℤ) (χ : GaussianInt → ℂ)
    (hmul : ∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → χ (z1 * z2) = χ z1 * χ z2) :
    quadEigen (grossenChar χ k) (c * m * n)
      = ∑ e ∈ primarySet c, ∑ w ∈ primarySet m, ∑ z ∈ primarySet n,
          grossenChar χ k e * grossenChar χ k w * grossenChar χ k z * JKSym (e * w * z) := by
  have hcmn : Nat.Coprime (c * m) n := hcn.mul_left hmn
  have hcm1 : 1 ≤ c * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h1 := quadEigen_decomp (m := c * m) (n := n) hcm1 hn hcmn k χ hmul
  rw [h1]
  have h2 := sum_primarySet_mul hc hm hcm
    (fun u => grossenChar χ k u * (∑ z ∈ primarySet n, grossenChar χ k z * JKSym (u * z)))
  rw [h2]
  refine Finset.sum_congr rfl (fun e he => ?_)
  refine Finset.sum_congr rfl (fun w hw => ?_)
  have heP : Work.FIPlan.IsPrimary e := isPrimary_of_mem_primarySet he
  have hwP : Work.FIPlan.IsPrimary w := isPrimary_of_mem_primarySet hw
  have hec : Work.FIPlan.gnorm e = c := gnorm_of_mem_primarySet he
  have hwc : Work.FIPlan.gnorm w = m := gnorm_of_mem_primarySet hw
  have hcop : IsCoprime e w := by
    refine isCoprime_of_coprime_gnorm ?_
    rw [hec, hwc]; exact hcm
  have hmulEW : grossenChar χ k (e * w) = grossenChar χ k e * grossenChar χ k w :=
    grossenChar_mul_of_coprime hmul (Work.FIArea4.isPrimary_ne_zero heP)
      (Work.FIArea4.isPrimary_ne_zero hwP) hcop
  rw [hmulEW, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z hz => ?_)
  ring

/-- **Vanishing of the Jacobi–Kubota symbol on Gauss-coprime pairs of non-coprime norm.**  If
primary `w, z` are Gauss-coprime but `gnorm w` and `gnorm z` share a prime, then `[wz] = 0`:
the common prime `q` makes `q ∣ wz` in `ℤ[i]`, so `wz` is not primitive
(`Work.FIArea7.JKSym_mul_eq_zero`). -/
lemma JKSym_mul_eq_zero_of_not_coprime_gnorm {w z : GaussianInt}
    (hw : Work.FIPlan.IsPrimary w) (hz : Work.FIPlan.IsPrimary z)
    (hcop : Work.FIPlan.GaussCoprime w z)
    (hnc : ¬ Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z)) :
    JKSym (w * z) = 0 := by
  have hw0 : Work.FIPlan.gnorm w ≠ 0 :=
    Work.FIArea4.gnorm_ne_zero (Work.FIArea4.isPrimary_ne_zero hw)
  have hz0 : Work.FIPlan.gnorm z ≠ 0 :=
    Work.FIArea4.gnorm_ne_zero (Work.FIArea4.isPrimary_ne_zero hz)
  have hq1 : 1 < Nat.gcd (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z) := by
    have hne : Nat.gcd (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z) ≠ 1 := fun h => hnc h
    have hpos : 0 < Nat.gcd (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z) := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      exact hw0 (Nat.eq_zero_of_gcd_eq_zero_left h0)
    omega
  exact Work.FIArea7.JKSym_mul_eq_zero hq1 hw hz hcop.symm
    (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)

end

end Work.FIArea7
