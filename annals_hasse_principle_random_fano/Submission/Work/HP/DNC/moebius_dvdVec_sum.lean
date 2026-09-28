import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP.DNC

/-- The gcd of a finite set of integers (with `0` as the gcd of the empty set) is nonnegative. -/
private lemma finset_gcd_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ) :
    0 ≤ s.gcd f := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.gcd_insert]
      exact Int.gcd_nonneg _ _

/-- `∑_{d ∣ m} μ(d) = [m = 1]` in `ℤ`, obtained from Möbius inversion `μ * ζ = 1`. -/
private lemma moebius_sum_divisors_int (m : ℕ) :
    ∑ d ∈ m.divisors, ArithmeticFunction.moebius d = if m = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply (R := ℤ) (f := ArithmeticFunction.moebius) (x := m),
    ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- The Möbius sum over the `k ∈ [1, N]` that divide every coordinate of the non-zero integer
vector `a` evaluates to the indicator of `gcd a = 1`, as soon as `N` dominates `|gcd a|`.
Equivalently: `∑_{k = 1}^{N} [k | a i ∀ i] μ(k) = [gcd a = 1]`. -/
theorem moebius_dvdVec_sum {ι : Type*} [Fintype ι] (a : ι → ℤ) (ha : a ≠ 0) (N : ℕ)
    (hN : (Finset.univ.gcd a).natAbs ≤ N) :
    (∑ k ∈ Finset.Icc 1 N,
      (if (∀ i, (k : ℤ) ∣ a i) then ArithmeticFunction.moebius k else 0))
      = if Finset.univ.gcd a = 1 then 1 else 0 := by
  classical
  set g : ℤ := Finset.univ.gcd a with hgdef
  have hg0 : g ≠ 0 := by
    rw [hgdef]
    intro h
    exact ha (funext (fun i => (Finset.gcd_eq_zero_iff.mp h) i (Finset.mem_univ i)))
  have hgnn : 0 ≤ g := by
    rw [hgdef]
    exact finset_gcd_nonneg _ _
  -- Dividing every coordinate of `a` is the same as dividing the gcd.
  have key : ∀ k : ℕ, (∀ i, (k : ℤ) ∣ a i) ↔ (k : ℤ) ∣ g := by
    intro k
    rw [hgdef, Finset.dvd_gcd_iff]
    simp
  -- The `k ∈ [1, N]` dividing the gcd are exactly the divisors of `g.natAbs`.
  have hfilterg : (Finset.Icc 1 N).filter (fun k : ℕ => (k : ℤ) ∣ g) = g.natAbs.divisors := by
    apply Finset.ext
    intro k
    rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨?_, Int.natAbs_ne_zero.mpr hg0⟩
      have : (k : ℤ).natAbs ∣ g.natAbs := Int.natAbs_dvd_natAbs.mpr h3
      simpa using this
    · rintro ⟨h1, h2⟩
      have hk0 : k ≠ 0 := by rintro rfl; exact h2 (by simpa using h1)
      have hle : k ≤ N := le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1) hN
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr hk0, hle⟩, ?_⟩
      exact Int.natAbs_dvd_natAbs.mp (by simpa using h1)
  have hfilter : (Finset.Icc 1 N).filter (fun k : ℕ => ∀ i, (k : ℤ) ∣ a i)
      = (Finset.Icc 1 N).filter (fun k : ℕ => (k : ℤ) ∣ g) :=
    Finset.filter_congr (fun k _ => key k)
  rw [← Finset.sum_filter, hfilter, hfilterg, moebius_sum_divisors_int]
  have hge1 : g.natAbs = 1 ↔ g = 1 := by
    constructor
    · intro hc
      rcases Int.natAbs_eq_iff.mp hc with h1 | h1
      · exact h1
      · exfalso; omega
    · intro h1; rw [h1]; norm_num
  simp only [hge1]

end Work.HP.DNC
