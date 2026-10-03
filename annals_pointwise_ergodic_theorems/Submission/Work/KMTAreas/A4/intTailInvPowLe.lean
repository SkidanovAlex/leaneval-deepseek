import Mathlib
import Submission.Work.Analysis.InverseTheory.riemann_shift

namespace Work.KMTAreas.A4

open Finset

/-- For an integer `m ≥ 0`, the natural number `m.toNat` cast to `ℝ` is `|m|`. -/
private lemma toNat_cast_eq_abs (m : ℤ) (hm : 0 ≤ m) :
    (((m.toNat : ℕ)) : ℝ) = |((m : ℤ) : ℝ)| := by
  have h1 : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    have := Int.toNat_of_nonneg hm
    exact_mod_cast this
  have h2 : (m : ℝ) = |((m : ℤ) : ℝ)| := by
    rw [abs_of_nonneg (by exact_mod_cast hm)]
  exact h1.trans h2

/-- Numeric core: a finite sum of the `12`-th powers of the reciprocals of naturals all at
least `K ≥ 1` is at most `2 K^{-11}`.

The sum is extended to the full range `Ico K (M+1)`, where `M` is the largest element of `A`;
the telescoping bound `∑_{i<m} (K+i)^{-(n+1)} ≤ 2 K^{-n}` of
`Work.Analysis.InverseTheory.sum_range_inv_pow_le` (at `n = 11`) then applies. -/
private lemma sum_inv_pow_le_nat (A : Finset ℕ) (K : ℕ) (hK : 1 ≤ K)
    (hA : ∀ n ∈ A, K ≤ n) :
    ∑ n ∈ A, (((n : ℝ))⁻¹) ^ 12 ≤ 2 * (((K : ℝ))⁻¹) ^ 11 := by
  let M : ℕ := A.sup id
  have hsub : A ⊆ Finset.Ico K (M + 1) := by
    intro n hn
    have h1 : K ≤ n := hA n hn
    have h2 : n ≤ M := Finset.le_sup (f := id) hn
    simp only [Finset.mem_Ico]
    omega
  calc ∑ n ∈ A, (((n : ℝ))⁻¹) ^ 12
      ≤ ∑ n ∈ Finset.Ico K (M + 1), (((n : ℝ))⁻¹) ^ 12 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    _ = ∑ k ∈ Finset.range ((M + 1) - K), ((((K + k : ℕ) : ℝ))⁻¹) ^ 12 :=
        Finset.sum_Ico_eq_sum_range (fun n : ℕ => (((n : ℝ))⁻¹) ^ 12) K (M + 1)
    _ ≤ 2 * (((K : ℝ))⁻¹) ^ 11 := by
        have h11 : (11 : ℕ) + 1 = 12 := by norm_num
        simpa [h11] using
          (Work.Analysis.InverseTheory.sum_range_inv_pow_le 11 K ((M + 1) - K) hK
            (by norm_num))

/-- The positive half of the integer tail: the `12`-th powers of the reciprocals of the
positive integers of `S` are at most `2 K^{-11}`. -/
private lemma int_tail_pos (S : Finset ℤ) (K : ℕ) (hK : 1 ≤ K)
    (hS : ∀ m ∈ S, (K : ℝ) ≤ |((m : ℤ) : ℝ)|) :
    ∑ m ∈ S.filter (fun m : ℤ => 0 < m), (((|((m : ℤ) : ℝ)|))⁻¹) ^ 12
      ≤ 2 * (((K : ℝ))⁻¹) ^ 11 := by
  let Sp : Finset ℤ := S.filter (fun m : ℤ => 0 < m)
  show ∑ m ∈ Sp, (((|((m : ℤ) : ℝ)|))⁻¹) ^ 12 ≤ 2 * (((K : ℝ))⁻¹) ^ 11
  have hmem : ∀ m ∈ Sp, 0 < m ∧ m ∈ S := by
    intro m hm
    have hm' : m ∈ S.filter (fun m : ℤ => 0 < m) := hm
    exact ⟨(Finset.mem_filter.mp hm').2, (Finset.mem_filter.mp hm').1⟩
  have hinj : Set.InjOn (fun m : ℤ => m.toNat) (↑Sp : Set ℤ) := by
    intro m1 hm1 m2 hm2 h
    have h' : m1.toNat = m2.toNat := h
    have h1 : 0 ≤ m1 := le_of_lt (hmem m1 hm1).1
    have h2 : 0 ≤ m2 := le_of_lt (hmem m2 hm2).1
    have e1 : ((m1.toNat : ℕ) : ℤ) = m1 := Int.toNat_of_nonneg h1
    have e2 : ((m2.toNat : ℕ) : ℤ) = m2 := Int.toNat_of_nonneg h2
    rw [← e1, ← e2]
    exact_mod_cast h'
  have hterm : ∀ m ∈ Sp,
      ((((m.toNat : ℕ) : ℝ))⁻¹) ^ 12 = (((|((m : ℤ) : ℝ)|))⁻¹) ^ 12 := by
    intro m hm
    rw [toNat_cast_eq_abs m (le_of_lt (hmem m hm).1)]
  have hstep : ∑ m ∈ Sp, (((|((m : ℤ) : ℝ)|))⁻¹) ^ 12
      = ∑ m ∈ Sp, ((((m.toNat : ℕ) : ℝ))⁻¹) ^ 12 :=
    Finset.sum_congr rfl fun m hm => (hterm m hm).symm
  have hA' : ∀ n ∈ Sp.image (fun m : ℤ => m.toNat), K ≤ n := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨m, hm, hm_eq⟩ := hn
    have hmS : m ∈ S := (hmem m hm).2
    have hcast : (((m.toNat : ℕ) : ℝ)) = |((m : ℤ) : ℝ)| :=
      toNat_cast_eq_abs m (le_of_lt (hmem m hm).1)
    rw [← hm_eq]
    have : (K : ℝ) ≤ ((m.toNat : ℕ) : ℝ) := by rw [hcast]; exact hS m hmS
    exact_mod_cast this
  have himage := Finset.sum_image (s := Sp) (g := fun m : ℤ => m.toNat)
    (f := fun n : ℕ => (((n : ℝ))⁻¹) ^ 12) hinj
  calc ∑ m ∈ Sp, (((|((m : ℤ) : ℝ)|))⁻¹) ^ 12
      = ∑ m ∈ Sp, ((((m.toNat : ℕ) : ℝ))⁻¹) ^ 12 := hstep
    _ = ∑ n ∈ Sp.image (fun m : ℤ => m.toNat), (((n : ℝ))⁻¹) ^ 12 := himage.symm
    _ ≤ 2 * (((K : ℝ))⁻¹) ^ 11 := sum_inv_pow_le_nat _ K hK hA'

/-- The negative half of the integer tail. -/
private lemma int_tail_neg (S : Finset ℤ) (K : ℕ) (hK : 1 ≤ K)
    (hS : ∀ m ∈ S, (K : ℝ) ≤ |((m : ℤ) : ℝ)|) :
    ∑ m ∈ S.filter (fun m : ℤ => m < 0), (((|((m : ℤ) : ℝ)|))⁻¹) ^ 12
      ≤ 2 * (((K : ℝ))⁻¹) ^ 11 := by
  let Sn : Finset ℤ := S.filter (fun m : ℤ => m < 0)
  show ∑ m ∈ Sn, (((|((m : ℤ) : ℝ)|))⁻¹) ^ 12 ≤ 2 * (((K : ℝ))⁻¹) ^ 11
  have hmem : ∀ m ∈ Sn, m < 0 ∧ m ∈ S := by
    intro m hm
    have hm' : m ∈ S.filter (fun m : ℤ => m < 0) := hm
    exact ⟨(Finset.mem_filter.mp hm').2, (Finset.mem_filter.mp hm').1⟩
  have hamp : ∀ m ∈ Sn, (((((-m).toNat : ℕ) : ℝ))⁻¹) ^ 12 = (((|((m : ℤ) : ℝ)|))⁻¹) ^ 12 := by
    intro m hm
    have hnm : 0 ≤ -m := by have := (hmem m hm).1; omega
    have hcast : ((((-m).toNat : ℕ) : ℝ)) = |((m : ℤ) : ℝ)| := by
      rw [toNat_cast_eq_abs (-m) hnm]
      simp
    rw [hcast]
  have hinj : Set.InjOn (fun m : ℤ => (-m).toNat) (↑Sn : Set ℤ) := by
    intro m1 hm1 m2 hm2 h
    have h' : (-m1).toNat = (-m2).toNat := h
    have h1 : 0 ≤ -m1 := by have := (hmem m1 hm1).1; omega
    have h2 : 0 ≤ -m2 := by have := (hmem m2 hm2).1; omega
    have e1 : (((-m1).toNat : ℕ) : ℤ) = -m1 := Int.toNat_of_nonneg h1
    have e2 : (((-m2).toNat : ℕ) : ℤ) = -m2 := Int.toNat_of_nonneg h2
    have hneg : -m1 = -m2 := by rw [← e1, ← e2]; exact_mod_cast h'
    linarith
  have hstep : ∑ m ∈ Sn, (((|((m : ℤ) : ℝ)|))⁻¹) ^ 12
      = ∑ m ∈ Sn, (((((-m).toNat : ℕ) : ℝ))⁻¹) ^ 12 :=
    Finset.sum_congr rfl fun m hm => (hamp m hm).symm
  have hA' : ∀ n ∈ Sn.image (fun m : ℤ => (-m).toNat), K ≤ n := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨m, hm, hm_eq⟩ := hn
    have hmS : m ∈ S := (hmem m hm).2
    have hnm : 0 ≤ -m := by have := (hmem m hm).1; omega
    have hcast : ((((-m).toNat : ℕ) : ℝ)) = |((m : ℤ) : ℝ)| := by
      rw [toNat_cast_eq_abs (-m) hnm]
      simp
    rw [← hm_eq]
    have : (K : ℝ) ≤ (((-m).toNat : ℕ) : ℝ) := by rw [hcast]; exact hS m hmS
    exact_mod_cast this
  have himage := Finset.sum_image (s := Sn) (g := fun m : ℤ => (-m).toNat)
    (f := fun n : ℕ => (((n : ℝ))⁻¹) ^ 12) hinj
  calc ∑ m ∈ Sn, (((|((m : ℤ) : ℝ)|))⁻¹) ^ 12
      = ∑ m ∈ Sn, (((((-m).toNat : ℕ) : ℝ))⁻¹) ^ 12 := hstep
    _ = ∑ n ∈ Sn.image (fun m : ℤ => (-m).toNat), (((n : ℝ))⁻¹) ^ 12 := himage.symm
    _ ≤ 2 * (((K : ℝ))⁻¹) ^ 11 := sum_inv_pow_le_nat _ K hK hA'

/-- The `12`-th powers of the reciprocals of the absolute values of the elements of a finite set
of integers of modulus at least `K ≥ 1` sum to at most `4 K^{-11}`. -/
private lemma int_tail_le (S : Finset ℤ) (K : ℕ) (hK : 1 ≤ K)
    (hS : ∀ m ∈ S, (K : ℝ) ≤ |((m : ℤ) : ℝ)|) :
    ∑ m ∈ S, (((|((m : ℤ) : ℝ)|))⁻¹) ^ 12 ≤ 4 * (((K : ℝ))⁻¹) ^ 11 := by
  have hne : ∀ m ∈ S, m ≠ 0 := by
    intro m hm hzero
    have h1 : (K : ℝ) ≤ |((m : ℤ) : ℝ)| := hS m hm
    rw [hzero] at h1
    simp at h1
    have h2 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hfil : S.filter (fun m : ℤ => ¬ 0 < m) = S.filter (fun m : ℤ => m < 0) := by
    ext m
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hm, hm'⟩
      exact ⟨hm, by have := hne m hm; omega⟩
    · rintro ⟨hm, hm'⟩
      exact ⟨hm, by omega⟩
  have hsplit : ∑ m ∈ S, (((|((m : ℤ) : ℝ)|))⁻¹) ^ 12
      = ∑ m ∈ S.filter (fun m : ℤ => 0 < m), (((|((m : ℤ) : ℝ)|))⁻¹) ^ 12
        + ∑ m ∈ S.filter (fun m : ℤ => m < 0), (((|((m : ℤ) : ℝ)|))⁻¹) ^ 12 := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun m : ℤ => 0 < m)
      (fun m => (((|((m : ℤ) : ℝ)|))⁻¹) ^ 12), hfil]
  have h1 := int_tail_pos S K hK hS
  have h2 := int_tail_neg S K hK hS
  linarith [hsplit, h1, h2]

theorem intTailInvPowLe (K : ℕ) (hK : 1 ≤ K) (v : Finset ℤ) : (∑ m ∈ v.filter (fun m : ℤ => (K : ℝ) ≤ |(m : ℝ)|), (((|(m : ℝ)|))⁻¹) ^ 12) ≤ 4 * ((K : ℝ)⁻¹) ^ 11 := by
  exact int_tail_le _ K hK (fun m hm => (Finset.mem_filter.mp hm).2)

end Work.KMTAreas.A4
