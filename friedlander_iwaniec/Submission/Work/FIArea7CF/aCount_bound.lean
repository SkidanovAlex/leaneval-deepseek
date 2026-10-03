/-
# `Submission.Work.FIArea7CF.aCount_bound` — clash-free copy of `Submission.Work.FIArea7.aCount_bound`

Imports redirected to the `FIArea7CF` copies; renamed: gnorm_mk_eq→cfx_gnorm_mk_eq, mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7.oddPartKernelDefs
import Submission.Work.FIArea7.R2_bound
import Submission.Work.FIArea7.Kern_of_mem_gBox
import Submission.Work.FIArea7.ACDefs
import Submission.Work.FIArea7CF.r2count_upper
import Submission.Work.FIArea7CF.r2count_sq_lower
import Submission.Work.FIArea7.Kern_decomp
import Submission.Work.FIArea7.r2_bound_arith_gen
import Submission.Work.FIArea7CF.Gwt_sum_le

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Elementary helpers -/

/-- The box `gBox R` is empty for `R < 0`. -/
lemma gBox_eq_empty_of_neg' {R : ℤ} (hR : R < 0) : Work.FIPlan.gBox R = ∅ := by
  have hI : Finset.Icc (-R) R = (∅ : Finset ℤ) := by
    rw [Finset.Icc_eq_empty_iff]; omega
  rw [Work.FIPlan.gBox, hI]; simp

/-- For `R < 0` the a-count vanishes. -/
lemma aCount_eq_zero_of_neg {R : ℤ} (hR : R < 0) (d : ℕ) : aCount R d = 0 := by
  unfold aCount
  rw [gBox_eq_empty_of_neg' hR]; simp

/-- `Gwt` is nonnegative. -/
lemma Gwt_nonneg (s : ℕ) : 0 ≤ Gwt s := by
  unfold Gwt
  exact Finset.prod_nonneg (fun p _ => by positivity)

/-- If `gnorm w = n` with `n > 0` then `w` lies in the box `gBox n`. -/
lemma mem_gBox_of_gnorm_eq_of_pos {w : GaussianInt} {n : ℕ} (h : Work.FIPlan.gnorm w = n) (hn : 0 < n) :
    w ∈ Work.FIPlan.gBox (n : ℤ) := by
  have hsum : w.re.natAbs ^ 2 + w.im.natAbs ^ 2 = n :=
    (gnorm_eq_natAbs_sq_add w).symm.trans h
  have h1 : w.re.natAbs ^ 2 ≤ n := by omega
  have h2 : w.im.natAbs ^ 2 ≤ n := by omega
  have hle : ∀ a : ℕ, a ^ 2 ≤ n → a ≤ n := by
    intro a ha
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · omega
    · calc a ≤ a ^ 2 := by nlinarith
        _ ≤ n := ha
  have hmem : ((w.re, w.im) : ℤ × ℤ) ∈
      (Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (-(n : ℤ)) (n : ℤ)) := by
    rw [Finset.mem_product]
    refine ⟨?_, ?_⟩
    · have hre : |w.re| ≤ (n : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hle _ h1
      rw [Finset.mem_Icc]
      exact abs_le.mp hre
    · have him : |w.im| ≤ (n : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hle _ h2
      rw [Finset.mem_Icc]
      exact abs_le.mp him
  exact Finset.mem_image.mpr ⟨(w.re, w.im), hmem, Zsqrtd.ext rfl rfl⟩

/-- Members of `gBox R` whose norm is `n` are counted by `r2count n`. -/
lemma fib_subset_r2count (R : ℤ) (n : ℕ) (hn : 0 < n) :
    ((Work.FIPlan.gBox R).filter (fun w => Work.FIPlan.gnorm w = n)) ⊆
      ((Work.FIPlan.gBox (n : ℤ)).filter (fun w => Work.FIPlan.gnorm w = n)) := by
  intro w hw
  rw [Finset.mem_filter] at hw ⊢
  exact ⟨mem_gBox_of_gnorm_eq_of_pos hw.2 hn, hw.2⟩

/-- `sqrt (2^j) = sqrt 2 ^ j`. -/
lemma sqrt_two_pow (j : ℕ) : Real.sqrt ((2 : ℝ) ^ j) = Real.sqrt 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- `sqrt 2` is not below `4/3`. -/
lemma four_thirds_le_sqrt_two : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
  have h : ((4 : ℝ) / 3) ^ 2 ≤ 2 := by norm_num
  calc (4 : ℝ) / 3 = Real.sqrt (((4 : ℝ) / 3) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h

/-- A geometric bound: `Σ_{j ∈ s} (1/√2)^j ≤ 4` for any finite `s`. -/
lemma geom_range_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (M : ℕ) :
    ∑ j ∈ Finset.range M, x ^ j ≤ 1 / (1 - x) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · rw [Finset.sum_range_zero]
    exact div_nonneg zero_le_one (by linarith)
  · rw [geom_sum_eq (by linarith : x ≠ 1)]
    have h : (x ^ M - 1) / (x - 1) = (1 - x ^ M) / (1 - x) := by
      rw [show x ^ M - 1 = -(1 - x ^ M) by ring, show x - 1 = -(1 - x) by ring, neg_div_neg_eq]
    rw [h, div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < 1 - x)]
    have : 0 ≤ x ^ M := by positivity
    linarith

lemma one_div_sqrt_two_le_three_quarters : 1 / Real.sqrt 2 ≤ (3 : ℝ) / 4 := by
  have hpos : (0 : ℝ) < 4 / 3 := by norm_num
  have h43 : (4 : ℝ) / 3 ≤ Real.sqrt 2 := four_thirds_le_sqrt_two
  have h := one_div_le_one_div_of_le hpos h43
  have h43' : (1 : ℝ) / (4 / 3) = 3 / 4 := by norm_num
  linarith [h, h43'.ge, h43'.le]

lemma geom_sqrt_two_inv_le (s : Finset ℕ) :
    ∑ j ∈ s, (1 / Real.sqrt 2) ^ j ≤ 4 := by
  have hx0 : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
  have hx1 : (1 : ℝ) / Real.sqrt 2 < 1 := by
    have h2 : (1 : ℝ) < Real.sqrt 2 := by
      have := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    exact (div_lt_one (Real.sqrt_pos.mpr (by norm_num))).mpr (by linarith)
  have hsub : s ⊆ Finset.range (s.sup id + 1) := by
    intro j hj
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun x : ℕ => x) hj)
  have hx34 : (1 : ℝ) / Real.sqrt 2 ≤ 3 / 4 := one_div_sqrt_two_le_three_quarters
  calc ∑ j ∈ s, (1 / Real.sqrt 2) ^ j
      ≤ ∑ j ∈ Finset.range (s.sup id + 1), (1 / Real.sqrt 2) ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    _ ≤ 1 / (1 - 1 / Real.sqrt 2) := geom_range_le hx0 hx1 _
    _ ≤ 4 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - 1 / Real.sqrt 2)]
        linarith

/-- `1 ≤ 1 + log (2 + n)`. -/
lemma one_le_log_two_add (n : ℕ) : (1 : ℝ) ≤ 1 + Real.log (2 + (n : ℝ)) := by
  have h : 0 ≤ Real.log (2 + (n : ℝ)) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
  linarith

/-! ### The index set and the fibres of the map `w ↦ |w|²` -/

/-- The set of pairs `(s,j)` that can occur as `(|w|² = d s² 2^j)` for a `w` with `|w|² ≤ N²`. -/
def aIdx (d N : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.Icc 1 N) ×ˢ (Finset.range (N ^ 2 + 1))).filter
    (fun p : ℕ × ℕ => d * p.1 ^ 2 * 2 ^ p.2 ≤ N ^ 2))

/-- The fibre of `w ↦ |w|²` above `d s² 2^j`, inside the box `gBox R`. -/
def aFib (R : ℤ) (d : ℕ) (p : ℕ × ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox R).filter (fun w => Work.FIPlan.gnorm w = d * p.1 ^ 2 * 2 ^ p.2)

lemma mem_aIdx {d N s j : ℕ} :
    (s, j) ∈ aIdx d N ↔ (1 ≤ s ∧ s ≤ N) ∧ j ≤ N ^ 2 ∧ d * s ^ 2 * 2 ^ j ≤ N ^ 2 := by
  simp only [aIdx, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
  omega

lemma mem_aFib {R : ℤ} {d : ℕ} {p : ℕ × ℕ} {w : GaussianInt} :
    w ∈ aFib R d p ↔ w ∈ Work.FIPlan.gBox R ∧
      Work.FIPlan.gnorm w = d * p.1 ^ 2 * 2 ^ p.2 := by
  simp only [aFib, Finset.mem_filter]

/-- Every counted element is covered by the fibre above its own `(s,j)`. -/
lemma aCount_le_sum_fib (R : ℤ) (d N : ℕ) (hd : 0 < d) (hN : (N : ℤ) = 2 * R + 1) :
    (aCount R d : ℝ) ≤ ∑ p ∈ aIdx d N, ((aFib R d p).card : ℝ) := by
  have hN' : (2 * R + 1).toNat = N := by
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg (by omega)]
    exact hN.symm
  have hcover : ((Work.FIPlan.gBox R).filter (fun w => Kern (Work.FIPlan.gnorm w) = d)) ⊆
      (aIdx d N).biUnion (aFib R d) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hwbox, hkw⟩ := hw
    have hnpos : 0 < Work.FIPlan.gnorm w := by
      rcases eq_or_ne (Work.FIPlan.gnorm w) 0 with h0 | h0
      · rw [h0, Kern_zero] at hkw
        omega
      · exact Nat.pos_of_ne_zero h0
    obtain ⟨s, j, hsodd, hseq⟩ := Kern_decomp (Work.FIPlan.gnorm w) d hnpos hd hkw
    have hleN : Work.FIPlan.gnorm w ≤ N ^ 2 := by
      have := gnorm_le_of_mem_gBox hwbox
      rw [hN'] at this
      exact this
    refine Finset.mem_biUnion.mpr ⟨(s, j), ?_, ?_⟩
    · rw [mem_aIdx]
      have hs1 : 1 ≤ s := by
        obtain ⟨k, hk⟩ := hsodd; omega
      have hs2 : s ^ 2 ≤ N ^ 2 := by
        have hds : s ^ 2 ≤ d * s ^ 2 * 2 ^ j := by
          have h1 : s ^ 2 ≤ d * s ^ 2 := Nat.le_mul_of_pos_left _ hd
          have h2 : d * s ^ 2 ≤ d * s ^ 2 * 2 ^ j :=
            Nat.le_mul_of_pos_right _ (Nat.one_le_two_pow)
          exact le_trans h1 h2
        rw [hseq] at hds
        exact le_trans hds hleN
      have hsN : s ≤ N := by
        have h := Nat.mul_self_le_mul_self_iff.mp (by simpa [pow_two] using hs2)
        simpa using h
      have hj2 : 2 ^ j ≤ N ^ 2 := by
        have h2 : 2 ^ j ≤ d * s ^ 2 * 2 ^ j := by
          have hd1 : 0 < d * s ^ 2 := Nat.mul_pos hd (pow_pos (by omega : 0 < s) 2)
          exact Nat.le_mul_of_pos_left (2 ^ j) hd1
        rw [hseq] at h2
        exact le_trans h2 hleN
      have hjN : j ≤ N ^ 2 := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · omega
        · have := Nat.lt_two_pow_self (n := j)
          omega
      exact ⟨⟨hs1, hsN⟩, hjN, by rw [hseq]; exact hleN⟩
    · rw [mem_aFib]
      exact ⟨hwbox, hseq.symm⟩
  have h1 : (((Work.FIPlan.gBox R).filter (fun w => Kern (Work.FIPlan.gnorm w) = d)).card
      ≤ ∑ p ∈ aIdx d N, (aFib R d p).card) :=
    le_trans (Finset.card_le_card hcover) (Finset.card_biUnion_le)
  calc (aCount R d : ℝ)
      = (((Work.FIPlan.gBox R).filter (fun w => Kern (Work.FIPlan.gnorm w) = d)).card : ℝ) := rfl
    _ ≤ ((∑ p ∈ aIdx d N, (aFib R d p).card : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ∑ p ∈ aIdx d N, ((aFib R d p).card : ℝ) := by push_cast; rfl

/-- The fibre above `(s,j)` has at most `4 · 2 ^ Ω(d) · Gwt s` elements. -/
lemma card_fib_le (R : ℤ) (d N : ℕ) (hd : 0 < d) (hN : (N : ℤ) = 2 * R + 1) (p : ℕ × ℕ)
    (hp : p ∈ aIdx d N) :
    ((aFib R d p).card : ℝ) ≤ 4 * (2 : ℝ) ^ (ArithmeticFunction.cardFactors d) * Gwt p.1 := by
  obtain ⟨⟨hs1, hsN⟩, hjN, hsz⟩ := mem_aIdx.mp hp
  have hnpos : 0 < d * p.1 ^ 2 * 2 ^ p.2 := by
    have h1 : 0 < p.1 ^ 2 := pow_pos (by omega : 0 < p.1) 2
    have h2 : 0 < 2 ^ p.2 := pow_pos (by norm_num) _
    positivity
  have h1 : (aFib R d p).card ≤ r2count (d * p.1 ^ 2 * 2 ^ p.2) :=
    Finset.card_le_card (fib_subset_r2count R _ hnpos)
  have h2 : (r2count (d * p.1 ^ 2 * 2 ^ p.2) : ℝ) ≤
      4 * (∏ q ∈ (d * p.1 ^ 2 * 2 ^ p.2).primeFactors.filter (fun q => q % 4 = 1),
        ((d * p.1 ^ 2 * 2 ^ p.2).factorization q + 1) : ℝ) := by
    have := r2count_upper (d * p.1 ^ 2 * 2 ^ p.2) hnpos
    exact_mod_cast this
  have h3 := r2_bound_arith_gen d p.1 p.2 hd (by omega : 0 < p.1)
  calc ((aFib R d p).card : ℝ) ≤ (r2count (d * p.1 ^ 2 * 2 ^ p.2) : ℝ) := by
        exact_mod_cast h1
    _ ≤ 4 * (∏ q ∈ (d * p.1 ^ 2 * 2 ^ p.2).primeFactors.filter (fun q => q % 4 = 1),
        ((d * p.1 ^ 2 * 2 ^ p.2).factorization q + 1) : ℝ) := h2
    _ ≤ 4 * (2 : ℝ) ^ (ArithmeticFunction.cardFactors d) * Gwt p.1 := h3

/-- The weighted sum over the index set. -/
lemma sum_Gwt_le (d N : ℕ) (hd : 0 < d) (hN1 : 1 ≤ N) (Cg : ℝ) (hCgnn : 0 ≤ Cg)
    (hCg : ∀ Y : ℕ, ∑ s ∈ Finset.range (Y + 1), Gwt s
      ≤ Cg * ((Y : ℝ) + 1) * (1 + Real.log (2 + (Y : ℝ)))) :
    ∑ p ∈ aIdx d N, Gwt p.1
      ≤ 8 * Cg * (N : ℝ) / Real.sqrt (d : ℝ) * (1 + Real.log (2 + (N : ℝ))) := by
  let S : ℕ → ℕ := fun j => Nat.floor ((N : ℝ) / Real.sqrt ((d : ℝ) * 2 ^ j))
  let J : Finset ℕ := (Finset.range (N ^ 2 + 1)).filter (fun j => d * 2 ^ j ≤ N ^ 2)
  have hsqrtd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hSle : ∀ j, S j ≤ N := by
    intro j
    have hden : (1 : ℝ) ≤ Real.sqrt ((d : ℝ) * 2 ^ j) := by
      have h1 : (1 : ℕ) ≤ d * 2 ^ j := by
        have h2 : 1 ≤ d := by omega
        have h3 := Nat.mul_le_mul h2 (Nat.one_le_two_pow (n := j))
        simpa using h3
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt ((d : ℝ) * 2 ^ j) := Real.sqrt_le_sqrt (by exact_mod_cast h1)
    have h : (S j : ℝ) ≤ (N : ℝ) := by
      calc (S j : ℝ) ≤ (N : ℝ) / Real.sqrt ((d : ℝ) * 2 ^ j) :=
            Nat.floor_le (by positivity)
        _ ≤ (N : ℝ) := div_le_self (by positivity) hden
    exact_mod_cast h
  have hfloor : ∀ j, (S j : ℝ) ≤ (N : ℝ) / Real.sqrt ((d : ℝ) * 2 ^ j) :=
    fun j => Nat.floor_le (by positivity)
  have hden1 : ∀ j ∈ J, (1 : ℝ) ≤ (N : ℝ) / Real.sqrt ((d : ℝ) * 2 ^ j) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨_, hdj⟩ := hj
    have hdjR : ((d : ℝ) * 2 ^ j) ≤ (N : ℝ) ^ 2 := by
      have h : ((d * 2 ^ j : ℕ) : ℝ) ≤ ((N ^ 2 : ℕ) : ℝ) := by exact_mod_cast hdj
      push_cast at h ⊢
      linarith
    have hroot : Real.sqrt ((d : ℝ) * 2 ^ j) ≤ (N : ℝ) := by
      calc Real.sqrt ((d : ℝ) * 2 ^ j) ≤ Real.sqrt ((N : ℝ) ^ 2) := Real.sqrt_le_sqrt hdjR
        _ = (N : ℝ) := Real.sqrt_sq (by positivity)
    have hpos : 0 < Real.sqrt ((d : ℝ) * 2 ^ j) := by
      apply Real.sqrt_pos.mpr
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      positivity
    rw [le_div_iff₀ hpos]
    linarith
  have hS1 : ∀ j ∈ J, (S j : ℝ) + 1 ≤ 2 * (N : ℝ) / Real.sqrt (d : ℝ) * ((1 / Real.sqrt 2) ^ j) := by
    intro j hj
    have h1 := hfloor j
    have h2 := hden1 j hj
    have hsplit : Real.sqrt ((d : ℝ) * 2 ^ j) = Real.sqrt (d : ℝ) * (Real.sqrt 2) ^ j := by
      rw [Real.sqrt_mul (by positivity), sqrt_two_pow]
    have hpow : (1 / Real.sqrt 2) ^ j = 1 / (Real.sqrt 2) ^ j := one_div_pow _ _
    have hne : (Real.sqrt (d : ℝ) * (Real.sqrt 2) ^ j) ≠ 0 := by
      apply mul_ne_zero (ne_of_gt hsqrtd)
      positivity
    calc (S j : ℝ) + 1 ≤ (N : ℝ) / Real.sqrt ((d : ℝ) * 2 ^ j)
                          + (N : ℝ) / Real.sqrt ((d : ℝ) * 2 ^ j) := by linarith
      _ = 2 * (N : ℝ) / (Real.sqrt (d : ℝ) * (Real.sqrt 2) ^ j) := by
            rw [hsplit]; ring
      _ = 2 * (N : ℝ) / Real.sqrt (d : ℝ) * (1 / (Real.sqrt 2) ^ j) := by
            rw [div_mul_eq_div_mul_one_div]
      _ = 2 * (N : ℝ) / Real.sqrt (d : ℝ) * ((1 / Real.sqrt 2) ^ j) := by rw [hpow]
  have hcover : aIdx d N ⊆ J.biUnion (fun j => (Finset.range (S j + 1)).image (fun s => (s, j))) := by
    intro p hp
    obtain ⟨⟨hs1, hsN⟩, hjN, hsz⟩ := mem_aIdx.mp hp
    have hjmem : p.2 ∈ J := by
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      calc d * 2 ^ p.2 ≤ d * p.1 ^ 2 * 2 ^ p.2 := by
            have h1 : d ≤ d * p.1 ^ 2 :=
              Nat.le_mul_of_pos_right d (pow_pos (by omega : 0 < p.1) 2)
            exact Nat.mul_le_mul_right _ h1
        _ ≤ N ^ 2 := hsz
    refine Finset.mem_biUnion.mpr ⟨p.2, hjmem, ?_⟩
    refine Finset.mem_image.mpr ⟨p.1, ?_, rfl⟩
    rw [Finset.mem_range]
    have hle : (p.1 : ℝ) ≤ (N : ℝ) / Real.sqrt ((d : ℝ) * 2 ^ p.2) := by
      rw [le_div_iff₀ (by positivity : 0 < Real.sqrt ((d : ℝ) * 2 ^ p.2))]
      have hsq : ((p.1 : ℝ)) ^ 2 * ((d : ℝ) * 2 ^ p.2) ≤ (N : ℝ) ^ 2 := by
        have h : ((d * p.1 ^ 2 * 2 ^ p.2 : ℕ) : ℝ) ≤ ((N ^ 2 : ℕ) : ℝ) := by exact_mod_cast hsz
        push_cast at h
        nlinarith [h]
      have hx2 : (Real.sqrt ((d : ℝ) * 2 ^ p.2)) ^ 2 = (d : ℝ) * 2 ^ p.2 :=
        Real.sq_sqrt (by positivity)
      have hx0 : 0 ≤ Real.sqrt ((d : ℝ) * 2 ^ p.2) := Real.sqrt_nonneg _
      have hp1nn : (0 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast Nat.zero_le p.1
      have hNnn : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
      nlinarith [hsq, hx2, hx0, hp1nn, hNnn]
    exact Nat.lt_succ_of_le (Nat.le_floor hle)
  have hdisj : (↑J : Set ℕ).PairwiseDisjoint
      (fun j => (Finset.range (S j + 1)).image (fun s => (s, j))) := by
    intro j hj j' hj' hne
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    simp only [Finset.mem_image, Finset.mem_range] at hx hx'
    obtain ⟨s, _, hsj⟩ := hx
    obtain ⟨s', _, hs'j⟩ := hx'
    refine hne ?_
    have e1 : j = x.2 := congrArg Prod.snd hsj
    have e2 : j' = x.2 := congrArg Prod.snd hs'j
    rw [e1, e2]
  calc ∑ p ∈ aIdx d N, Gwt p.1
      ≤ ∑ p ∈ J.biUnion (fun j => (Finset.range (S j + 1)).image (fun s => (s, j))), Gwt p.1 :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun i _ _ => Gwt_nonneg i.1)
    _ = ∑ j ∈ J, ∑ s ∈ Finset.range (S j + 1), Gwt s := by
        rw [Finset.sum_biUnion hdisj]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_image]
        intro a _ b _ hab
        simpa using hab
    _ ≤ ∑ j ∈ J, Cg * ((S j : ℝ) + 1) * (1 + Real.log (2 + (S j : ℝ))) :=
        Finset.sum_le_sum (fun j hj => hCg (S j))
    _ ≤ ∑ j ∈ J, Cg * (2 * (N : ℝ) / Real.sqrt (d : ℝ) * ((1 / Real.sqrt 2) ^ j))
            * (1 + Real.log (2 + (N : ℝ))) := by
        apply Finset.sum_le_sum
        intro j hj
        have hA := hS1 j hj
        have hlog : 1 + Real.log (2 + (S j : ℝ)) ≤ 1 + Real.log (2 + (N : ℝ)) := by
          have hle : (2 + (S j : ℝ)) ≤ (2 + (N : ℝ)) := by
            have : (S j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hSle j
            linarith
          have := Real.log_le_log (by positivity) hle
          linarith
        have hnn1 : (0 : ℝ) ≤ 1 + Real.log (2 + (S j : ℝ)) := by
          have h2 : 1 ≤ 2 + (S j : ℝ) := by
            have : (0 : ℝ) ≤ (S j : ℝ) := by positivity
            linarith
          have : 0 ≤ Real.log (2 + (S j : ℝ)) := Real.log_nonneg h2
          linarith
        have hnn2 : (0 : ℝ) ≤ Cg * (2 * (N : ℝ) / Real.sqrt (d : ℝ) * ((1 / Real.sqrt 2) ^ j)) := by
          have : 0 ≤ 2 * (N : ℝ) / Real.sqrt (d : ℝ) := by positivity
          have : 0 ≤ (1 / Real.sqrt 2) ^ j := by positivity
          positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hA hCgnn) hlog hnn1 hnn2
    _ = Cg * (2 * (N : ℝ) / Real.sqrt (d : ℝ)) * (1 + Real.log (2 + (N : ℝ)))
            * ∑ j ∈ J, (1 / Real.sqrt 2) ^ j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ ≤ Cg * (2 * (N : ℝ) / Real.sqrt (d : ℝ)) * (1 + Real.log (2 + (N : ℝ))) * 4 := by
        have hsum := geom_sqrt_two_inv_le J
        have : (0 : ℝ) ≤ Cg * (2 * (N : ℝ) / Real.sqrt (d : ℝ)) * (1 + Real.log (2 + (N : ℝ))) := by
          have : 0 ≤ 2 * (N : ℝ) / Real.sqrt (d : ℝ) := by positivity
          have : 0 ≤ 1 + Real.log (2 + (N : ℝ)) := le_trans zero_le_one (one_le_log_two_add N)
          positivity
        exact mul_le_mul_of_nonneg_left hsum this
    _ = 8 * Cg * (N : ℝ) / Real.sqrt (d : ℝ) * (1 + Real.log (2 + (N : ℝ))) := by ring

/-! ### The main bound -/

theorem aCount_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℤ) (d : ℕ), d ≠ 0 →
      (aCount R d : ℝ) ≤ C * (2 : ℝ) ^ (ArithmeticFunction.cardFactors d) / Real.sqrt d
        * (((2 * R + 1).toNat : ℝ)) * (1 + Real.log (2 + (((2 * R + 1).toNat : ℝ)))) := by
  obtain ⟨Cg, hCgpos, hCgB⟩ := Gwt_sum_le
  refine ⟨32 * Cg, by positivity, ?_⟩
  intro R d hd
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  rcases lt_or_ge R 0 with hR | hR
  · have hN0 : (2 * R + 1).toNat = 0 := by
      apply Int.toNat_of_nonpos; omega
    rw [aCount_eq_zero_of_neg hR d, hN0]
    simp
  ·
    obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = (2 * R + 1).toNat := ⟨_, rfl⟩
    have hNcast : (N : ℤ) = 2 * R + 1 := by rw [hNdef]; exact Int.toNat_of_nonneg (by omega)
    have hN1 : 1 ≤ N := by omega
    calc (aCount R d : ℝ)
        ≤ ∑ p ∈ aIdx d N, ((aFib R d p).card : ℝ) := aCount_le_sum_fib R d N hdpos hNcast
      _ ≤ ∑ p ∈ aIdx d N, 4 * (2 : ℝ) ^ (ArithmeticFunction.cardFactors d) * Gwt p.1 :=
          Finset.sum_le_sum (fun p hp => card_fib_le R d N hdpos hNcast p hp)
      _ = 4 * (2 : ℝ) ^ (ArithmeticFunction.cardFactors d) * ∑ p ∈ aIdx d N, Gwt p.1 := by
          rw [Finset.mul_sum]
      _ ≤ 4 * (2 : ℝ) ^ (ArithmeticFunction.cardFactors d)
            * (8 * Cg * (N : ℝ) / Real.sqrt (d : ℝ) * (1 + Real.log (2 + (N : ℝ)))) := by
          gcongr
          exact sum_Gwt_le d N hdpos hN1 Cg hCgpos.le hCgB
      _ = 32 * Cg * (2 : ℝ) ^ (ArithmeticFunction.cardFactors d) / Real.sqrt (d : ℝ)
            * (N : ℝ) * (1 + Real.log (2 + (N : ℝ))) := by ring
      _ = 32 * Cg * (2 : ℝ) ^ (ArithmeticFunction.cardFactors d) / Real.sqrt (d : ℝ)
            * (((2 * R + 1).toNat : ℝ)) * (1 + Real.log (2 + (((2 * R + 1).toNat : ℝ)))) := by
          rw [hNdef]

end

end Work.FIArea7
