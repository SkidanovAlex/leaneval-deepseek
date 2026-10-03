import Mathlib
import Submission.Work.FIArea2.R6.BSBoxDefs
import Submission.Work.FIArea2.sum_tau_pow_le

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

/-! ## Elementary membership lemmas for the boxes -/

lemma bpg_mem_Icc_natAbs_iff (R : ℕ) (u : ℤ) :
    u ∈ Finset.Icc (-(R:ℤ)) (R:ℤ) ↔ u.natAbs ≤ R := by
  rw [Finset.mem_Icc, ← abs_le, Int.abs_eq_natAbs]
  exact Int.ofNat_le

lemma bpg_mem_zBox_iff (R : ℕ) (u : ℤ) : u ∈ zBox R ↔ u.natAbs ≤ R := bpg_mem_Icc_natAbs_iff R u

lemma bpg_mem_zPz_iff (N : ℕ) (x : ℤ) : x ∈ zPz N ↔ x ≠ 0 ∧ x.natAbs ≤ N := by
  rw [zPz, Finset.mem_filter, bpg_mem_zBox_iff]; tauto

/-! ## Reindexing a `zBox`-sum along the multiples of `g` -/

lemma bpg_sum_dvd_natAbs_eq (R g : ℕ) (hg : 1 ≤ g) (f : ℤ → ℝ) :
    (∑ u ∈ zBox R, (if g ∣ u.natAbs then f u else 0))
      = ∑ v ∈ zBox (R/g), f ((g:ℤ) * v) := by
  rw [← Finset.sum_filter]
  have hgpos : 0 < g := by omega
  have himg : (zBox R).filter (fun u => g ∣ u.natAbs)
      = (zBox (R/g)).image (fun v : ℤ => (g:ℤ) * v) := by
    ext u
    rw [Finset.mem_filter, Finset.mem_image, bpg_mem_zBox_iff]
    constructor
    · rintro ⟨hau, hdvd⟩
      have hdvdZ : (g:ℤ) ∣ u := (Int.dvd_natAbs).mp (by exact_mod_cast hdvd)
      refine ⟨u/(g:ℤ), ?_, ?_⟩
      · have hu : u.natAbs = (u/(g:ℤ)).natAbs * g := by
          have h := congrArg Int.natAbs (Int.ediv_mul_cancel hdvdZ)
          rw [← h, Int.natAbs_mul, Int.natAbs_natCast]
        rw [bpg_mem_zBox_iff, Nat.le_div_iff_mul_le hgpos, ← hu]
        exact hau
      · rw [mul_comm]; exact Int.ediv_mul_cancel hdvdZ
    · rintro ⟨v, hv, rfl⟩
      rw [bpg_mem_zBox_iff] at hv
      refine ⟨?_, ?_⟩
      · rw [Int.natAbs_mul, Int.natAbs_natCast]
        calc g * v.natAbs ≤ g * (R/g) := Nat.mul_le_mul_left g hv
          _ ≤ R := Nat.mul_div_le R g
      · rw [Int.natAbs_mul, Int.natAbs_natCast]; exact dvd_mul_right g v.natAbs
  rw [himg, Finset.sum_image]
  intro v _ w _ h
  exact mul_left_cancel₀ (by omega : (g:ℤ) ≠ 0) h

/-! ## The gcd-as-totient-sum expansion -/

lemma bpg_gcd_cast_eq_sum_phi (R a b : ℕ) (ha : 1 ≤ a) (_hb : 1 ≤ b) (haR : a ≤ R) (_hbR : b ≤ R) :
    (Nat.gcd a b : ℝ)
      = ∑ g ∈ Finset.Icc 1 R,
          (Nat.totient g : ℝ) * (if g ∣ a then (1:ℝ) else 0) * (if g ∣ b then (1:ℝ) else 0) := by
  have hgcdpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b (by omega)
  have hgcdR : Nat.gcd a b ≤ R := le_trans (Nat.gcd_le_left b (by omega)) haR
  have hset : (Finset.Icc 1 R).filter (fun g => g ∣ a ∧ g ∣ b) = (Nat.gcd a b).divisors := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1,h2⟩, hda, hdb⟩
      exact ⟨Nat.dvd_gcd hda hdb, by omega⟩
    · rintro ⟨hdg, hgne⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdg hgcdpos, le_trans (Nat.le_of_dvd hgcdpos hdg) hgcdR⟩,
        hdg.trans (Nat.gcd_dvd_left a b), hdg.trans (Nat.gcd_dvd_right a b)⟩
  have h1 : (∑ g ∈ (Nat.gcd a b).divisors, (Nat.totient g : ℝ)) = (Nat.gcd a b : ℝ) := by
    rw [← Nat.cast_sum, Nat.sum_totient]
  rw [← h1, ← hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g hg
  by_cases hda : g ∣ a <;> by_cases hdb : g ∣ b <;> simp [hda, hdb]

/-! ## The inner sum `bpg_Inn` and the expansion coefficient `bpg_Cg` -/

/-- The inner `(h₁,h₂)`-sum of `bulkPart`, with the `h`-variables restricted to the non-zero part. -/
def bpg_Inn (X Y : ℕ) (u1 u2 : ℤ) : ℝ :=
  ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
    (if u1 ≠ 0 ∧ u2 ≠ 0 then T4 u1 u2 h1 h2 else 0)

/-- The `g`-th expansion coefficient of the gcd weight. -/
def bpg_Cg (g : ℕ) (u1 u2 : ℤ) : ℝ :=
  if u1 ≠ 0 ∧ u2 ≠ 0 then
    (if g ∣ u1.natAbs then (1:ℝ) else 0) * (if g ∣ u2.natAbs then (1:ℝ) else 0) else 0

/-! ## Sums over `zPz` versus sums over `zBox` -/

lemma bpg_sum_zPz_eq (X : ℕ) (f : ℤ → ℝ) :
    (∑ x ∈ zPz X, f x) = ∑ x ∈ zBox X, (if x ≠ 0 then f x else 0) := by
  rw [show zPz X = (zBox X).filter (fun x => x ≠ 0) from rfl, Finset.sum_filter]

lemma bpg_sum_zPz_zPz_eq (X Y : ℕ) (f : ℤ → ℤ → ℝ) :
    (∑ x ∈ zPz X, ∑ y ∈ zPz Y, f x y)
      = ∑ x ∈ zBox X, ∑ y ∈ zBox Y, (if x ≠ 0 ∧ y ≠ 0 then f x y else 0) := by
  calc (∑ x ∈ zPz X, ∑ y ∈ zPz Y, f x y)
      = ∑ x ∈ zPz X, ∑ y ∈ zBox Y, (if y ≠ 0 then f x y else 0) := by
        apply Finset.sum_congr rfl; intro x _; exact bpg_sum_zPz_eq Y (f x)
    _ = ∑ x ∈ zBox X,
          (if x ≠ 0 then (∑ y ∈ zBox Y, (if y ≠ 0 then f x y else 0)) else 0) :=
        bpg_sum_zPz_eq X (fun x => ∑ y ∈ zBox Y, (if y ≠ 0 then f x y else 0))
    _ = ∑ x ∈ zBox X, ∑ y ∈ zBox Y, (if x ≠ 0 ∧ y ≠ 0 then f x y else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx0 : x = 0
        · rw [if_neg (by simp [hx0])]
          apply Eq.symm
          apply Finset.sum_eq_zero
          intro y _
          rw [if_neg]; intro hh; exact hh.1 hx0
        · rw [if_pos hx0]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy0 : y = 0
          · rw [if_neg (by simp [hy0]), if_neg]; intro hh; exact hh.2 hy0
          · rw [if_pos hy0, if_pos ⟨hx0, hy0⟩]

/-! ## Basic properties of `bpg_Inn` -/

lemma bpg_bulkPart_eq (R X Y : ℕ) :
    bulkPart R X Y
      = ∑ u1 ∈ zBox R, ∑ u2 ∈ zBox R, (Nat.gcd u1.natAbs u2.natAbs : ℝ) * bpg_Inn X Y u1 u2 := by
  unfold bulkPart bpg_Inn
  apply Finset.sum_congr rfl; intro u1 _
  apply Finset.sum_congr rfl; intro u2 _
  congr 1
  rw [bpg_sum_zPz_zPz_eq X Y (fun h1 h2 => if u1 ≠ 0 ∧ u2 ≠ 0 then T4 u1 u2 h1 h2 else 0)]
  apply Finset.sum_congr rfl; intro h1 _
  apply Finset.sum_congr rfl; intro h2 _
  by_cases hP : u1 ≠ 0 ∧ u2 ≠ 0 <;> by_cases hh1 : h1 = 0 <;> by_cases hh2 : h2 = 0 <;>
    simp [hP, hh1, hh2]

lemma bpg_Inn_eq_zero (X Y : ℕ) (u1 u2 : ℤ) (h : ¬(u1 ≠ 0 ∧ u2 ≠ 0)) : bpg_Inn X Y u1 u2 = 0 := by
  unfold bpg_Inn
  apply Finset.sum_eq_zero; intro h1 _
  apply Finset.sum_eq_zero; intro h2 _
  rw [if_neg h]

lemma bpg_Inn_of_ne_zero (X Y : ℕ) (u1 u2 : ℤ) (h : u1 ≠ 0 ∧ u2 ≠ 0) :
    bpg_Inn X Y u1 u2 = ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, T4 u1 u2 h1 h2 := by
  unfold bpg_Inn
  apply Finset.sum_congr rfl; intro h1 _
  apply Finset.sum_congr rfl; intro h2 _
  rw [if_pos h]

lemma bpg_gcd_mul_Inn (R X Y : ℕ) (u1 u2 : ℤ) (hu1 : u1 ∈ zBox R) (hu2 : u2 ∈ zBox R) :
    (Nat.gcd u1.natAbs u2.natAbs : ℝ) * bpg_Inn X Y u1 u2
      = (∑ g ∈ Finset.Icc 1 R, (Nat.totient g : ℝ) * bpg_Cg g u1 u2) * bpg_Inn X Y u1 u2 := by
  by_cases hc : u1 ≠ 0 ∧ u2 ≠ 0
  · have hb1 : u1.natAbs ≤ R := (bpg_mem_zBox_iff R u1).mp hu1
    have hb2 : u2.natAbs ≤ R := (bpg_mem_zBox_iff R u2).mp hu2
    have hn1 : 1 ≤ u1.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hc.1)
    have hn2 : 1 ≤ u2.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hc.2)
    rw [bpg_gcd_cast_eq_sum_phi R u1.natAbs u2.natAbs hn1 hn2 hb1 hb2]
    congr 1
    apply Finset.sum_congr rfl; intro g _
    unfold bpg_Cg; rw [if_pos hc]; ring
  · rw [bpg_Inn_eq_zero X Y u1 u2 hc]; ring

lemma bpg_Cg_mul_Inn (X Y : ℕ) (g : ℕ) (u1 u2 : ℤ) :
    bpg_Cg g u1 u2 * bpg_Inn X Y u1 u2
      = (if g ∣ u1.natAbs then (1:ℝ) else 0) *
          ((if g ∣ u2.natAbs then (1:ℝ) else 0) * bpg_Inn X Y u1 u2) := by
  by_cases hc : u1 ≠ 0 ∧ u2 ≠ 0
  · unfold bpg_Cg; rw [if_pos hc]; ring
  · rw [bpg_Inn_eq_zero X Y u1 u2 hc]; unfold bpg_Cg; rw [if_neg hc]; ring

/-! ## Reindexing the squared `u`-sum -/

lemma bpg_reindex2 (R g : ℕ) (hg : 1 ≤ g) (F : ℤ → ℤ → ℝ) :
    (∑ u1 ∈ zBox R, ∑ u2 ∈ zBox R,
      (if g ∣ u1.natAbs then (1:ℝ) else 0) * ((if g ∣ u2.natAbs then (1:ℝ) else 0) * F u1 u2))
      = ∑ v1 ∈ zBox (R/g), ∑ v2 ∈ zBox (R/g), F ((g:ℤ)*v1) ((g:ℤ)*v2) := by
  have h1 : (∑ u1 ∈ zBox R, ∑ u2 ∈ zBox R,
        (if g ∣ u1.natAbs then (1:ℝ) else 0) * ((if g ∣ u2.natAbs then (1:ℝ) else 0) * F u1 u2))
      = ∑ u1 ∈ zBox R, (if g ∣ u1.natAbs then (1:ℝ) else 0) *
          (∑ u2 ∈ zBox R, (if g ∣ u2.natAbs then (1:ℝ) else 0) * F u1 u2) := by
    apply Finset.sum_congr rfl; intro u1 _; rw [Finset.mul_sum]
  rw [h1]
  simp_rw [boole_mul]
  rw [bpg_sum_dvd_natAbs_eq R g hg (fun u1 => ∑ u2 ∈ zBox R, (if g ∣ u2.natAbs then F u1 u2 else 0))]
  apply Finset.sum_congr rfl; intro v1 _
  rw [bpg_sum_dvd_natAbs_eq R g hg (fun u2 => F ((g:ℤ)*v1) u2)]

lemma bpg_sum_zBox_Inn_eq_zPz (R X Y g : ℕ) (_hg : 1 ≤ g) :
    (∑ v1 ∈ zBox (R/g), ∑ v2 ∈ zBox (R/g), bpg_Inn X Y ((g:ℤ)*v1) ((g:ℤ)*v2))
      = ∑ v1 ∈ zPz (R/g), ∑ v2 ∈ zPz (R/g), bpg_Inn X Y ((g:ℤ)*v1) ((g:ℤ)*v2) := by
  have hsub : zPz (R/g) ⊆ zBox (R/g) := Finset.filter_subset _ _
  have h1 : (∑ v1 ∈ zPz (R/g), ∑ v2 ∈ zPz (R/g), bpg_Inn X Y ((g:ℤ)*v1) ((g:ℤ)*v2))
      = ∑ v1 ∈ zBox (R/g), ∑ v2 ∈ zPz (R/g), bpg_Inn X Y ((g:ℤ)*v1) ((g:ℤ)*v2) := by
    apply Finset.sum_subset hsub
    intro v1 hv1 hv1not
    have h0 : v1 = 0 := by
      by_contra hne
      exact hv1not (by rw [bpg_mem_zPz_iff]; exact ⟨hne, (bpg_mem_zBox_iff (R/g) v1).mp hv1⟩)
    rw [h0]
    apply Finset.sum_eq_zero
    intro v2 _
    exact bpg_Inn_eq_zero X Y _ _ (by simp)
  rw [h1]
  apply Finset.sum_congr rfl; intro v1 _
  apply Eq.symm
  apply Finset.sum_subset hsub
  intro v2 hv2 hv2not
  have h0 : v2 = 0 := by
    by_contra hne
    exact hv2not (by rw [bpg_mem_zPz_iff]; exact ⟨hne, (bpg_mem_zBox_iff (R/g) v2).mp hv2⟩)
  rw [h0]
  exact bpg_Inn_eq_zero X Y _ _ (by simp)

lemma bpg_sum3_swap (s : Finset ℤ) (t : Finset ℕ) (f : ℤ → ℤ → ℕ → ℝ) :
    (∑ a∈s, ∑ b∈s, ∑ c∈t, f a b c) = ∑ c∈t, ∑ a∈s, ∑ b∈s, f a b c := by
  have h : (∑ a∈s, ∑ b∈s, ∑ c∈t, f a b c) = ∑ a∈s, ∑ c∈t, ∑ b∈s, f a b c := by
    apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]
  rw [h, Finset.sum_comm]

lemma bpg_sum_Cg_Inn (R X Y g : ℕ) (hg : 1 ≤ g) :
    (∑ u1 ∈ zBox R, ∑ u2 ∈ zBox R, bpg_Cg g u1 u2 * bpg_Inn X Y u1 u2)
      = ∑ v1 ∈ zPz (R/g), ∑ v2 ∈ zPz (R/g), bpg_Inn X Y ((g:ℤ)*v1) ((g:ℤ)*v2) := by
  simp_rw [bpg_Cg_mul_Inn X Y g]
  rw [bpg_reindex2 R g hg (bpg_Inn X Y)]
  exact bpg_sum_zBox_Inn_eq_zPz R X Y g hg

/-! ## The pointwise bound `T4 (g x) (g y) h₁ h₂ ≤ τ(g)⁴ · T4 x y h₁ h₂` -/

lemma bpg_T4_eq_tauR (a b c d : ℤ) :
    T4 a b c d = (Work.FIArea2.tauR ((a*c^2 - b*d^2).natAbs))^4 := rfl

lemma bpg_T4_mul_le (g : ℕ) (v1 v2 h1 h2 : ℤ) :
    T4 ((g:ℤ)*v1) ((g:ℤ)*v2) h1 h2 ≤ ((g.divisors.card : ℝ))^4 * T4 v1 v2 h1 h2 := by
  rw [bpg_T4_eq_tauR ((g:ℤ)*v1) ((g:ℤ)*v2) h1 h2, bpg_T4_eq_tauR v1 v2 h1 h2]
  have hsplit : ((g:ℤ)*v1) * h1^2 - ((g:ℤ)*v2) * h2^2 = (g:ℤ) * (v1*h1^2 - v2*h2^2) := by ring
  rw [hsplit, Int.natAbs_mul, Int.natAbs_natCast]
  have h := pow_le_pow_left₀ (Work.FIArea2.tauR_nonneg (g * (v1*h1^2 - v2*h2^2).natAbs))
      (Work.FIArea2.tauR_mul_le g ((v1*h1^2 - v2*h2^2).natAbs)) 4
  rw [mul_pow] at h
  have hgt : Work.FIArea2.tauR g = ((g.divisors.card : ℝ)) := rfl
  rw [hgt] at h
  exact h

lemma bpg_sum_T4_le_uboxSum (r X Y g : ℕ) :
    (∑ v1 ∈ zPz r, ∑ v2 ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
        T4 ((g:ℤ)*v1) ((g:ℤ)*v2) h1 h2)
      ≤ ((g.divisors.card : ℝ))^4 * uboxSum r X Y := by
  change (∑ v1 ∈ zPz r, ∑ v2 ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
        T4 ((g:ℤ)*v1) ((g:ℤ)*v2) h1 h2)
      ≤ ((g.divisors.card : ℝ))^4 *
        (∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, T4 x y h1 h2)
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro v1 _
  apply Finset.sum_le_sum; intro v2 _
  apply Finset.sum_le_sum; intro h1 _
  apply Finset.sum_le_sum; intro h2 _
  exact bpg_T4_mul_le g v1 v2 h1 h2

/-! ## The main result -/

/-- Hint: `bulkPart R X Y` is the sum over `u₁,u₂ ∈ zPz R`, `h₁ ∈ zPz X`, `h₂ ∈ zPz Y` of
`gcd(|u₁|,|u₂|)·T4 u₁ u₂ h₁ h₂`.  Expand `gcd(a,b) = Σ_{g ∣ a, g ∣ b} φ(g)`
(`Work.FIArea2.R6.gcd_cast_eq_sum_phi`, in `Submission.Work.FIArea2.R6.hbox6_crux`), reindex
`u₁ = g·x`, `u₂ = g·y` with `x,y ∈ zPz ⌊R/g⌋` (`Work.FIArea2.R6.sum_dvd_natAbs_eq`, same module),
and bound `T4 (g·x) (g·y) h₁ h₂ = τ(|g·(xh₁²-yh₂²)|)⁴ ≤ τ(g)⁴·T4 x y h₁ h₂`
(`Work.FIArea2.tauR_mul_le`, in `Submission.Work.FIArea2.sum_tau_pow_le`). -/
theorem bulkPart_le_gsum (R X Y : ℕ) :
    Work.FIArea2.R6.bulkPart R X Y
      ≤ ∑ g ∈ Finset.Icc 1 R, (Nat.totient g : ℝ) * ((g.divisors.card : ℝ)) ^ 4
          * Work.FIArea2.R6.uboxSum (R / g) X Y := by
  have step1 : (∑ u1 ∈ zBox R, ∑ u2 ∈ zBox R,
          (Nat.gcd u1.natAbs u2.natAbs : ℝ) * bpg_Inn X Y u1 u2)
      = ∑ u1 ∈ zBox R, ∑ u2 ∈ zBox R,
          (∑ g ∈ Finset.Icc 1 R, (Nat.totient g : ℝ) * bpg_Cg g u1 u2) * bpg_Inn X Y u1 u2 := by
    apply Finset.sum_congr rfl; intro u1 hu1
    apply Finset.sum_congr rfl; intro u2 hu2
    exact bpg_gcd_mul_Inn R X Y u1 u2 hu1 hu2
  have step2 : (∑ u1 ∈ zBox R, ∑ u2 ∈ zBox R,
          (∑ g ∈ Finset.Icc 1 R, (Nat.totient g : ℝ) * bpg_Cg g u1 u2) * bpg_Inn X Y u1 u2)
      = ∑ g ∈ Finset.Icc 1 R, (Nat.totient g : ℝ) *
          ∑ u1 ∈ zBox R, ∑ u2 ∈ zBox R, bpg_Cg g u1 u2 * bpg_Inn X Y u1 u2 := by
    have e1 : ∀ u1 u2, (∑ g ∈ Finset.Icc 1 R, (Nat.totient g : ℝ) * bpg_Cg g u1 u2) * bpg_Inn X Y u1 u2
        = ∑ g ∈ Finset.Icc 1 R, ((Nat.totient g : ℝ) * bpg_Cg g u1 u2) * bpg_Inn X Y u1 u2 := by
      intro u1 u2; exact Finset.sum_mul _ _ _
    simp_rw [e1]
    rw [bpg_sum3_swap (zBox R) (Finset.Icc 1 R)
        (fun u1 u2 g => ((Nat.totient g : ℝ) * bpg_Cg g u1 u2) * bpg_Inn X Y u1 u2)]
    apply Finset.sum_congr rfl; intro g _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u1 _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u2 _
    ring
  rw [bpg_bulkPart_eq R X Y, step1, step2]
  calc
    (∑ g ∈ Finset.Icc 1 R, (Nat.totient g : ℝ) *
        ∑ u1 ∈ zBox R, ∑ u2 ∈ zBox R, bpg_Cg g u1 u2 * bpg_Inn X Y u1 u2)
      = ∑ g ∈ Finset.Icc 1 R, (Nat.totient g : ℝ) *
          (∑ v1 ∈ zPz (R/g), ∑ v2 ∈ zPz (R/g), ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
            T4 ((g:ℤ)*v1) ((g:ℤ)*v2) h1 h2) := by
        apply Finset.sum_congr rfl; intro g hg
        have hg1 : 1 ≤ g := (Finset.mem_Icc.mp hg).1
        have hgz : (g:ℤ) ≠ 0 := by
          have : g ≠ 0 := by omega
          exact_mod_cast this
        congr 1
        rw [bpg_sum_Cg_Inn R X Y g hg1]
        apply Finset.sum_congr rfl; intro v1 hv1
        apply Finset.sum_congr rfl; intro v2 hv2
        exact bpg_Inn_of_ne_zero X Y ((g:ℤ)*v1) ((g:ℤ)*v2)
          ⟨mul_ne_zero hgz ((bpg_mem_zPz_iff (R/g) v1).mp hv1).1,
           mul_ne_zero hgz ((bpg_mem_zPz_iff (R/g) v2).mp hv2).1⟩
    _ ≤ ∑ g ∈ Finset.Icc 1 R, (Nat.totient g : ℝ) *
          (((g.divisors.card : ℝ))^4 * uboxSum (R/g) X Y) := by
        apply Finset.sum_le_sum; intro g _
        exact mul_le_mul_of_nonneg_left (bpg_sum_T4_le_uboxSum (R/g) X Y g) (Nat.cast_nonneg _)
    _ = ∑ g ∈ Finset.Icc 1 R, (Nat.totient g : ℝ) * ((g.divisors.card : ℝ)) ^ 4
          * uboxSum (R / g) X Y := by
        apply Finset.sum_congr rfl; intro g _; ring

end

end Work.FIArea2.R6
