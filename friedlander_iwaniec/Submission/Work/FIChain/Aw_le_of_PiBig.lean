import Mathlib
import Submission.Work.FIChain.BpWinDefs
import Submission.Work.FIChain.chainWindowFacts
import Submission.Work.FIChain.Xf_sum_le_BformPi
import Submission.Work.FITop.SumIteDivDvd
import Submission.Work.FIChain.singleDvd_atilc_le

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem Xf_window_split_aw (x Pz c : ℕ) (u : ℝ) (hc : 1 ≤ c) (hu : 1 ≤ u) :
    Work.FIChain.Xf x Pz c u =
      Work.FIChain.Xf x Pz c ((⌊u⌋₊ : ℕ) : ℝ) +
        (if (((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * u) ∧ c * (2 * ⌊u⌋₊ + 1) ≤ x ∧
              Work.FITop4.PiCond Pz (2 * ⌊u⌋₊ + 1)
          then (ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ) *
              Work.FIChain.atilc (c * (2 * ⌊u⌋₊ + 1)) else 0) := by
  classical
  rw [Work.FIChain.Xf, Work.FIChain.Xf, Finset.sum_filter, Finset.sum_filter]
  set n : ℕ := 2 * ⌊u⌋₊ + 1 with hn
  have hncast : ((n : ℕ) : ℝ) = 2 * ((⌊u⌋₊ : ℕ) : ℝ) + 1 := by rw [hn]; push_cast; ring
  have hfl : ((⌊u⌋₊ : ℕ) : ℝ) ≤ u := Nat.floor_le (by linarith)
  have hflt : u < ((⌊u⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one u
  have hnlt : u < (n : ℝ) := by
    rw [hncast]
    have h0 : (0 : ℝ) ≤ ((⌊u⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  set Cnd : Prop := ((n : ℝ) ≤ 2 * u ∧ c * n ≤ x ∧ Work.FITop4.PiCond Pz n) with hCnd
  set X : ℝ := (if Cnd then (ArithmeticFunction.moebius n : ℝ) * Work.FIChain.atilc (c * n)
    else 0) with hX
  have hXsum : X = ∑ a ∈ Finset.Icc 1 x, (if a = n then X else 0) := by
    rw [Finset.sum_ite_eq']
    by_cases hcd : Cnd
    · have hnx : n ≤ x := by
        have h2 : 1 * n ≤ c * n := Nat.mul_le_mul_right n hc
        have h3 : c * n ≤ x := by rw [hCnd] at hcd; exact hcd.2.1
        omega
      rw [if_pos (Finset.mem_Icc.mpr ⟨by omega, hnx⟩)]
    · have hX0 : X = 0 := by rw [hX, if_neg hcd]
      rw [hX0]
      by_cases hm : n ∈ Finset.Icc 1 x
      · rw [if_pos hm]
      · rw [if_neg hm]
  rw [hXsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  by_cases han : a = n
  · rw [han, if_pos rfl, hX]
    have hfv : ¬ (c * n ≤ x ∧ ((⌊u⌋₊ : ℕ) : ℝ) < (n : ℝ) ∧
        (n : ℝ) ≤ 2 * ((⌊u⌋₊ : ℕ) : ℝ) ∧ Work.FITop4.PiCond Pz n) := by
      rintro ⟨-, -, h3, -⟩
      rw [hncast] at h3
      linarith
    rw [if_neg hfv, zero_add]
    by_cases hcd : Cnd
    · rw [if_pos hcd]
      rw [hCnd] at hcd
      rw [if_pos ⟨hcd.2.1, hnlt, hcd.1, hcd.2.2⟩]
    · rw [if_neg hcd]
      rw [if_neg (fun hh => hcd (by rw [hCnd]; exact ⟨hh.2.2.1, hh.1, hh.2.2.2⟩))]
  · rw [if_neg han, add_zero]
    have hiff : (c * a ≤ x ∧ u < ((a : ℕ) : ℝ) ∧ ((a : ℕ) : ℝ) ≤ 2 * u ∧
          Work.FITop4.PiCond Pz a)
        ↔ (c * a ≤ x ∧ ((⌊u⌋₊ : ℕ) : ℝ) < ((a : ℕ) : ℝ) ∧
            ((a : ℕ) : ℝ) ≤ 2 * ((⌊u⌋₊ : ℕ) : ℝ) ∧ Work.FITop4.PiCond Pz a) := by
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨h1, ?_, ?_, h4⟩
        · have h : ((⌊u⌋₊ : ℕ) : ℝ) < (a : ℝ) := by
            by_contra hcon
            exact absurd (le_trans (not_lt.mp hcon) hfl) (not_le.mpr h2)
          exact_mod_cast h
        · have hlt2 : (a : ℝ) < ((2 * ⌊u⌋₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
          have hle : a ≤ 2 * ⌊u⌋₊ + 1 := by
            have h' : a < 2 * ⌊u⌋₊ + 2 := by exact_mod_cast hlt2
            omega
          have hne : a ≠ 2 * ⌊u⌋₊ + 1 := by
            intro hh; exact han (by rw [hn, hh])
          have : a ≤ 2 * ⌊u⌋₊ := by omega
          exact_mod_cast this
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨h1, ?_, ?_, h4⟩
        · have h2n : ⌊u⌋₊ < a := by exact_mod_cast h2
          have hle : ((⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ (a : ℝ) :=
            Nat.cast_le.mpr (Nat.succ_le_of_lt h2n)
          push_cast at hle
          linarith
        · linarith
    by_cases h : (c * a ≤ x ∧ u < ((a : ℕ) : ℝ) ∧ ((a : ℕ) : ℝ) ≤ 2 * u ∧
        Work.FITop4.PiCond Pz a)
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hh => h (hiff.mpr hh))]

theorem Aw_le_of_PiBig (h : Work.FITop4.Prop41StatementPiBig) (η : ℝ) (hη : 0 < η)
    (hη32 : η < 3 / 32) :
    ∃ B K : ℝ, ∃ x₀ : ℕ, 0 < B ∧ 0 < K ∧ ∀ x : ℕ, x₀ ≤ x → ∀ u : ℝ,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η / 2) + 2 < u →
      u ≤ Work.FIChain.sc x B * (Real.exp 1 * Work.FIChain.Yc x B) →
      Work.FIChain.Aw x (Work.FIChain.Pzc x) u
        ≤ K * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) := by
  obtain ⟨B₀, K₁, x₁, hB₀pos, _hB₀le, hK₁pos, hProp⟩ := h (η / 2) (by linarith) (by linarith)
  obtain ⟨C₂, hC₂pos, x₂, hC₂⟩ := singleDvd_atilc_le (η / 2) (by linarith)
  have hη4 : η / 4 < 1 / 32 := by linarith
  obtain ⟨xw, hxw⟩ := Filter.eventually_atTop.mp (chainWindowFacts (η / 4) B₀ (by linarith) hη4 hB₀pos)
  refine ⟨B₀ + 2, K₁ + C₂, max (max x₁ x₂) xw + 16, by linarith, by positivity, ?_⟩
  intro x hx u hulo huhi
  have hx1 : x₁ ≤ x := by omega
  have hx2 : x₂ ≤ x := by omega
  have hxw' : xw ≤ x := by omega
  obtain ⟨hwin1, hwin2, hwin3, hPz1, hPz2, hPz3, hx3, hloglog2⟩ := hxw x hxw'
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by
    rw [Real.le_log_iff_exp_le hxpos]
    linarith [Real.exp_one_lt_three]
  have hloglog1 : (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) := by linarith
  have hu1 : (1 : ℝ) ≤ u := by
    have h1 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 + η / 2) := Real.one_le_rpow hx1R (by linarith)
    linarith
  -- the aligned window `N = ⌊u⌋`
  have hNlo : (x : ℝ) ^ ((1 : ℝ) / 4 + η / 2) < ((⌊u⌋₊ : ℕ) : ℝ) := by
    have h1 := Nat.lt_floor_add_one u
    linarith
  have hNhi : ((⌊u⌋₊ : ℕ) : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B₀) := by
    have hle : ((⌊u⌋₊ : ℕ) : ℝ) ≤ u := Nat.floor_le (by linarith)
    linarith
  have hN1 : (1 : ℝ) ≤ ((⌊u⌋₊ : ℕ) : ℝ) :=
    le_trans (Real.one_le_rpow hx1R (by linarith)) hNlo.le
  have hCone : (1 : ℝ) ≤ ((⌊u⌋₊ : ℕ) : ℝ) ^ (1 - η / 2) := Real.one_le_rpow hN1 (by linarith)
  have hPropN : Work.FITop.BformPi x ⌊u⌋₊ 1 (Work.FIChain.Pzc x)
      ≤ K₁ * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) := by
    have h1 := hProp x hx1 ⌊u⌋₊ hNlo hNhi hloglog1 1 le_rfl hCone (Work.FIChain.Pzc x) hPz1 hPz2 hPz3
    rwa [show (4 : ℝ) - Work.FITop4.Astar = -((2 : ℝ) ^ (26 : ℕ)) by
      rw [Work.FITop4.Astar]; ring] at h1
  -- the correction term (the single integer `2⌊u⌋+1`)
  have hn₀lo : (x : ℝ) ^ ((1 : ℝ) / 4 + η / 2) ≤ (((2 * ⌊u⌋₊ + 1 : ℕ)) : ℝ) := by
    have h1 := Nat.lt_floor_add_one u
    have h2 : (2 : ℝ) * u - 1 < (((2 * ⌊u⌋₊ + 1 : ℕ)) : ℝ) := by push_cast; linarith
    linarith
  have hn₀hi : (((2 * ⌊u⌋₊ + 1 : ℕ)) : ℝ) ≤ Real.sqrt (x : ℝ) := by
    have hle : ((⌊u⌋₊ : ℕ) : ℝ) ≤ u := Nat.floor_le (by linarith)
    rw [Real.sqrt_eq_rpow]
    push_cast
    linarith
  have hcorr : (∑ c ∈ Finset.Icc 1 x,
        |(if (((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * u ∧ c * (2 * ⌊u⌋₊ + 1) ≤ x ∧
              Work.FITop4.PiCond (Work.FIChain.Pzc x) (2 * ⌊u⌋₊ + 1))
          then (ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ) *
              Work.FIChain.atilc (c * (2 * ⌊u⌋₊ + 1)) else 0)|)
      ≤ C₂ * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) := by
    have hpt : ∀ c : ℕ,
        |(if (((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * u ∧ c * (2 * ⌊u⌋₊ + 1) ≤ x ∧
              Work.FITop4.PiCond (Work.FIChain.Pzc x) (2 * ⌊u⌋₊ + 1))
          then (ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ) *
              Work.FIChain.atilc (c * (2 * ⌊u⌋₊ + 1)) else 0)|
          ≤ (if c * (2 * ⌊u⌋₊ + 1) ≤ x then
              Work.FIChain.atilc (c * (2 * ⌊u⌋₊ + 1)) else 0) := by
      intro c
      by_cases h : (((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * u ∧ c * (2 * ⌊u⌋₊ + 1) ≤ x ∧
          Work.FITop4.PiCond (Work.FIChain.Pzc x) (2 * ⌊u⌋₊ + 1))
      · rw [if_pos h, if_pos h.2.1, abs_mul]
        have hmu : |(ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ)| ≤ 1 := by
          have hμ := ArithmeticFunction.abs_moebius_le_one (n := 2 * ⌊u⌋₊ + 1)
          exact_mod_cast hμ
        have hnn : 0 ≤ Work.FIChain.atilc (c * (2 * ⌊u⌋₊ + 1)) := Work.FITop.atilFIa_nonneg _
        calc |(ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ)| *
              |Work.FIChain.atilc (c * (2 * ⌊u⌋₊ + 1))|
            ≤ 1 * |Work.FIChain.atilc (c * (2 * ⌊u⌋₊ + 1))| :=
              mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
          _ = Work.FIChain.atilc (c * (2 * ⌊u⌋₊ + 1)) := by
              rw [one_mul, abs_of_nonneg hnn]
      · rw [if_neg h, abs_zero]
        by_cases h2 : c * (2 * ⌊u⌋₊ + 1) ≤ x
        · rw [if_pos h2]; exact Work.FITop.atilFIa_nonneg _
        · rw [if_neg h2]
    have hsum1 : (∑ c ∈ Finset.Icc 1 x,
          |(if (((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * u ∧ c * (2 * ⌊u⌋₊ + 1) ≤ x ∧
                Work.FITop4.PiCond (Work.FIChain.Pzc x) (2 * ⌊u⌋₊ + 1))
            then (ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ) *
                Work.FIChain.atilc (c * (2 * ⌊u⌋₊ + 1)) else 0)|)
        ≤ ∑ c ∈ Finset.Icc 1 x, (if c * (2 * ⌊u⌋₊ + 1) ≤ x then
            Work.FIChain.atilc (c * (2 * ⌊u⌋₊ + 1)) else 0) :=
      Finset.sum_le_sum (fun c _ => hpt c)
    have hswap : (∑ c ∈ Finset.Icc 1 x, (if c * (2 * ⌊u⌋₊ + 1) ≤ x then
            Work.FIChain.atilc (c * (2 * ⌊u⌋₊ + 1)) else 0))
        = ∑ c ∈ Finset.Icc 1 x, (if (2 * ⌊u⌋₊ + 1) * c ≤ x then
            Work.FIChain.atilc ((2 * ⌊u⌋₊ + 1) * c) else 0) := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Nat.mul_comm c (2 * ⌊u⌋₊ + 1)]
    have hsum2 : (∑ c ∈ Finset.Icc 1 x, (if (2 * ⌊u⌋₊ + 1) * c ≤ x then
            Work.FIChain.atilc ((2 * ⌊u⌋₊ + 1) * c) else 0))
        ≤ ∑ n ∈ (Finset.Icc 1 x).filter (fun n => (2 * ⌊u⌋₊ + 1) ∣ n),
            Work.FIChain.atilc n := by
      have h := Work.FITop.SumIteDivDvd (2 * ⌊u⌋₊ + 1) x (by omega) (fun _ : ℕ => (1 : ℝ))
        Work.FIChain.atilc
      simpa using h
    have hfin := hC₂ x hx2 (2 * ⌊u⌋₊ + 1) hn₀lo hn₀hi
    exact le_trans hsum1 (le_trans (le_of_eq hswap) (le_trans hsum2 hfin))
  -- assemble
  have hsplit : ∀ c ∈ Finset.Icc 1 x, |Work.FIChain.Xf x (Work.FIChain.Pzc x) c u|
      ≤ |Work.FIChain.Xf x (Work.FIChain.Pzc x) c ((⌊u⌋₊ : ℕ) : ℝ)|
        + |(if (((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * u ∧ c * (2 * ⌊u⌋₊ + 1) ≤ x ∧
              Work.FITop4.PiCond (Work.FIChain.Pzc x) (2 * ⌊u⌋₊ + 1))
            then (ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ) *
                Work.FIChain.atilc (c * (2 * ⌊u⌋₊ + 1)) else 0)| := by
    intro c hc
    rw [Xf_window_split_aw x (Work.FIChain.Pzc x) c u (Finset.mem_Icc.mp hc).1 hu1]
    exact abs_add_le _ _
  have hsumsplit := Finset.sum_le_sum hsplit
  rw [Finset.sum_add_distrib] at hsumsplit
  calc Work.FIChain.Aw x (Work.FIChain.Pzc x) u
      = ∑ c ∈ Finset.Icc 1 x, |Work.FIChain.Xf x (Work.FIChain.Pzc x) c u| := rfl
    _ ≤ (∑ c ∈ Finset.Icc 1 x, |Work.FIChain.Xf x (Work.FIChain.Pzc x) c ((⌊u⌋₊ : ℕ) : ℝ)|)
        + ∑ c ∈ Finset.Icc 1 x,
            |(if (((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * u ∧ c * (2 * ⌊u⌋₊ + 1) ≤ x ∧
                  Work.FITop4.PiCond (Work.FIChain.Pzc x) (2 * ⌊u⌋₊ + 1))
                then (ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ) *
                    Work.FIChain.atilc (c * (2 * ⌊u⌋₊ + 1)) else 0)| := hsumsplit
    _ ≤ Work.FITop.BformPi x ⌊u⌋₊ 1 (Work.FIChain.Pzc x)
        + C₂ * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) :=
        add_le_add (Xf_sum_le_BformPi x ⌊u⌋₊ (Work.FIChain.Pzc x)) hcorr
    _ ≤ K₁ * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ)))
        + C₂ * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) :=
        add_le_add hPropN le_rfl
    _ = (K₁ + C₂) * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) := by
        ring

end

end Work.FIChain
