/-
# `Submission.Work.FIChain.Ad_block_eq_real` — the `(1.7)`-block with **real** endpoints

The sum of `a (ℓ*c)` over `A < c ≤ B` (`A`, `B` real), `ℓ c ≤ N`, `d ∣ c` is the difference of the
congruence sums of `a` at modulus `ℓ*d` and the **real** endpoints `min (ℓ B) N` and `ℓ A`.  The
real (rather than integer/floored) endpoints are what keep the `b`-window conditions of the
downstream `(2.4)`-application free of the modulus `ℓ`: with `n = ℓc` the block is
`Ad a (ℓd)(min (ℓB) N) − Ad a (ℓd)(ℓA) = Σ_{ℓA<n≤min(ℓB,N), ℓd|n} a n`. -/
import Mathlib
import Submission.Work.FIChain.S3plusC_route_defs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

noncomputable section



/-- **The `(1.7)`-block with real endpoints.** -/
lemma Ad_block_eq_real (a : ℕ → ℝ) (N ℓ d : ℕ) (A B : ℝ) (hℓ : 1 ≤ ℓ)
    (hA0 : 0 ≤ A) (hAB : A ≤ B) (hAN : (ℓ : ℝ) * A ≤ (N : ℝ)) :
    (∑ c ∈ (Finset.Icc 1 N).filter
        (fun c : ℕ => A < (c:ℝ) ∧ (c:ℝ) ≤ B ∧ ℓ * c ≤ N ∧ d ∣ c), a (ℓ * c))
      = Submission.ASP.Ad a (ℓ * d) (min ((ℓ : ℝ) * B) (N : ℝ))
        - Submission.ASP.Ad a (ℓ * d) ((ℓ : ℝ) * A) := by
  classical
  have hℓ0 : 0 < ℓ := by omega
  have hℓpos : (0:ℝ) < (ℓ:ℝ) := by exact_mod_cast hℓ0
  set M : ℝ := min ((ℓ:ℝ) * B) (N:ℝ) with hM
  have hMA : (ℓ:ℝ) * A ≤ M := le_min (mul_le_mul_of_nonneg_left hAB (by positivity)) hAN
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact le_min (mul_nonneg (Nat.cast_nonneg _) (le_trans hA0 hAB)) (Nat.cast_nonneg _)
  set s : Finset ℕ := (Finset.Icc 1 N).filter
        (fun c : ℕ => A < (c:ℝ) ∧ (c:ℝ) ≤ B ∧ ℓ * c ≤ N ∧ d ∣ c) with hs
  set t : Finset ℕ := (Finset.Icc 1 ⌊M⌋₊).filter
        (fun n : ℕ => ℓ * d ∣ n ∧ (ℓ:ℝ) * A < (n:ℝ)) with ht
  have hbij : ∑ c ∈ s, a (ℓ * c) = ∑ n ∈ t, a n := by
    refine Finset.sum_bij (fun c _ => ℓ * c) ?_ ?_ ?_ ?_
    · intro c hc
      rw [hs, Finset.mem_filter, Finset.mem_Icc] at hc
      obtain ⟨⟨hc1, hcN⟩, hAc, hcB, hclN, hdc⟩ := hc
      rw [ht, Finset.mem_filter, Finset.mem_Icc]
      have hcast : ((ℓ * c : ℕ) : ℝ) = (ℓ:ℝ) * (c:ℝ) := by push_cast; ring
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      · refine Nat.le_floor ?_
        rw [hM, hcast]
        exact le_min (mul_le_mul_of_nonneg_left hcB (by positivity)) (by rw [← hcast]; exact_mod_cast hclN)
      · exact Nat.mul_dvd_mul_left ℓ hdc
      · rw [hcast]; exact mul_lt_mul_of_pos_left hAc hℓpos
    · intro c₁ hc₁ c₂ hc₂ heq
      exact Nat.eq_of_mul_eq_mul_left hℓ0 heq
    · intro n hn
      rw [ht, Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnM⟩, hldn, hAn⟩ := hn
      have hnpos : 0 < n := hn1
      have hℓn : ℓ ∣ n := (dvd_mul_right ℓ d).trans hldn
      have hlc : ℓ * (n / ℓ) = n := Nat.mul_div_cancel' hℓn
      have hge : ℓ ≤ n := Nat.le_of_dvd hnpos hℓn
      have hcast : ((n:ℕ):ℝ) ≤ M := le_trans (by exact_mod_cast hnM) (Nat.floor_le hM0)
      have hcastl : ((n:ℕ):ℝ) = (ℓ:ℝ) * ((n / ℓ : ℕ):ℝ) := by
        conv_lhs => rw [← hlc]
        push_cast
        ring
      have hcast' := hcast
      rw [hM] at hcast'
      have hnN : n ≤ N := by
        have h4 : ((n:ℕ):ℝ) ≤ (N:ℝ) := le_trans hcast' (min_le_right _ _)
        exact_mod_cast h4
      have hc1 : 1 ≤ n / ℓ := by
        apply Nat.le_of_mul_le_mul_left _ hℓ0
        rw [mul_one, hlc]; exact hge
      have hAc : A < ((n / ℓ : ℕ) : ℝ) := by
        have h2 : (ℓ:ℝ) * A < (ℓ:ℝ) * ((n/ℓ : ℕ) : ℝ) := by rw [← hcastl]; exact hAn
        exact lt_of_mul_lt_mul_left h2 hℓpos.le
      have hcB : ((n / ℓ : ℕ) : ℝ) ≤ B := by
        have h2 : (ℓ:ℝ) * ((n/ℓ : ℕ) : ℝ) ≤ (ℓ:ℝ) * B := by
          rw [← hcastl]
          rw [hM] at hcast
          exact le_trans hcast (min_le_left _ _)
        exact le_of_mul_le_mul_left h2 hℓpos
      have hcN : ℓ * (n / ℓ) ≤ N := by rw [hlc]; exact hnN
      have hcN' : n / ℓ ≤ N := le_trans (Nat.div_le_self n ℓ) hnN
      have hdc : d ∣ n / ℓ := by
        have hthis : ℓ * d ∣ ℓ * (n / ℓ) := by rw [hlc]; exact hldn
        exact (Nat.mul_dvd_mul_iff_left hℓ0).mp hthis
      refine ⟨n / ℓ, ?_, hlc⟩
      · rw [hs, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hc1, hcN'⟩, hAc, hcB, hcN, hdc⟩
    · intro c _
      rfl
  have hAdM : Submission.ASP.Ad a (ℓ * d) M
      = ∑ n ∈ (Finset.Icc 1 ⌊M⌋₊).filter (fun n => ℓ * d ∣ n), a n := by
    simp only [Submission.ASP.Ad, Nat.floor_natCast]
  have hAdA : Submission.ASP.Ad a (ℓ * d) ((ℓ:ℝ) * A)
      = ∑ n ∈ (Finset.Icc 1 ⌊(ℓ:ℝ) * A⌋₊).filter (fun n => ℓ * d ∣ n), a n := by
    simp only [Submission.ASP.Ad, Nat.floor_natCast]
  have hsub : (Finset.Icc 1 ⌊(ℓ:ℝ) * A⌋₊).filter (fun n => ℓ * d ∣ n)
      ⊆ (Finset.Icc 1 ⌊M⌋₊).filter (fun n => ℓ * d ∣ n) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, le_trans hn.1.2 (Nat.floor_mono hMA)⟩, hn.2⟩
  have hsdiff : (Finset.Icc 1 ⌊M⌋₊).filter (fun n => ℓ * d ∣ n)
      \ (Finset.Icc 1 ⌊(ℓ:ℝ) * A⌋₊).filter (fun n => ℓ * d ∣ n) = t := by
    rw [ht]
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hn1, hnM⟩, hdvd⟩, hnot⟩
      refine ⟨⟨hn1, hnM⟩, hdvd, ?_⟩
      by_contra hcon
      push_neg at hcon
      exact hnot ⟨⟨hn1, Nat.le_floor hcon⟩, hdvd⟩
    · rintro ⟨⟨hn1, hnM⟩, hdvd, hAn⟩
      refine ⟨⟨⟨hn1, hnM⟩, hdvd⟩, ?_⟩
      rintro ⟨⟨-, hle⟩, -⟩
      have : (n:ℝ) ≤ (ℓ:ℝ) * A := le_trans (by exact_mod_cast hle) (Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) hA0))
      linarith
  have hRHS : (∑ n ∈ (Finset.Icc 1 ⌊M⌋₊).filter (fun n => ℓ * d ∣ n)
        \ (Finset.Icc 1 ⌊(ℓ:ℝ) * A⌋₊).filter (fun n => ℓ * d ∣ n), a n)
      = (∑ n ∈ (Finset.Icc 1 ⌊M⌋₊).filter (fun n => ℓ * d ∣ n), a n)
        - (∑ n ∈ (Finset.Icc 1 ⌊(ℓ:ℝ) * A⌋₊).filter (fun n => ℓ * d ∣ n), a n) := by
    have h := Finset.sum_sdiff (f := a) hsub
    linarith
  rw [hbij, hAdM, hAdA, ← hRHS, ← hsdiff]


end

end Work.FIChain
