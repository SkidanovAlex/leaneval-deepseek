import Mathlib

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Double-counting identity: summing `F (d / e) e` over pairs `(d, e)` with `d ∈ [1, Y]`,
`X < d` and `e ∣ d` agrees with summing `F d' e` over pairs `(e, d')` with `e ∈ [1, Y]`,
`d' ∈ [1, Y / e]` and `X < e * d'`.  The change of variables is `(d, e) ↦ (e, d / e)`, whose
inverse on the relevant set is `(e, d') ↦ (e * d', e)`. -/
theorem S15EG_sum_divisors_Icc_filter (X Y : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ d ∈ (Finset.Icc 1 Y).filter (fun d => X < d), ∑ e ∈ d.divisors, F (d / e) e)
      = ∑ e ∈ Finset.Icc 1 Y,
          ∑ d' ∈ (Finset.Icc 1 (Y / e)).filter (fun d' => X < e * d'), F d' e := by
  classical
  set S : Finset ℕ := (Finset.Icc 1 Y).filter (fun d => X < d) with hS
  set T : Finset ℕ := Finset.Icc 1 Y with hT
  set A : Finset (Σ _ : ℕ, ℕ) := S.sigma (fun d => d.divisors) with hA
  set B : Finset (Σ _ : ℕ, ℕ) :=
    T.sigma (fun e => (Finset.Icc 1 (Y / e)).filter (fun d' => X < e * d')) with hB
  have hL : (∑ d ∈ S, ∑ e ∈ d.divisors, F (d / e) e) = ∑ x ∈ A, F (x.1 / x.2) x.2 := by
    rw [hA]
    exact Finset.sum_sigma' S (fun d => d.divisors) (fun d e => F (d / e) e)
  have hR : (∑ e ∈ T, ∑ d' ∈ (Finset.Icc 1 (Y / e)).filter (fun d' => X < e * d'), F d' e)
      = ∑ x ∈ B, F x.2 x.1 := by
    rw [hB]
    exact Finset.sum_sigma' T
      (fun e => (Finset.Icc 1 (Y / e)).filter (fun d' => X < e * d'))
      (fun e d' => F d' e)
  rw [hL, hR]
  refine Finset.sum_nbij' (fun x => (⟨x.2, x.1 / x.2⟩ : Σ _ : ℕ, ℕ))
      (fun y => (⟨y.1 * y.2, y.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_ ?_
  · -- forward map lands in `B`
    intro a ha
    rw [hB, Finset.mem_sigma]
    rw [hA, Finset.mem_sigma] at ha
    obtain ⟨haS, hadiv⟩ := ha
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at haS
    obtain ⟨⟨h1a, hYa⟩, hXa⟩ := haS
    have hdvd : a.2 ∣ a.1 := Nat.dvd_of_mem_divisors hadiv
    have hane : a.1 ≠ 0 := (Nat.mem_divisors.mp hadiv).2
    have hpos : 0 < a.2 := Nat.pos_of_mem_divisors hadiv
    have hle : a.2 ≤ a.1 := Nat.le_of_dvd (by omega) hdvd
    refine ⟨?_, ?_⟩
    · rw [hT, Finset.mem_Icc]
      exact ⟨hpos, le_trans hle hYa⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [Nat.le_div_iff_mul_le hpos]
        simpa using hle
      · exact Nat.div_le_div_right hYa
      · rw [Nat.mul_div_cancel' hdvd]
        exact hXa
  · -- backward map lands in `A`
    intro b hb
    rw [hA, Finset.mem_sigma]
    rw [hB, Finset.mem_sigma] at hb
    obtain ⟨hbT, hbfilt⟩ := hb
    rw [hT, Finset.mem_Icc] at hbT
    obtain ⟨h1b, hYb⟩ := hbT
    rw [Finset.mem_filter, Finset.mem_Icc] at hbfilt
    obtain ⟨⟨h1b', hYb'⟩, hXb⟩ := hbfilt
    have hbpos : 0 < b.1 := by omega
    refine ⟨?_, ?_⟩
    · rw [hS, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, hXb⟩
      · have hmul := Nat.mul_le_mul h1b h1b'
        simpa using hmul
      · have h := (Nat.le_div_iff_mul_le hbpos).mp hYb'
        rwa [Nat.mul_comm] at h
    · rw [Nat.mem_divisors]
      exact ⟨Nat.dvd_mul_right b.1 b.2, by positivity⟩
  · -- left inverse
    intro a ha
    obtain ⟨d, e⟩ := a
    rw [hA, Finset.mem_sigma] at ha
    have hdvd : e ∣ d := Nat.dvd_of_mem_divisors ha.2
    simp only [Nat.mul_div_cancel' hdvd]
  · -- right inverse
    intro b hb
    obtain ⟨e, d'⟩ := b
    rw [hB, Finset.mem_sigma] at hb
    rw [hT, Finset.mem_Icc] at hb
    have hpos : 0 < e := hb.1.1
    simp only [Nat.mul_div_right d' hpos]
  · -- the summands agree
    intro a ha
    rfl

end Work.FIArea4
