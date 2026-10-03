import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FIArea7.Wcut_reflection
import Submission.Work.FIArea7.totient_div_eq_sum_moebius

/-!
# `Submission.Work.FIArea7.WBcutTools`

The tools for the §17 expansion of the **union** of the two cuts of (10.17) and of the boundary
case: `WcutMod + BcutMod`, whose cut is `X < d ∧ |Δ| ≤ 4dX`.

* `WBcut_reflection` — the reflection `d ↦ M/(4d)` of the union cut (turning it into
  `e ≤ X ∧ 4eX < M`, exactly `WBcutExpandedInner`'s `e`-condition);
* `WBcut_inner_totient_expansion` — the per-pair identity (17.1) for the union cut;
* `TcutMod_eq_sum_ofReal`, `TcutMod_add_cut`, `TcutMod_congr_cut` — the `TcutMod` book-keeping:
  `TcutMod` is the coercion of an `ℝ`-valued sum, and it is additive in its cut;
* `cutW_add_cutB` — the two indicator cuts add up to the union indicator.
-/

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The §17 reflection for the union cut `X < d ∧ |Δ| ≤ 4dX` -/

/-- Divisibility test: for `e > 0`, the single condition `4be ∣ M` on the product is equivalent to
the conjunction of `4e ∣ M` and `b ∣ M/(4e)`. -/
private lemma dvd_four_mul_iff_aux' {M b e : ℕ} (he : 0 < e) :
    (4 * b * e ∣ M) ↔ (4 * e ∣ M ∧ b ∣ M / (4 * e)) := by
  have h4e : 0 < 4 * e := by omega
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨⟨b * k, by rw [hk]; ring⟩, k, ?_⟩
    rw [hk, show 4 * b * e * k = 4 * e * (b * k) by ring, Nat.mul_div_right (b * k) h4e]
  · rintro ⟨⟨c, hc⟩, ⟨k, hk⟩⟩
    have hc2 : M / (4 * e) = c := by rw [hc, Nat.mul_div_right c h4e]
    rw [hc2] at hk
    exact ⟨k, by rw [hc, hk]; ring⟩

/-- Exchange of summation order for the divisor expansion `φ(m e)/m e = Σ_{b ∣ m e} μ(b)/b`:
provided the divisors of `m e` are exactly the `b ∈ B` with `b ∣ m e`, the sum over `e` of the
expanded inner sum equals the double sum over `b ∈ B` and the `e` with `b ∣ m e`. -/
private lemma sum_divisors_mul_swap' {B E : Finset ℕ} (m : ℕ → ℕ) (F S : ℕ → ℝ)
    (hdiv : ∀ e ∈ E, (m e).divisors = B.filter (fun b => b ∣ m e)) :
    (∑ e ∈ E, (∑ b ∈ (m e).divisors, F b) * S e)
      = ∑ b ∈ B, ∑ e ∈ E.filter (fun e => b ∣ m e), F b * S e := by
  have step : ∀ e ∈ E, (∑ b ∈ (m e).divisors, F b) * S e
      = ∑ b ∈ B, (if b ∣ m e then F b * S e else 0) := by
    intro e he
    rw [hdiv e he, Finset.sum_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro b hb
    by_cases h : b ∣ m e <;> simp [h]
  calc (∑ e ∈ E, (∑ b ∈ (m e).divisors, F b) * S e)
      = ∑ e ∈ E, ∑ b ∈ B, (if b ∣ m e then F b * S e else 0) :=
        Finset.sum_congr rfl step
    _ = ∑ b ∈ B, ∑ e ∈ E, (if b ∣ m e then F b * S e else 0) := Finset.sum_comm
    _ = ∑ b ∈ B, ∑ e ∈ E.filter (fun e => b ∣ m e), F b * S e := by
        apply Finset.sum_congr rfl; intro b hb
        rw [Finset.sum_filter]

/-- ***FI* §17: the reflection `d ↦ M/(4d)` of the **union** cut `X < d ∧ M ≤ 4dX`.**

On the divisors `d` of `M/4` with `d ≥ 1` the map `d ↦ M/(4d)` is an involution exchanging the
cut `X < d` with `4eX < M` and the cut `M ≤ 4dX` with `e ≤ X`; hence for `M ≥ 1` and any
`g : ℕ → ℝ`,

  `Σ_{d ∈ [1, M/4+1], 4d ∣ M, X < d, M ≤ 4dX} g d
     = Σ_{e ∈ [1, M/4+1], 4e ∣ M, e ≤ X, 4eX < M} g (M/(4e))`.

This is `Work.FIArea7.Wcut_reflection` (`M < 4dX`) combined with the boundary equality
`M = 4dX`, i.e. exactly the reflection of `WcutMod + BcutMod`. -/
theorem WBcut_reflection {M X : ℕ} (hM : 0 < M) (g : ℕ → ℝ) :
    ∑ d ∈ (Finset.Icc 1 (M / 4 + 1)).filter
        (fun d => 4 * d ∣ M ∧ X < d ∧ M ≤ 4 * d * X), g d
      = ∑ e ∈ (Finset.Icc 1 (M / 4 + 1)).filter
        (fun e => 4 * e ∣ M ∧ e ≤ X ∧ 4 * e * X < M), g (M / (4 * e)) := by
  refine Finset.sum_bij' (fun d _ => M / (4 * d)) (fun e _ => M / (4 * e))
    (fun d hd => ?_) (fun e he => ?_) ?_ ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
    obtain ⟨⟨hd1, _⟩, hdiv, hXd, hMX⟩ := hd
    have h1 : M / (4 * d) * (4 * d) = M := Nat.div_mul_cancel hdiv
    have hMeq : M = 4 * (M / (4 * d)) * d := by nth_rewrite 1 [← h1]; ring
    have he0 : 0 < M / (4 * d) := by
      rcases Nat.eq_zero_or_pos (M / (4 * d)) with h | h
      · rw [h, zero_mul] at h1; omega
      · exact h
    refine ⟨⟨by omega, ?_⟩, ⟨d, hMeq⟩, ?_, ?_⟩
    · have hmul : M / (4 * d) * 4 ≤ M := by
        calc M / (4 * d) * 4 = 4 * (M / (4 * d)) := by ring
          _ ≤ 4 * (M / (4 * d)) * d := Nat.le_mul_of_pos_right _ (by omega)
          _ = M := hMeq.symm
      have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr hmul
      omega
    · have hle : (4 * d) * (M / (4 * d)) ≤ (4 * d) * X := by
        rw [show (4 * d) * (M / (4 * d)) = 4 * (M / (4 * d)) * d by ring]
        rw [← hMeq]; exact hMX
      exact Nat.le_of_mul_le_mul_left hle (by omega)
    · calc 4 * (M / (4 * d)) * X < 4 * (M / (4 * d)) * d :=
            (Nat.mul_lt_mul_left (by omega : 0 < 4 * (M / (4 * d)))).mpr hXd
        _ = M := hMeq.symm
  · simp only [Finset.mem_filter, Finset.mem_Icc] at he ⊢
    obtain ⟨⟨he1, _⟩, hdiv, heX, h4eX⟩ := he
    have h1 : M / (4 * e) * (4 * e) = M := Nat.div_mul_cancel hdiv
    have hMeq : M = 4 * (M / (4 * e)) * e := by nth_rewrite 1 [← h1]; ring
    have hd0 : 0 < M / (4 * e) := by
      rcases Nat.eq_zero_or_pos (M / (4 * e)) with h | h
      · rw [h, zero_mul] at h1; omega
      · exact h
    have hpos : 0 < 4 * e := by omega
    refine ⟨⟨by omega, ?_⟩, ⟨e, hMeq⟩, ?_, ?_⟩
    · have hmul : M / (4 * e) * 4 ≤ M := by
        calc M / (4 * e) * 4 = 4 * (M / (4 * e)) := by ring
          _ ≤ 4 * (M / (4 * e)) * e := Nat.le_mul_of_pos_right _ (by omega)
          _ = M := hMeq.symm
      have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr hmul
      omega
    · have hM' : M = (4 * e) * (M / (4 * e)) := by rw [mul_comm]; exact h1.symm
      rw [hM'] at h4eX
      exact (Nat.mul_lt_mul_left hpos).mp h4eX
    · calc M = 4 * (M / (4 * e)) * e := hMeq
        _ ≤ 4 * (M / (4 * e)) * X := Nat.mul_le_mul_left _ heX
  · intro a ha
    exact Wcut_reflect_invol hM (Finset.mem_filter.mp ha).2.1
  · intro a ha
    exact Wcut_reflect_invol hM (Finset.mem_filter.mp ha).2.1
  · intro a ha
    rw [Wcut_reflect_invol hM (Finset.mem_filter.mp ha).2.1]

/-! ## 2. The per-pair Möbius expansion with the union cut (`e ≤ X`) -/

/-! ## 3. `TcutMod` tooling -/

/-- `Work.FITop3.TcutMod` writes its inner sum in a context of expected type `ℂ`, so the
elaborated summand is a `ℂ`-valued sum of coerced factors.  This lemma exhibits `TcutMod` as the
coercion of the corresponding `ℝ`-valued inner sum, which is the form in which the §17 identities
(`WBcut_inner_totient_expansion`) are stated. -/
theorem TcutMod_eq_sum_ofReal (Rz : ℤ) (cut : GaussianInt → GaussianInt → ℕ → ℝ)
    (β : GaussianInt → ℂ) :
    Work.FITop3.TcutMod Rz cut β
      = 2 * ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            β z1 * star (β z2)
              * ((∑ d ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
                    (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2),
                    ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                      * (jacobiSym ((star z1 * z2).re) d : ℝ) * Work.FITop3.logFac z1 z2 : ℝ) : ℂ)
           else 0) := by
  simp only [Work.FITop3.TcutMod]
  congr 1
  apply Finset.sum_congr rfl; intro z1 _
  apply Finset.sum_congr rfl; intro z2 _
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hg, if_true]
    congr 1
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl; intro d _
    push_cast; ring
  · simp only [hg, if_false]

/-- `Work.FITop3.TcutMod` is additive in its cut: the `d`-sum is linear in the cut with no
rearrangement, so that `WcutMod + BcutMod` is `TcutMod` with the sum of the two indicator cuts. -/
theorem TcutMod_add_cut (Rz : ℤ) (c1 c2 : GaussianInt → GaussianInt → ℕ → ℝ)
    (β : GaussianInt → ℂ) :
    Work.FITop3.TcutMod Rz c1 β + Work.FITop3.TcutMod Rz c2 β
      = Work.FITop3.TcutMod Rz (fun z1 z2 d => c1 z1 z2 d + c2 z1 z2 d) β := by
  rw [TcutMod_eq_sum_ofReal Rz c1 β, TcutMod_eq_sum_ofReal Rz c2 β,
    TcutMod_eq_sum_ofReal Rz (fun z1 z2 d => c1 z1 z2 d + c2 z1 z2 d) β]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro z1 _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro z2 _
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hg, if_true]
    rw [← mul_add, ← Complex.ofReal_add]
    congr 1
    rw [Complex.ofReal_inj, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro d _
    ring
  · simp only [hg, if_false]; ring

/-- `Work.FITop3.TcutMod` depends only on the values of the cut. -/
theorem TcutMod_congr_cut (Rz : ℤ) (c1 c2 : GaussianInt → GaussianInt → ℕ → ℝ)
    (β : GaussianInt → ℂ) (h : ∀ z1 z2 d, c1 z1 z2 d = c2 z1 z2 d) :
    Work.FITop3.TcutMod Rz c1 β = Work.FITop3.TcutMod Rz c2 β := by
  simp only [Work.FITop3.TcutMod]
  congr 1
  apply Finset.sum_congr rfl; intro z1 _
  apply Finset.sum_congr rfl; intro z2 _
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hg, if_true]
    congr 1
    apply Finset.sum_congr rfl; intro d _
    rw [h z1 z2 d]
  · simp only [hg, if_false]

/-! ## 4. The two indicator cuts add up to the union indicator -/

/-- `1_{4dX > M} + 1_{4dX = M} = 1_{M ≤ 4dX}` on the range `X < d`, and `0 = 0` off it. -/
theorem cutW_add_cutB (M X d : ℕ) :
    (if X < d ∧ 4 * d * X > M then (1 : ℝ) else 0)
      + (if X < d ∧ 4 * d * X = M then (1 : ℝ) else 0)
      = if X < d ∧ M ≤ 4 * d * X then (1 : ℝ) else 0 := by
  by_cases h1 : X < d
  · rcases lt_trichotomy (4 * d * X) M with h | h | h
    · rw [if_neg (by rintro ⟨_, hh⟩; omega), if_neg (by rintro ⟨_, hh⟩; omega),
        if_neg (by rintro ⟨_, hh⟩; omega)]
      norm_num
    · rw [if_neg (by rintro ⟨_, hh⟩; omega), if_pos ⟨h1, h⟩, if_pos ⟨h1, le_of_eq h.symm⟩]
      norm_num
    · rw [if_pos ⟨h1, h⟩, if_neg (by rintro ⟨_, hh⟩; omega), if_pos ⟨h1, le_of_lt h⟩]
      norm_num
  · rw [if_neg (by rintro ⟨hh, _⟩; exact h1 hh), if_neg (by rintro ⟨hh, _⟩; exact h1 hh),
      if_neg (by rintro ⟨hh, _⟩; exact h1 hh)]
    norm_num

end

end Work.FIArea7
