import Mathlib
import Submission.Work.FIArea7.UniCut6
import Submission.Work.FIArea7.WBcutTools
import Submission.Work.FIArea7.Wcut_reflection
import Submission.Work.FIArea7.totient_div_eq_sum_moebius

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The uniform inner totient expansion (*FI* §17)

The uniform cut `|Δ| ≤ 4dX` (no condition on `d`) reflected by `d ↦ e = M/(4d)` produces the
*uniform* reflected range `e ≤ X` (as opposed to the pair-dependent range `e < X ∧ 4eX < M` of
the large-moduli cut).  Expanding `φ(m)/m = Σ_{b∣m} μ(b)/b` and swapping the two index sets then
gives the double sum `Work.FIArea7.WUniInner` with the congruence condition `4be ∣ M`. -/

/-- Divisibility test: for `e > 0`, the single condition `4be ∣ M` on the product is equivalent to
the conjunction of `4e ∣ M` and `b ∣ M/(4e)`. -/
private lemma dvd_four_mul_iff_aux {M b e : ℕ} (he : 0 < e) :
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

/-- Exchange of summation order for the divisor expansion `φ(m)/m = Σ_{b∣m} μ(b)/b`. -/
private lemma sum_divisors_mul_swap {B E : Finset ℕ} (m : ℕ → ℕ) (F S : ℕ → ℝ)
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

/-- The reflection `d ↦ M/(4d)` sends the uniform cut `{4d ∣ M, M ≤ 4dX}` to the small
complementary divisors `{4e ∣ M, e ≤ X}`. -/
private lemma WUni_reflect_mem {M X d : ℕ} (hM : 0 < M)
    (hd : d ∈ (Finset.Icc 1 (M / 4 + 1)).filter (fun d => 4 * d ∣ M ∧ M ≤ 4 * d * X)) :
    M / (4 * d) ∈ (Finset.Icc 1 (M / 4 + 1)).filter (fun e => 4 * e ∣ M ∧ e ≤ X) := by
  simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
  obtain ⟨⟨hd1, _⟩, hdiv, hMX⟩ := hd
  have h1 : M / (4 * d) * (4 * d) = M := Nat.div_mul_cancel hdiv
  have hMeq : M = 4 * (M / (4 * d)) * d := by nth_rewrite 1 [← h1]; ring
  have he0 : 0 < M / (4 * d) := by
    rcases Nat.eq_zero_or_pos (M / (4 * d)) with h | h
    · rw [h, zero_mul] at h1; omega
    · exact h
  have h4dpos : 0 < 4 * d := by omega
  refine ⟨⟨by omega, ?_⟩, ?_, ?_⟩
  · have hmul : M / (4 * d) * 4 ≤ M := by
      calc M / (4 * d) * 4 = 4 * (M / (4 * d)) := by ring
        _ ≤ 4 * (M / (4 * d)) * d := Nat.le_mul_of_pos_right _ (by omega : 0 < d)
        _ = M := hMeq.symm
    have hle := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr hmul
    omega
  · exact ⟨d, hMeq⟩
  · have hMX' : 4 * d * (M / (4 * d)) ≤ 4 * d * X := by
      calc 4 * d * (M / (4 * d)) = 4 * (M / (4 * d)) * d := by ring
        _ = M := hMeq.symm
        _ ≤ 4 * d * X := hMX
    exact Nat.le_of_mul_le_mul_left hMX' h4dpos

/-- The inverse direction: the reflection sends the small complementary divisors `{4e ∣ M, e ≤ X}`
back to the uniform-cut divisors `{4d ∣ M, M ≤ 4dX}`. -/
private lemma WUni_reflect_mem' {M X e : ℕ} (hM : 0 < M)
    (he : e ∈ (Finset.Icc 1 (M / 4 + 1)).filter (fun e => 4 * e ∣ M ∧ e ≤ X)) :
    M / (4 * e) ∈ (Finset.Icc 1 (M / 4 + 1)).filter (fun d => 4 * d ∣ M ∧ M ≤ 4 * d * X) := by
  simp only [Finset.mem_filter, Finset.mem_Icc] at he ⊢
  obtain ⟨⟨he1, _⟩, hdiv, heX⟩ := he
  have h1 : M / (4 * e) * (4 * e) = M := Nat.div_mul_cancel hdiv
  have hMeq : M = 4 * (M / (4 * e)) * e := by nth_rewrite 1 [← h1]; ring
  have hd0 : 0 < M / (4 * e) := by
    rcases Nat.eq_zero_or_pos (M / (4 * e)) with h | h
    · rw [h, zero_mul] at h1; omega
    · exact h
  refine ⟨⟨by omega, ?_⟩, ?_, ?_⟩
  · have hmul : M / (4 * e) * 4 ≤ M := by
      calc M / (4 * e) * 4 = 4 * (M / (4 * e)) := by ring
        _ ≤ 4 * (M / (4 * e)) * e := Nat.le_mul_of_pos_right _ (by omega : 0 < e)
        _ = M := hMeq.symm
    have hle := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr hmul
    omega
  · exact ⟨e, hMeq⟩
  · calc M = 4 * (M / (4 * e)) * e := hMeq
      _ ≤ 4 * (M / (4 * e)) * X := Nat.mul_le_mul_left _ heX

theorem WUni_inner_totient_expansion {M X : ℕ} (hM : 0 < M) (sym : ℕ → ℤ) (L : ℝ) :
    (∑ d ∈ (Finset.Icc 1 (M / 4 + 1)).filter (fun d => 4 * d ∣ M),
        ((Nat.totient d : ℝ) / (d : ℝ))
          * (if M ≤ 4 * d * X then (1 : ℝ) else 0) * (sym d : ℝ) * L)
      = Work.FIArea7.WUniInner X sym L M := by
  classical
  set B : Finset ℕ := Finset.Icc 1 (M / 4 + 1) with hBdef
  set E : Finset ℕ := B.filter (fun e => 4 * e ∣ M ∧ e ≤ X) with hEdef
  -- Step 1: turn the cut indicator into a filter on the index set.
  have hL : (∑ d ∈ B.filter (fun d => 4 * d ∣ M),
        ((Nat.totient d : ℝ) / (d : ℝ))
          * (if M ≤ 4 * d * X then (1 : ℝ) else 0) * (sym d : ℝ) * L)
      = ∑ d ∈ B.filter (fun d => 4 * d ∣ M ∧ M ≤ 4 * d * X),
          (Nat.totient d : ℝ) / (d : ℝ) * (sym d : ℝ) * L := by
    calc
      _ = ∑ d ∈ B.filter (fun d => 4 * d ∣ M),
            (if M ≤ 4 * d * X then
              (Nat.totient d : ℝ) / (d : ℝ) * (sym d : ℝ) * L else 0) :=
          Finset.sum_congr rfl (fun d _ => by
            by_cases hc : M ≤ 4 * d * X
            · rw [if_pos hc, if_pos hc]; ring
            · rw [if_neg hc, if_neg hc]; ring)
      _ = ∑ d ∈ B.filter (fun d => 4 * d ∣ M ∧ M ≤ 4 * d * X),
            (Nat.totient d : ℝ) / (d : ℝ) * (sym d : ℝ) * L := by
          rw [← Finset.sum_filter, Finset.filter_filter]
  -- Step 2: reflection `d ↦ M/(4d)` of the uniform cut.
  have hreflect : (∑ d ∈ B.filter (fun d => 4 * d ∣ M ∧ M ≤ 4 * d * X),
          (Nat.totient d : ℝ) / (d : ℝ) * (sym d : ℝ) * L)
      = ∑ e ∈ E, (Nat.totient (M / (4 * e)) : ℝ) / ((M / (4 * e) : ℕ) : ℝ)
          * (sym (M / (4 * e)) : ℝ) * L := by
    rw [hEdef]
    refine Finset.sum_bij' (fun d _ => M / (4 * d)) (fun e _ => M / (4 * e))
      (fun d hd => by rw [hBdef] at hd ⊢; exact WUni_reflect_mem hM hd)
      (fun e he => by rw [hBdef] at he ⊢; exact WUni_reflect_mem' hM he) ?_ ?_ ?_
    · intro a ha
      exact Wcut_reflect_invol hM
        (by rw [hBdef] at ha; exact (Finset.mem_filter.mp ha).2.1)
    · intro a ha
      exact Wcut_reflect_invol hM
        (by rw [hBdef] at ha; exact (Finset.mem_filter.mp ha).2.1)
    · intro a ha
      rw [Wcut_reflect_invol hM
        (by rw [hBdef] at ha; exact (Finset.mem_filter.mp ha).2.1)]
  -- Step 3: the reflected moduli are positive.
  have hme_pos : ∀ e ∈ E, 0 < M / (4 * e) := by
    intro e he
    rw [hEdef, Finset.mem_filter] at he
    obtain ⟨heB, h4e, _⟩ := he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp (by rw [← hBdef]; exact heB)).1
    have h4epos : 0 < 4 * e := by omega
    exact Nat.div_pos (Nat.le_of_dvd hM h4e) h4epos
  -- Step 4: the divisors of `M/(4e)` are exactly the relevant `b ≤ M/4+1`.
  have hdiv : ∀ e ∈ E, (M / (4 * e)).divisors = B.filter (fun b => b ∣ M / (4 * e)) := by
    intro e he
    rw [hEdef, Finset.mem_filter] at he
    obtain ⟨heB, h4e, heX⟩ := he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp (by rw [← hBdef]; exact heB)).1
    have h4epos : 0 < 4 * e := by omega
    have hmpos : 0 < M / (4 * e) := Nat.div_pos (Nat.le_of_dvd hM h4e) h4epos
    ext b
    rw [Nat.mem_divisors, Finset.mem_filter, hBdef, Finset.mem_Icc]
    constructor
    · rintro ⟨hbd, _⟩
      have hb1 : 1 ≤ b := Nat.pos_of_dvd_of_pos hbd hmpos
      have hble : b ≤ M / (4 * e) := Nat.le_of_dvd hmpos hbd
      have hle : M / (4 * e) ≤ M / 4 :=
        Nat.div_le_div_left (by omega : 4 ≤ 4 * e) (by norm_num)
      exact ⟨⟨hb1, by omega⟩, hbd⟩
    · rintro ⟨⟨hb1, _⟩, hbd⟩
      exact ⟨hbd, hmpos.ne'⟩
  -- Step 5: exchange the two summation orders.
  have hswap : (∑ e ∈ E, (∑ b ∈ (M / (4 * e)).divisors,
          (ArithmeticFunction.moebius b : ℝ) / (b : ℝ))
          * ((sym (M / (4 * e)) : ℝ) * L))
      = ∑ b ∈ B, ∑ e ∈ E.filter (fun e => b ∣ M / (4 * e)),
          (ArithmeticFunction.moebius b : ℝ) / (b : ℝ)
            * ((sym (M / (4 * e)) : ℝ) * L) :=
    sum_divisors_mul_swap (fun e => M / (4 * e))
      (fun b => (ArithmeticFunction.moebius b : ℝ) / (b : ℝ))
      (fun e => (sym (M / (4 * e)) : ℝ) * L) hdiv
  -- Step 6: `b ∣ M/(4e)` with `4e ∣ M` is `4be ∣ M`.
  have hEb : ∀ b ∈ B, B.filter (fun e => 4 * b * e ∣ M ∧ e ≤ X)
      = E.filter (fun e => b ∣ M / (4 * e)) := by
    intro b hb
    rw [hEdef]
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨heB, h4be, heX⟩
      have hepos : 0 < e := by
        have : e ∈ Finset.Icc 1 (M / 4 + 1) := by rw [← hBdef]; exact heB
        exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp this).1
      have hiff := (dvd_four_mul_iff_aux (M := M) (b := b) (e := e) hepos).mp h4be
      exact ⟨⟨heB, hiff.1, heX⟩, hiff.2⟩
    · rintro ⟨⟨heB, h4e, heX⟩, hbme⟩
      have hepos : 0 < e := by
        have : e ∈ Finset.Icc 1 (M / 4 + 1) := by rw [← hBdef]; exact heB
        exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp this).1
      exact ⟨heB, (dvd_four_mul_iff_aux (M := M) (b := b) (e := e) hepos).mpr
        ⟨h4e, hbme⟩, heX⟩
  have hT1 : (∑ d ∈ B.filter (fun d => 4 * d ∣ M ∧ M ≤ 4 * d * X), (Nat.totient d : ℝ) / (d : ℝ) * (sym d : ℝ) * L)
      = ∑ e ∈ E, (Nat.totient (M / (4 * e)) : ℝ) / ((M / (4 * e) : ℕ) : ℝ) * (sym (M / (4 * e)) : ℝ) * L :=
    hreflect
  have hT2 : (∑ e ∈ E, (Nat.totient (M / (4 * e)) : ℝ) / ((M / (4 * e) : ℕ) : ℝ) * (sym (M / (4 * e)) : ℝ) * L)
      = ∑ e ∈ E, (∑ b ∈ (M / (4 * e)).divisors, (ArithmeticFunction.moebius b : ℝ) / (b : ℝ)) * ((sym (M / (4 * e)) : ℝ) * L) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [totient_div_eq_sum_moebius (hme_pos e he)]
    ring
  have hT4 : (∑ b ∈ B, ∑ e ∈ E.filter (fun e => b ∣ M / (4 * e)), (ArithmeticFunction.moebius b : ℝ) / (b : ℝ) * ((sym (M / (4 * e)) : ℝ) * L))
      = ∑ b ∈ B, ∑ e ∈ B.filter (fun e => 4 * b * e ∣ M ∧ e ≤ X), (ArithmeticFunction.moebius b : ℝ) / (b : ℝ) * ((sym (M / (4 * e)) : ℝ) * L) := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [← hEb b hb]
  have hT5 : (∑ b ∈ B, ∑ e ∈ B.filter (fun e => 4 * b * e ∣ M ∧ e ≤ X), (ArithmeticFunction.moebius b : ℝ) / (b : ℝ) * ((sym (M / (4 * e)) : ℝ) * L))
      = ∑ b ∈ B, ∑ e ∈ B.filter (fun e => 4 * b * e ∣ M ∧ e ≤ X), (ArithmeticFunction.moebius b : ℝ) / (b : ℝ) * (sym (M / (4 * e)) : ℝ) * L := by
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro e he
    ring
  have hT : (∑ d ∈ B.filter (fun d => 4 * d ∣ M ∧ M ≤ 4 * d * X), (Nat.totient d : ℝ) / (d : ℝ) * (sym d : ℝ) * L)
      = ∑ b ∈ B, ∑ e ∈ B.filter (fun e => 4 * b * e ∣ M ∧ e ≤ X), (ArithmeticFunction.moebius b : ℝ) / (b : ℝ) * (sym (M / (4 * e)) : ℝ) * L :=
    hT1.trans (hT2.trans (hswap.trans (hT4.trans hT5)))
  rw [hL, hT]
  rw [WUniInner, hBdef]

end

end Work.FIArea7
