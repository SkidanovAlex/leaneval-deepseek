import Mathlib
import Submission.Work.Analysis.InverseTheory.calc_of_decay

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.Analysis.InverseTheory

/-! ## The sharp Riemann-sum comparison

The sibling bound `riemann_shift` carries the constant `2 ^ 60`; the half-line approximation needs
the sharper `⟨t⟩ ^ (-10)` error with an absolute constant, so we redo the comparison here.  The
only analytic ingredient is the telescoping inequality `ε x^{-12} ≤ (x - ε)^{-11} - x^{-11}`
for `0 < ε < x`, which follows from `(x - ε)^{11} (x + ε) ≤ x^{12}` (i.e.
`(1-δ)^{11}(1+δ) ≤ 1` for `δ = ε/x ∈ (0,1)`). -/

lemma eps_mul_inv_pow_twelve_le_sub {x ε : ℝ} (hε : 0 < ε) (hεx : ε < x) :
    ε * x⁻¹ ^ 12 ≤ (x - ε)⁻¹ ^ 11 - x⁻¹ ^ 11 := by
  have hx : 0 < x := lt_trans hε hεx
  have hu : 0 < x - ε := sub_pos.mpr hεx
  have hkey : (x - ε) ^ 11 * (x + ε) ≤ x ^ 12 := by
    have hr0 : 0 ≤ (x - ε) / x := div_nonneg hu.le hx.le
    have hr1 : (x - ε) / x ≤ 1 := by rw [div_le_iff₀ hx]; linarith
    have hpow : ((x - ε) / x) ^ 11 ≤ (x - ε) / x := by
      simpa using pow_le_pow_of_le_one hr0 hr1 (show (1 : ℕ) ≤ 11 by norm_num)
    have hquad : ((x - ε) / x) * (2 - (x - ε) / x) ≤ 1 := by
      nlinarith [sq_nonneg (1 - (x - ε) / x)]
    have h2 : ((x - ε) / x) ^ 11 * (2 - (x - ε) / x) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right hpow (by linarith)) hquad
    have heq : ((x - ε) / x) ^ 11 * (2 - (x - ε) / x) * x ^ 12
        = (x - ε) ^ 11 * (x + ε) := by
      field_simp
      try ring
    calc (x - ε) ^ 11 * (x + ε)
        = ((x - ε) / x) ^ 11 * (2 - (x - ε) / x) * x ^ 12 := heq.symm
      _ ≤ 1 * x ^ 12 := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = x ^ 12 := one_mul _
  have hmul : (ε * (x ^ 12)⁻¹ + (x ^ 11)⁻¹) * (x ^ 12 * (x - ε) ^ 11)
      ≤ ((x - ε) ^ 11)⁻¹ * (x ^ 12 * (x - ε) ^ 11) := by
    have h1 : (x ^ 12)⁻¹ * (x ^ 12 * (x - ε) ^ 11) = (x - ε) ^ 11 := by
      field_simp
    have h2 : (x ^ 11)⁻¹ * (x ^ 12 * (x - ε) ^ 11) = x * (x - ε) ^ 11 := by
      field_simp
      try ring
    have h3 : ((x - ε) ^ 11)⁻¹ * (x ^ 12 * (x - ε) ^ 11) = x ^ 12 := by
      field_simp
    rw [add_mul, mul_assoc ε (x ^ 12)⁻¹ (x ^ 12 * (x - ε) ^ 11), h1, h2, h3]
    nlinarith [hkey]
  have hfin : ε * (x ^ 12)⁻¹ + (x ^ 11)⁻¹ ≤ ((x - ε) ^ 11)⁻¹ :=
    le_of_mul_le_mul_right hmul (by positivity)
  rw [inv_pow, inv_pow, inv_pow]
  linarith [hfin]

/-- **Sharp Riemann-sum comparison.** For `0 < ε ≤ 1` and `t ≥ 0`,
`ε ⟨t⟩^{-12} + ∑_{n ≥ 0} ε ⟨t + ε(n+1)⟩^{-12} ≤ 8 ⟨t⟩^{-10}`. -/
lemma riemann_tail_split {ε t : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    ε * jbDecay 12 t + ∑' n : ℕ, ε * jbDecay 12 (t + ε * (((n : ℤ) + 1 : ℤ) : ℝ))
      ≤ 8 * jbDecay 10 t := by
  set L : ℝ := jb t with hLdef
  have hL1 : 1 ≤ L := one_le_jb t
  have hL0 : 0 < L := jb_pos t
  have hLinv1 : L⁻¹ ≤ 1 := by rw [hLdef]; exact jb_inv_le_one t
  have h10 : jbDecay 10 t = L⁻¹ ^ 10 := by rw [jbDecay, ← hLdef]
  have h12 : jbDecay 12 t = L⁻¹ ^ 12 := by rw [jbDecay, ← hLdef]
  have hLmul : L * L⁻¹ ^ 12 = L⁻¹ ^ 11 := by
    calc L * L⁻¹ ^ 12 = L⁻¹ ^ 11 * (L * L⁻¹) := by ring
      _ = L⁻¹ ^ 11 := by rw [mul_inv_cancel₀ hL0.ne', mul_one]
  have hhead : ε * jbDecay 12 t ≤ jbDecay 10 t := by
    rw [h10, h12]
    calc ε * L⁻¹ ^ 12 ≤ 1 * L⁻¹ ^ 12 := mul_le_mul_of_nonneg_right hε1 (by positivity)
      _ = L⁻¹ ^ 12 := one_mul _
      _ ≤ L⁻¹ ^ 10 := pow_le_pow_of_le_one (by positivity) hLinv1 (show 10 ≤ 12 by norm_num)
  set K : ℕ := ⌈2 * L / ε⌉₊ with hKdef
  have hKge : 2 * L / ε ≤ (K : ℝ) := by rw [hKdef]; exact Nat.le_ceil _
  have hKlt : (K : ℝ) < 2 * L / ε + 1 := by
    rw [hKdef]; exact Nat.ceil_lt_add_one (by positivity)
  have hKet : ε * (K : ℝ) ≤ 3 * L := by
    have hdiv : ε * (2 * L / ε) = 2 * L := by field_simp
    have h2 : ε * (K : ℝ) < ε * (2 * L / ε + 1) := mul_lt_mul_of_pos_left hKlt hε0
    rw [mul_add, hdiv, mul_one] at h2
    nlinarith [h2, hε1, hL1]
  have hKεL : L ≤ ε * (K : ℝ) := by
    have h : ε * (2 * L / ε) ≤ ε * (K : ℝ) := mul_le_mul_of_nonneg_left hKge hε0.le
    rw [show ε * (2 * L / ε) = 2 * L by field_simp] at h
    linarith
  have hK1 : 1 ≤ K := by
    have h : (1 : ℝ) ≤ (K : ℝ) := by
      nlinarith [hKεL, hL1, hε1, Nat.cast_nonneg (α := ℝ) K]
    exact_mod_cast h
  have hterm : ∀ n : ℕ,
      ε * jbDecay 12 (t + ε * (((n : ℤ) + 1 : ℤ) : ℝ)) ≤ ε * L⁻¹ ^ 12 := by
    intro n
    have hu : t ≤ t + ε * (((n : ℤ) + 1 : ℤ) : ℝ) := by
      have h : (0 : ℝ) ≤ ε * (((n : ℤ) + 1 : ℤ) : ℝ) := by positivity
      linarith
    have hmono : L ≤ jb (t + ε * (((n : ℤ) + 1 : ℤ) : ℝ)) := by
      rw [hLdef]; exact jb_le_jb_of_nonneg ht hu
    refine mul_le_mul_of_nonneg_left ?_ hε0.le
    rw [jbDecay]
    refine pow_le_pow_left₀ (jb_inv_nonneg _) ?_ 12
    exact (inv_le_inv₀ (jb_pos _) hL0).mpr hmono
  have hfirst : ∑ n ∈ Finset.range K,
      ε * jbDecay 12 (t + ε * (((n : ℤ) + 1 : ℤ) : ℝ)) ≤ 3 * jbDecay 10 t := by
    have h1 : ∑ n ∈ Finset.range K, ε * jbDecay 12 (t + ε * (((n : ℤ) + 1 : ℤ) : ℝ))
        ≤ (K : ℝ) * (ε * L⁻¹ ^ 12) := by
      calc ∑ n ∈ Finset.range K, ε * jbDecay 12 (t + ε * (((n : ℤ) + 1 : ℤ) : ℝ))
          ≤ ∑ _n ∈ Finset.range K, ε * L⁻¹ ^ 12 := Finset.sum_le_sum (fun n _ => hterm n)
        _ = (K : ℝ) * (ε * L⁻¹ ^ 12) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc ∑ n ∈ Finset.range K, ε * jbDecay 12 (t + ε * (((n : ℤ) + 1 : ℤ) : ℝ))
        ≤ (K : ℝ) * (ε * L⁻¹ ^ 12) := h1
      _ = (ε * (K : ℝ)) * L⁻¹ ^ 12 := by ring
      _ ≤ (3 * L) * L⁻¹ ^ 12 := mul_le_mul_of_nonneg_right hKet (by positivity)
      _ = 3 * L⁻¹ ^ 11 := by rw [mul_assoc, hLmul]
      _ ≤ 3 * jbDecay 10 t := by
          rw [h10]
          have h2 : L⁻¹ ^ 11 ≤ L⁻¹ ^ 10 :=
            pow_le_pow_of_le_one (by positivity) hLinv1 (show 10 ≤ 11 by norm_num)
          have h3 : (0 : ℝ) ≤ L⁻¹ ^ 10 := by positivity
          linarith
  have hpartial : ∀ m : ℕ,
      ∑ n ∈ Finset.range m, ε * jbDecay 12 (t + ε * (((n : ℤ) + 1 : ℤ) : ℝ))
        ≤ 4 * jbDecay 10 t := by
    intro m
    rcases le_or_gt m K with hm | hm
    · have hsub : Finset.range m ⊆ Finset.range K := Finset.range_subset_range.mpr hm
      have hmono := Finset.sum_mono_set_of_nonneg
        (f := fun n : ℕ => ε * jbDecay 12 (t + ε * (((n : ℤ) + 1 : ℤ) : ℝ)))
        (fun n => mul_nonneg hε0.le (jbDecay_nonneg 12 _)) hsub
      have hM : (0 : ℝ) ≤ jbDecay 10 t := jbDecay_nonneg 10 t
      linarith [hmono, hfirst]
    · have hm' : m = K + (m - K) := by omega
      rw [hm', Finset.sum_range_add]
      have hB : ∑ i ∈ Finset.range (m - K),
          ε * jbDecay 12 (t + ε * ((((K + i : ℕ) : ℤ) + 1 : ℤ) : ℝ)) ≤ jbDecay 10 t := by
        have hpt : ∀ i : ℕ, ε * jbDecay 12 (t + ε * ((((K + i : ℕ) : ℤ) + 1 : ℤ) : ℝ))
            ≤ (t + ε * ((K + i : ℕ) : ℝ))⁻¹ ^ 11
              - (t + ε * ((K + (i + 1) : ℕ) : ℝ))⁻¹ ^ 11 := by
          intro i
          have harg : t + ε * ((((K + i : ℕ) : ℤ) + 1 : ℤ) : ℝ)
              = t + ε * ((K + (i + 1) : ℕ) : ℝ) := by push_cast; ring
          rw [harg]
          have hzi : (0 : ℝ) < t + ε * ((K + (i + 1) : ℕ) : ℝ) := by
            have h1 : (1 : ℝ) ≤ ((K + (i + 1) : ℕ) : ℝ) := by
              exact_mod_cast (show 1 ≤ K + (i + 1) by omega)
            have h2 := mul_le_mul_of_nonneg_left h1 hε0.le
            nlinarith [h2, hε0]
          have hlt : ε < t + ε * ((K + (i + 1) : ℕ) : ℝ) := by
            have h1 : (2 : ℝ) ≤ ((K + (i + 1) : ℕ) : ℝ) := by
              exact_mod_cast (show 2 ≤ K + (i + 1) by omega)
            have h2 := mul_le_mul_of_nonneg_left h1 hε0.le
            linarith [h2, ht]
          have hjb : jbDecay 12 (t + ε * ((K + (i + 1) : ℕ) : ℝ))
              ≤ (t + ε * ((K + (i + 1) : ℕ) : ℝ))⁻¹ ^ 12 := by
            rw [jbDecay]
            refine pow_le_pow_left₀ (jb_inv_nonneg _) ?_ 12
            exact (inv_le_inv₀ (jb_pos _) hzi).mpr ((le_abs_self _).trans (abs_le_jb _))
          calc ε * jbDecay 12 (t + ε * ((K + (i + 1) : ℕ) : ℝ))
              ≤ ε * (t + ε * ((K + (i + 1) : ℕ) : ℝ))⁻¹ ^ 12 :=
                mul_le_mul_of_nonneg_left hjb hε0.le
            _ ≤ (t + ε * ((K + i : ℕ) : ℝ))⁻¹ ^ 11
                  - (t + ε * ((K + (i + 1) : ℕ) : ℝ))⁻¹ ^ 11 := by
                have hsub : t + ε * ((K + (i + 1) : ℕ) : ℝ) - ε = t + ε * ((K + i : ℕ) : ℝ) := by
                  push_cast; ring
                rw [← hsub]
                exact eps_mul_inv_pow_twelve_le_sub hε0 hlt
        have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range (m - K)) => hpt i)
        have htel := Finset.sum_range_sub'
          (fun i : ℕ => (t + ε * ((K + i : ℕ) : ℝ))⁻¹ ^ 11) (m - K)
        rw [htel] at hsum
        rw [Nat.add_zero] at hsum
        have hb : (t + ε * ((K : ℕ) : ℝ))⁻¹ ^ 11 ≤ jbDecay 10 t := by
          rw [h10]
          have hz : L ≤ t + ε * ((K : ℕ) : ℝ) := by linarith [hKεL, ht]
          have h1 : (t + ε * ((K : ℕ) : ℝ))⁻¹ ≤ L⁻¹ :=
            (inv_le_inv₀ (by positivity) hL0).mpr hz
          have h2 : (t + ε * ((K : ℕ) : ℝ))⁻¹ ^ 11 ≤ L⁻¹ ^ 11 :=
            pow_le_pow_left₀ (by positivity) h1 11
          have h3 : L⁻¹ ^ 11 ≤ L⁻¹ ^ 10 :=
            pow_le_pow_of_le_one (by positivity) hLinv1 (show 10 ≤ 11 by norm_num)
          linarith
        have hlast : (0 : ℝ) ≤ (t + ε * ((K + (m - K) : ℕ) : ℝ))⁻¹ ^ 11 := by positivity
        linarith [hsum, hb, hlast]
      have hM : (0 : ℝ) ≤ jbDecay 10 t := jbDecay_nonneg 10 t
      linarith [hfirst, hB]
  have htail : ∑' n : ℕ, ε * jbDecay 12 (t + ε * (((n : ℤ) + 1 : ℤ) : ℝ))
      ≤ 4 * jbDecay 10 t := tsum_le_of_forall_range_sum_le hpartial
  have hM : (0 : ℝ) ≤ jbDecay 10 t := jbDecay_nonneg 10 t
  linarith [hhead, htail]

/-- Summability restated with the shift written as `t + ε j`. -/
lemma summable_eps_jbDecay_shift' {ε t : ℝ} (hε0 : 0 < ε) (ht : 0 ≤ t) :
    Summable (fun j : ℕ => ε * jbDecay 12 (t + ε * (j : ℝ))) := by
  have h := summable_eps_jbDecay_shift (ε := ε) hε0 (t / ε)
  refine h.congr (fun j => ?_)
  congr 2
  field_simp

/-- The weighted Riemann sum bound in the form needed below. -/
lemma sum_eps_jbDecay_le {ε t : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    (∑' j : ℕ, ε * jbDecay 12 (t + ε * (j : ℝ))) ≤ 8 * jbDecay 10 t := by
  have hg := summable_eps_jbDecay_shift' hε0 ht
  have key : (∑' j : ℕ, ε * jbDecay 12 (t + ε * (j : ℝ)))
      = ε * jbDecay 12 t + ∑' n : ℕ, ε * jbDecay 12 (t + ε * ((n : ℝ) + 1)) := by
    have hh := hg.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at hh
    simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, mul_zero, add_zero] at hh
    exact hh.symm
  have hcast : (∑' n : ℕ, ε * jbDecay 12 (t + ε * ((n : ℝ) + 1)))
      = ∑' n : ℕ, ε * jbDecay 12 (t + ε * (((n : ℤ) + 1 : ℤ) : ℝ)) := by
    refine tsum_congr fun n => ?_
    congr 2
    push_cast
    try ring
  rw [key, hcast]
  exact riemann_tail_split hε0 hε1 ht

/-- Sharp right-tail bound: for `x ≤ k` the one-sided sum of `calcS` is bounded by
`C · 2^20 · ⟨ε(k-x)⟩^{-10}` (the constant-`2^20` version of `norm_tsum_calcS_right`). -/
lemma norm_tsum_calcS_right_sharp {ψ : ℝ → ℂ} {C : ℝ} {ε : ℝ} {x : ℤ}
    (hdecay : ∀ t : ℝ, ‖ψ t‖ ≤ C * jbDecay 12 t) (hC0 : 0 ≤ C)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (k : ℤ) (hk : (x : ℝ) ≤ (k : ℝ)) :
    ‖∑' j : ℕ, calcS ψ ε x (k + (j : ℤ))‖
      ≤ C * (2 : ℝ) ^ 20 * jbDecay 10 (ε * ((k : ℝ) - (x : ℝ))) := by
  have ht : 0 ≤ ε * ((k : ℝ) - (x : ℝ)) := mul_nonneg hε0.le (sub_nonneg.mpr hk)
  have hmajor : Summable
      (fun j : ℕ => C * (ε * jbDecay 12 (ε * (((k : ℝ) - (x : ℝ)) + (j : ℝ))))) :=
    (summable_eps_jbDecay_shift hε0 ((k : ℝ) - (x : ℝ))).mul_left C
  have hbdd : ‖∑' j : ℕ, calcS ψ ε x (k + (j : ℤ))‖
      ≤ ∑' j : ℕ, C * (ε * jbDecay 12 (ε * (((k : ℝ) - (x : ℝ)) + (j : ℝ)))) := by
    refine tsum_of_norm_bounded hmajor.hasSum fun j => ?_
    refine (norm_calcS_le hdecay hε0 (k + (j : ℤ))).trans ?_
    have h2 : ε * ((x : ℝ) - (((k + (j : ℤ) : ℤ)) : ℝ))
        = -(ε * (((k : ℝ) - (x : ℝ)) + (j : ℝ))) := by push_cast; ring
    rw [h2, jbDecay_neg]
  calc ‖∑' j : ℕ, calcS ψ ε x (k + (j : ℤ))‖
      ≤ ∑' j : ℕ, C * (ε * jbDecay 12 (ε * (((k : ℝ) - (x : ℝ)) + (j : ℝ)))) := hbdd
    _ = C * ∑' j : ℕ, ε * jbDecay 12 (ε * (((k : ℝ) - (x : ℝ)) + (j : ℝ))) := by
        rw [tsum_mul_left]
    _ = C * ∑' j : ℕ, ε * jbDecay 12 (ε * ((k : ℝ) - (x : ℝ)) + ε * (j : ℝ)) := by
        congr 1
        refine tsum_congr fun j => ?_
        congr 2
        ring
    _ ≤ C * (8 * jbDecay 10 (ε * ((k : ℝ) - (x : ℝ)))) :=
        mul_le_mul_of_nonneg_left (sum_eps_jbDecay_le hε0 hε1 ht) hC0
    _ ≤ C * (2 : ℝ) ^ 20 * jbDecay 10 (ε * ((k : ℝ) - (x : ℝ))) := by
        have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ 20 := by norm_num
        have hnn := jbDecay_nonneg 10 (ε * ((k : ℝ) - (x : ℝ)))
        nlinarith [mul_le_mul_of_nonneg_right h8 hnn, hC0]

/-- Sharp left-tail bound: for `k ≤ x` the one-sided sum of `calcS` is bounded by
`C · 2^20 · ⟨ε(x-k)⟩^{-10}` (the constant-`2^20` version of `norm_tsum_calcS_left`). -/
lemma norm_tsum_calcS_left_sharp {ψ : ℝ → ℂ} {C : ℝ} {ε : ℝ} {x : ℤ}
    (hdecay : ∀ t : ℝ, ‖ψ t‖ ≤ C * jbDecay 12 t) (hC0 : 0 ≤ C)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (k : ℤ) (hk : (k : ℝ) ≤ (x : ℝ)) :
    ‖∑' j : ℕ, calcS ψ ε x (k - (j : ℤ))‖
      ≤ C * (2 : ℝ) ^ 20 * jbDecay 10 (ε * ((x : ℝ) - (k : ℝ))) := by
  have ht : 0 ≤ ε * ((x : ℝ) - (k : ℝ)) := mul_nonneg hε0.le (sub_nonneg.mpr hk)
  have hmajor : Summable
      (fun j : ℕ => C * (ε * jbDecay 12 (ε * (((x : ℝ) - (k : ℝ)) + (j : ℝ))))) :=
    (summable_eps_jbDecay_shift hε0 ((x : ℝ) - (k : ℝ))).mul_left C
  have hbdd : ‖∑' j : ℕ, calcS ψ ε x (k - (j : ℤ))‖
      ≤ ∑' j : ℕ, C * (ε * jbDecay 12 (ε * (((x : ℝ) - (k : ℝ)) + (j : ℝ)))) := by
    refine tsum_of_norm_bounded hmajor.hasSum fun j => ?_
    refine (norm_calcS_le hdecay hε0 (k - (j : ℤ))).trans ?_
    have h2 : ε * ((x : ℝ) - (((k - (j : ℤ) : ℤ)) : ℝ))
        = ε * (((x : ℝ) - (k : ℝ)) + (j : ℝ)) := by push_cast; ring
    rw [h2]
  calc ‖∑' j : ℕ, calcS ψ ε x (k - (j : ℤ))‖
      ≤ ∑' j : ℕ, C * (ε * jbDecay 12 (ε * (((x : ℝ) - (k : ℝ)) + (j : ℝ)))) := hbdd
    _ = C * ∑' j : ℕ, ε * jbDecay 12 (ε * (((x : ℝ) - (k : ℝ)) + (j : ℝ))) := by
        rw [tsum_mul_left]
    _ = C * ∑' j : ℕ, ε * jbDecay 12 (ε * ((x : ℝ) - (k : ℝ)) + ε * (j : ℝ)) := by
        congr 1
        refine tsum_congr fun j => ?_
        congr 2
        ring
    _ ≤ C * (8 * jbDecay 10 (ε * ((x : ℝ) - (k : ℝ)))) :=
        mul_le_mul_of_nonneg_left (sum_eps_jbDecay_le hε0 hε1 ht) hC0
    _ ≤ C * (2 : ℝ) ^ 20 * jbDecay 10 (ε * ((x : ℝ) - (k : ℝ))) := by
        have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ 20 := by norm_num
        have hnn := jbDecay_nonneg 10 (ε * ((x : ℝ) - (k : ℝ)))
        nlinarith [mul_le_mul_of_nonneg_right h8 hnn, hC0]

/-! ## Reindexing half-lines as `ℕ`-indexed sums -/

/-- A `ℤ`-sum of a function vanishing below `y₀` equals the `ℕ`-indexed sum along `y₀ + j`. -/
lemma tsum_eq_tsum_nat_of_vanishes_below {F : ℤ → ℂ} {y₀ : ℤ}
    (hvan : ∀ y : ℤ, y < y₀ → F y = 0)
    (hsum : Summable fun j : ℕ => F (y₀ + (j : ℤ))) :
    (∑' y : ℤ, F y) = ∑' j : ℕ, F (y₀ + (j : ℤ)) := by
  have hshift : (∑' y : ℤ, F (y₀ + y)) = ∑' y : ℤ, F y :=
    Equiv.tsum_eq (Equiv.addLeft y₀) F
  have h1 : Summable (fun j : ℕ => F (y₀ + ((j : ℤ) + 1))) :=
    ((summable_nat_add_iff (f := fun j : ℕ => F (y₀ + (j : ℤ))) 1).mpr hsum).congr
      (fun j => by rw [show ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 by push_cast; ring])
  have h2 : Summable (fun j : ℕ => F (y₀ + (-((j : ℤ) + 1)))) :=
    summable_zero.congr fun j => by
      have hlt : y₀ + (-((j : ℤ) + 1)) < y₀ := by
        have h2 := Int.natCast_nonneg j
        linarith
      rw [hvan _ hlt]
  have hsplit := tsum_of_add_one_of_neg_add_one (f := fun z : ℤ => F (y₀ + z)) h1 h2
  have hz0 : F (y₀ + (0 : ℤ)) = F y₀ := by norm_num
  have hz3 : (∑' j : ℕ, F (y₀ + (-((j : ℤ) + 1)))) = 0 :=
    (tsum_congr fun j => hvan _ (by
      have h2 := Int.natCast_nonneg j
      linarith)).trans tsum_zero
  have hnat : (∑' j : ℕ, F (y₀ + (j : ℤ))) = F y₀ + ∑' j : ℕ, F (y₀ + ((j : ℤ) + 1)) := by
    have hs := hsum.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at hs
    have h0 : F (y₀ + (((0 : ℕ)) : ℤ)) = F y₀ := by norm_num
    have hc : (∑' i : ℕ, F (y₀ + ((i + 1 : ℕ) : ℤ)))
        = ∑' j : ℕ, F (y₀ + ((j : ℤ) + 1)) := by
      refine tsum_congr fun i => ?_
      rw [show ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 by push_cast; ring]
    rw [h0, hc] at hs
    exact hs.symm
  rw [← hshift, hsplit, hz0, hz3, hnat]
  try ring

/-- A sum over the upper half-line `{y₀ ≤ y}` is the `ℕ`-indexed sum along `y₀ + j`. -/
lemma tsum_Ici_ite_eq_tsum_nat (G : ℤ → ℂ) (y₀ : ℤ)
    (hsum : Summable fun j : ℕ => G (y₀ + (j : ℤ))) :
    (∑' y : ℤ, (if y₀ ≤ y then G y else 0)) = ∑' j : ℕ, G (y₀ + (j : ℤ)) := by
  have hle : ∀ j : ℕ, y₀ ≤ y₀ + (j : ℤ) := fun j =>
    Int.le_add_of_nonneg_right (Int.natCast_nonneg j)
  have hvan : ∀ y : ℤ, y < y₀ → (fun y : ℤ => if y₀ ≤ y then G y else 0) y = 0 := by
    intro y hy
    change (if y₀ ≤ y then G y else 0) = 0
    rw [if_neg (by linarith)]
  have h := tsum_eq_tsum_nat_of_vanishes_below hvan
    (hsum.congr fun j => by rw [if_pos (hle j)])
  rw [h]
  exact tsum_congr fun j => by rw [if_pos (hle j)]

/-- A sum over the lower half-line `{y ≤ z₁}` is the `ℕ`-indexed sum along `z₁ - j`. -/
lemma tsum_Iic_ite_eq_tsum_nat (G : ℤ → ℂ) (z₁ : ℤ)
    (hsum : Summable fun j : ℕ => G (z₁ - (j : ℤ))) :
    (∑' y : ℤ, (if y ≤ z₁ then G y else 0)) = ∑' j : ℕ, G (z₁ - (j : ℤ)) := by
  have h1 : (∑' y : ℤ, (if y ≤ z₁ then G y else 0))
      = ∑' y : ℤ, (if -z₁ ≤ y then G (-y) else 0) := by
    rw [← Equiv.tsum_eq (Equiv.neg ℤ)]
    simp only [Equiv.neg_apply]
    refine tsum_congr fun c => ?_
    by_cases h : (-z₁ : ℤ) ≤ c
    · rw [if_pos (show -c ≤ z₁ by omega), if_pos h]
    · rw [if_neg (show ¬(-c ≤ z₁) by omega), if_neg h]
  have hG : Summable fun j : ℕ => (fun y : ℤ => G (-y)) (-z₁ + (j : ℤ)) :=
    hsum.congr fun j => by congr 1; ring
  have h2 : (∑' y : ℤ, (if -z₁ ≤ y then G (-y) else 0))
      = ∑' j : ℕ, G (z₁ - (j : ℤ)) := by
    rw [tsum_Ici_ite_eq_tsum_nat (fun y : ℤ => G (-y)) (-z₁) hG]
    refine tsum_congr fun j => ?_
    congr 1
    ring
  exact h1.trans h2

/-- Approximation of a half-line indicator: with `ψ` as in `poisson_approx`, for every real `a`,
`0 < ε ≤ 1` and `x ∈ ℤ`, the sum `∑_{y ≥ a} ε ψ(ε(x-y))` differs from the indicator of
`{x ≥ a}` by at most `2 ^ 40 C ^ 2 (ε^10 + ⟨ε(x-a)⟩^{-10})`.

Route: if `x < a` the sum is a pure tail and only `hdecay` is used; if `x ≥ a`, write
`∑_{y ≥ a} = ∑_{y ∈ ℤ} - ∑_{y < a}`, use the full-line Poisson approximation (this is
`poisson_approx`, error `2 ^ 30 C ^ 2 ε ^ 10`) for the full sum, and the Riemann-sum bound
(`riemann_shift`, `n = 11`, after the substitution `u = ε(x-y)`) for the tail.  These auxiliary
statements may be re-derived in-file if the sibling modules are not available. -/
theorem halfLine_approx (ψ : ℝ → ℂ) (hcont : Continuous ψ) (C : ℝ) (hC : 1 ≤ C)
    (hint : ∫ t, ψ t = 1)
    (hdecay : ∀ t : ℝ, ‖ψ t‖ ≤ C * jbDecay 12 t)
    (hFdecay : ∀ t : ℝ, ‖realFourier ψ t‖ ≤ C * jbDecay 12 t)
    (a : ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (x : ℤ) :
    ‖(∑' y : ℤ, (if a ≤ (y : ℝ) then (ε : ℂ) * ψ (ε * ((x : ℝ) - y)) else 0))
        - (if a ≤ (x : ℝ) then (1 : ℂ) else 0)‖
      ≤ (2 : ℝ) ^ 40 * C ^ 2 * (ε ^ 10 + jbDecay 10 (ε * ((x : ℝ) - a))) := by
  classical
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  set y₀ : ℤ := ⌈a⌉ with hy₀def
  have ha_y₀ : a ≤ (y₀ : ℝ) := by rw [hy₀def]; exact Int.le_ceil a
  have hy₀_lt : (y₀ : ℝ) < a + 1 := by rw [hy₀def]; exact Int.ceil_lt_add_one a
  have hy₁_lt_a : ((y₀ - 1 : ℤ) : ℝ) < a := by
    have h : ((y₀ - 1 : ℤ) : ℝ) = (y₀ : ℝ) - 1 := by push_cast; ring
    rw [h]; linarith
  have hthr : ∀ y : ℤ, (a ≤ (y : ℝ)) ↔ y₀ ≤ y := by
    intro y; rw [hy₀def]; exact (Int.ceil_le (z := y)).symm
  have hthr' : ∀ y : ℤ, ((y : ℝ) < a) ↔ y ≤ y₀ - 1 := by
    intro y
    constructor
    · intro h
      have h1 : (y : ℝ) < (y₀ : ℝ) := lt_of_lt_of_le h ha_y₀
      have h2 : y < y₀ := by exact_mod_cast h1
      omega
    · intro h
      have h2 : (y : ℝ) ≤ ((y₀ - 1 : ℤ) : ℝ) := by exact_mod_cast h
      linarith [hy₁_lt_a]
  have hSumR : (∑' y : ℤ, (if a ≤ (y : ℝ) then (ε : ℂ) * ψ (ε * ((x : ℝ) - y)) else 0))
      = ∑' j : ℕ, calcS ψ ε x (y₀ + (j : ℤ)) := by
    rw [show (∑' y : ℤ, (if a ≤ (y : ℝ) then (ε : ℂ) * ψ (ε * ((x : ℝ) - y)) else 0))
        = ∑' y : ℤ, (if y₀ ≤ y then calcS ψ ε x y else 0) from
      tsum_congr fun y => by
        simp only [hthr y, calcS]]
    exact tsum_Ici_ite_eq_tsum_nat (fun y => calcS ψ ε x y) y₀
      (summable_calcS_right (ψ := ψ) (C := C) (ε := ε) (x := x) hdecay hC0 hε0 y₀)
  have hSumL : (∑' y : ℤ, (if (y : ℝ) < a then (ε : ℂ) * ψ (ε * ((x : ℝ) - y)) else 0))
      = ∑' j : ℕ, calcS ψ ε x (y₀ - 1 - (j : ℤ)) := by
    rw [show (∑' y : ℤ, (if (y : ℝ) < a then (ε : ℂ) * ψ (ε * ((x : ℝ) - y)) else 0))
        = ∑' y : ℤ, (if y ≤ y₀ - 1 then calcS ψ ε x y else 0) from
      tsum_congr fun y => by
        simp only [hthr' y, calcS]]
    exact tsum_Iic_ite_eq_tsum_nat (fun y => calcS ψ ε x y) (y₀ - 1)
      (summable_calcS_left (ψ := ψ) (C := C) (ε := ε) (x := x) hdecay hC0 hε0 (y₀ - 1))
  rcases (lt_or_ge (x : ℝ) a).symm with hax | hxa
  · -- case `a ≤ x`: the indicator is `1`, split the full line
    have hkL : ((y₀ - 1 : ℤ) : ℝ) ≤ (x : ℝ) := by linarith [hy₁_lt_a]
    have hT := norm_tsum_calcS_left_sharp (ψ := ψ) (C := C) (ε := ε) (x := x)
      hdecay hC0 hε0 hε1 (y₀ - 1) hkL
    have hcmpL : jbDecay 10 (ε * ((x : ℝ) - ((y₀ - 1 : ℤ) : ℝ)))
        ≤ jbDecay 10 (ε * ((x : ℝ) - a)) := by
      refine jbDecay_le_of_abs_le ?_
      calc |ε * ((x : ℝ) - a)| = ε * |(x : ℝ) - a| := by rw [abs_mul, abs_of_pos hε0]
        _ ≤ ε * |(x : ℝ) - ((y₀ - 1 : ℤ) : ℝ)| := by
            refine mul_le_mul_of_nonneg_left ?_ hε0.le
            rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (x : ℝ) - a),
                abs_of_nonneg (by linarith [hy₁_lt_a] : (0 : ℝ) ≤ (x : ℝ) - ((y₀ - 1 : ℤ) : ℝ))]
            linarith [hy₁_lt_a]
        _ = |ε * ((x : ℝ) - ((y₀ - 1 : ℤ) : ℝ))| := by rw [abs_mul, abs_of_pos hε0]
    have hsplit := tsum_calcS_eq_right_add_left (ψ := ψ) (C := C) (ε := ε) (x := x)
      hdecay hC0 hε0 y₀
    have hfull : ‖(∑' y : ℤ, calcS ψ ε x y) - 1‖ ≤ (2 : ℝ) ^ 30 * C ^ 2 * ε ^ 10 := by
      rw [show (∑' y : ℤ, calcS ψ ε x y)
          = ∑' y : ℤ, (ε : ℂ) * ψ (ε * ((x : ℝ) - y)) from by simp only [calcS]]
      exact poisson_approx ψ hcont C hC hint hdecay hFdecay hε0 hε1 x
    rw [if_pos hax, hSumR]
    have halg : (∑' j : ℕ, calcS ψ ε x (y₀ + (j : ℤ))) - 1
        = ((∑' y : ℤ, calcS ψ ε x y) - 1) - ∑' j : ℕ, calcS ψ ε x (y₀ - 1 - (j : ℤ)) := by
      rw [hsplit]; ring
    calc ‖(∑' j : ℕ, calcS ψ ε x (y₀ + (j : ℤ))) - 1‖
        = ‖((∑' y : ℤ, calcS ψ ε x y) - 1)
            - ∑' j : ℕ, calcS ψ ε x (y₀ - 1 - (j : ℤ))‖ := by rw [halg]
      _ ≤ ‖(∑' y : ℤ, calcS ψ ε x y) - 1‖
            + ‖∑' j : ℕ, calcS ψ ε x (y₀ - 1 - (j : ℤ))‖ := norm_sub_le _ _
      _ ≤ (2 : ℝ) ^ 30 * C ^ 2 * ε ^ 10 + C * (2 : ℝ) ^ 20 * jbDecay 10 (ε * ((x : ℝ) - a)) :=
          add_le_add hfull (hT.trans (mul_le_mul_of_nonneg_left hcmpL (by positivity)))
      _ ≤ (2 : ℝ) ^ 40 * C ^ 2 * (ε ^ 10 + jbDecay 10 (ε * ((x : ℝ) - a))) := by
          have hD : (0 : ℝ) ≤ jbDecay 10 (ε * ((x : ℝ) - a)) := jbDecay_nonneg 10 _
          have he : (0 : ℝ) ≤ ε ^ 10 := by positivity
          have hC2 : (0 : ℝ) ≤ C ^ 2 := by positivity
          have h1 : (2 : ℝ) ^ 30 * C ^ 2 * ε ^ 10 ≤ (2 : ℝ) ^ 40 * C ^ 2 * ε ^ 10 := by
            refine mul_le_mul_of_nonneg_right ?_ he
            exact mul_le_mul_of_nonneg_right (by norm_num) hC2
          have h2 : C * (2 : ℝ) ^ 20 * jbDecay 10 (ε * ((x : ℝ) - a))
              ≤ (2 : ℝ) ^ 40 * C ^ 2 * jbDecay 10 (ε * ((x : ℝ) - a)) := by
            refine mul_le_mul_of_nonneg_right ?_ hD
            nlinarith [hC, sq_nonneg C]
          nlinarith [h1, h2, hD, he]
  · -- case `x < a`: the indicator is `0`
    rw [if_neg (not_le.mpr hxa), sub_zero, hSumR]
    have hkR : (x : ℝ) ≤ (y₀ : ℝ) := le_trans hxa.le ha_y₀
    have hS := norm_tsum_calcS_right_sharp (ψ := ψ) (C := C) (ε := ε) (x := x)
      hdecay hC0 hε0 hε1 y₀ hkR
    have hcmpR : jbDecay 10 (ε * ((y₀ : ℝ) - (x : ℝ))) ≤ jbDecay 10 (ε * ((x : ℝ) - a)) := by
      refine jbDecay_le_of_abs_le ?_
      calc |ε * ((x : ℝ) - a)| = ε * |(x : ℝ) - a| := by rw [abs_mul, abs_of_pos hε0]
        _ ≤ ε * |(y₀ : ℝ) - (x : ℝ)| := by
            refine mul_le_mul_of_nonneg_left ?_ hε0.le
            rw [abs_of_nonpos (by linarith : (x : ℝ) - a ≤ 0),
                abs_of_nonneg (by linarith : (0 : ℝ) ≤ (y₀ : ℝ) - (x : ℝ))]
            linarith [ha_y₀]
        _ = |ε * ((y₀ : ℝ) - (x : ℝ))| := by rw [abs_mul, abs_of_pos hε0]
    calc ‖∑' j : ℕ, calcS ψ ε x (y₀ + (j : ℤ))‖
        ≤ C * (2 : ℝ) ^ 20 * jbDecay 10 (ε * ((y₀ : ℝ) - (x : ℝ))) := hS
      _ ≤ C * (2 : ℝ) ^ 20 * jbDecay 10 (ε * ((x : ℝ) - a)) :=
          mul_le_mul_of_nonneg_left hcmpR (by positivity)
      _ ≤ (2 : ℝ) ^ 40 * C ^ 2 * (ε ^ 10 + jbDecay 10 (ε * ((x : ℝ) - a))) := by
          have hD : (0 : ℝ) ≤ jbDecay 10 (ε * ((x : ℝ) - a)) := jbDecay_nonneg 10 _
          have he : (0 : ℝ) ≤ ε ^ 10 := by positivity
          have h2 : C * (2 : ℝ) ^ 20 * jbDecay 10 (ε * ((x : ℝ) - a))
              ≤ (2 : ℝ) ^ 40 * C ^ 2 * jbDecay 10 (ε * ((x : ℝ) - a)) := by
            refine mul_le_mul_of_nonneg_right ?_ hD
            nlinarith [hC, sq_nonneg C]
          nlinarith [h2, hD, he]

end Work.Analysis.InverseTheory
