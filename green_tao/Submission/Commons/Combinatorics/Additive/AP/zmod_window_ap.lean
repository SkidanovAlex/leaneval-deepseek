import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.Data.ZMod.Basic

namespace Commons.Combinatorics.Additive.AP

/-- Core integer lemma.

Let `X : ℕ → ℤ` be a sequence whose first `k` values all lie in the window
`[ε N, 2 ε N]` with `4 ε < 1`, and suppose that `X` is "additively consistent
modulo `N`" in the sense that `N ∣ X (i+j) - X i - X j + X 0` whenever
`i + j < k`.  Then `X` is affine on `{0, …, k-1}`. -/
lemma int_ap_of_window {N k : ℕ} (hk : 2 ≤ k) (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε)
    (hε4 : 4 * ε < 1) (X : ℕ → ℤ)
    (hwin : ∀ i, i < k → ε * (N : ℝ) ≤ (X i : ℝ) ∧ (X i : ℝ) ≤ 2 * ε * (N : ℝ))
    (hcongr : ∀ i j, i + j < k → (N : ℤ) ∣ X (i + j) - X i - X j + X 0) :
    ∀ i, i < k → X i = X 0 + (i : ℤ) * (X 1 - X 0) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h2lt : 2 * ε * (N : ℝ) < (N : ℝ) := by
    have h4 : 4 * ε * (N : ℝ) < (N : ℝ) := by
      have h := mul_lt_mul_of_pos_right hε4 hNpos
      linarith
    nlinarith [hε, mul_pos (show (0 : ℝ) < 2 * ε by linarith) hNpos]
  have hsadd : ∀ i j, i + j < k → X (i + j) - X 0 = (X i - X 0) + (X j - X 0) := by
    intro i j hij
    have hi : i < k := by omega
    have hj : j < k := by omega
    have h0 : 0 < k := by omega
    have hdvd := hcongr i j hij
    have hb1 : |(X (i + j) : ℝ) - (X i : ℝ)| ≤ ε * (N : ℝ) := by
      rw [abs_le]
      exact ⟨by linarith [(hwin (i + j) hij).1, (hwin i hi).2],
             by linarith [(hwin (i + j) hij).2, (hwin i hi).1]⟩
    have hb2 : |(X 0 : ℝ) - (X j : ℝ)| ≤ ε * (N : ℝ) := by
      rw [abs_le]
      exact ⟨by linarith [(hwin 0 h0).1, (hwin j hj).2],
             by linarith [(hwin 0 h0).2, (hwin j hj).1]⟩
    have hreal : (((X (i + j) - X i - X j + X 0).natAbs : ℕ) : ℝ)
        = |(X (i + j) : ℝ) - (X i : ℝ) - (X j : ℝ) + (X 0 : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      push_cast
      ring
    have hltR : (((X (i + j) - X i - X j + X 0).natAbs : ℕ) : ℝ) < (N : ℝ) := by
      rw [hreal]
      have hsplit : (X (i + j) : ℝ) - (X i : ℝ) - (X j : ℝ) + (X 0 : ℝ)
          = ((X (i + j) : ℝ) - (X i : ℝ)) + ((X 0 : ℝ) - (X j : ℝ)) := by ring
      rw [hsplit]
      calc |((X (i + j) : ℝ) - (X i : ℝ)) + ((X 0 : ℝ) - (X j : ℝ))|
          ≤ |(X (i + j) : ℝ) - (X i : ℝ)| + |(X 0 : ℝ) - (X j : ℝ)| := abs_add_le _ _
        _ ≤ ε * (N : ℝ) + ε * (N : ℝ) := add_le_add hb1 hb2
        _ < (N : ℝ) := by linarith
    have hm : (X (i + j) - X i - X j + X 0).natAbs < (N : ℤ).natAbs := by
      rw [Int.natAbs_natCast]
      exact_mod_cast hltR
    have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hm
    linarith
  have hS : ∀ i, i < k → X i - X 0 = (i : ℤ) * (X 1 - X 0) := by
    intro i
    induction i with
    | zero => intro _; ring
    | succ n ih =>
        intro hn
        have hn' : n < k := by omega
        have h1 := hsadd n 1 hn
        rw [h1, ih hn']
        push_cast
        ring
  intro i hi
  have h := hS i hi
  linarith

theorem zmod_window_ap {N k : ℕ} [NeZero N] (hk : 2 ≤ k) {ε : ℝ} (hε : 0 < ε)
    (hε4 : 4 * ε < 1) (v r : ZMod N) (hr : r ≠ 0)
    (hwin : ∀ i : ℕ, i < k → ε * (N : ℝ) ≤ (((v + (i : ZMod N) * r).val : ℕ) : ℝ) ∧
      (((v + (i : ZMod N) * r).val : ℕ) : ℝ) ≤ 2 * ε * (N : ℝ)) :
    ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k →
      ∃ i : ℕ, i < k ∧ ((v + (i : ZMod N) * r).val : ℕ) = a + b * j := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  let Xn : ℕ → ℕ := fun i => (v + (i : ZMod N) * r).val
  let X : ℕ → ℤ := fun i => (Xn i : ℤ)
  have hcast : ∀ l : ℕ, ((X l : ℤ) : ZMod N) = v + (l : ZMod N) * r := by
    intro l
    simp only [X, Xn, Int.cast_natCast]
    exact ZMod.natCast_zmod_val (v + (l : ZMod N) * r)
  have hwinX : ∀ i, i < k → ε * (N : ℝ) ≤ (X i : ℝ) ∧ (X i : ℝ) ≤ 2 * ε * (N : ℝ) := by
    intro i hi
    have h := hwin i hi
    simpa only [X, Xn, Int.cast_natCast] using h
  have hcongrX : ∀ i j, i + j < k → (N : ℤ) ∣ X (i + j) - X i - X j + X 0 := by
    intro i j hij
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
    have hred : ((X (i + j) - X i - X j + X 0 : ℤ) : ZMod N)
        = (v + ((i + j : ℕ) : ZMod N) * r) - (v + (i : ZMod N) * r)
          - (v + (j : ZMod N) * r) + (v + ((0 : ℕ) : ZMod N) * r) := by
      rw [Int.cast_add, Int.cast_sub, Int.cast_sub, hcast, hcast, hcast, hcast]
    rw [hred]
    push_cast
    ring
  have hAP := int_ap_of_window hk hN hε hε4 X hwinX hcongrX
  let d : ℤ := (Xn 1 : ℤ) - (Xn 0 : ℤ)
  have hAPn : ∀ i, i < k → (Xn i : ℤ) = (Xn 0 : ℤ) + (i : ℤ) * d := by
    intro i hi
    have h := hAP i hi
    simpa only [X, d] using h
  have hdne : d ≠ 0 := by
    intro hd0
    have h10 : (Xn 1 : ℤ) = (Xn 0 : ℤ) := by
      have : (Xn 1 : ℤ) - (Xn 0 : ℤ) = 0 := hd0
      linarith
    have hX : ((X 1 : ℤ) : ZMod N) = ((X 0 : ℤ) : ZMod N) := by
      simp only [X]
      rw [h10]
    rw [hcast 1, hcast 0] at hX
    have h1 := add_left_cancel hX
    exact hr (by simpa using h1)
  by_cases hdpos : 0 < d
  · refine ⟨Xn 0, d.toNat, ?_, ?_⟩
    · have hd1 : (1 : ℤ) ≤ d := by omega
      have h2 : (1 : ℤ) ≤ (d.toNat : ℤ) := by
        rw [Int.toNat_of_nonneg (le_of_lt hdpos)]
        exact hd1
      exact_mod_cast h2
    · intro j hj
      refine ⟨j, hj, ?_⟩
      have hb : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (le_of_lt hdpos)
      have hkey : (Xn j : ℤ) = (Xn 0 : ℤ) + (j : ℤ) * d := hAPn j hj
      have htarget : (Xn j : ℤ) = ((Xn 0 + d.toNat * j : ℕ) : ℤ) := by
        rw [hkey]; push_cast; rw [hb]; ring
      exact Int.ofNat_inj.mp htarget
  · simp only [not_lt] at hdpos
    refine ⟨Xn (k - 1), (-d).toNat, ?_, ?_⟩
    · have hd1 : (1 : ℤ) ≤ -d := by omega
      have h2 : (1 : ℤ) ≤ ((-d).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -d)]
        exact hd1
      exact_mod_cast h2
    · intro j hj
      refine ⟨k - 1 - j, by omega, ?_⟩
      have hb : ((-d).toNat : ℤ) = -d := Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -d)
      have hcast_sub : ((k - 1 - j : ℕ) : ℤ) = ((k - 1 : ℕ) : ℤ) - (j : ℤ) := by
        have h : k - 1 - j + j = k - 1 := by omega
        have h2 : (((k - 1 - j + j : ℕ)) : ℤ) = ((k - 1 : ℕ) : ℤ) := by rw [h]
        push_cast at h2
        linarith
      have h1 := hAPn (k - 1 - j) (by omega)
      have h2 := hAPn (k - 1) (by omega)
      have hkey : (Xn (k - 1 - j) : ℤ) = (Xn (k - 1) : ℤ) + (j : ℤ) * (-d) := by
        rw [h1, h2, hcast_sub]; ring
      have htarget : (Xn (k - 1 - j) : ℤ) = ((Xn (k - 1) + (-d).toNat * j : ℕ) : ℤ) := by
        rw [hkey]; push_cast; rw [hb]; ring
      exact Int.ofNat_inj.mp htarget

end Commons.Combinatorics.Additive.AP