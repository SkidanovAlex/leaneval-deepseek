import Mathlib

namespace Work.NN.Core

open Filter
open scoped Topology

/-- Real-variable endgame: if `(1-ε) * r ≤ (1+ε) * s` holds for every `ε ∈ (0,1)` and
`r, s ≥ 0`, then `r ≤ s`. -/
private lemma real_le_of_forall_mul {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → (1 - ε) * r ≤ (1 + ε) * s) : r ≤ s := by
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ r + s by linarith) with hsum | hsum
  · have hr0 : r = 0 := by linarith
    have hs0 : s = 0 := by linarith
    linarith
  · have ht : (r - s) / (r + s) ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro δ hδ
      have hε0 : 0 < min (1/2 : ℝ) δ := lt_min (by norm_num) hδ
      have hε1 : min (1/2 : ℝ) δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
      have h1 := h _ hε0 hε1
      have h2 : r - s ≤ (min (1/2 : ℝ) δ) * (r + s) := by nlinarith [h1]
      have h3 : (min (1/2 : ℝ) δ) * (r + s) ≤ δ * (r + s) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
      have h4 : r - s ≤ δ * (r + s) := le_trans h2 h3
      rw [div_le_iff₀ hsum]
      linarith
    rw [div_le_iff₀ hsum] at ht
    linarith

/-- ENNReal endgame: if `ofReal (1-ε) * A ≤ ofReal (1+ε) * B` for every `ε ∈ (0,1)`,
then `A ≤ B`. -/
private lemma ENNReal_le_of_forall {A B : ENNReal}
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → ENNReal.ofReal (1 - ε) * A ≤ ENNReal.ofReal (1 + ε) * B) :
    A ≤ B := by
  by_cases hA : A = ⊤
  · have h12 := h (1/2) (by norm_num) (by norm_num)
    rw [hA] at h12
    have hne : ENNReal.ofReal (1 - 1/2 : ℝ) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)
    rw [ENNReal.mul_top hne] at h12
    have htop : ENNReal.ofReal (1 + 1/2 : ℝ) * B = ⊤ := top_le_iff.mp h12
    have hBtop : B = ⊤ := by
      rcases ENNReal.mul_eq_top.mp htop with ⟨-, hB⟩ | ⟨h', -⟩
      · exact hB
      · exact absurd h' ENNReal.ofReal_lt_top.ne
    rw [hBtop]; exact le_top
  · by_cases hB : B = ⊤
    · rw [hB]; exact le_top
    · have hr : (0:ℝ) ≤ A.toReal := ENNReal.toReal_nonneg
      have hs : (0:ℝ) ≤ B.toReal := ENNReal.toReal_nonneg
      have hreal : A.toReal ≤ B.toReal := by
        apply real_le_of_forall_mul hr hs
        intro ε hε0 hε1
        have h1 := h ε hε0 hε1
        rw [← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_toReal hB] at h1
        rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1 - ε by linarith),
            ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1 + ε by linarith)] at h1
        exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by linarith) hs)).mp h1
      calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
        _ ≤ ENNReal.ofReal B.toReal := ENNReal.ofReal_le_ofReal hreal
        _ = B := ENNReal.ofReal_toReal hB

/-- The basic estimate: from the defining relation and the two `|·|`-bounds one gets
`(1-ε) * a n ≤ (1+ε) * b n + (1/ε + 1) * (y n + z n)`. -/
private lemma key_ineq {a b y z x w : ℕ → ℝ}
    (_ha : ∀ n, 0 ≤ a n) (_hb : ∀ n, 0 ≤ b n) (hy : ∀ n, 0 ≤ y n) (_hz : ∀ n, 0 ≤ z n)
    (hid : ∀ n, a n + x n + y n = b n + w n + z n)
    (hx : ∀ n ε, 0 < ε → ε < 1 → |x n| ≤ ε * a n + y n / ε)
    (hw : ∀ n ε, 0 < ε → ε < 1 → |w n| ≤ ε * b n + z n / ε) :
    ∀ n ε, 0 < ε → ε < 1 → (1 - ε) * a n ≤ (1 + ε) * b n + (1/ε + 1) * (y n + z n) := by
  intro n ε hε0 hε1
  have hyz : z n - y n ≤ z n + y n := by linarith [hy n]
  have hw' : w n ≤ ε * b n + z n / ε := le_trans (le_abs_self _) (hw n ε hε0 hε1)
  have hx' : -x n ≤ ε * a n + y n / ε := le_trans (neg_le_abs _) (hx n ε hε0 hε1)
  have hdiv : (y n + z n) / ε = y n / ε + z n / ε := by ring
  have h1 : a n - b n = w n + -x n + (z n - y n) := by linarith [hid n]
  have h2 : a n - b n ≤ ε * a n + ε * b n + (y n + z n) / ε + (y n + z n) := by
    rw [hdiv, h1]
    linarith
  have e1 : (1 - ε) * a n = a n - ε * a n := by ring
  have e2 : (1 + ε) * b n = b n + ε * b n := by ring
  have e3 : (1/ε + 1) * (y n + z n) = (y n + z n) / ε + (y n + z n) := by ring
  linarith [h2, e1, e2, e3]

/-- Passing the estimate to the limit in `ENNReal`. -/
private lemma ofReal_limit_le {a b s : ℕ → ℝ} (_ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hs : ∀ n, 0 ≤ s n) (hs0 : Tendsto s Filter.atTop (nhds 0))
    (hineq : ∀ n ε, 0 < ε → ε < 1 → (1 - ε) * a n ≤ (1 + ε) * b n + (1/ε + 1) * s n)
    {A B : ENNReal}
    (haA : Tendsto (fun n => ENNReal.ofReal (a n)) Filter.atTop (nhds A))
    (hbB : Tendsto (fun n => ENNReal.ofReal (b n)) Filter.atTop (nhds B)) :
    ∀ ε, 0 < ε → ε < 1 → ENNReal.ofReal (1 - ε) * A ≤ ENNReal.ofReal (1 + ε) * B := by
  intro ε hε0 hε1
  have hc1 : (0:ℝ) ≤ 1 - ε := by linarith
  have hc2 : (0:ℝ) ≤ 1 + ε := by linarith
  have hC : (0:ℝ) ≤ 1/ε + 1 := by
    have h : 0 < 1/ε := one_div_pos.mpr hε0
    linarith
  have hpoint : ∀ n, ENNReal.ofReal (1 - ε) * ENNReal.ofReal (a n)
      ≤ ENNReal.ofReal (1 + ε) * ENNReal.ofReal (b n)
        + ENNReal.ofReal (1/ε + 1) * ENNReal.ofReal (s n) := by
    intro n
    have h1 := hineq n ε hε0 hε1
    calc ENNReal.ofReal (1 - ε) * ENNReal.ofReal (a n)
        = ENNReal.ofReal ((1 - ε) * a n) := (ENNReal.ofReal_mul hc1).symm
      _ ≤ ENNReal.ofReal ((1 + ε) * b n + (1/ε + 1) * s n) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal ((1 + ε) * b n) + ENNReal.ofReal ((1/ε + 1) * s n) :=
            ENNReal.ofReal_add (mul_nonneg hc2 (hb n)) (mul_nonneg hC (hs n))
      _ = ENNReal.ofReal (1 + ε) * ENNReal.ofReal (b n)
            + ENNReal.ofReal (1/ε + 1) * ENNReal.ofReal (s n) := by
            rw [ENNReal.ofReal_mul hc2, ENNReal.ofReal_mul hC]
  have hL : Tendsto (fun n => ENNReal.ofReal (1 - ε) * ENNReal.ofReal (a n)) Filter.atTop
      (nhds (ENNReal.ofReal (1 - ε) * A)) := by
    have h := ((ENNReal.continuous_const_mul (a := ENNReal.ofReal (1 - ε))
        ENNReal.ofReal_lt_top.ne).tendsto A).comp haA
    simpa only [Function.comp_def] using h
  have hs0' : Tendsto (fun n => ENNReal.ofReal (s n)) Filter.atTop (nhds 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp hs0
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using h
  have hR : Tendsto (fun n => ENNReal.ofReal (1 + ε) * ENNReal.ofReal (b n)
        + ENNReal.ofReal (1/ε + 1) * ENNReal.ofReal (s n)) Filter.atTop
      (nhds (ENNReal.ofReal (1 + ε) * B)) := by
    have h1 : Tendsto (fun n => ENNReal.ofReal (1 + ε) * ENNReal.ofReal (b n)) Filter.atTop
        (nhds (ENNReal.ofReal (1 + ε) * B)) := by
      have h := ((ENNReal.continuous_const_mul (a := ENNReal.ofReal (1 + ε))
          ENNReal.ofReal_lt_top.ne).tendsto B).comp hbB
      simpa only [Function.comp_def] using h
    have h2 : Tendsto (fun n => ENNReal.ofReal (1/ε + 1) * ENNReal.ofReal (s n)) Filter.atTop
        (nhds 0) := by
      have h := ((ENNReal.continuous_const_mul (a := ENNReal.ofReal (1/ε + 1))
          ENNReal.ofReal_lt_top.ne).tendsto 0).comp hs0'
      simpa only [Function.comp_def, mul_zero] using h
    have h3 := h1.add h2
    simpa only [add_zero] using h3
  exact le_of_tendsto_of_tendsto' hL hR hpoint

theorem energy_eq_of_approx {A B : ENNReal} {a b y z x w : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hy : ∀ n, 0 ≤ y n) (hz : ∀ n, 0 ≤ z n)
    (haA : Filter.Tendsto (fun n => ENNReal.ofReal (a n)) Filter.atTop (nhds A))
    (hbB : Filter.Tendsto (fun n => ENNReal.ofReal (b n)) Filter.atTop (nhds B))
    (hy0 : Filter.Tendsto y Filter.atTop (nhds 0)) (hz0 : Filter.Tendsto z Filter.atTop (nhds 0))
    (hid : ∀ n, a n + x n + y n = b n + w n + z n)
    (hx : ∀ n ε, 0 < ε → ε < 1 → |x n| ≤ ε * a n + y n / ε)
    (hw : ∀ n ε, 0 < ε → ε < 1 → |w n| ≤ ε * b n + z n / ε) :
    A = B := by
  have hs : ∀ n, 0 ≤ y n + z n := fun n => add_nonneg (hy n) (hz n)
  have hs0 : Tendsto (fun n => y n + z n) Filter.atTop (nhds 0) := by
    have h := hy0.add hz0
    simpa using h
  have hineq1 : ∀ n ε, 0 < ε → ε < 1 →
      (1 - ε) * a n ≤ (1 + ε) * b n + (1/ε + 1) * (y n + z n) :=
    key_ineq ha hb hy hz hid hx hw
  have hineq2 : ∀ n ε, 0 < ε → ε < 1 →
      (1 - ε) * b n ≤ (1 + ε) * a n + (1/ε + 1) * (y n + z n) := by
    have h := key_ineq hb ha hz hy (fun n => (hid n).symm) hw hx
    intro n ε hε0 hε1
    have h' := h n ε hε0 hε1
    have hr : (1/ε + 1) * (z n + y n) = (1/ε + 1) * (y n + z n) := by ring
    linarith [h', hr]
  have key1 := ofReal_limit_le ha hb hs hs0 hineq1 haA hbB
  have key2 := ofReal_limit_le hb ha hs hs0 hineq2 hbB haA
  exact le_antisymm (ENNReal_le_of_forall key1) (ENNReal_le_of_forall key2)

end Work.NN.Core
