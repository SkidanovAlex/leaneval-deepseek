import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.NrmSpec
import Submission.Work.CNum.LgUpSpec
import Submission.Work.CNum.LogUpMSpec
import Submission.Work.CNum.LogDnMSpec
import Submission.Work.CNum.LgInfra
import Submission.Work.CNum.SerDnDefs
import Submission.Work.CNum.SerInvTerm
import Submission.Work.CNum.LogDnMWeak
import Submission.Work.CNum.SerDnTail
import Submission.Work.CNum.SerDnNum
import Submission.Work.CNum.SerDnInvStep
import Submission.Work.CNum.SerDnTerm
import Submission.Work.CNum.SerDnInit
import Submission.Work.ANum.h_log_bound
import Submission.Work.ANum.norm_pow_succ_sub_pow_succ_le

set_option maxHeartbeats 4000000

namespace Work.CNum

open Work.ANum
open scoped BigOperators

/-! ## Shifting the iterator by one -/

lemma sdIterFrom_next (x y σ : ℤ) (s : SD) (j : ℕ) :
    sdIterFrom x y σ (sdNext x y σ s) j = sdIterFrom x y σ s (j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [sdIterFrom_succ, ih, ← sdIterFrom_succ]

lemma sdIterFrom_next_expl (x y σ px py pe sg : ℤ) (j : ℕ) :
    sdIterFrom x y σ
        (⟨Int.ediv (px * x - py * y) SC, Int.ediv (px * y + py * x) SC,
          mulU σ pe + 2, mulU sg σ⟩ : SD) j
      = sdIterFrom x y σ (⟨px, py, pe, sg⟩ : SD) (j + 1) :=
  sdIterFrom_next x y σ ⟨px, py, pe, sg⟩ j

lemma sdIterFrom_zero (x y σ : ℤ) (s : SD) : sdIterFrom x y σ s 0 = s := rfl

/-! ## Evaluation of `serDnAux` -/

lemma serDnAux_eval (x y σ e : ℤ) :
    ∀ (N : ℕ) (px py pe sg acc : ℤ),
      serDnAux x y σ e N px py pe sg acc
        = acc + 24 * ∑ j ∈ Finset.range N,
            logDnM (sdLo σ e ((N - j : ℕ) : ℤ)
              (sdIterFrom x y σ (⟨px, py, pe, sg⟩ : SD) j)) := by
  intro N
  induction N with
  | zero =>
      intro px py pe sg acc
      simp [serDnAux]
  | succ N ih =>
      intro px py pe sg acc
      have hstep : serDnAux x y σ e (N + 1) px py pe sg acc
          = serDnAux x y σ e N (Int.ediv (px * x - py * y) SC)
              (Int.ediv (px * y + py * x) SC) (mulU σ pe + 2) (mulU sg σ)
              (acc + 24 * logDnM (sdLo σ e ((N + 1 : ℕ) : ℤ) ⟨px, py, pe, sg⟩)) := by
        simp only [serDnAux, sdLo]
        push_cast
        ring
      rw [hstep, ih]
      rw [Finset.sum_range_succ']
      have hsum : (∑ j ∈ Finset.range N,
            logDnM (sdLo σ e ((N - j : ℕ) : ℤ)
              (sdIterFrom x y σ
                (⟨Int.ediv (px * x - py * y) SC, Int.ediv (px * y + py * x) SC,
                  mulU σ pe + 2, mulU sg σ⟩ : SD) j)))
          = ∑ j ∈ Finset.range N,
              logDnM (sdLo σ e ((N - j : ℕ) : ℤ)
                (sdIterFrom x y σ (⟨px, py, pe, sg⟩ : SD) (j + 1))) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [sdIterFrom_next_expl]
      rw [hsum]
      simp only [Nat.succ_sub_succ_eq_sub, tsub_zero, sdIterFrom_zero]
      ring

/-! ## `m2r` of a finite sum -/

lemma m2r_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    m2r (∑ i ∈ s, f i) = ∑ i ∈ s, m2r (f i) := by
  simp only [m2r, Int.cast_sum, Finset.sum_div]


/-! ## The main specification -/

theorem SerDnSpec {x y e : ℤ} {w : ℂ} (he : 0 ≤ e) (he1 : Work.ANum.m2r e ≤ 1 / 10 ^ 6)
    (hx : Int.natAbs x ≤ 2 ^ 34) (hy : Int.natAbs y ≤ 2 ^ 34)
    (hσ1 : Work.ANum.m2r (Work.CNum.nrmUp x y + e) ≤ 79 / 100)
    (hσ0 : Work.ANum.m2r e < Work.ANum.m2r (Work.CNum.nrmDn x y))
    (hw : ‖w - ((x : ℝ) + (y : ℝ) * Complex.I) / (Work.ANum.SC : ℝ)‖ ≤ Work.ANum.m2r e) :
    Work.ANum.m2r (Work.CNum.serDn x y e) ≤ Real.log ‖Submission.CDTPlan.hauptH w‖ := by
  set σ : ℤ := nrmUp x y + e with hσdef
  have hσ1' : m2r σ ≤ 79 / 100 := by rw [hσdef]; exact hσ1
  have he0 : (0 : ℝ) ≤ m2r e := (m2r_nonneg_iff e).mpr he
  have hc_le : ‖spt x y‖ ≤ m2r (nrmUp x y) := NrmUpSpec hx hy
  have hc_ge : m2r (nrmDn x y) ≤ ‖spt x y‖ := NrmDnSpec hx hy
  have hRσ : srad x y e ≤ m2r σ := by
    simp only [srad, hσdef, m2r_add]
    linarith
  have hRnn : 0 ≤ srad x y e := by
    simp only [srad]; linarith [norm_nonneg (spt x y)]
  have hR79 : srad x y e ≤ 79 / 100 := le_trans hRσ hσ1'
  have hR_le1 : srad x y e ≤ 1 := le_trans hR79 (by norm_num)
  have hR_lt1 : srad x y e < 1 := lt_of_le_of_lt hR79 (by norm_num)
  have hdenR : 0 < 1 - srad x y e := by linarith
  -- facts about `w`
  have hw_ball : ‖w - spt x y‖ ≤ m2r e := hw
  have hw_lt1 : ‖w‖ < 1 := by
    have h1 : ‖w‖ ≤ ‖w - spt x y‖ + ‖spt x y‖ := by
      calc ‖w‖ = ‖(w - spt x y) + spt x y‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h2 : m2r e + m2r (nrmUp x y) = m2r σ := by rw [hσdef, m2r_add]; ring
    linarith [h1, hw_ball, hc_le, h2, hσ1']
  have hw_gt0 : 0 < ‖w‖ := by
    have h1 : ‖spt x y‖ ≤ ‖w - spt x y‖ + ‖w‖ := by
      calc ‖spt x y‖ = ‖(spt x y - w) + w‖ := by ring_nf
        _ ≤ ‖spt x y - w‖ + ‖w‖ := norm_add_le _ _
        _ = ‖w - spt x y‖ + ‖w‖ := by rw [norm_sub_rev]
    linarith [h1, hw_ball, hc_ge, hσ0]
  have hwne : w ≠ 0 := norm_pos_iff.mp hw_gt0
  have hwnorm : ‖w‖ ≤ srad x y e := by
    have h1 : ‖w‖ ≤ ‖w - spt x y‖ + ‖spt x y‖ := by
      calc ‖w‖ = ‖(w - spt x y) + spt x y‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    simp only [srad]; linarith [h1, hw_ball]
  -- the series argument stays away from `0`
  have h1wpos : ∀ j : ℕ, 0 < ‖(1 : ℂ) + w ^ (j + 1)‖ := by
    intro j
    have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) + w ^ (j + 1)‖ + ‖w ^ (j + 1)‖ := by
      have h := norm_add_le ((1 : ℂ) + w ^ (j + 1)) (-(w ^ (j + 1)))
      have hL : ((1 : ℂ) + w ^ (j + 1)) + (-(w ^ (j + 1))) = 1 := by ring
      rw [hL, norm_one, norm_neg] at h
      exact h
    have h2 : ‖w ^ (j + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg w) hw_lt1 (Nat.succ_ne_zero j)
    linarith
  have h1wge : ∀ j : ℕ, 1 - srad x y e ^ (j + 1) ≤ ‖(1 : ℂ) + w ^ (j + 1)‖ := by
    intro j
    have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) + w ^ (j + 1)‖ + ‖w ^ (j + 1)‖ := by
      have h := norm_add_le ((1 : ℂ) + w ^ (j + 1)) (-(w ^ (j + 1)))
      have hL : ((1 : ℂ) + w ^ (j + 1)) + (-(w ^ (j + 1))) = 1 := by ring
      rw [hL, norm_one, norm_neg] at h
      exact h
    have h2 : ‖w ^ (j + 1)‖ ≤ srad x y e ^ (j + 1) := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg w) hwnorm _
    linarith
  -- the invariant
  have hInv : ∀ k : ℕ, SDInv x y e σ k (sdIter x y σ k) := by
    intro k
    induction k with
    | zero => simpa [sdIter_zero] using SerDnInit he hσ1' hx hy hRσ
    | succ k ih => rw [sdIter_succ]; exact SerDnInvStep he hσ1' hRσ ih
  set L : ℕ → ℤ := fun j => sdLo σ e ((SERM - j : ℕ) : ℤ) (sdIter x y σ j) with hLdef
  -- the per-term facts
  have hTerm : ∀ (j : ℕ), j < SERM →
      1 ≤ L j ∧ L j ≤ 2 ^ 60 ∧
      m2r (L j) - ‖(1 : ℂ) + w ^ (j + 1)‖
        ≤ (2 * (j : ℝ) + 1 - SERM) * m2r e * srad x y e ^ j := by
    intro j hj
    have h3 := SerDnTerm (x := x) (y := y) (e := e) (σ := σ) (w := w) (k := j)
      (s := sdIter x y σ j) he he1 hσ1' hRσ hw_ball hj (hInv j)
    exact ⟨h3.1, h3.2.1, by linarith [h3.2.2]⟩
  -- per-term logarithmic bound
  have hper : ∀ j ∈ Finset.range SERM,
      m2r (logDnM (L j)) ≤ Real.log ‖(1 : ℂ) + w ^ (j + 1)‖
        + (m2r (L j) - ‖(1 : ℂ) + w ^ (j + 1)‖) / ‖(1 : ℂ) + w ^ (j + 1)‖ := by
    intro j hj
    have hjk : j < SERM := Finset.mem_range.mp hj
    obtain ⟨hge, hle, -⟩ := hTerm j hjk
    have hpos : 0 < m2r (L j) := (m2r_pos_iff (L j)).mpr (by omega)
    have hb : 0 < ‖(1 : ℂ) + w ^ (j + 1)‖ := h1wpos j
    have hlog1 : m2r (logDnM (L j)) ≤ Real.log (m2r (L j)) :=
      LogDnMWeak hge hle hpos le_rfl
    have hsplit : Real.log (m2r (L j)) ≤ Real.log ‖(1 : ℂ) + w ^ (j + 1)‖
        + (m2r (L j) - ‖(1 : ℂ) + w ^ (j + 1)‖) / ‖(1 : ℂ) + w ^ (j + 1)‖ := by
      have h := Real.log_le_sub_one_of_pos
        (show 0 < m2r (L j) / ‖(1 : ℂ) + w ^ (j + 1)‖ from div_pos hpos hb)
      rw [Real.log_div (ne_of_gt hpos) (ne_of_gt hb)] at h
      have heq : m2r (L j) / ‖(1 : ℂ) + w ^ (j + 1)‖ - 1
          = (m2r (L j) - ‖(1 : ℂ) + w ^ (j + 1)‖) / ‖(1 : ℂ) + w ^ (j + 1)‖ := by
        field_simp
      linarith [h, heq]
    linarith [hlog1, hsplit]
  -- small indices
  have hg1 : ∀ j ∈ Finset.range 22,
      (m2r (L j) - ‖(1 : ℂ) + w ^ (j + 1)‖) / ‖(1 : ℂ) + w ^ (j + 1)‖ ≤ 0 := by
    intro j hj
    have hj22 : j < 22 := Finset.mem_range.mp hj
    have hjS : j < SERM := by norm_num [SERM]; omega
    obtain ⟨-, -, hδ⟩ := hTerm j hjS
    have hj21 : (j : ℝ) ≤ 21 := by
      have : j ≤ 21 := by omega
      exact_mod_cast this
    have hcoef : (2 * (j : ℝ) + 1 - SERM) ≤ 0 := by
      have hS : (SERM : ℝ) = 44 := by norm_num [SERM]
      rw [hS]; linarith
    have hρR : 0 ≤ m2r e * srad x y e ^ j := mul_nonneg he0 (pow_nonneg hRnn j)
    have hδ0 : m2r (L j) - ‖(1 : ℂ) + w ^ (j + 1)‖ ≤ 0 := by
      nlinarith [hδ, hcoef, hρR]
    exact div_nonpos_of_nonpos_of_nonneg hδ0 (le_of_lt (h1wpos j))
  -- large indices
  have hg2 : ∀ j ∈ Finset.range 22,
      (m2r (L (22 + j)) - ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖) / ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖
        ≤ ((2 * ((22 + j : ℕ) : ℝ) - 43) * m2r e * srad x y e ^ (22 + j))
            / (1 - srad x y e ^ 23) := by
    intro j hj
    have hj22 : j < 22 := Finset.mem_range.mp hj
    have hjS : 22 + j < SERM := by norm_num [SERM]; omega
    obtain ⟨-, -, hδ⟩ := hTerm (22 + j) hjS
    have hcoef : (2 * ((22 + j : ℕ) : ℝ) + 1 - SERM) = 2 * ((22 + j : ℕ) : ℝ) - 43 := by
      have hS : (SERM : ℝ) = 44 := by norm_num [SERM]
      rw [hS]; ring
    rw [hcoef] at hδ
    have hb : 0 < ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖ := h1wpos (22 + j)
    have hR23 : srad x y e ^ 23 < 1 :=
      pow_lt_one₀ hRnn (lt_of_le_of_lt hR79 (by norm_num)) (by norm_num)
    have hden : 0 < 1 - srad x y e ^ 23 := by linarith
    have hRjm : srad x y e ^ ((22 + j) + 1) ≤ srad x y e ^ 23 := by
      refine pow_le_pow_of_le_one hRnn hR_le1 ?_
      omega
    have hb23 : (1 : ℝ) - srad x y e ^ 23 ≤ ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖ := by
      linarith [h1wge (22 + j), hRjm]
    have hYnn : 0 ≤ (2 * ((22 + j : ℕ) : ℝ) - 43) * m2r e * srad x y e ^ (22 + j) := by
      have h1 : (0 : ℝ) ≤ 2 * ((22 + j : ℕ) : ℝ) - 43 := by
        have h2 : (0 : ℝ) ≤ ((22 + j : ℕ) : ℝ) := Nat.cast_nonneg _
        push_cast at h2 ⊢
        linarith
      exact mul_nonneg (mul_nonneg h1 he0) (pow_nonneg hRnn _)
    rw [div_le_div_iff₀ hb hden]
    by_cases hh : 0 ≤ m2r (L (22 + j)) - ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖
    · have h1 : (m2r (L (22 + j)) - ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖) * (1 - srad x y e ^ 23)
          ≤ (m2r (L (22 + j)) - ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖)
              * ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖ :=
        mul_le_mul_of_nonneg_left hb23 hh
      have h2 : (m2r (L (22 + j)) - ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖)
              * ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖
          ≤ ((2 * ((22 + j : ℕ) : ℝ) - 43) * m2r e * srad x y e ^ (22 + j))
              * ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖ :=
        mul_le_mul_of_nonneg_right hδ (le_of_lt hb)
      linarith
    · have h1 : (m2r (L (22 + j)) - ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖) * (1 - srad x y e ^ 23)
          ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.mp hh)) hden.le
      have h2 : 0 ≤ ((2 * ((22 + j : ℕ) : ℝ) - 43) * m2r e * srad x y e ^ (22 + j))
              * ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖ := mul_nonneg hYnn (le_of_lt hb)
      linarith
  -- the sum of the excesses
  have hgsum : ∑ j ∈ Finset.range SERM,
      (m2r (L j) - ‖(1 : ℂ) + w ^ (j + 1)‖) / ‖(1 : ℂ) + w ^ (j + 1)‖ ≤ 4096 / (SC : ℝ) := by
    have hsplit : ∑ j ∈ Finset.range SERM,
          (m2r (L j) - ‖(1 : ℂ) + w ^ (j + 1)‖) / ‖(1 : ℂ) + w ^ (j + 1)‖
        = ∑ j ∈ Finset.range 22, (m2r (L j) - ‖(1 : ℂ) + w ^ (j + 1)‖) / ‖(1 : ℂ) + w ^ (j + 1)‖
          + ∑ j ∈ Finset.range 22,
              (m2r (L (22 + j)) - ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖)
                / ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖ := by
      have h22 : SERM = 22 + 22 := by norm_num [SERM]
      rw [h22, Finset.sum_range_add]
    rw [hsplit]
    have hs1 : ∑ j ∈ Finset.range 22,
        (m2r (L j) - ‖(1 : ℂ) + w ^ (j + 1)‖) / ‖(1 : ℂ) + w ^ (j + 1)‖ ≤ 0 :=
      Finset.sum_nonpos hg1
    have hs2 : ∑ j ∈ Finset.range 22,
        (m2r (L (22 + j)) - ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖) / ‖(1 : ℂ) + w ^ ((22 + j) + 1)‖
        ≤ (∑ j ∈ Finset.range 22,
            (2 * ((22 + j : ℕ) : ℝ) - 43) * m2r e * srad x y e ^ (22 + j))
          / (1 - srad x y e ^ 23) := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum hg2
    have hreindex : (∑ j ∈ Finset.range 22,
            (2 * ((22 + j : ℕ) : ℝ) - 43) * m2r e * srad x y e ^ (22 + j))
        = ∑ j ∈ Finset.Icc (22 : ℕ) 43, (2 * (j : ℝ) - 43) * m2r e * srad x y e ^ j := by
      have hIcc : Finset.Icc (22 : ℕ) 43 = Finset.Ico 22 (43 + 1) :=
        (Finset.Ico_add_one_right_eq_Icc 22 43).symm
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
    have hNum := SerDnNum (R := srad x y e) (ρ := m2r e) hRnn hR79 he0 he1
    rw [← hreindex] at hNum
    have hden : 0 < 1 - srad x y e ^ 23 := by
      have hR23 : srad x y e ^ 23 < 1 :=
        pow_lt_one₀ hRnn (lt_of_le_of_lt hR79 (by norm_num)) (by norm_num)
      linarith
    have hfin : (∑ j ∈ Finset.range 22,
            (2 * ((22 + j : ℕ) : ℝ) - 43) * m2r e * srad x y e ^ (22 + j))
          / (1 - srad x y e ^ 23) ≤ 4096 / (SC : ℝ) := by
      have h2 : ((1 - srad x y e ^ 23) * (4096 / (SC : ℝ))) / (1 - srad x y e ^ 23)
          = 4096 / (SC : ℝ) := by field_simp
      calc (∑ j ∈ Finset.range 22,
            (2 * ((22 + j : ℕ) : ℝ) - 43) * m2r e * srad x y e ^ (22 + j))
          / (1 - srad x y e ^ 23)
          ≤ ((1 - srad x y e ^ 23) * (4096 / (SC : ℝ))) / (1 - srad x y e ^ 23) :=
            div_le_div_of_nonneg_right hNum hden.le
        _ = 4096 / (SC : ℝ) := h2
    linarith [hs1, hs2, hfin]
  -- evaluation of `serDnAux`
  have hS : m2r (serDnAux x y σ e SERM x y 0 SC 0)
      = 24 * ∑ j ∈ Finset.range SERM, m2r (logDnM (L j)) := by
    rw [serDnAux_eval x y σ e SERM x y 0 SC 0]
    simp only [sdIter, sd0, hLdef]
    rw [m2r_add, m2r_mul_int', m2r_sum]
    simp only [m2r_zero, zero_add]
    norm_num
  -- bound on the accumulated series
  have hC : m2r (serDnAux x y σ e SERM x y 0 SC 0)
      ≤ 24 * (∑ j ∈ Finset.range SERM, Real.log ‖(1 : ℂ) + w ^ (j + 1)‖)
        + 24 * (4096 / (SC : ℝ)) := by
    have hsum1 : ∑ j ∈ Finset.range SERM, m2r (logDnM (L j))
        ≤ (∑ j ∈ Finset.range SERM, Real.log ‖(1 : ℂ) + w ^ (j + 1)‖)
          + ∑ j ∈ Finset.range SERM,
              (m2r (L j) - ‖(1 : ℂ) + w ^ (j + 1)‖) / ‖(1 : ℂ) + w ^ (j + 1)‖ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hper
    rw [hS]
    nlinarith [hsum1, hgsum]
  -- the `lgDn (256 * SC)` term
  have hA : m2r (lgDn (256 * SC)) ≤ Real.log 256 := by
    have h1 : SC ≤ (256 * SC : ℤ) := by nlinarith [SC_pos]
    have h2 : (256 * SC : ℤ) ≤ 2 ^ 60 := by norm_num [SC]
    have h4 : m2r (256 * SC) = (256 : ℝ) := m2r_mul_SC' (256 : ℤ)
    calc m2r (lgDn (256 * SC)) ≤ Real.log (m2r (256 * SC)) := lgDn_spec h1 h2
      _ = Real.log 256 := by rw [h4]
  -- the `logDnM` term
  have hB : m2r (logDnM (nrmDn x y - e)) ≤ Real.log ‖w‖ := by
    have hlo1 : 1 ≤ nrmDn x y - e := by
      have h1 : e < nrmDn x y := (LgUpSpec_m2r_lt_iff e (nrmDn x y)).mp hσ0
      omega
    have hlo60 : nrmDn x y - e ≤ 2 ^ 60 := by
      have h1 : nrmDn x y ≤ nrmUp x y := by
        simp only [nrmDn, nrmUp, sqDn, sqUp]; omega
      have h2 : nrmUp x y ≤ 2 ^ 36 := nrmUp_le hx hy
      omega
    have hle : m2r (nrmDn x y - e) ≤ ‖w‖ := by
      have h1 : m2r (nrmDn x y - e) = m2r (nrmDn x y) - m2r e := m2r_sub _ _
      have h2 : ‖spt x y‖ ≤ m2r e + ‖w‖ := by
        calc ‖spt x y‖ = ‖(spt x y - w) + w‖ := by ring_nf
          _ ≤ ‖spt x y - w‖ + ‖w‖ := norm_add_le _ _
          _ = ‖w - spt x y‖ + ‖w‖ := by rw [norm_sub_rev]
          _ ≤ m2r e + ‖w‖ := by linarith [hw_ball]
      linarith [h1, h2, hc_ge]
    exact LogDnMWeak hlo1 hlo60 hw_gt0 hle
  -- the tail
  have hsumm : Summable (fun n : ℕ => Real.log ‖(1 : ℂ) + w ^ (n + 1)‖) := by
    have hgeo : Summable (fun n : ℕ => w ^ (n + 1)) :=
      (summable_nat_add_iff 1).2 (summable_geometric_iff_norm_lt_one.mpr hw_lt1)
    exact hgeo.norm.summable_log_norm_one_add
  have htail_le : srad x y e ^ (SERM + 1) / ((1 - srad x y e) * (1 - srad x y e ^ (SERM + 1)))
      ≤ 2 * (srad x y e ^ (SERM + 1) / (1 - srad x y e)) := by
    have hR45 : srad x y e ^ (SERM + 1) ≤ 1 / 2 := by
      have h1 : srad x y e ^ (SERM + 1) ≤ (79 / 100 : ℝ) ^ (SERM + 1) :=
        pow_le_pow_left₀ hRnn hR79 _
      have h2 : (79 / 100 : ℝ) ^ (SERM + 1) ≤ (79 / 100 : ℝ) ^ 10 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num [SERM])
      have h3 : (79 / 100 : ℝ) ^ 10 ≤ 1 / 2 := by norm_num
      linarith
    have hden2 : 0 < 1 - srad x y e ^ (SERM + 1) := by linarith
    have hR45nn : 0 ≤ srad x y e ^ (SERM + 1) := pow_nonneg hRnn _
    have h : (1 : ℝ) ≤ 2 * (1 - srad x y e ^ (SERM + 1)) := by linarith [hR45]
    rw [← mul_div_assoc, div_le_div_iff₀ (mul_pos hdenR hden2) hdenR]
    nlinarith [h, mul_nonneg hR45nn hdenR.le, hR45nn, hdenR]
  have htailb : ∑' n : ℕ, Real.log ‖(1 : ℂ) + w ^ (n + 1)‖
      ≥ (∑ n ∈ Finset.range SERM, Real.log ‖(1 : ℂ) + w ^ (n + 1)‖)
        - 2 * (srad x y e ^ (SERM + 1) / (1 - srad x y e)) := by
    have hsp := hsumm.sum_add_tsum_nat_add SERM
    have htl := SerDnTail (q := w) (R := srad x y e) hRnn hR_lt1 hwnorm SERM
    have htl' : -(2 * (srad x y e ^ (SERM + 1) / (1 - srad x y e)))
        ≤ ∑' n : ℕ, Real.log ‖(1 : ℂ) + w ^ (n + SERM + 1)‖ :=
      le_trans (by linarith [htail_le]) htl
    rw [← hsp]
    linarith [htl']
  -- the contour/evaluation-tube term
  have hσ_lt : σ < SC := by
    have h1 : m2r σ < m2r SC := by rw [m2r_SC]; linarith
    exact (LgUpSpec_m2r_lt_iff σ SC).mp h1
  have hdσ : 0 < SC - σ := by omega
  have hdenσ : 0 < 1 - m2r σ := by linarith [hσ1']
  have hpow : srad x y e ^ (SERM + 1) ≤ m2r (powM true σ (SERM + 1)) := by
    have h1 : srad x y e ^ (SERM + 1) ≤ (m2r σ) ^ (SERM + 1) := pow_le_pow_left₀ hRnn hRσ _
    exact le_trans h1 (powM_true_ge (le_trans hRnn hRσ) (SERM + 1))
  have hdiv : srad x y e ^ (SERM + 1) / (1 - srad x y e)
      ≤ m2r (divUz (SC * powM true σ (SERM + 1)) (SC - σ)) := by
    have h1 : m2r (SC * powM true σ (SERM + 1)) / ((SC - σ : ℤ) : ℝ)
        ≤ m2r (divUz (SC * powM true σ (SERM + 1)) (SC - σ)) := divUz_ge hdσ _
    have hmul : m2r (SC * powM true σ (SERM + 1))
        = (SC : ℝ) * m2r (powM true σ (SERM + 1)) := m2r_mul_int' _ _
    have hcast : ((SC - σ : ℤ) : ℝ) = (SC : ℝ) * (1 - m2r σ) := by
      have hσr : (SC : ℝ) * m2r σ = (σ : ℝ) := by
        show (SC : ℝ) * ((σ : ℝ) / (SC : ℝ)) = (σ : ℝ)
        rw [mul_comm]
        exact div_mul_cancel₀ (σ : ℝ) (ne_of_gt SC_posR)
      rw [Int.cast_sub, ← hσr]; ring
    have h2 : (SC : ℝ) * m2r (powM true σ (SERM + 1)) / ((SC - σ : ℤ) : ℝ)
        = m2r (powM true σ (SERM + 1)) / (1 - m2r σ) := by
      rw [hcast, mul_div_mul_left _ _ (ne_of_gt SC_posR)]
    have h3 : srad x y e ^ (SERM + 1) / (1 - srad x y e)
        ≤ m2r (powM true σ (SERM + 1)) / (1 - m2r σ) := by
      rw [div_le_div_iff₀ hdenR hdenσ]
      nlinarith [hpow, hRσ, hRnn, hdenR, hdenσ, pow_nonneg hRnn (SERM + 1)]
    rw [hmul] at h1
    rw [h2] at h1
    linarith [h1, h3]
  have hCT : 24 * (2 * m2r (divUz (SC * powM true σ (SERM + 1)) (SC - σ)) + 4096 / (SC : ℝ))
      ≥ 24 * (2 * (srad x y e ^ (SERM + 1) / (1 - srad x y e)) + 4096 / (SC : ℝ)) := by
    nlinarith [hdiv]
  -- assemble
  have h4096 : m2r (4096 : ℤ) = 4096 / (SC : ℝ) := by simp only [m2r]; norm_num
  have hserDn : serDn x y e
      = lgDn (256 * SC) + logDnM (nrmDn x y - e) + serDnAux x y σ e SERM x y 0 SC 0
        - 24 * (2 * divUz (SC * powM true σ (SERM + 1)) (SC - σ) + 4096) := by
    simp only [serDn]
    rw [← hσdef]
  have hlog := log_norm_hauptH_of_norm_lt_one (q := w) hw_lt1 hwne
  have hlog' : Real.log ‖Submission.CDTPlan.hauptH w‖
      = Real.log 256 + Real.log ‖w‖ + 24 * ∑' n : ℕ, Real.log ‖(1 : ℂ) + w ^ (n + 1)‖ := by
    rw [hlog, tsum_mul_left]
  rw [hserDn]
  simp only [m2r_add, m2r_sub, m2r_mul_int', h4096]
  rw [hlog']
  linarith [hA, hB, hC, hCT, htailb]

end Work.CNum
