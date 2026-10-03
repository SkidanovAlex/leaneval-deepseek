import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Setup
import Submission.Work.Parab.germ
import Submission.Work.Parab.chartEstimate.chart_estimate
import Submission.Work.Parab.coordData.iterate_sub_translate_bound
import Submission.Work.Parab.coordData.budget_ineq_c

namespace Work.Parab.coordData

open scoped Topology
open Set Filter Metric

set_option maxHeartbeats 1600000

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}

/-- **One step of the chart dynamics, in norm form.**  There are a level `N > 0` and a constant
`K ≥ 0` such that for `‖v‖ > N` the chart dynamics `wMap f v = -1 / f (-1 / v)` is a translation
by `1` up to `K / ‖v‖`, and moves the real part to the right by at least `1 / 2`. -/
private theorem step_bound (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ N K : ℝ, 0 < N ∧ 0 ≤ K ∧ ∀ v : ℂ, N < ‖v‖ →
      ‖Work.FatouCoord.wMap f v - (v + 1)‖ ≤ K / ‖v‖ ∧
        v.re + 1 / 2 ≤ (Work.FatouCoord.wMap f v).re := by
  obtain ⟨N₀, K₀, hN₀, -, hK₀, hchart⟩ := Work.Parab.chartEstimate.chart_estimate hb
  refine ⟨max N₀ (2 * K₀ + 1) + 1, K₀, by positivity, hK₀, ?_⟩
  intro v hv
  have hvN₀ : N₀ < ‖v‖ := by
    have h : N₀ ≤ max N₀ (2 * K₀ + 1) := le_max_left _ _
    linarith
  have hvK : 2 * K₀ < ‖v‖ := by
    have h : 2 * K₀ + 1 ≤ max N₀ (2 * K₀ + 1) := le_max_right _ _
    linarith
  obtain ⟨h1, -⟩ := hchart v hvN₀
  have hvpos : 0 < ‖v‖ := lt_of_lt_of_le hN₀ hvN₀.le
  have hdiv : K₀ / ‖v‖ ≤ 1 / 2 := by
    rw [div_le_iff₀ hvpos]
    linarith
  refine ⟨h1, ?_⟩
  have hre : (Work.FatouCoord.wMap f v).re
      = v.re + 1 + (Work.FatouCoord.wMap f v - (v + 1)).re := by
    have h : (Work.FatouCoord.wMap f v - (v + 1)).re
        = (Work.FatouCoord.wMap f v).re - v.re - 1 := by
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
      ring
    rw [h]
    ring
  have hlow : -‖Work.FatouCoord.wMap f v - (v + 1)‖
      ≤ (Work.FatouCoord.wMap f v - (v + 1)).re := by
    have hh := Complex.abs_re_le_norm (Work.FatouCoord.wMap f v - (v + 1))
    rw [abs_le] at hh
    linarith [hh.1]
  rw [hre]
  linarith

/-- Harmonic bound `∑_{s<M} 1/(s+1) ≤ 1 + log M`. -/
private theorem sum_range_inv_succ_le_log (M : ℕ) :
    ∑ s ∈ Finset.range M, (1 : ℝ) / ((s : ℝ) + 1) ≤ 1 + Real.log (M : ℝ) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp [Real.log_zero]
  · obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, (Nat.succ_pred_eq_of_pos hM).symm⟩
    have hstep : ∀ s : ℕ,
        (1 : ℝ) / ((s : ℝ) + 2) ≤ Real.log ((s : ℝ) + 2) - Real.log ((s : ℝ) + 1) := by
      intro s
      have h1 : 0 < ((s : ℝ) + 1) / ((s : ℝ) + 2) := by positivity
      have h2 := Real.log_le_sub_one_of_pos h1
      have h3 : Real.log (((s : ℝ) + 1) / ((s : ℝ) + 2))
          = Real.log ((s : ℝ) + 1) - Real.log ((s : ℝ) + 2) :=
        Real.log_div (by positivity) (by positivity)
      rw [h3] at h2
      have h4 : ((s : ℝ) + 1) / ((s : ℝ) + 2) - 1 = -(1 / ((s : ℝ) + 2)) := by
        field_simp
        ring
      rw [h4] at h2
      linarith
    have htel : ∑ s ∈ Finset.range N, (Real.log ((s : ℝ) + 2) - Real.log ((s : ℝ) + 1))
        = Real.log ((N : ℝ) + 1) := by
      have h := Finset.sum_range_sub (fun s : ℕ => Real.log ((s : ℝ) + 1)) N
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] at h
      rw [Real.log_one, sub_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [show (s : ℝ) + 1 + 1 = (s : ℝ) + 2 by ring]
    have hsum_le : ∑ s ∈ Finset.range N, (1 : ℝ) / ((s : ℝ) + 2)
        ≤ ∑ s ∈ Finset.range N, (Real.log ((s : ℝ) + 2) - Real.log ((s : ℝ) + 1)) :=
      Finset.sum_le_sum (fun s _ => hstep s)
    have hhead : ∑ s ∈ Finset.range (N + 1), (1 : ℝ) / ((s : ℝ) + 1)
        = 1 + ∑ s ∈ Finset.range N, (1 : ℝ) / ((s : ℝ) + 2) := by
      rw [Finset.sum_range_succ']
      have h0 : (1 : ℝ) / (((0 : ℕ) : ℝ) + 1) = 1 := by norm_num
      have h1 : ∑ s ∈ Finset.range N, (1 : ℝ) / ((((s + 1 : ℕ)) : ℝ) + 1)
          = ∑ s ∈ Finset.range N, (1 : ℝ) / ((s : ℝ) + 2) := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        have h2 : (((s + 1 : ℕ)) : ℝ) + 1 = (s : ℝ) + 2 := by push_cast; ring
        rw [h2]
      rw [h0, h1, add_comm]
    calc ∑ s ∈ Finset.range (N + 1), (1 : ℝ) / ((s : ℝ) + 1)
        = 1 + ∑ s ∈ Finset.range N, (1 : ℝ) / ((s : ℝ) + 2) := hhead
      _ ≤ 1 + ∑ s ∈ Finset.range N, (Real.log ((s : ℝ) + 2) - Real.log ((s : ℝ) + 1)) := by
          linarith [hsum_le]
      _ = 1 + Real.log ((N : ℝ) + 1) := by rw [htel]
      _ = 1 + Real.log (((N + 1 : ℕ)) : ℝ) := by push_cast; ring_nf

/-- One-sided sum bound: for `a ≥ 0`, `δ ≥ 0`, `c > 0`,
`∑_{j<m} 1/max (c/2) (a + j - δ) ≤ 2δ/c + 2 + 4/c + log (m+1)`. -/
private theorem one_sided_sum_inv {c δ a : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) (ha : 0 ≤ a) (m : ℕ) :
    ∑ j ∈ Finset.range m, (1 : ℝ) / max (c / 2) (a + (j : ℝ) - δ)
      ≤ 2 * δ / c + 2 + 4 / c + Real.log ((m : ℝ) + 1) := by
  have hc2 : 0 < c / 2 := by linarith
  have hδc : 0 ≤ δ + c / 2 := by linarith
  set J : ℕ := Nat.ceil (max (δ + c / 2 - a) (0:ℝ)) with hJ
  have hJspec : δ + c / 2 - a ≤ (J : ℝ) := by
    rw [hJ]
    exact le_trans (le_max_left _ _) (Nat.le_ceil _)
  have hJle : (J : ℝ) ≤ δ + c / 2 + 1 := by
    rw [hJ]
    have h1 : (⌈max (δ + c / 2 - a) (0:ℝ)⌉₊ : ℝ) < max (δ + c / 2 - a) (0:ℝ) + 1 :=
      Nat.ceil_lt_add_one (le_max_right (δ + c / 2 - a) (0:ℝ))
    have h2 : max (δ + c / 2 - a) 0 ≤ δ + c / 2 := max_le (by linarith) hδc
    linarith
  set N : ℕ := min m J with hN
  have hsplit : (∑ j ∈ Finset.range N, (1 : ℝ) / max (c / 2) (a + (j : ℝ) - δ))
      + (∑ j ∈ Finset.Ico N m, (1 : ℝ) / max (c / 2) (a + (j : ℝ) - δ))
      = ∑ j ∈ Finset.range m, (1 : ℝ) / max (c / 2) (a + (j : ℝ) - δ) := by
    rw [show Finset.range N = Finset.Ico 0 N from (Nat.Ico_zero_eq_range N).symm,
      show Finset.range m = Finset.Ico 0 m from (Nat.Ico_zero_eq_range m).symm]
    exact Finset.sum_Ico_consecutive (fun j : ℕ => (1 : ℝ) / max (c / 2) (a + (j : ℝ) - δ))
      (Nat.zero_le N) (min_le_left m J)
  have hpart1 : ∑ j ∈ Finset.range N, (1 : ℝ) / max (c / 2) (a + (j : ℝ) - δ)
      ≤ 2 * δ / c + 1 + 2 / c := by
    have h1 : ∑ j ∈ Finset.range N, (1 : ℝ) / max (c / 2) (a + (j : ℝ) - δ)
        ≤ ∑ _j ∈ Finset.range N, (2 / c) := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      have h2 : c / 2 ≤ max (c / 2) (a + (j : ℝ) - δ) := le_max_left _ _
      calc (1 : ℝ) / max (c / 2) (a + (j : ℝ) - δ) ≤ 1 / (c / 2) :=
            one_div_le_one_div_of_le hc2 h2
        _ = 2 / c := by field_simp
    have h3 : ∑ _j ∈ Finset.range N, (2 / c) = N * (2 / c) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h4 : (N : ℝ) ≤ δ + c / 2 + 1 := by
      have h5 : (N : ℝ) ≤ (J : ℝ) := by
        rw [hN]
        exact_mod_cast min_le_right m J
      linarith
    have h6 : (0 : ℝ) ≤ 2 / c := by positivity
    calc ∑ j ∈ Finset.range N, (1 : ℝ) / max (c / 2) (a + (j : ℝ) - δ)
        ≤ ∑ _j ∈ Finset.range N, (2 / c) := h1
      _ = N * (2 / c) := h3
      _ ≤ (δ + c / 2 + 1) * (2 / c) := mul_le_mul_of_nonneg_right h4 h6
      _ = 2 * δ / c + 1 + 2 / c := by
          field_simp
  have hpart2 : ∑ j ∈ Finset.Ico N m, (1 : ℝ) / max (c / 2) (a + (j : ℝ) - δ)
      ≤ 2 / c + 1 + Real.log (m : ℝ) := by
    rcases min_choice m J with hmin | hmin
    · rw [hN, hmin, Finset.Ico_self, Finset.sum_empty]
      have hlog : 0 ≤ Real.log (m : ℝ) := by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h
          rw [Nat.cast_zero, Real.log_zero]
        · exact Real.log_nonneg (by exact_mod_cast h)
      have h2 : (0 : ℝ) ≤ 2 / c := by positivity
      linarith
    · rw [hN, hmin]
      have hstep : ∀ j ∈ Finset.Ico J m,
          (1 : ℝ) / max (c / 2) (a + (j : ℝ) - δ) ≤ 1 / (c / 2 + ((j - J : ℕ) : ℝ)) := by
        intro j hj
        obtain ⟨hjJ, hjm⟩ := Finset.mem_Ico.mp hj
        have h1 : δ + c / 2 - a ≤ (j : ℝ) := by
          have h2 : (J : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjJ
          linarith
        have hmax : max (c / 2) (a + (j : ℝ) - δ) = a + (j : ℝ) - δ := max_eq_right (by linarith)
        rw [hmax]
        have h3 : ((j - J : ℕ) : ℝ) = (j : ℝ) - (J : ℝ) := by
          rw [Nat.cast_sub hjJ]
        have h4 : c / 2 + ((j - J : ℕ) : ℝ) ≤ a + (j : ℝ) - δ := by
          rw [h3]
          linarith
        have h6 : 0 < c / 2 + ((j - J : ℕ) : ℝ) := by
          have h7 : (0 : ℝ) ≤ ((j - J : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        exact one_div_le_one_div_of_le h6 h4
      have hA := Finset.sum_le_sum hstep
      have hB : ∑ j ∈ Finset.Ico J m, (1 : ℝ) / (c / 2 + ((j - J : ℕ) : ℝ))
          = ∑ x ∈ Finset.range (m - J), (1 : ℝ) / (c / 2 + (x : ℝ)) := by
        rw [Finset.sum_Ico_eq_sum_range (fun j : ℕ => (1 : ℝ) / (c / 2 + ((j - J : ℕ) : ℝ))) J m]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Nat.add_sub_cancel_left]
      rw [hB] at hA
      have hsum2 : ∑ x ∈ Finset.range (m - J), (1 : ℝ) / (c / 2 + (x : ℝ))
          ≤ ∑ x ∈ Finset.range m, (1 : ℝ) / (c / 2 + (x : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.sub_le m J))
          (fun x _ _ => by positivity)
      have hsum3 : ∑ x ∈ Finset.range m, (1 : ℝ) / (c / 2 + (x : ℝ))
          ≤ 2 / c + 1 + Real.log (m : ℝ) := by
        rcases Nat.eq_zero_or_pos m with hm | hm
        · rw [hm, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero]
          have h1 : (0 : ℝ) ≤ 2 / c := by positivity
          linarith
        · obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
          have h0 : (1 : ℝ) / (c / 2 + (((0 : ℕ)) : ℝ)) = 2 / c := by
            rw [Nat.cast_zero, add_zero]
            field_simp
          have hA : ∀ x : ℕ, (1 : ℝ) / (c / 2 + ((((x + 1 : ℕ)) : ℝ))) ≤ 1 / ((x : ℝ) + 1) := by
            intro x
            have h1 : (x : ℝ) + 1 ≤ c / 2 + (((x + 1 : ℕ)) : ℝ) := by push_cast; linarith
            exact one_div_le_one_div_of_le (by positivity) h1
          have hB : ∑ x ∈ Finset.range M, (1 : ℝ) / (c / 2 + ((((x + 1 : ℕ)) : ℝ)))
              ≤ ∑ x ∈ Finset.range M, (1 : ℝ) / ((x : ℝ) + 1) :=
            Finset.sum_le_sum (fun x _ => hA x)
          have hC := sum_range_inv_succ_le_log M
          have hlog : Real.log (M : ℝ) ≤ Real.log ((M : ℝ) + 1) := by
            rcases Nat.eq_zero_or_pos M with hM | hM
            · rw [hM, Nat.cast_zero, Real.log_zero, zero_add, Real.log_one]
            · exact Real.log_le_log (by exact_mod_cast hM) (by linarith)
          have htarget : Real.log (((M + 1 : ℕ)) : ℝ) = Real.log ((M : ℝ) + 1) := by
            congr 1
            push_cast
            ring
          rw [Finset.sum_range_succ', h0, htarget]
          linarith
      linarith [hA, hsum2, hsum3]
  have hlogm : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.cast_zero, Real.log_zero, zero_add, Real.log_one]
    · exact Real.log_le_log (by exact_mod_cast h) (by linarith)
  calc ∑ j ∈ Finset.range m, (1 : ℝ) / max (c / 2) (a + (j : ℝ) - δ)
      = (∑ j ∈ Finset.range N, (1 : ℝ) / max (c / 2) (a + (j : ℝ) - δ))
        + (∑ j ∈ Finset.Ico N m, (1 : ℝ) / max (c / 2) (a + (j : ℝ) - δ)) := hsplit.symm
    _ ≤ (2 * δ / c + 1 + 2 / c) + (2 / c + 1 + Real.log (m : ℝ)) := add_le_add hpart1 hpart2
    _ ≤ 2 * δ / c + 2 + 4 / c + Real.log ((m : ℝ) + 1) := by
        have hrew : (2 * δ / c + 1 + 2 / c) + (2 / c + 1 + Real.log (m : ℝ))
            = 2 * δ / c + 2 + 4 / c + Real.log (m : ℝ) := by ring
        rw [hrew]
        linarith [hlogm]

/-- **Sum bound with an explicit, `c`-independent constant.**  For `c ≥ 1` and `δ ≥ 0`,
`∑_{i<k} 1/max (c/2) (|x+i| - δ) ≤ 16 (1 + log (2 + |x| + k + δ)) + 4δ/c + 4`. -/
private theorem sum_inv_max_explicit {c : ℝ} (hc : 1 ≤ c) (x δ : ℝ) (k : ℕ) (hδ : 0 ≤ δ) :
    ∑ i ∈ Finset.range k, (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ)
      ≤ 16 * (1 + Real.log (2 + |x| + (k : ℝ) + δ)) + 4 * δ / c + 4 := by
  have hc0 : 0 < c := by linarith
  set i₁ : ℕ := min k (Nat.ceil (-x)) with hi₁
  have hlow : ∀ i ∈ Finset.Ico 0 i₁, x + (i : ℝ) < 0 := by
    intro i hi
    obtain ⟨-, hii⟩ := Finset.mem_Ico.mp hi
    have h1 : i < Nat.ceil (-x) :=
      lt_of_lt_of_le hii (by rw [hi₁]; exact min_le_right k _)
    rcases le_total (-x) 0 with h | h
    · have h4 : (Nat.ceil (-x) : ℕ) = 0 := Nat.ceil_eq_zero.mpr h
      exfalso
      omega
    · have h5 : ((Nat.ceil (-x) : ℕ) : ℝ) - 1 < -x := by
        have h6 := Nat.ceil_lt_add_one h
        linarith
      have h7 : (i : ℝ) ≤ ((Nat.ceil (-x) : ℕ) : ℝ) - 1 := by
        have h8 : (i : ℝ) + 1 ≤ ((Nat.ceil (-x) : ℕ) : ℝ) := by exact_mod_cast h1
        linarith
      linarith
  have hhigh : ∀ i ∈ Finset.Ico i₁ k, 0 ≤ x + (i : ℝ) := by
    intro i hi
    obtain ⟨hii, hik⟩ := Finset.mem_Ico.mp hi
    have h2 : ((Nat.ceil (-x) : ℕ) : ℝ) ≤ (i : ℝ) := by
      rcases min_choice k (Nat.ceil (-x)) with hm | hm
      · exfalso
        rw [hi₁, hm] at hii
        omega
      · rw [hi₁, hm] at hii
        exact_mod_cast hii
    have h3 : -x ≤ ((Nat.ceil (-x) : ℕ) : ℝ) := Nat.le_ceil _
    linarith
  have hsplit : (∑ i ∈ Finset.Ico 0 i₁, (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ))
      + (∑ i ∈ Finset.Ico i₁ k, (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ))
      = ∑ i ∈ Finset.range k, (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ) := by
    rw [show Finset.range k = Finset.Ico 0 k from (Nat.Ico_zero_eq_range k).symm]
    exact Finset.sum_Ico_consecutive (fun i : ℕ => (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ))
      (Nat.zero_le i₁) (min_le_left k _)
  have hpart1 : ∑ i ∈ Finset.Ico 0 i₁, (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ)
      ≤ 2 * δ / c + 2 + 4 / c + Real.log ((i₁ : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos i₁ with h0 | hpos
    · rw [h0, Finset.Ico_self, Finset.sum_empty, Nat.cast_zero, zero_add, Real.log_one]
      have h1 : (0 : ℝ) ≤ 2 * δ / c := by positivity
      have h2 : (0 : ℝ) ≤ 4 / c := by positivity
      linarith
    · have ha : 0 ≤ -(x + (i₁ : ℝ) - 1) := by
        have h1 : x + (((i₁ - 1 : ℕ)) : ℝ) < 0 :=
          hlow (i₁ - 1) (Finset.mem_Ico.mpr ⟨Nat.zero_le _, by omega⟩)
        have h2 : (((i₁ - 1 : ℕ)) : ℝ) = (i₁ : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ i₁)]
          push_cast
          ring
        linarith
      have hrefl : ∑ i ∈ Finset.Ico 0 i₁, (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ)
          = ∑ j ∈ Finset.Ico 0 i₁,
              (1 : ℝ) / max (c / 2) (|x + (((i₁ - 1 - j : ℕ)) : ℝ)| - δ) := by
        have h := Finset.sum_Ico_reflect (fun i : ℕ => (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ))
          0 (m := i₁) (n := i₁ - 1) (by omega)
        have e1 : i₁ - 1 + 1 - i₁ = 0 := by omega
        have e2 : i₁ - 1 + 1 - 0 = i₁ := by omega
        rw [e1, e2] at h
        exact h.symm
      have hstep : ∀ j ∈ Finset.range i₁,
          (1 : ℝ) / max (c / 2) (|x + (((i₁ - 1 - j : ℕ)) : ℝ)| - δ)
            = 1 / max (c / 2) (-(x + (i₁ : ℝ) - 1) + (j : ℝ) - δ) := by
        intro j hj
        have hjlt : j < i₁ := Finset.mem_range.mp hj
        have hcast : (((i₁ - 1 - j : ℕ)) : ℝ) = (i₁ : ℝ) - 1 - (j : ℝ) := by
          rw [Nat.cast_sub (by omega : j ≤ i₁ - 1), Nat.cast_sub (by omega : 1 ≤ i₁)]
          push_cast
          ring
        have hneg : x + (((i₁ - 1 - j : ℕ)) : ℝ) < 0 :=
          hlow (i₁ - 1 - j) (Finset.mem_Ico.mpr ⟨Nat.zero_le _, by omega⟩)
        have habs : |x + (((i₁ - 1 - j : ℕ)) : ℝ)| = -(x + (i₁ : ℝ) - 1) + (j : ℝ) := by
          rw [abs_of_neg hneg, hcast]
          ring
        rw [habs]
      calc ∑ i ∈ Finset.Ico 0 i₁, (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ)
          = ∑ j ∈ Finset.Ico 0 i₁,
              (1 : ℝ) / max (c / 2) (|x + (((i₁ - 1 - j : ℕ)) : ℝ)| - δ) := hrefl
        _ = ∑ j ∈ Finset.range i₁,
              (1 : ℝ) / max (c / 2) (|x + (((i₁ - 1 - j : ℕ)) : ℝ)| - δ) := by
              rw [show Finset.Ico 0 i₁ = Finset.range i₁ from Nat.Ico_zero_eq_range i₁]
        _ = ∑ j ∈ Finset.range i₁,
              1 / max (c / 2) (-(x + (i₁ : ℝ) - 1) + (j : ℝ) - δ) :=
              Finset.sum_congr rfl (fun j hj => hstep j hj)
        _ ≤ 2 * δ / c + 2 + 4 / c + Real.log ((i₁ : ℝ) + 1) :=
              one_sided_sum_inv hc0 hδ ha i₁
  have hpart2 : ∑ i ∈ Finset.Ico i₁ k, (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ)
      ≤ 2 * δ / c + 2 + 4 / c + Real.log ((((k - i₁ : ℕ)) : ℝ) + 1) := by
    rcases lt_or_eq_of_le (show i₁ ≤ k from min_le_left k (Nat.ceil (-x))) with hlt | heq
    · have ha : 0 ≤ x + (i₁ : ℝ) :=
        hhigh i₁ (Finset.mem_Ico.mpr ⟨le_rfl, hlt⟩)
      have hstep : ∀ t ∈ Finset.range (k - i₁),
          (1 : ℝ) / max (c / 2) (|x + (((i₁ + t : ℕ)) : ℝ)| - δ)
            = 1 / max (c / 2) ((x + (i₁ : ℝ)) + (t : ℝ) - δ) := by
        intro t ht
        have hnonneg : 0 ≤ x + (((i₁ + t : ℕ)) : ℝ) :=
          hhigh (i₁ + t) (Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by
            have hh := Finset.mem_range.mp ht; omega⟩)
        have hcast : (((i₁ + t : ℕ)) : ℝ) = (i₁ : ℝ) + (t : ℝ) := by push_cast; ring
        rw [abs_of_nonneg hnonneg, hcast]
        congr 1
        ring
      calc ∑ i ∈ Finset.Ico i₁ k, (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ)
          = ∑ t ∈ Finset.range (k - i₁),
              (1 : ℝ) / max (c / 2) (|x + (((i₁ + t : ℕ)) : ℝ)| - δ) := by
              rw [Finset.sum_Ico_eq_sum_range
                (fun i : ℕ => (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ)) i₁ k]
        _ = ∑ t ∈ Finset.range (k - i₁),
              1 / max (c / 2) ((x + (i₁ : ℝ)) + (t : ℝ) - δ) :=
              Finset.sum_congr rfl (fun t ht => hstep t ht)
        _ ≤ 2 * δ / c + 2 + 4 / c + Real.log ((((k - i₁ : ℕ)) : ℝ) + 1) :=
              one_sided_sum_inv hc0 hδ ha (k - i₁)
    · rw [heq, Finset.Ico_self, Finset.sum_empty, Nat.sub_self, Nat.cast_zero, zero_add,
        Real.log_one]
      have h1 : (0 : ℝ) ≤ 2 * δ / c := by positivity
      have h2 : (0 : ℝ) ≤ 4 / c := by positivity
      linarith
  have hi₁_le : (i₁ : ℝ) ≤ |x| + 1 := by
    rcases Nat.eq_zero_or_pos i₁ with h0 | hpos
    · rw [h0]
      push_cast
      positivity
    · have h1 : x + (((i₁ - 1 : ℕ)) : ℝ) < 0 :=
        hlow (i₁ - 1) (Finset.mem_Ico.mpr ⟨Nat.zero_le _, by omega⟩)
      have h2 : (((i₁ - 1 : ℕ)) : ℝ) = (i₁ : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ i₁)]
        push_cast
        ring
      have h3 : -x ≤ |x| := neg_le_abs x
      linarith
  have hlogt : 0 ≤ Real.log (2 + |x| + (k : ℝ) + δ) := by
    refine Real.log_nonneg ?_
    have h2 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h1 : (0 : ℝ) ≤ |x| := abs_nonneg x
    linarith
  have hlogi : Real.log ((i₁ : ℝ) + 1) ≤ Real.log (2 + |x| + (k : ℝ) + δ) := by
    refine Real.log_le_log (by positivity) ?_
    have h2 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hlogk : Real.log ((((k - i₁ : ℕ)) : ℝ) + 1) ≤ Real.log (2 + |x| + (k : ℝ) + δ) := by
    refine Real.log_le_log (by positivity) ?_
    have h2 : ((k - i₁ : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k i₁
    have h3 : (0 : ℝ) ≤ |x| := abs_nonneg x
    linarith
  have hrew : (2 * δ / c + 2 + 4 / c + Real.log ((i₁ : ℝ) + 1))
      + (2 * δ / c + 2 + 4 / c + Real.log ((((k - i₁ : ℕ)) : ℝ) + 1))
      = 4 * δ / c + 4 + 8 / c + Real.log ((i₁ : ℝ) + 1)
        + Real.log ((((k - i₁ : ℕ)) : ℝ) + 1) := by ring
  calc ∑ i ∈ Finset.range k, (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ)
      = (∑ i ∈ Finset.Ico 0 i₁, (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ))
        + (∑ i ∈ Finset.Ico i₁ k, (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ)) := hsplit.symm
    _ ≤ (2 * δ / c + 2 + 4 / c + Real.log ((i₁ : ℝ) + 1))
        + (2 * δ / c + 2 + 4 / c + Real.log ((((k - i₁ : ℕ)) : ℝ) + 1)) :=
        add_le_add hpart1 hpart2
    _ = 4 * δ / c + 4 + 8 / c + Real.log ((i₁ : ℝ) + 1)
        + Real.log ((((k - i₁ : ℕ)) : ℝ) + 1) := hrew
    _ ≤ 16 * (1 + Real.log (2 + |x| + (k : ℝ) + δ)) + 4 * δ / c + 4 := by
        have h8 : 8 / c ≤ 8 := by
          rw [div_le_iff₀ hc0]
          linarith
        linarith [hlogi, hlogk, hlogt, h8]


/-- **The orbit of a point high above the real axis stays high.**  This is the analytic core of
Shishikura's A.3/(4.1.4): the chart orbit of `ζ` stays outside the disc of radius `2R` and its
real part grows at speed at least `1/2`, up to a logarithmic error whose size is controlled by
the constant `c` appearing in the hypothesis `2R + cS ≤ |Im ζ|`, `S = 1 + log (2 + ‖ζ‖)`.

The two analytic inputs are `hsum` (a bound for `∑ 1 / max (c/2) (|x+i| - δ)`;
`sum_inv_max_uniform`) and `hbudget` (the arithmetic absorption of the logarithmic error;
`budget_ineq_c`). -/
private theorem orbit_bound_aux {g : ℂ → ℂ} {N K R c C₀ : ℝ}
    (hN : 0 < N) (hK : 0 ≤ K) (hR : 0 < R) (hc0 : 0 ≤ c) (hcN : 2 * (N + 1) ≤ c)
    (hstep : ∀ v : ℂ, N < ‖v‖ → ‖g v - (v + 1)‖ ≤ K / ‖v‖ ∧ v.re + 1 / 2 ≤ (g v).re)
    (hsum : ∀ (x δ : ℝ) (k : ℕ), 0 ≤ δ →
      ∑ i ∈ Finset.range k, (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ)
        ≤ C₀ * (1 + Real.log (2 + |x| + (k : ℝ) + δ)) + 4 * δ / c + 4)
    (hbudget : ∀ (S x k D : ℝ), 1 ≤ S → D = c / 2 * S → 0 ≤ k → Real.log (2 + |x|) ≤ S →
      k ≤ max N (2 * R + 1) + 3 + |x| + D →
      K * (C₀ * (1 + Real.log (2 + |x| + k + D)) + 4 * D / c + 4) ≤ D)
    {ζ : ℂ} (hζ : 2 * R + c * (1 + Real.log (2 + ‖ζ‖)) ≤ |ζ.im|) :
    ∀ j : ℕ, 2 * R ≤ ‖(g^[j]) ζ‖ ∧
      ((g^[j]) ζ).re ≥ min ζ.re 0 + (j : ℝ) / 2 - c * (1 + Real.log (2 + (j : ℝ) + ‖ζ‖)) := by
  let w : ℕ → ℂ := fun j => (g^[j]) ζ
  change ∀ j : ℕ, 2 * R ≤ ‖w j‖ ∧
    (w j).re ≥ min ζ.re 0 + (j : ℝ) / 2 - c * (1 + Real.log (2 + (j : ℝ) + ‖ζ‖))
  let S : ℝ := 1 + Real.log (2 + ‖ζ‖)
  have hSdef : S = 1 + Real.log (2 + ‖ζ‖) := rfl
  let x : ℝ := ζ.re
  have hxdef : x = ζ.re := rfl
  let D : ℝ := c / 2 * S
  have hDdef : D = c / 2 * S := rfl
  have hS1 : 1 ≤ S := by
    have h : (0 : ℝ) ≤ Real.log (2 + ‖ζ‖) := Real.log_nonneg (by have := norm_nonneg ζ; linarith)
    rw [hSdef]
    linarith
  have hDnn : 0 ≤ D := by rw [hDdef]; exact mul_nonneg (by linarith) (by linarith)
  have hA : 2 * R + c * S ≤ |ζ.im| := by rw [hSdef]; exact hζ
  have hlogx : Real.log (2 + |x|) ≤ S := by
    have h1 : 0 < 2 + |x| := by positivity
    have h2 : 2 + |x| ≤ 2 + ‖ζ‖ := by
      have h3 : |x| ≤ ‖ζ‖ := by rw [hxdef]; exact Complex.abs_re_le_norm ζ
      linarith
    have h3 : Real.log (2 + |x|) ≤ Real.log (2 + ‖ζ‖) := Real.log_le_log h1 h2
    rw [hSdef]
    linarith
  have hmin : min ζ.re 0 ≤ x := by rw [hxdef]; exact min_le_left _ _
  have hSc : ∀ j : ℕ, D ≤ c * (1 + Real.log (2 + (j : ℝ) + ‖ζ‖)) := by
    intro j
    have h1 : S ≤ 1 + Real.log (2 + (j : ℝ) + ‖ζ‖) := by
      have h2 : 0 < 2 + ‖ζ‖ := by positivity
      have h3 : 2 + ‖ζ‖ ≤ 2 + (j : ℝ) + ‖ζ‖ := by
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      have h4 := Real.log_le_log h2 h3
      rw [hSdef]
      linarith
    have h5 : c * S ≤ c * (1 + Real.log (2 + (j : ℝ) + ‖ζ‖)) :=
      mul_le_mul_of_nonneg_left h1 hc0
    rw [hDdef]
    linarith
  have hstepw : ∀ i : ℕ, N < ‖w i‖ → ‖w (i + 1) - w i - 1‖ ≤ K / ‖w i‖ ∧
      (w i).re + 1 / 2 ≤ (w (i + 1)).re := by
    intro i hi
    have h := hstep (w i) hi
    have hidx : w (i + 1) = g (w i) := by simp only [w, Function.iterate_succ_apply']
    rw [hidx]
    exact ⟨by simpa only [sub_sub] using h.1, h.2⟩
  have htel : ∀ j : ℕ, (∀ i < j, N < ‖w i‖) →
      ‖w j - ζ - (j : ℂ)‖ ≤ ∑ i ∈ Finset.range j, K / ‖w i‖ := by
    intro j hj
    have h := iterate_sub_translate_bound hN.le hK (fun v hv => (hstep v hv).1) ζ j
      (fun i hi => by simpa only [w] using hj i hi)
    simpa only [w] using h
  have himb : ∀ (j : ℕ) (s : ℝ), (∀ i < j, N < ‖w i‖) →
      (∑ i ∈ Finset.range j, K / ‖w i‖) ≤ s → |(w j).im - ζ.im| ≤ s := by
    intro j s hj hs
    have h1 := htel j hj
    have h2 : |(w j - ζ - (j : ℂ)).im| ≤ ‖w j - ζ - (j : ℂ)‖ := Complex.abs_im_le_norm _
    have h3 : (w j - ζ - (j : ℂ)).im = (w j).im - ζ.im := by simp
    rw [h3] at h2
    linarith
  have hreb : ∀ (j : ℕ) (s : ℝ), (∀ i < j, N < ‖w i‖) →
      (∑ i ∈ Finset.range j, K / ‖w i‖) ≤ s → |(w j).re - x - (j : ℝ)| ≤ s := by
    intro j s hj hs
    have h1 := htel j hj
    have h2 : |(w j - ζ - (j : ℂ)).re| ≤ ‖w j - ζ - (j : ℂ)‖ := Complex.abs_re_le_norm _
    have h3 : (w j - ζ - (j : ℂ)).re = (w j).re - x - (j : ℝ) := by
      have h4 : (w j - ζ - (j : ℂ)).re = (w j).re - ζ.re - ((j : ℂ)).re := by simp
      have h5 : ((j : ℂ)).re = (j : ℝ) := by simp
      rw [h4, h5, ← hxdef]
    rw [h3] at h2
    linarith
  have hmaxnorm : ∀ (i : ℕ) (s : ℝ), (∀ l < i, N < ‖w l‖) →
      (∑ l ∈ Finset.range i, K / ‖w l‖) ≤ s → s ≤ D →
      max (c / 2) (|x + (i : ℝ)| - D) ≤ ‖w i‖ := by
    intro i s hi hs hsD
    have h1 := himb i s hi hs
    have h2 := hreb i s hi hs
    have him' : |ζ.im| - D ≤ |(w i).im| := by
      have h3 := abs_abs_sub_abs_le_abs_sub ((w i).im) (ζ.im)
      have h4 := le_trans h3 (le_trans h1 hsD)
      have h5 := (abs_le.mp h4).1
      linarith
    have hre' : |x + (i : ℝ)| - D ≤ |(w i).re| := by
      have h3 : |(w i).re - (x + (i : ℝ))| ≤ D := by
        have h4 : (w i).re - x - (i : ℝ) = (w i).re - (x + (i : ℝ)) := by ring
        rw [h4] at h2
        exact le_trans h2 hsD
      have h4 := abs_abs_sub_abs_le_abs_sub ((w i).re) (x + (i : ℝ))
      have h5 := le_trans h4 h3
      have h6 := (abs_le.mp h5).1
      linarith
    refine max_le ?_ ?_
    · have h5 : (c / 2) * S ≤ |ζ.im| - D := by rw [hDdef]; linarith [hA]
      have h6 : (c / 2) * 1 ≤ (c / 2) * S := mul_le_mul_of_nonneg_left hS1 (by linarith)
      have h7 : c / 2 ≤ |(w i).im| := by linarith
      exact le_trans h7 (Complex.abs_im_le_norm _)
    · exact le_trans hre' (Complex.abs_re_le_norm _)
  by_cases hxbig : max N (2 * R + 1) + 1 ≤ x
  · -- Case 1: the real part is already past the barrier
    have hregrow : ∀ j : ℕ, x + (j : ℝ) / 2 ≤ (w j).re := by
      intro j
      induction j with
      | zero => simp only [w, Function.iterate_zero_apply]; linarith
      | succ j ih =>
        have hNw : N < ‖w j‖ := by
          have h1 : N < x := by linarith [le_max_left N (2 * R + 1)]
          have h2 : x ≤ (w j).re := by
            have h3 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
            linarith
          linarith [Complex.re_le_norm (w j)]
        have hs := (hstepw j hNw).2
        push_cast
        linarith
    intro j
    have hre_j : x + (j : ℝ) / 2 ≤ (w j).re := hregrow j
    constructor
    · have h3 : 2 * R + 1 ≤ (w j).re := by
        have h5 : 2 * R + 1 ≤ max N (2 * R + 1) + 1 := by
          have := le_max_right N (2 * R + 1); linarith
        have h6 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith [hxbig, hre_j, h5, h6]
      have h4 := Complex.re_le_norm (w j)
      linarith
    · have h3 := hSc j
      have h4 : (j : ℝ) / 2 ≤ (j : ℝ) := by
        have h5 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      linarith [hmin, hre_j]
  · -- Case 2: the window
    have hZpos : 0 < max N (2 * R + 1) + 1 - x + D := by linarith
    let W : ℕ := Nat.ceil (max N (2 * R + 1) + 1 - x + D)
    have hWdef : W = Nat.ceil (max N (2 * R + 1) + 1 - x + D) := rfl
    have hWge : max N (2 * R + 1) + 1 - x + D ≤ (W : ℝ) := by
      rw [hWdef]; exact Nat.le_ceil _
    have hWlt : (W : ℝ) < max N (2 * R + 1) + 1 - x + D + 1 := by
      rw [hWdef]; exact Nat.ceil_lt_add_one hZpos.le
    have hwin : ∀ s : ℕ, s ≤ W → (∀ i ≤ s, N < ‖w i‖) ∧
        (∑ i ∈ Finset.range s, K / ‖w i‖) ≤ D := by
      intro s
      induction s with
      | zero =>
        intro _
        refine ⟨?_, ?_⟩
        · intro i hi
          have hi0 : i = 0 := Nat.le_zero.mp hi
          subst hi0
          simp only [w, Function.iterate_zero_apply]
          have h1 : N + 1 ≤ (c / 2) * S := by
            have h2 : (c / 2) * 1 ≤ (c / 2) * S :=
              mul_le_mul_of_nonneg_left hS1 (by linarith)
            have h3 : N + 1 ≤ c / 2 := by linarith
            linarith
          have h4 : (c / 2) * S ≤ 2 * R + c * S := by linarith
          have h5 : N + 1 ≤ |ζ.im| := le_trans h1 (le_trans h4 hA)
          have h6 : |ζ.im| ≤ ‖ζ‖ := Complex.abs_im_le_norm ζ
          linarith
        · simpa using hDnn
      | succ s ih =>
        intro hs
        have hle : s ≤ W := Nat.le_of_succ_le hs
        have hch_s : ∀ i ≤ s, N < ‖w i‖ := (ih hle).1
        have hsig_s : (∑ i ∈ Finset.range s, K / ‖w i‖) ≤ D := (ih hle).2
        have hsig_succ : (∑ i ∈ Finset.range (s + 1), K / ‖w i‖) ≤ D := by
          have hnorm : ∀ i ≤ s, max (c / 2) (|x + (i : ℝ)| - D) ≤ ‖w i‖ := by
            intro i hi
            have hch : ∀ l < i, N < ‖w l‖ := fun l hl => hch_s l (le_trans (le_of_lt hl) hi)
            have hmono : (∑ l ∈ Finset.range i, K / ‖w l‖) ≤ D :=
              le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hi)
                (fun l _ _ => by positivity)) hsig_s
            exact hmaxnorm i (∑ l ∈ Finset.range i, K / ‖w l‖) hch le_rfl hmono
          have hbridge : (∑ i ∈ Finset.range (s + 1), K / ‖w i‖)
              ≤ K * ∑ i ∈ Finset.range (s + 1),
                  (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - D) := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum (fun i hi => ?_)
            have hi_le : i ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hmax := hnorm i hi_le
            have hpos : 0 < max (c / 2) (|x + (i : ℝ)| - D) :=
              lt_of_lt_of_le (by linarith : (0 : ℝ) < c / 2) (le_max_left _ _)
            simpa only [div_eq_mul_inv, one_mul] using div_le_div_of_nonneg_left hK hpos hmax
          have hsumk := hsum x D (s + 1) hDnn
          have hkbound : (((s + 1 : ℕ)) : ℝ) ≤ max N (2 * R + 1) + 3 + |x| + D := by
            have h1 : (((s + 1 : ℕ)) : ℝ) ≤ (W : ℝ) := by exact_mod_cast hs
            have h3 : -x ≤ |x| := neg_le_abs x
            linarith
          have hbud := hbudget S x (((s + 1 : ℕ)) : ℝ) D hS1 hDdef (by positivity) hlogx hkbound
          calc (∑ i ∈ Finset.range (s + 1), K / ‖w i‖)
              ≤ K * ∑ i ∈ Finset.range (s + 1),
                  (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - D) := hbridge
            _ ≤ K * (C₀ * (1 + Real.log (2 + |x| + (((s + 1 : ℕ)) : ℝ) + D)) + 4 * D / c + 4) :=
                mul_le_mul_of_nonneg_left hsumk hK
            _ ≤ D := hbud
        refine ⟨?_, hsig_succ⟩
        intro i hi
        rcases Nat.lt_or_eq_of_le hi with hlt | heq
        · exact hch_s i (Nat.lt_succ_iff.mp hlt)
        · subst heq
          have hch : ∀ l < s + 1, N < ‖w l‖ := fun l hl => hch_s l (Nat.lt_succ_iff.mp hl)
          have h1 := himb (s + 1) D hch hsig_succ
          have h2 : |ζ.im| - D ≤ |(w (s + 1)).im| := by
            have h3 := abs_abs_sub_abs_le_abs_sub ((w (s + 1)).im) (ζ.im)
            have h4 := le_trans h3 h1
            have h5 := (abs_le.mp h4).1
            linarith
          have h6 : N + 1 ≤ |ζ.im| - D := by
            have h7 : (c / 2) * 1 ≤ (c / 2) * S := mul_le_mul_of_nonneg_left hS1 (by linarith)
            have h8 : N + 1 ≤ c / 2 := by linarith
            linarith [hA]
          have h9 : |(w (s + 1)).im| ≤ ‖w (s + 1)‖ := Complex.abs_im_le_norm _
          linarith
    have hchW : ∀ i ≤ W, N < ‖w i‖ := (hwin W le_rfl).1
    have hsigW : (∑ i ∈ Finset.range W, K / ‖w i‖) ≤ D := (hwin W le_rfl).2
    have hreW : x + (W : ℝ) - D ≤ (w W).re := by
      have h1 := hreb W D (fun l hl => hchW l (le_of_lt hl)) hsigW
      have h2 := (abs_le.mp h1).1
      linarith
    have hreW2 : max N (2 * R + 1) + 1 ≤ (w W).re := by linarith [hWge, hreW]
    have hgrowth : ∀ t : ℕ, (w (W + t)).re ≥ (w W).re + (t : ℝ) / 2 := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        have hre_t : max N (2 * R + 1) + 1 ≤ (w (W + t)).re := by
          have h1 : (0 : ℝ) ≤ (t : ℝ) / 2 := by positivity
          linarith [hreW2]
        have hNt : N < ‖w (W + t)‖ := by
          have h1 : N < max N (2 * R + 1) + 1 := by linarith [le_max_left N (2 * R + 1)]
          linarith [Complex.re_le_norm (w (W + t))]
        have hs := (hstepw (W + t) hNt).2
        have hidx : W + (t + 1) = (W + t) + 1 := by ring
        rw [hidx]
        push_cast
        linarith
    intro j
    by_cases hj : j ≤ W
    · have hchj : ∀ i < j, N < ‖w i‖ := fun i hi => hchW i (le_trans (le_of_lt hi) hj)
      have hsigj : (∑ i ∈ Finset.range j, K / ‖w i‖) ≤ D :=
        le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hj)
          (fun i _ _ => by positivity)) hsigW
      have h1 := himb j D hchj hsigj
      have h2 := hreb j D hchj hsigj
      have himj : |ζ.im| - D ≤ |(w j).im| := by
        have h3 := abs_abs_sub_abs_le_abs_sub ((w j).im) (ζ.im)
        have h4 := le_trans h3 h1
        have h5 := (abs_le.mp h4).1
        linarith
      have hrej : x + (j : ℝ) - D ≤ (w j).re := by
        have h3 := (abs_le.mp h2).1
        linarith
      constructor
      · have h6 : (c / 2) * 1 ≤ (c / 2) * S := mul_le_mul_of_nonneg_left hS1 (by linarith)
        have h5 : 2 * R ≤ |(w j).im| := by linarith [hA]
        exact le_trans h5 (Complex.abs_im_le_norm _)
      · have h3 := hSc j
        have h4 : (j : ℝ) / 2 ≤ (j : ℝ) := by
          have h5 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
          linarith
        linarith [hmin, hrej]
    · have hWj : W ≤ j := le_of_lt (lt_of_not_ge hj)
      have hidx : (j : ℝ) = (W : ℝ) + (((j - W : ℕ)) : ℝ) := by
        have h1 : W + (j - W) = j := Nat.add_sub_of_le hWj
        have h2 : ((W + (j - W) : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by rw [h1]
        push_cast at h2
        linarith
      have hgr : (w j).re ≥ (w W).re + (((j - W : ℕ)) : ℝ) / 2 := by
        have h1 : W + (j - W) = j := Nat.add_sub_of_le hWj
        simpa only [h1] using hgrowth (j - W)
      have hmain : x + (j : ℝ) / 2 - D ≤ (w j).re := by
        have h1 : (0 : ℝ) ≤ (W : ℝ) := Nat.cast_nonneg W
        linarith [hreW, hgr, hidx]
      constructor
      · have h1 : 2 * R + 1 ≤ (w j).re := by
          have h2 : 2 * R + 1 ≤ max N (2 * R + 1) + 1 := by
            have := le_max_right N (2 * R + 1); linarith
          have h3 : (0 : ℝ) ≤ (((j - W : ℕ)) : ℝ) / 2 := by positivity
          linarith [hreW2, hgr, h2, h3]
        linarith [Complex.re_le_norm (w j)]
      · have h3 := hSc j
        linarith [hmin, hmain, h3]

/-- **The orbit bound of Shishikura A.3/(4.1.4).**  For a parabolic germ with quantitative bounds
`ParabolicBounds f h a r A A'` and every `R > 0` there is a constant `c ≥ 0` so that every point
`ζ` of the chart plane lying above the real axis at height `2R + c (1 + log (2 + ‖ζ‖))` has its
whole chart orbit outside the disc of radius `2R`, and the real part of the `j`-th iterate is at
least `min ζ.re 0 + j/2 - c (1 + log (2 + j + ‖ζ‖))`. -/
theorem orbit_bound {f : ℂ → ℂ} {h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∀ R : ℝ, 0 < R → ∃ c : ℝ, 0 ≤ c ∧
      ∀ ζ : ℂ, 2 * R + c * (1 + Real.log (2 + ‖ζ‖)) ≤ |ζ.im| → ∀ j : ℕ,
        2 * R ≤ ‖(Work.FatouCoord.wMap f)^[j] ζ‖ ∧
        ((Work.FatouCoord.wMap f)^[j] ζ).re ≥
          min ζ.re 0 + (j : ℝ) / 2 - c * (1 + Real.log (2 + (j : ℝ) + ‖ζ‖)) := by
  obtain ⟨N, K, hN, hK, hstep⟩ := step_bound hb
  intro R hR
  obtain ⟨c, hc2, hcN, -, hbudget⟩ :=
    budget_ineq_c (K := K) (C := 16) (N := N) (R := R) hK (by norm_num) hN.le hR.le
  have hc0 : 0 ≤ c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have hsum : ∀ (x δ : ℝ) (k : ℕ), 0 ≤ δ →
      ∑ i ∈ Finset.range k, (1 : ℝ) / max (c / 2) (|x + (i : ℝ)| - δ)
        ≤ 16 * (1 + Real.log (2 + |x| + (k : ℝ) + δ)) + 4 * δ / c + 4 :=
    fun x δ k hδ => sum_inv_max_explicit hc1 x δ k hδ
  exact ⟨c, hc0, fun ζ hζ j =>
    orbit_bound_aux hN hK hR hc0 hcN hstep hsum hbudget hζ j⟩

end

end Work.Parab.coordData
