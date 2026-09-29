/-
# The Riemann sums of the model function of Lemma `lcm-2`

This module proves the paper's "horizontal integration" passage: the Riemann sums of the model
function `modelFun w` of `Submission.CDT.IntegratedLcm` converge to its integral, i.e. (for `1 ≤ m`)
to the paper's integrated lcm cost `I_0^m(w)/m` (`tendsto_riemannSum_modelFun_integratedLcm`).

The model function is piecewise affine on the grid `0, 1, 1+B, 1+2B, …` with `B = max 1 w`:

* `harmonicFun w t = Σ_{h ≤ ⌊(t-1)/B⌋} 1/h` is constant `Σ_{h≤k} 1/h` on `[1+kB, 1+(k+1)B)`;
* `correctionFun w t = max(t/⌊(t+max 0 (w-1))/B⌋ - w, 0)` equals `max(t/(k+1) - w, 0)` there
  (the two floors agree on the grid because `1 + max(0,w-1) = max(1,w)`);
* the two branches of the *definition* of `modelFun` agree at the grid points, so the piecewise
  formula even holds on the closed intervals `[a k, a (k+1)]` (`modelFun_eq_piece_closed`).

Hence `modelFun w` is 1-Lipschitz on each piece (`abs_modelFun_sub_le_grid`) and bounded by
`Σ_{h≤N} 1/h + max (m-w) 0` on `[0,m]` (`abs_modelFun_le`), so
`Submission.CDT.RiemannSum.tendsto_riemannSum_of_lipschitz_pieces` applies.
-/
import Mathlib
import Submission.CDT.IntegratedLcm
import Submission.CDT.RiemannSum

namespace Submission.CDT.IntegratedLcm

/-- The step `B = max 1 w` of the model function. -/
noncomputable def stepB (w : ℝ) : ℝ := max 1 w

theorem one_le_stepB (w : ℝ) : 1 ≤ stepB w := le_max_left _ _

theorem stepB_pos (w : ℝ) : 0 < stepB w := lt_of_lt_of_le one_pos (one_le_stepB w)

theorem stepB_sub_one (w : ℝ) : stepB w - 1 = max 0 (w - 1) := by
  rcases le_total 1 w with h | h
  · rw [stepB, max_eq_right h, max_eq_right (by linarith)]
  · rw [stepB, max_eq_left h, max_eq_left (by linarith)]
    norm_num

/-- The grid of the model function: `0, 1, 1+B, 1+2B, …`. -/
noncomputable def modelGrid (w : ℝ) : ℕ → ℝ
  | 0 => 0
  | (k + 1) => 1 + (k : ℝ) * stepB w

@[simp] theorem modelGrid_zero (w : ℝ) : modelGrid w 0 = 0 := rfl

theorem modelGrid_succ (w : ℝ) (k : ℕ) : modelGrid w (k + 1) = 1 + (k : ℝ) * stepB w := rfl

theorem modelGrid_lt_succ (w : ℝ) (i : ℕ) : modelGrid w i < modelGrid w (i + 1) := by
  cases i with
  | zero => simp [modelGrid_succ]
  | succ k =>
    rw [modelGrid_succ, modelGrid_succ]
    have h : 0 < stepB w := stepB_pos w
    push_cast
    nlinarith

theorem harmonicFun_eq_piece (w : ℝ) (k : ℕ) (t : ℝ)
    (ht1 : 1 + (k : ℝ) * stepB w ≤ t) (ht2 : t < 1 + ((k : ℝ) + 1) * stepB w) :
    harmonicFun w t = ∑ h ∈ Finset.Icc 1 k, (1:ℝ)/h := by
  simp only [harmonicFun, stepB] at ht1 ht2 ⊢
  have hB : 0 < max 1 w := by positivity
  have h1 : (k : ℝ) ≤ (t - 1) / max 1 w := by
    rw [le_div_iff₀ hB]; linarith
  have h2 : (t - 1) / max 1 w < (k : ℝ) + 1 := by
    rw [div_lt_iff₀ hB]; linarith
  have h3 : 0 ≤ (t - 1) / max 1 w := le_trans (by positivity) h1
  rw [(Nat.floor_eq_iff h3).mpr ⟨h1, h2⟩]

theorem correctionFun_eq_piece (w : ℝ) (k : ℕ) (t : ℝ)
    (ht1 : 1 + (k : ℝ) * stepB w ≤ t) (ht2 : t < 1 + ((k : ℝ) + 1) * stepB w) :
    correctionFun w t = max (t / ((k : ℝ) + 1) - w) 0 := by
  simp only [stepB] at ht1 ht2 ⊢
  have hB : 0 < max 1 w := by positivity
  have hc : max 0 (w - 1) = max 1 w - 1 := by
    rcases le_total 1 w with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]
    · rw [max_eq_left h, max_eq_left (by linarith)]
      norm_num
  unfold correctionFun
  rw [hc]
  congr 1
  have h1 : (k : ℝ) + 1 ≤ (t + (max 1 w - 1)) / max 1 w := by
    rw [le_div_iff₀ hB]; linarith
  have h2 : (t + (max 1 w - 1)) / max 1 w < (k : ℝ) + 1 + 1 := by
    rw [div_lt_iff₀ hB]; linarith
  have ht1' : 1 ≤ t := by
    have : 0 ≤ (k:ℝ) * max 1 w := mul_nonneg (by positivity) (by positivity)
    linarith
  have h3 : 0 ≤ (t + (max 1 w - 1)) / max 1 w :=
    div_nonneg (by linarith [le_max_left (1:ℝ) w]) (le_of_lt hB)
  have hfloor : ⌊(t + (max 1 w - 1)) / max 1 w⌋₊ = k + 1 := by
    rw [Nat.floor_eq_iff h3]
    exact ⟨by push_cast; linarith, by push_cast; linarith⟩
  rw [hfloor]
  push_cast
  ring_nf

theorem modelFun_eq_piece (w : ℝ) (k : ℕ) (t : ℝ)
    (ht1 : 1 + (k : ℝ) * stepB w ≤ t) (ht2 : t < 1 + ((k : ℝ) + 1) * stepB w) :
    modelFun w t = (∑ h ∈ Finset.Icc 1 k, (1:ℝ)/h) + max (t / ((k : ℝ) + 1) - w) 0 := by
  have hB : 1 ≤ stepB w := one_le_stepB w
  have h1 : 1 ≤ t := by
    have h0 : 0 ≤ (k:ℝ) * stepB w := mul_nonneg (by positivity) (le_of_lt (stepB_pos w))
    linarith
  rw [modelFun]
  by_cases ht : t ≤ 1
  · rw [if_pos ht]
    have ht1' : t = 1 := le_antisymm ht h1
    subst ht1'
    have hk : k = 0 := by
      by_contra hk0
      have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
      have : 0 < (k:ℝ) * stepB w := mul_pos hkpos (stepB_pos w)
      linarith
    subst hk
    simp
  · rw [if_neg ht]
    rw [harmonicFun_eq_piece w k t ht1 ht2, correctionFun_eq_piece w k t ht1 ht2]

section Closed

theorem modelFun_eq_grid_right (w : ℝ) (k : ℕ) :
    modelFun w (1 + ((k : ℝ) + 1) * stepB w)
      = (∑ h ∈ Finset.Icc 1 k, (1:ℝ)/h)
        + max ((1 + ((k : ℝ) + 1) * stepB w) / ((k : ℝ) + 1) - w) 0 := by
  simp only [stepB] at *
  have hB : 0 < max 1 w := by positivity
  have hgt : 1 < 1 + ((k : ℝ) + 1) * max 1 w := by
    have : 0 < ((k:ℝ)+1) * max 1 w := mul_pos (by positivity) hB
    linarith
  have hharm : harmonicFun w (1 + ((k : ℝ) + 1) * max 1 w) = ∑ h ∈ Finset.Icc 1 (k+1), (1:ℝ)/h := by
    simp only [harmonicFun]
    have hnn : 0 ≤ ((1 + ((k:ℝ)+1) * max 1 w) - 1) / max 1 w :=
      div_nonneg (by nlinarith [hB, Nat.cast_nonneg (α := ℝ) k, le_max_left (1:ℝ) w])
        (le_of_lt hB)
    have hf : ⌊((1 + ((k:ℝ)+1) * max 1 w) - 1) / max 1 w⌋₊ = k + 1 := by
      rw [Nat.floor_eq_iff hnn]
      exact ⟨by rw [le_div_iff₀ hB]; push_cast; ring_nf; linarith,
        by rw [div_lt_iff₀ hB]; push_cast; ring_nf; nlinarith [hB]⟩
    rw [hf]
  have hcor : correctionFun w (1 + ((k : ℝ) + 1) * max 1 w)
      = max ((1 + ((k:ℝ)+1) * max 1 w) / ((k:ℝ) + 2) - w) 0 := by
    unfold correctionFun
    congr 1
    have hc : max 0 (w - 1) = max 1 w - 1 := by
      rcases le_total 1 w with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)]
      · rw [max_eq_left h, max_eq_left (by linarith)]
        norm_num
    rw [hc]
    have hnn : 0 ≤ ((1 + ((k:ℝ)+1) * max 1 w) + (max 1 w - 1)) / max 1 w :=
      div_nonneg (by nlinarith [hB, Nat.cast_nonneg (α := ℝ) k, le_max_left (1:ℝ) w])
        (le_of_lt hB)
    have hf : ⌊((1 + ((k:ℝ)+1) * max 1 w) + (max 1 w - 1)) / max 1 w⌋₊ = k + 2 := by
      rw [Nat.floor_eq_iff hnn]
      exact ⟨by rw [le_div_iff₀ hB]; push_cast; ring_nf; linarith,
        by rw [div_lt_iff₀ hB]; push_cast; ring_nf; nlinarith [hB]⟩
    rw [hf]
    push_cast
    ring_nf
  rw [modelFun_of_lt w _ hgt, hharm, hcor]
  have hsum : (∑ h ∈ Finset.Icc 1 (k+1), (1:ℝ)/h)
      = (∑ h ∈ Finset.Icc 1 k, (1:ℝ)/h) + 1/((k:ℝ)+1) := by
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    push_cast
    ring
  rw [hsum]
  rcases le_total 1 w with hw | hw
  · rw [max_eq_right hw]
    have hz : max ((1 + ((k:ℝ)+1) * w) / ((k:ℝ) + 2) - w) 0 = 0 := by
      rw [max_eq_right (by rw [sub_nonpos, div_le_iff₀ (by positivity)]; nlinarith)]
    have hz2 : max ((1 + ((k:ℝ)+1) * w) / ((k:ℝ) + 1) - w) 0 = 1/((k:ℝ)+1) := by
      have h : (1 + ((k:ℝ)+1) * w) / ((k:ℝ) + 1) - w = 1/((k:ℝ)+1) := by
        field_simp
        ring
      rw [h, max_eq_left (by positivity)]
    rw [hz, hz2]
    ring
  · rw [max_eq_left hw]
    have hz : max ((1 + ((k:ℝ)+1) * (1:ℝ)) / ((k:ℝ) + 2) - w) 0 = 1 - w := by
      have h : (1 + ((k:ℝ)+1) * (1:ℝ)) / ((k:ℝ) + 2) - w = 1 - w := by
        have hk : (1 + ((k:ℝ)+1) * (1:ℝ)) = ((k:ℝ) + 2) := by ring
        rw [hk, div_self (by positivity)]
      rw [h, max_eq_left (by linarith)]
    have hz2 : max ((1 + ((k:ℝ)+1) * (1:ℝ)) / ((k:ℝ) + 1) - w) 0 = 1 + 1/((k:ℝ)+1) - w := by
      have h : (1 + ((k:ℝ)+1) * (1:ℝ)) / ((k:ℝ) + 1) - w = 1 + 1/((k:ℝ)+1) - w := by
        have hk : (1 + ((k:ℝ)+1) * (1:ℝ)) = ((k:ℝ) + 2) := by ring
        have hk' : ((k:ℝ) + 2) / ((k:ℝ) + 1) = 1 + 1/((k:ℝ)+1) := by
          field_simp; ring
        rw [hk, hk']
      rw [h, max_eq_left (by linarith [hw, one_div_pos.mpr (by positivity : (0:ℝ) < (k:ℝ)+1)])]
    rw [hz, hz2]
    ring


theorem modelFun_eq_piece_closed (w : ℝ) (k : ℕ) (t : ℝ)
    (ht1 : 1 + (k : ℝ) * stepB w ≤ t) (ht2 : t ≤ 1 + ((k : ℝ) + 1) * stepB w) :
    modelFun w t = (∑ h ∈ Finset.Icc 1 k, (1:ℝ)/h) + max (t / ((k : ℝ) + 1) - w) 0 := by
  rcases lt_or_eq_of_le ht2 with h | h
  · exact modelFun_eq_piece w k t ht1 h
  · subst h
    exact modelFun_eq_grid_right w k

theorem abs_modelFun_sub_le_first (w : ℝ) {t u : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hu : u ∈ Set.Icc (0:ℝ) 1) :
    |modelFun w t - modelFun w u| ≤ |t - u| := by
  rw [modelFun_of_le_one w t ht.2, modelFun_of_le_one w u hu.2]
  calc |max (t - w) 0 - max (u - w) 0| ≤ |(t - w) - (u - w)| := abs_max_sub_max_le_abs _ _ _
    _ = |t - u| := by ring_nf

theorem abs_modelFun_sub_le_piece (w : ℝ) (k : ℕ) {t u : ℝ}
    (ht1 : 1 + (k : ℝ) * stepB w ≤ t) (ht2 : t ≤ 1 + ((k : ℝ) + 1) * stepB w)
    (hu1 : 1 + (k : ℝ) * stepB w ≤ u) (hu2 : u ≤ 1 + ((k : ℝ) + 1) * stepB w) :
    |modelFun w t - modelFun w u| ≤ |t - u| := by
  have hpos : (0:ℝ) < (k:ℝ) + 1 := by positivity
  rw [modelFun_eq_piece_closed w k t ht1 ht2, modelFun_eq_piece_closed w k u hu1 hu2]
  have hA : |(∑ h ∈ Finset.Icc 1 k, (1:ℝ)/h) + max (t / ((k:ℝ) + 1) - w) 0
      - ((∑ h ∈ Finset.Icc 1 k, (1:ℝ)/h) + max (u / ((k:ℝ) + 1) - w) 0)|
      = |max (t / ((k:ℝ) + 1) - w) 0 - max (u / ((k:ℝ) + 1) - w) 0| := by ring_nf
  rw [hA]
  calc |max (t / ((k:ℝ) + 1) - w) 0 - max (u / ((k:ℝ) + 1) - w) 0|
      ≤ |(t / ((k:ℝ) + 1) - w) - (u / ((k:ℝ) + 1) - w)| := abs_max_sub_max_le_abs _ _ _
    _ = |t - u| / ((k:ℝ) + 1) := by
        rw [show (t / ((k:ℝ) + 1) - w) - (u / ((k:ℝ) + 1) - w)
          = (t - u) / ((k:ℝ) + 1) by ring, abs_div, abs_of_pos hpos]
    _ ≤ |t - u| := by
        rw [div_le_iff₀ hpos]
        nlinarith [abs_nonneg (t - u)]

theorem abs_modelFun_sub_le_grid (w : ℝ) {i : ℕ} {t u : ℝ}
    (ht : t ∈ Set.Icc (modelGrid w i) (modelGrid w (i+1)))
    (hu : u ∈ Set.Icc (modelGrid w i) (modelGrid w (i+1))) :
    |modelFun w t - modelFun w u| ≤ |t - u| := by
  cases i with
  | zero =>
    simp only [modelGrid_zero, modelGrid_succ, Nat.cast_zero, zero_mul, add_zero] at ht hu
    exact abs_modelFun_sub_le_first w ht hu
  | succ k =>
    simp only [modelGrid_succ, Nat.cast_add, Nat.cast_one] at ht hu
    exact abs_modelFun_sub_le_piece w k ht.1 ht.2 hu.1 hu.2

theorem abs_modelFun_le (w m : ℝ) (hm : 0 ≤ m) {N : ℕ} (hN : 1 ≤ N)
    (hNm : m ≤ modelGrid w N) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) m) :
    |modelFun w t| ≤ (∑ h ∈ Finset.Icc 1 N, (1:ℝ)/h) + max (m - w) 0 := by
  have hM : 0 ≤ (∑ h ∈ Finset.Icc 1 N, (1:ℝ)/h) + max (m - w) 0 :=
    add_nonneg (Finset.sum_nonneg fun h _ => by positivity) (le_max_right _ _)
  have hB : 0 < stepB w := stepB_pos w
  rw [abs_of_nonneg (modelFun_nonneg w t)]
  by_cases ht1 : t ≤ 1
  · rw [modelFun_of_le_one w t ht1]
    exact le_trans (max_le_max (le_trans (sub_le_sub_right ht.2 w) le_rfl) le_rfl)
      (le_add_of_nonneg_left (Finset.sum_nonneg fun h _ => by positivity))
  · have ht1' : 1 < t := not_le.mp ht1
    have hNm' : modelGrid w N = 1 + ((N:ℝ) - 1) * stepB w := by
      rcases N with _ | M
      · omega
      · rw [modelGrid_succ]; push_cast; ring
    have hk1 : 1 + ((⌊(t - 1) / stepB w⌋₊ : ℕ) : ℝ) * stepB w ≤ t := by
      have h : ((⌊(t - 1) / stepB w⌋₊ : ℕ) : ℝ) ≤ (t - 1) / stepB w :=
        Nat.floor_le (by apply div_nonneg _ (le_of_lt hB); linarith)
      rw [le_div_iff₀ hB] at h
      linarith
    have hk2 : t < 1 + (((⌊(t - 1) / stepB w⌋₊ : ℕ) : ℝ) + 1) * stepB w := by
      have h : (t - 1) / stepB w < ((⌊(t - 1) / stepB w⌋₊ : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      rw [div_lt_iff₀ hB] at h
      linarith
    have hkN : ⌊(t - 1) / stepB w⌋₊ ≤ N - 1 := by
      have h2 : ((⌊(t - 1) / stepB w⌋₊ : ℕ) : ℝ) ≤ (t - 1) / stepB w :=
        Nat.floor_le (by apply div_nonneg _ (le_of_lt hB); linarith)
      have h1 : (t - 1) / stepB w < (N : ℝ) := by
        have ht2 : t ≤ modelGrid w N := le_trans ht.2 hNm
        rw [hNm'] at ht2
        rw [div_lt_iff₀ hB]
        linarith
      have h3 : ((⌊(t - 1) / stepB w⌋₊ : ℕ) : ℝ) < N := lt_of_le_of_lt h2 h1
      have h4 : ⌊(t - 1) / stepB w⌋₊ < N := by exact_mod_cast h3
      omega
    rw [modelFun_of_lt w t ht1',
      harmonicFun_eq_piece w ⌊(t - 1) / stepB w⌋₊ t hk1 hk2,
      correctionFun_eq_piece w ⌊(t - 1) / stepB w⌋₊ t hk1 hk2]
    have hsum : (∑ h ∈ Finset.Icc 1 ⌊(t - 1) / stepB w⌋₊, (1:ℝ)/h)
        ≤ ∑ h ∈ Finset.Icc 1 N, (1:ℝ)/h :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (le_trans hkN (Nat.sub_le N 1)))
        (fun _ _ _ => by positivity)
    have hcor : max (t / (((⌊(t - 1) / stepB w⌋₊ : ℕ) : ℝ) + 1) - w) 0 ≤ max (m - w) 0 := by
      refine max_le ?_ (le_max_right _ _)
      have hle : t / (((⌊(t - 1) / stepB w⌋₊ : ℕ) : ℝ) + 1) ≤ m := by
        rcases Nat.eq_zero_or_pos ⌊(t - 1) / stepB w⌋₊ with h | h
        · rw [h]; push_cast; linarith [ht.2]
        · have h1 : (1:ℝ) ≤ ((⌊(t - 1) / stepB w⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
          rw [div_le_iff₀ (by linarith : (0:ℝ) < ((⌊(t - 1) / stepB w⌋₊ : ℕ) : ℝ) + 1)]
          nlinarith [ht.2, ht1'.le, h1]
      linarith [le_max_left (m - w) 0]
    linarith


/-! ### The Riemann-sum passage for the model function -/

theorem modelGrid_eventually_ge (w m : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ m ≤ modelGrid w N := by
  refine ⟨⌈(m - 1) / stepB w⌉₊ + 1, by omega, ?_⟩
  rw [modelGrid_succ]
  have h1 : (m - 1) / stepB w ≤ ((⌈(m - 1) / stepB w⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hB : 0 < stepB w := stepB_pos w
  rw [div_le_iff₀ hB] at h1
  linarith

theorem sum_nonneg_Icc (N : ℕ) : 0 ≤ (∑ h ∈ Finset.Icc 1 N, (1:ℝ)/h) :=
  Finset.sum_nonneg fun h _ => by positivity

theorem tendsto_riemannSum_modelFun (w m : ℝ) (hm : 0 < m) :
    Filter.Tendsto (fun d : ℕ =>
        (∑ j ∈ Finset.Icc 1 d, modelFun w (m * (j : ℝ) / (d : ℝ))) / (d : ℝ))
      Filter.atTop (nhds ((∫ t in (0 : ℝ)..m, modelFun w t) / m)) := by
  obtain ⟨N, hN1, hNm⟩ := modelGrid_eventually_ge w m
  have hL : 0 ≤ (∑ h ∈ Finset.Icc 1 N, (1:ℝ)/h) + max (m - w) 0 + 1 := by
    linarith [sum_nonneg_Icc N, le_max_right (m - w) 0]
  exact tendsto_riemannSum_of_lipschitz_pieces hm (fun i _ => modelGrid_lt_succ w i) (modelGrid_zero w) hNm hL
    (fun t ht => by
      have h1 := abs_modelFun_le w m hm.le hN1 hNm ht
      linarith [sum_nonneg_Icc N, le_max_right (m - w) 0])
    (fun i _ t ht u hu => by
      have h1 : |modelFun w t - modelFun w u| ≤ |t - u| := abs_modelFun_sub_le_grid w ht hu
      have h2 : (1:ℝ) ≤ (∑ h ∈ Finset.Icc 1 N, (1:ℝ)/h) + max (m - w) 0 + 1 := by
        linarith [sum_nonneg_Icc N, le_max_right (m - w) 0]
      calc |modelFun w t - modelFun w u| ≤ |t - u| := h1
        _ = 1 * |t - u| := by ring
        _ ≤ ((∑ h ∈ Finset.Icc 1 N, (1:ℝ)/h) + max (m - w) 0 + 1) * |t - u| :=
            mul_le_mul_of_nonneg_right h2 (abs_nonneg _))

/-- **The Riemann sums of the model function converge to the paper's integrated lcm cost.** -/
theorem tendsto_riemannSum_modelFun_integratedLcm (w m : ℝ) (hm : 1 ≤ m) :
    Filter.Tendsto (fun d : ℕ =>
        (∑ j ∈ Finset.Icc 1 d, modelFun w (m * (j : ℝ) / (d : ℝ))) / (d : ℝ))
      Filter.atTop (nhds (integratedLcm 0 m w / m)) := by
  have h := tendsto_riemannSum_modelFun w m (lt_of_lt_of_le one_pos hm)
  rwa [← integratedLcm_zero_left m w hm] at h

end Closed

end Submission.CDT.IntegratedLcm
