import Mathlib
import Submission.Work.Diff.Alg.Pinch.Chat_shift_inclusion_any
import Submission.Work.Diff.Alg.Pinch.chat_shift_threshold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The uniform shift inclusion for the Brendle–Schoen family Ĉ(s) on a window of `s`

The Brendle–Schoen pinching family `Chat n s = Ĉ(s)` (`s > 0`) shrinks to the ray `ℝ₊ • Iso n` as
`s → ∞`, and the round sphere `Iso n` is a *relative interior* point of every `Ĉ(s)`.  The
quantitative content is the "shift inclusion"

`R + Iso n ∈ Ĉ(s)`,  `scalAlg R ≤ N`  ⟹  `R + 2 • Iso n ∈ Ĉ(s + δ)`

for `δ` below an explicit threshold depending on `n`, `N` and `s`
(`Work.Diff.Alg.Pinch.chat_shift_threshold`, a quantitative form of
`Work.Diff.Alg.Pinch.Chat_shift_inclusion_any`).

This file deduces the *uniform* form needed by the pinching-set machinery: for every `ε > 0` and
`N > 0` there is a single `δ₁ > 0` such that the shift works simultaneously for every `s` in the
window `[ε, 1/2]` and every `δ ∈ (0, δ₁]`.

The point is that on the window `s ≤ 1/2` all three thresholds of `chat_shift_threshold` are
monotone in `s` in the favourable direction:

* the `a`-parameter is `anyAA n s = chatA n s` there, which is nondecreasing, so the `K`-threshold
  `1/(2 K(s) C_EF C_T M)` is *smallest* at `s = 1/2`;
* the `p`-defect bound `c0(s) = min (1/(1+(n-2)(s+1)²)) (4/((n-2)+8(s+1)))` is nonincreasing, so the
  `L`-threshold `L(s) = (1/2/K(s))(n-1)c0(s)` is again *smallest* at `s = 1/2`;
* the remaining two thresholds `1` and `n/(4·Ca·M)` do not depend on `s` at all.

Hence the threshold at `s = 1/2` works for the whole window, and the claim follows by substituting
the hypotheses of `chat_shift_threshold` with the window-uniform constants
`Kb = K(1/2)`, `cb = c0(1/2)`, `Lb = L(1/2)` and
`δ₁ := min 1 (min (n/(4 Ca M)) (min (1/(2 Kb C_EF C_T M)) (Lb/(M D2))))`.

Note that `Chat n ·` is *not* monotone in `s` (`Work.Diff.Alg.Pinch.Chat_mono` is false, see
`Chat_mono_counterexample`), so the argument really has to go through the explicit thresholds.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg Work.Diff.Alg.Pinch.ChatAny

set_option maxHeartbeats 8000000

variable {n : ℕ}

/-- On the window `0 < s ≤ 1/2` the `a`-parameter `anyAA n ·` of `Ĉ(·)` is nondecreasing. -/
lemma anyAA_le_anyAA_half (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (hshalf : s ≤ 1 / 2) :
    ChatAny.anyAA n s ≤ ChatAny.anyAA n (1 / 2) := by
  rw [ChatAny.anyAA_eq, ChatAny.anyAA_eq, if_pos hshalf, if_pos le_rfl]
  exact (chatA_mono_lip n hn hs.le hshalf le_rfl).1

/-- The `p`-defect bound `c0(s) = min (1/(1+(n-2)(s+1)²)) (4/((n-2)+8(s+1)))` is nonincreasing on
`(0, 1/2]`. -/
lemma wscb_le_c0 (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (hshalf : s ≤ 1 / 2) :
    min (1 / (1 + ((n : ℝ) - 2) * (1 / 2 + 1) ^ 2)) (4 / (((n : ℝ) - 2) + 8 * (1 / 2 + 1)))
      ≤ min (1 / (1 + ((n : ℝ) - 2) * (s + 1) ^ 2)) (4 / (((n : ℝ) - 2) + 8 * (s + 1))) := by
  have hc : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  refine le_min ?_ ?_
  · refine le_trans (min_le_left _ _) ?_
    refine one_div_le_one_div_of_le ?_ ?_
    · nlinarith [hc, sq_nonneg (s + 1)]
    · have h3 : (s + 1) ^ 2 ≤ (1 / 2 + 1) ^ 2 := by nlinarith
      nlinarith [hc, h3]
  · refine le_trans (min_le_right _ _) ?_
    refine div_le_div_of_nonneg_left (by norm_num) ?_ ?_
    · nlinarith [hc, hs]
    · linarith

theorem Chat_window_shift (n : ℕ) (hn : 2 ≤ n) (ε N : ℝ) (hε : 0 < ε) (hN : 0 < N) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      ∀ s : ℝ, ε ≤ s → s ≤ 1 / 2 → ∀ R : Submission.Diff.Alg.Curv4 n,
        R + Submission.Diff.Alg.Iso n ∈ Work.Diff.Alg.Pinch.Chat n s →
        Submission.Diff.Alg.scalAlg R ≤ N →
        R + (2 : ℝ) • Submission.Diff.Alg.Iso n ∈ Work.Diff.Alg.Pinch.Chat n (s + δ) := by
  by_cases hε2 : ε ≤ 1 / 2
  · -- the window is nonempty: use the threshold at `s = 1/2`
    obtain ⟨C_EF, hC_EFpos, hC_EF⟩ := EF_algCurv_bound n
    obtain ⟨C_T₀, hC_T₀0, hC_T₀⟩ := ChatShift.knProd_ric0_norm_bound n
    obtain ⟨C_ric₀, hC_ric₀0, hC_ric₀⟩ := ChatShift.ric0_form_bound n
    set C_T : ℝ := max C_T₀ 1 with hC_Tdef
    set C_ric : ℝ := max C_ric₀ 1 with hC_ricdef
    have hC_Tpos : 0 < C_T := lt_max_iff.mpr (Or.inr one_pos)
    have hC_ricpos : 0 < C_ric := lt_max_iff.mpr (Or.inr one_pos)
    have hC_T : ∀ S : Curv4 n, IsAlgCurv S → InPIC2 S →
        ‖knProd (ric0 S) (id2 n)‖ ≤ C_T * scalAlg S := by
      intro S h1 h2
      exact (hC_T₀ S h1 h2).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) ((inPIC2_metric_basic n).2.2 S h2))
    have hC_ric : ∀ S : Curv4 n, IsAlgCurv S → InPIC2 S → ∀ v : Fin n → ℝ,
        |∑ i, ∑ j, ric0 S i j * v i * v j| ≤ C_ric * scalAlg S * (∑ i, v i * v i) := by
      intro S h1 h2 v
      refine (hC_ric₀ S h1 h2 v).trans ?_
      have hσ : 0 ≤ scalAlg S := (inPIC2_metric_basic n).2.2 S h2
      have hV : 0 ≤ ∑ i, v i * v i := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hσ) hV
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hc : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
    -- the `s = 1/2` values of the thresholds
    set M : ℝ := N + (n : ℝ) * ((n : ℝ) - 1) with hMdef
    set Ca : ℝ := (n : ℝ) / 2 + 1 with hCadef
    set Kb : ℝ := 1 + 2 * ((n : ℝ) - 1) * (anyAA n (1 / 2) + Ca) with hKbdef
    set cb : ℝ := min (1 / (1 + ((n : ℝ) - 2) * (1 / 2 + 1) ^ 2))
      (4 / (((n : ℝ) - 2) + 8 * (1 / 2 + 1))) with hcbdef
    set Lb : ℝ := 1 / 2 / Kb * ((n : ℝ) - 1) * cb with hLbdef
    set D2 : ℝ := ((n : ℝ) - 2) * C_ric + 1 with hD2def
    have hMpos : 0 < M := by rw [hMdef]; positivity
    have hCapos : 0 < Ca := by rw [hCadef]; positivity
    have hKb1 : 1 ≤ Kb := by
      rw [hKbdef]
      have h1 : 0 ≤ (n : ℝ) - 1 := le_of_lt hn1
      have h2 : 0 ≤ anyAA n (1 / 2) + Ca := by
        have h3 := anyAA_nonneg n hn (by norm_num : (0 : ℝ) ≤ 1 / 2)
        linarith [hCapos]
      nlinarith
    have hKbpos : 0 < Kb := lt_of_lt_of_le one_pos hKb1
    have hcbpos : 0 < cb := by
      rw [hcbdef]
      exact lt_min (one_div_pos.mpr (by nlinarith [hc, sq_nonneg (1 / 2 + 1)]))
        (div_pos (by norm_num) (by nlinarith [hc]))
    have hLbpos : 0 < Lb := by rw [hLbdef]; positivity
    have hD2pos : 0 < D2 := by rw [hD2def]; nlinarith [mul_nonneg hc hC_ricpos.le]
    set δ₁ : ℝ := min 1 (min (n / (4 * Ca * M)) (min (1 / (2 * Kb * C_EF * C_T * M))
      (Lb / (M * D2)))) with hδ₁def
    have hδ₁pos : 0 < δ₁ := by
      rw [hδ₁def]
      refine lt_min one_pos (lt_min ?_ (lt_min ?_ ?_))
      · exact div_pos hn0 (by positivity)
      · exact one_div_pos.mpr (by positivity)
      · exact div_pos hLbpos (by positivity)
    refine ⟨δ₁, hδ₁pos, ?_⟩
    intro δ hδ0 hδle s hs hshalf R hXR hRscal
    have hs0 : 0 < s := lt_of_lt_of_le hε hs
    -- the four consequences of `δ ≤ δ₁`
    have hδ1 : δ ≤ 1 := le_trans hδle (min_le_left _ _)
    have hδCa : δ ≤ n / (4 * Ca * M) :=
      le_trans hδle (le_trans (min_le_right _ _) (min_le_left _ _))
    have hδK' : δ ≤ 1 / (2 * Kb * C_EF * C_T * M) :=
      le_trans hδle (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hδL' : δ * M * D2 ≤ Lb := by
      have h : δ ≤ Lb / (M * D2) :=
        le_trans hδle (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
      have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < M * D2)).mp h
      have h3 : δ * M * D2 = δ * (M * D2) := by ring
      rw [h3]
      exact h2
    -- monotonicity of the thresholds on the window
    have hanyAA : anyAA n s ≤ anyAA n (1 / 2) := anyAA_le_anyAA_half n hn hs0 hshalf
    have hK1le : 1 + 2 * ((n : ℝ) - 1) * (anyAA n s + Ca) ≤ Kb := by
      rw [hKbdef]
      have h1 : 0 ≤ (n : ℝ) - 1 := le_of_lt hn1
      nlinarith [hanyAA, h1]
    have hK1pos : 0 < 1 + 2 * ((n : ℝ) - 1) * (anyAA n s + Ca) := by
      have h1 : 0 ≤ anyAA n s := anyAA_nonneg n hn (le_of_lt hs0)
      have h2 : 0 ≤ (n : ℝ) - 1 := le_of_lt hn1
      have h3 : 0 ≤ anyAA n s + Ca := by linarith
      nlinarith [mul_nonneg h2 h3]
    set K1 : ℝ := 1 + 2 * ((n : ℝ) - 1) * (anyAA n s + Ca) with hK1def
    set c0s : ℝ := min (1 / (1 + ((n : ℝ) - 2) * (s + 1) ^ 2))
      (4 / (((n : ℝ) - 2) + 8 * (s + 1))) with hc0def
    have hcbc0 : cb ≤ c0s := wscb_le_c0 n hn hs0 hshalf
    -- the three hypotheses of `chat_shift_threshold`
    have hδK : δ ≤ 1 / (2 * K1 * C_EF * C_T * M) := by
      refine le_trans hδK' ?_
      refine one_div_le_one_div_of_le (by positivity) ?_
      have h2 : (0 : ℝ) ≤ 2 * C_EF * C_T * M := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hK1le h2]
    have hδL : δ * M * D2 ≤ 1 / 2 / K1 * ((n : ℝ) - 1) * c0s := by
      refine le_trans hδL' ?_
      have hstep1 : 1 / 2 / Kb ≤ 1 / 2 / K1 := by
        rw [div_le_div_iff₀ hKbpos hK1pos]
        linarith
      have hstep2 : ((n : ℝ) - 1) * cb ≤ ((n : ℝ) - 1) * c0s :=
        mul_le_mul_of_nonneg_left hcbc0 (le_of_lt hn1)
      have hstep3 : (0 : ℝ) ≤ 1 / 2 / K1 := by positivity
      have hstep4 : (0 : ℝ) ≤ ((n : ℝ) - 1) * cb := mul_nonneg (le_of_lt hn1) hcbpos.le
      calc 1 / 2 / Kb * ((n : ℝ) - 1) * cb
          = (1 / 2 / Kb) * (((n : ℝ) - 1) * cb) := by ring
        _ ≤ (1 / 2 / K1) * (((n : ℝ) - 1) * c0s) := mul_le_mul hstep1 hstep2 hstep4 hstep3
        _ = 1 / 2 / K1 * ((n : ℝ) - 1) * c0s := by ring
    exact chat_shift_threshold n hn N hN hC_EFpos.le hC_Tpos.le hC_ricpos.le hC_EF hC_T hC_ric
      hs0 hδ0 hδ1 hδCa hδK hδL R hXR hRscal
  · -- the window is empty: any positive `δ₁` works
    refine ⟨1, one_pos, ?_⟩
    intro δ hδ0 hδle s hs hshalf
    exfalso
    linarith

end Work.Diff.Alg.Pinch
