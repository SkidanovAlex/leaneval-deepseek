import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The parameters of the Böhm–Wilking family `Ĉ(s)`, and their quantitative continuity

The Brendle–Schoen family `Chat n s = Ĉ(s)` is defined piecewise (`s ≤ 1/2` versus `s ≥ 1/2`), but
each piece is the cone `Ccone a b p = ℓ_{a,b} '' Dpic p` for explicit parameters.  This file
records the family as a *single* cone

`Chat n s = Ccone (anyAA n s) (anyBB s) (anyPP n s)`,

with parameters that are (piecewise) smooth functions of `s`:

`anyAA n s = chatA n (min s (1/2)) + max (s - 1/2) 0`,  `anyBB s = min s (1/2)`,
`anyPP n s = (1 - 4/((n-2) + 8 max s (1/2))) + (chatP n (min s (1/2)) - chatP n (1/2))`.

Here `chatA n s = (2s + (n-2)s²)/(2(1+(n-2)s²))` and `chatP n s = (n-2)s²/(1+(n-2)s²)` are the two
parameters of the `s ≤ 1/2` branch, and the two pieces agree at `s = 1/2`.

The main quantitative content is that, for `δ ≥ 0`,

* `anyAA n (s+δ) - anyAA n s ∈ [0, (n/2+1)δ]`,
* `anyBB (s+δ) - anyBB s ∈ [0, δ]`,
* `anyPP n (s+δ) - anyPP n s ∈ [0, n δ]`,
* `1 - anyPP n (s+δ) ≥ min (1/(1+(n-2)(s+1)²)) (4/((n-2)+8(s+1))) > 0` (for `δ ≤ 1`).

The two parameters `chatA`, `chatP` are monotone and Lipschitz on `[0, 1/2]`
(`chatA_mono_lip`, `chatP_mono_lip`, from the difference formulae `chatA_sub_eq`, `chatP_sub_eq`),
while `x ↦ 1 - 4/((n-2)+8x)` is monotone with Lipschitz constant `2` on `x ≥ 1/2`, and
`x ↦ min x (1/2)`, `x ↦ max x (1/2)`, `x ↦ max (x-1/2) 0` are all `1`-Lipschitz.
-/

namespace Work.Diff.Alg.Pinch.ChatAny

open Finset Submission.Diff.Alg Work.Diff.Alg.Pinch

variable {n : ℕ}

/-! ## The parameters as a single continuous family -/

/-- The `a`-parameter of `Ĉ(s)` (`chatA n s` for `s ≤ 1/2`, `s` for `s ≥ 1/2`). -/
noncomputable def anyAA (n : ℕ) (s : ℝ) : ℝ := chatA n (min s (1 / 2)) + max (s - 1 / 2) 0

/-- The `b`-parameter of `Ĉ(s)` (`s` for `s ≤ 1/2`, `1/2` for `s ≥ 1/2`). -/
noncomputable def anyBB (s : ℝ) : ℝ := min s (1 / 2)

/-- The `p`-parameter of `Ĉ(s)` (`chatP n s` for `s ≤ 1/2`, `1 - 4/((n-2)+8s)` for `s ≥ 1/2`). -/
noncomputable def anyPP (n : ℕ) (s : ℝ) : ℝ :=
  (1 - 4 / (((n : ℝ) - 2) + 8 * max s (1 / 2))) + (chatP n (min s (1 / 2)) - chatP n (1 / 2))

lemma chatA_half (n : ℕ) : chatA n (1 / 2) = 1 / 2 := by
  have h1 : (0 : ℝ) < 1 + ((n : ℝ) - 2) * (1 / 2) ^ 2 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have h2 : (2 : ℝ) * (1 + ((n : ℝ) - 2) * (1 / 2) ^ 2) ≠ 0 :=
    mul_ne_zero two_ne_zero (ne_of_gt h1)
  rw [chatA, div_eq_iff h2]
  ring

lemma chatP_half (n : ℕ) : chatP n (1 / 2) = 1 - 4 / (((n : ℝ) - 2) + 4) := by
  have h1 : (1 : ℝ) + ((n : ℝ) - 2) * (1 / 2) ^ 2 = (((n : ℝ) - 2) + 4) / 4 := by ring
  rw [chatP, h1, one_div_div]

lemma anyAA_eq (n : ℕ) (s : ℝ) : anyAA n s = if s ≤ 1 / 2 then chatA n s else s := by
  by_cases h : s ≤ 1 / 2
  · rw [if_pos h, anyAA, min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [if_neg h, anyAA, min_eq_right (le_of_lt (not_le.mp h)), max_eq_left (by linarith),
      chatA_half]; ring

lemma anyBB_eq (s : ℝ) : anyBB s = if s ≤ 1 / 2 then s else 1 / 2 := by
  by_cases h : s ≤ 1 / 2
  · rw [if_pos h, anyBB, min_eq_left h]
  · rw [if_neg h, anyBB, min_eq_right (le_of_lt (not_le.mp h))]

lemma anyPP_eq (n : ℕ) (s : ℝ) :
    anyPP n s = if s ≤ 1 / 2 then chatP n s else 1 - 4 / (((n : ℝ) - 2) + 8 * s) := by
  by_cases h : s ≤ 1 / 2
  · rw [if_pos h, anyPP, min_eq_left h, max_eq_right h, chatP_half n]; ring
  · rw [if_neg h, anyPP, min_eq_right (le_of_lt (not_le.mp h)),
      max_eq_left (le_of_lt (not_le.mp h)), chatP_half n]; ring

/-- The family `Ĉ(s)` is the single cone with parameters `(anyAA n s, anyBB s, anyPP n s)`. -/
lemma chat_eq_cone_param (n : ℕ) {s : ℝ} :
    Chat n s = Ccone (n := n) (anyAA n s) (anyBB s) (anyPP n s) := by
  rw [anyAA_eq, anyBB_eq, anyPP_eq, Chat]
  split_ifs <;> rfl

/-! ## Difference formulae for the two parameter functions -/

/-- Difference formula for `chatA`. -/
lemma chatA_sub_eq (n : ℕ) (hn : 2 ≤ n) (u v : ℝ) :
    chatA n v - chatA n u =
      (v - u) * (4 - 4 * ((n : ℝ) - 2) * u * v + 2 * ((n : ℝ) - 2) * (u + v))
        / (4 * (1 + ((n : ℝ) - 2) * v ^ 2) * (1 + ((n : ℝ) - 2) * u ^ 2)) := by
  have hu : (1 : ℝ) + ((n : ℝ) - 2) * u ^ 2 ≠ 0 := ne_of_gt (chatA_denom_pos hn u)
  have hv : (1 : ℝ) + ((n : ℝ) - 2) * v ^ 2 ≠ 0 := ne_of_gt (chatA_denom_pos hn v)
  have hD : (4 * (1 + ((n : ℝ) - 2) * v ^ 2) * (1 + ((n : ℝ) - 2) * u ^ 2)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hv) hu
  rw [eq_div_iff hD]
  have kv : chatA n v * (2 * (1 + ((n : ℝ) - 2) * v ^ 2)) = 2 * v + ((n : ℝ) - 2) * v ^ 2 := by
    rw [chatA]
    exact div_mul_cancel₀ _ (mul_ne_zero two_ne_zero hv)
  have ku : chatA n u * (2 * (1 + ((n : ℝ) - 2) * u ^ 2)) = 2 * u + ((n : ℝ) - 2) * u ^ 2 := by
    rw [chatA]
    exact div_mul_cancel₀ _ (mul_ne_zero two_ne_zero hu)
  calc (chatA n v - chatA n u)
        * (4 * (1 + ((n : ℝ) - 2) * v ^ 2) * (1 + ((n : ℝ) - 2) * u ^ 2))
      = (chatA n v * (2 * (1 + ((n : ℝ) - 2) * v ^ 2))) * (2 * (1 + ((n : ℝ) - 2) * u ^ 2))
        - (chatA n u * (2 * (1 + ((n : ℝ) - 2) * u ^ 2)))
            * (2 * (1 + ((n : ℝ) - 2) * v ^ 2)) := by ring
    _ = (2 * v + ((n : ℝ) - 2) * v ^ 2) * (2 * (1 + ((n : ℝ) - 2) * u ^ 2))
        - (2 * u + ((n : ℝ) - 2) * u ^ 2) * (2 * (1 + ((n : ℝ) - 2) * v ^ 2)) := by
        rw [kv, ku]
    _ = (v - u) * (4 - 4 * ((n : ℝ) - 2) * u * v + 2 * ((n : ℝ) - 2) * (u + v)) := by ring

/-- Difference formula for `chatP`. -/
lemma chatP_sub_eq (n : ℕ) (hn : 2 ≤ n) (u v : ℝ) :
    chatP n v - chatP n u =
      ((n : ℝ) - 2) * (v - u) * (v + u)
        / ((1 + ((n : ℝ) - 2) * v ^ 2) * (1 + ((n : ℝ) - 2) * u ^ 2)) := by
  have hu : (1 : ℝ) + ((n : ℝ) - 2) * u ^ 2 ≠ 0 := ne_of_gt (chatA_denom_pos hn u)
  have hv : (1 : ℝ) + ((n : ℝ) - 2) * v ^ 2 ≠ 0 := ne_of_gt (chatA_denom_pos hn v)
  have hD : ((1 + ((n : ℝ) - 2) * v ^ 2) * (1 + ((n : ℝ) - 2) * u ^ 2)) ≠ 0 :=
    mul_ne_zero hv hu
  rw [eq_div_iff hD]
  have kv : chatP n v * (1 + ((n : ℝ) - 2) * v ^ 2) = ((n : ℝ) - 2) * v ^ 2 := by
    rw [chatP_eq_div hn v]
    exact div_mul_cancel₀ _ hv
  have ku : chatP n u * (1 + ((n : ℝ) - 2) * u ^ 2) = ((n : ℝ) - 2) * u ^ 2 := by
    rw [chatP_eq_div hn u]
    exact div_mul_cancel₀ _ hu
  calc (chatP n v - chatP n u)
        * ((1 + ((n : ℝ) - 2) * v ^ 2) * (1 + ((n : ℝ) - 2) * u ^ 2))
      = (chatP n v * (1 + ((n : ℝ) - 2) * v ^ 2)) * (1 + ((n : ℝ) - 2) * u ^ 2)
        - (chatP n u * (1 + ((n : ℝ) - 2) * u ^ 2)) * (1 + ((n : ℝ) - 2) * v ^ 2) := by ring
    _ = ((n : ℝ) - 2) * v ^ 2 * (1 + ((n : ℝ) - 2) * u ^ 2)
        - ((n : ℝ) - 2) * u ^ 2 * (1 + ((n : ℝ) - 2) * v ^ 2) := by rw [kv, ku]
    _ = ((n : ℝ) - 2) * (v - u) * (v + u) := by ring

/-- `1 - chatP n w = 1/(1 + (n-2)w²)`. -/
lemma one_sub_chatP (n : ℕ) (w : ℝ) : 1 - chatP n w = 1 / (1 + ((n : ℝ) - 2) * w ^ 2) := by
  rw [chatP]
  ring

/-! ## Monotonicity and Lipschitz bounds for `chatA`, `chatP` on `[0, 1/2]` -/

/-- `chatA n` is nondecreasing on `[0, 1/2]` and `n/2`-Lipschitz there. -/
lemma chatA_mono_lip (n : ℕ) (hn : 2 ≤ n) {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1 / 2) :
    chatA n u ≤ chatA n v ∧ chatA n v - chatA n u ≤ ((n : ℝ) / 2) * (v - u) := by
  have hc : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  have hsub := chatA_sub_eq n hn u v
  have hu1 : (1 : ℝ) ≤ 1 + ((n : ℝ) - 2) * u ^ 2 := by nlinarith [hc, sq_nonneg u]
  have hv1 : (1 : ℝ) ≤ 1 + ((n : ℝ) - 2) * v ^ 2 := by nlinarith [hc, sq_nonneg v]
  have hD : (0 : ℝ) < 4 * (1 + ((n : ℝ) - 2) * v ^ 2) * (1 + ((n : ℝ) - 2) * u ^ 2) := by
    have h1 := chatA_denom_pos hn v
    have h2 := chatA_denom_pos hn u
    positivity
  have hD4 : (4 : ℝ) ≤ 4 * (1 + ((n : ℝ) - 2) * v ^ 2) * (1 + ((n : ℝ) - 2) * u ^ 2) := by
    have hmul : (1 : ℝ) ≤ (1 + ((n : ℝ) - 2) * v ^ 2) * (1 + ((n : ℝ) - 2) * u ^ 2) :=
      one_le_mul_of_one_le_of_one_le hv1 hu1
    linarith
  have hvu : (0 : ℝ) ≤ v - u := by linarith
  have hB : 4 - 4 * ((n : ℝ) - 2) * u * v + 2 * ((n : ℝ) - 2) * (u + v)
      ≤ 4 + 2 * ((n : ℝ) - 2) := by
    nlinarith [hc, hu0, huv, hv, mul_nonneg hc hu0, mul_nonneg hc hvu]
  have hB0 : 0 ≤ 4 - 4 * ((n : ℝ) - 2) * u * v + 2 * ((n : ℝ) - 2) * (u + v) := by
    nlinarith [hc, hu0, huv, hv, mul_nonneg hc hu0, mul_nonneg hc hvu]
  have hn2 : (n : ℝ) = 2 + ((n : ℝ) - 2) := by ring
  constructor
  · rw [← sub_nonneg, hsub]
    exact div_nonneg (mul_nonneg hvu hB0) hD.le
  · rw [hsub, div_le_iff₀ hD]
    have h1 : (v - u) * (4 - 4 * ((n : ℝ) - 2) * u * v + 2 * ((n : ℝ) - 2) * (u + v))
        ≤ (v - u) * (4 + 2 * ((n : ℝ) - 2)) := mul_le_mul_of_nonneg_left hB hvu
    have hmid : ((n : ℝ) / 2) * (v - u) * 4
        ≤ ((n : ℝ) / 2) * (v - u)
            * (4 * (1 + ((n : ℝ) - 2) * v ^ 2) * (1 + ((n : ℝ) - 2) * u ^ 2)) :=
      mul_le_mul_of_nonneg_left hD4 (by positivity)
    nlinarith [h1, hmid, hn2]

/-- `chatP n` is nondecreasing on `[0, 1/2]` and `(n-2)`-Lipschitz there. -/
lemma chatP_mono_lip (n : ℕ) (hn : 2 ≤ n) {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1 / 2) :
    chatP n u ≤ chatP n v ∧ chatP n v - chatP n u ≤ ((n : ℝ) - 2) * (v - u) := by
  have hc : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  have hsub := chatP_sub_eq n hn u v
  have hu1 : (1 : ℝ) ≤ 1 + ((n : ℝ) - 2) * u ^ 2 := by nlinarith [hc, sq_nonneg u]
  have hv1 : (1 : ℝ) ≤ 1 + ((n : ℝ) - 2) * v ^ 2 := by nlinarith [hc, sq_nonneg v]
  have hD : (0 : ℝ) < (1 + ((n : ℝ) - 2) * v ^ 2) * (1 + ((n : ℝ) - 2) * u ^ 2) := by
    have h1 := chatA_denom_pos hn v
    have h2 := chatA_denom_pos hn u
    positivity
  have hD1 : (1 : ℝ) ≤ (1 + ((n : ℝ) - 2) * v ^ 2) * (1 + ((n : ℝ) - 2) * u ^ 2) :=
    one_le_mul_of_one_le_of_one_le hv1 hu1
  have hvu : (0 : ℝ) ≤ v - u := by linarith
  have hvu0 : (0 : ℝ) ≤ v + u := by linarith
  have huv1 : v + u ≤ 1 := by linarith
  constructor
  · rw [← sub_nonneg, hsub]
    exact div_nonneg (mul_nonneg (mul_nonneg hc hvu) hvu0) hD.le
  · rw [hsub, div_le_iff₀ hD]
    have hcl : (0 : ℝ) ≤ ((n : ℝ) - 2) * (v - u) := mul_nonneg hc hvu
    have hDge : v + u ≤ (1 + ((n : ℝ) - 2) * v ^ 2) * (1 + ((n : ℝ) - 2) * u ^ 2) := by
      linarith
    exact mul_le_mul_of_nonneg_left hDge hcl

/-! ## Bounds for the three parameters -/

/-- `anyBB (s+δ) - anyBB s ∈ [0, δ]`. -/
lemma anyBB_shift {s δ : ℝ} (hδ : 0 ≤ δ) :
    anyBB s ≤ anyBB (s + δ) ∧ anyBB (s + δ) - anyBB s ≤ δ := by
  have h1 : anyBB s ≤ anyBB (s + δ) := by
    rw [anyBB, anyBB]
    exact min_le_min (by linarith) le_rfl
  refine ⟨h1, ?_⟩
  have h2 : anyBB (s + δ) ≤ anyBB s + δ := by
    have h3 : min (s + δ) (1 / 2) ≤ min s (1 / 2) + δ := by
      have h4 : min (s + δ) (1 / 2) ≤ min (s + δ) (1 / 2 + δ) :=
        min_le_min le_rfl (by linarith)
      rwa [min_add_add_right] at h4
    rw [anyBB, anyBB]
    linarith
  linarith

/-- `anyAA n (s+δ) - anyAA n s ∈ [0, (n/2+1)δ]`. -/
lemma anyAA_shift (n : ℕ) (hn : 2 ≤ n) {s δ : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ) :
    anyAA n s ≤ anyAA n (s + δ) ∧
      anyAA n (s + δ) - anyAA n s ≤ ((n : ℝ) / 2 + 1) * δ := by
  have hd : anyAA n (s + δ) - anyAA n s
      = (chatA n (min (s + δ) (1 / 2)) - chatA n (min s (1 / 2)))
        + (max (s + δ - 1 / 2) 0 - max (s - 1 / 2) 0) := by
    rw [anyAA, anyAA]; ring
  have hmin1 : min s (1 / 2) ≤ min (s + δ) (1 / 2) := min_le_min (by linarith) le_rfl
  have hmin2 : min (s + δ) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hmin0 : 0 ≤ min s (1 / 2) := le_min hs.le (by norm_num)
  obtain ⟨hA1, hA2⟩ := chatA_mono_lip n hn hmin0 hmin1 hmin2
  have hmax1 : max (s - 1 / 2) 0 ≤ max (s + δ - 1 / 2) 0 :=
    max_le_max (by linarith) le_rfl
  have hmax2 : max (s + δ - 1 / 2) 0 - max (s - 1 / 2) 0 ≤ δ := by
    have h := max_sub_max_le_max (s + δ - 1 / 2) 0 (s - 1 / 2) 0
    have h' : s + δ - 1 / 2 - (s - 1 / 2) = δ := by ring
    rw [h', sub_self] at h
    exact h.trans_eq (max_eq_left hδ)
  have hb2 : min (s + δ) (1 / 2) - min s (1 / 2) ≤ δ := (anyBB_shift (s := s) hδ).2
  have hA3 : chatA n (min (s + δ) (1 / 2)) - chatA n (min s (1 / 2)) ≤ ((n : ℝ) / 2) * δ := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
    nlinarith [hA2, hb2, hn0]
  constructor
  · rw [← sub_nonneg, hd]; linarith
  · rw [hd]; linarith

/-- `anyPP n (s+δ) - anyPP n s ∈ [0, n δ]`. -/
lemma anyPP_shift_le (n : ℕ) (hn : 2 ≤ n) {s δ : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ) :
    anyPP n s ≤ anyPP n (s + δ) ∧ anyPP n (s + δ) - anyPP n s ≤ (n : ℝ) * δ := by
  have hc : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  have hx : (1 / 2 : ℝ) ≤ max s (1 / 2) := le_max_right _ _
  have hx' : (1 / 2 : ℝ) ≤ max (s + δ) (1 / 2) := le_max_right _ _
  have hxx' : max s (1 / 2) ≤ max (s + δ) (1 / 2) := max_le_max (by linarith) le_rfl
  have hc0 : 0 < ((n : ℝ) - 2) + 8 * max s (1 / 2) := by nlinarith [hc, hx]
  have hc0' : 0 < ((n : ℝ) - 2) + 8 * max (s + δ) (1 / 2) := by nlinarith [hc, hx']
  have hmin1 : min s (1 / 2) ≤ min (s + δ) (1 / 2) := min_le_min (by linarith) le_rfl
  have hmin2 : min (s + δ) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hmin0 : 0 ≤ min s (1 / 2) := le_min hs.le (by norm_num)
  obtain ⟨hP1, hP2⟩ := chatP_mono_lip n hn hmin0 hmin1 hmin2
  have hbb4 : min (s + δ) (1 / 2) - min s (1 / 2) ≤ δ := (anyBB_shift (s := s) hδ).2
  have hP3 : chatP n (min (s + δ) (1 / 2)) - chatP n (min s (1 / 2)) ≤ ((n : ℝ) - 2) * δ := by
    nlinarith [hP2, hbb4, hc]
  have hg0 : (1 - 4 / (((n : ℝ) - 2) + 8 * max s (1 / 2)))
      ≤ 1 - 4 / (((n : ℝ) - 2) + 8 * max (s + δ) (1 / 2)) := by
    have hle : 4 / (((n : ℝ) - 2) + 8 * max (s + δ) (1 / 2))
        ≤ 4 / (((n : ℝ) - 2) + 8 * max s (1 / 2)) := by
      rw [div_le_div_iff₀ hc0' hc0]
      linarith [hxx']
    linarith
  have hg2 : (1 - 4 / (((n : ℝ) - 2) + 8 * max (s + δ) (1 / 2)))
      - (1 - 4 / (((n : ℝ) - 2) + 8 * max s (1 / 2))) ≤ 2 * δ := by
    have hmain : 4 / (((n : ℝ) - 2) + 8 * max s (1 / 2))
        - 4 / (((n : ℝ) - 2) + 8 * max (s + δ) (1 / 2)) ≤ 2 * δ := by
      have hstep : (4 / (((n : ℝ) - 2) + 8 * max s (1 / 2))
          - 4 / (((n : ℝ) - 2) + 8 * max (s + δ) (1 / 2)))
          * ((((n : ℝ) - 2) + 8 * max (s + δ) (1 / 2))
              * (((n : ℝ) - 2) + 8 * max s (1 / 2)))
          = 32 * (max (s + δ) (1 / 2) - max s (1 / 2)) := by
        field_simp
        ring
      have hD : (0 : ℝ) < (((n : ℝ) - 2) + 8 * max (s + δ) (1 / 2))
          * (((n : ℝ) - 2) + 8 * max s (1 / 2)) := mul_pos hc0' hc0
      have hdiv : 4 / (((n : ℝ) - 2) + 8 * max s (1 / 2))
          - 4 / (((n : ℝ) - 2) + 8 * max (s + δ) (1 / 2))
          = 32 * (max (s + δ) (1 / 2) - max s (1 / 2))
            / ((((n : ℝ) - 2) + 8 * max (s + δ) (1 / 2))
                * (((n : ℝ) - 2) + 8 * max s (1 / 2))) := by
        rw [eq_div_iff hD.ne']
        exact hstep
      have hxδ : max (s + δ) (1 / 2) - max s (1 / 2) ≤ δ := by
        have h := max_sub_max_le_max (s + δ) (1 / 2) s (1 / 2)
        have h' : (1 : ℝ) / 2 - 1 / 2 = 0 := by ring
        have h'' : s + δ - s = δ := by ring
        rw [h'', h'] at h
        rw [max_eq_left hδ] at h
        exact h
      rw [hdiv, div_le_iff₀ hD]
      have hDge : (((n : ℝ) - 2) + 4) ^ 2
          ≤ (((n : ℝ) - 2) + 8 * max (s + δ) (1 / 2)) * (((n : ℝ) - 2) + 8 * max s (1 / 2)) := by
        nlinarith [hc, hx, hx', hxx']
      have h16 : (32 : ℝ) ≤ 2 * (((n : ℝ) - 2) + 4) ^ 2 := by nlinarith [hc]
      have hp : 2 * δ * (((n : ℝ) - 2) + 4) ^ 2
          ≤ 2 * δ * ((((n : ℝ) - 2) + 8 * max (s + δ) (1 / 2))
              * (((n : ℝ) - 2) + 8 * max s (1 / 2))) :=
        mul_le_mul_of_nonneg_left hDge (by linarith)
      nlinarith [hxδ, h16, hp]
    linarith
  have hn2 : (n : ℝ) = 2 + ((n : ℝ) - 2) := by ring
  constructor
  · rw [anyPP, anyPP]; linarith
  · rw [anyPP, anyPP]; linarith

/-- The defect of `anyPP` is bounded below by a positive constant (for `0 ≤ δ ≤ 1`). -/
lemma one_sub_anyPP_ge (n : ℕ) (hn : 2 ≤ n) {s δ : ℝ} (hs : 0 < s) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    min (1 / (1 + ((n : ℝ) - 2) * (s + 1) ^ 2)) (4 / (((n : ℝ) - 2) + 8 * (s + 1)))
      ≤ 1 - anyPP n (s + δ) := by
  have hc : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  have hs1 : 0 < s + δ := by linarith
  rw [anyPP_eq]
  split_ifs with h
  · rw [one_sub_chatP n (s + δ)]
    refine le_trans (min_le_left _ _) ?_
    rw [div_le_div_iff₀ (by nlinarith [hc, sq_nonneg (s + 1)])
      (by nlinarith [hc, hs1])]
    have hsq : (s + δ) ^ 2 ≤ (s + 1) ^ 2 :=
      pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ s + δ) (by linarith : s + δ ≤ s + 1) 2
    have hcl : ((n : ℝ) - 2) * (s + δ) ^ 2 ≤ ((n : ℝ) - 2) * (s + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hc
    linarith
  · refine le_trans (min_le_right _ _) ?_
    have h1 : 1 - (1 - 4 / (((n : ℝ) - 2) + 8 * (s + δ)))
        = 4 / (((n : ℝ) - 2) + 8 * (s + δ)) := by ring
    rw [h1]
    rw [div_le_div_iff₀ (by nlinarith [hc, hs]) (by nlinarith [hc, hs1])]
    nlinarith [hδ1]

/-- `anyPP n (s+δ) < 1`. -/
lemma anyPP_shift_lt_one (n : ℕ) (hn : 2 ≤ n) {s δ : ℝ} (hs : 0 < s) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) : anyPP n (s + δ) < 1 := by
  have h := one_sub_anyPP_ge n hn hs hδ0 hδ1
  have hc : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  have hpos : 0 < min (1 / (1 + ((n : ℝ) - 2) * (s + 1) ^ 2))
      (4 / (((n : ℝ) - 2) + 8 * (s + 1))) :=
    lt_min (one_div_pos.mpr (by nlinarith [hc, sq_nonneg (s + 1)]))
      (div_pos (by norm_num) (by nlinarith [hc, hs]))
  linarith

/-- `0 ≤ anyAA n s` for `s ≥ 0`. -/
lemma anyAA_nonneg (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ anyAA n s := by
  have h1 : 0 ≤ chatA n (min s (1 / 2)) := chatA_nonneg hn (le_min hs (by norm_num))
  have h2 : 0 ≤ max (s - 1 / 2) 0 := le_max_right _ _
  rw [anyAA]; linarith

/-- `1 + 2(n-1)·anyAA n s ≠ 0` for `s ≥ 0`. -/
lemma anyAA_denom (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    1 + 2 * ((n : ℝ) - 1) * anyAA n s ≠ 0 := by
  have h1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h2 := anyAA_nonneg n hn hs
  have : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * anyAA n s := by nlinarith
  exact ne_of_gt this

/-- `1 + (n-2)·anyBB s ≠ 0` for `s ≥ 0`. -/
lemma anyBB_denom (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    1 + ((n : ℝ) - 2) * anyBB s ≠ 0 := by
  have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  have h3 : 0 ≤ anyBB s := le_min hs (by norm_num)
  have : (0 : ℝ) < 1 + ((n : ℝ) - 2) * anyBB s := by nlinarith
  exact ne_of_gt this

/-- `1 + 2(n-1)·anyAA n (s+δ) ≤ K` for `K = 1 + 2(n-1)(anyAA n s + (n/2+1))`. -/
lemma one_add_two_anyAA_le (n : ℕ) (hn : 2 ≤ n) {s δ : ℝ} (hs : 0 < s) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    1 + 2 * ((n : ℝ) - 1) * anyAA n (s + δ)
      ≤ 1 + 2 * ((n : ℝ) - 1) * (anyAA n s + ((n : ℝ) / 2 + 1)) := by
  obtain ⟨-, h2⟩ := anyAA_shift n hn hs hδ0
  have h3 : anyAA n (s + δ) ≤ anyAA n s + ((n : ℝ) / 2 + 1) := by
    have h4 : (0 : ℝ) ≤ (n : ℝ) / 2 + 1 := by positivity
    have h5 : ((n : ℝ) / 2 + 1) * δ ≤ ((n : ℝ) / 2 + 1) * 1 :=
      mul_le_mul_of_nonneg_left hδ1 h4
    linarith
  have h1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  nlinarith [h3]

end Work.Diff.Alg.Pinch.ChatAny
