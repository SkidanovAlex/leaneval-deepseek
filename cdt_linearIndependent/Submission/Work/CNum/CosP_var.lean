import Mathlib
import Submission.Work.CNum.cosT_bound

/-!
# Variation bound for the cosine Taylor polynomial on `[0, π/4]`

We prove that for `0 ≤ s ≤ t ≤ π/4` the partial sum `cosP · 11` of the cosine
series decreases at least as fast as `x ↦ -x²/16`, up to a tiny error:

`(s + t) * (t - s) / 8 - 2 / 24! ≤ cosP s 11 - cosP t 11`.

The proof combines three ingredients:
* the Lagrange remainder bound `cos_bound` (from `cosT_bound`), which controls
  `|cos x - cosP x 11| ≤ x ^ 23 / 23!`;
* the lower bound `x / 4 ≤ sin x` on `[0, π/4]`, obtained from `Real.mul_le_sin`
  (`2 / π * x ≤ sin x`), which through the antitone function `cos x + x²/8`
  yields `(t² - s²) / 8 ≤ cos s - cos t`;
* a purely arithmetic estimate showing `(s^23 + t^23) / 23! ≤ 2 / 24!`.
-/

namespace Work.CNum

/-- On `[0, π/4]` the sine is at least a quarter of its argument. -/
lemma sin_ge_div_four {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 4) :
    x / 4 ≤ Real.sin x := by
  have hx2 : x ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h := Real.mul_le_sin h0 hx2
  have hp : (1 : ℝ) / 4 ≤ 2 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_four]
  have h4 : x / 4 ≤ 2 / Real.pi * x := by
    have hh := mul_le_mul_of_nonneg_right hp h0
    have e : (1 : ℝ) / 4 * x = x / 4 := by ring
    rwa [e] at hh
  linarith

/-- The elementary inequality `(t² - s²) / 8 ≤ cos s - cos t` for
`0 ≤ s ≤ t ≤ π/4`.  It follows from the fact that `x ↦ cos x + x²/8` is
antitone on `[0, π/4]`, since its derivative `-sin x + x/4` is nonpositive
there by `sin_ge_div_four`. -/
lemma cos_sub_cos_ge {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) (h1 : t ≤ Real.pi / 4) :
    (t ^ 2 - s ^ 2) / 8 ≤ Real.cos s - Real.cos t := by
  have hanti : AntitoneOn (fun x : ℝ => Real.cos x + x ^ 2 / 8) (Set.Icc 0 (Real.pi / 4)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      rw [interior_Icc] at hx
      have hd : deriv (fun x : ℝ => Real.cos x + x ^ 2 / 8) x = -Real.sin x + x / 4 := by
        have h1 : HasDerivAt (fun x : ℝ => Real.cos x) (-Real.sin x) x := Real.hasDerivAt_cos x
        have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 8) (x / 4) x := by
          have h3 := (hasDerivAt_pow 2 x).div_const 8
          have e : (↑(2 : ℕ) * x ^ (2 - 1)) / 8 = x / 4 := by norm_num; ring
          rwa [e] at h3
        exact (h1.add h2).deriv
      rw [hd]
      have := sin_ge_div_four (le_of_lt hx.1) (le_of_lt hx.2)
      linarith
  have hs : s ∈ Set.Icc 0 (Real.pi / 4) := ⟨h0, hst.trans h1⟩
  have ht : t ∈ Set.Icc 0 (Real.pi / 4) := ⟨h0.trans hst, h1⟩
  have hh := hanti hs ht hst
  simp only at hh
  linarith

/-- The numerical estimate `(s ^ 23 + t ^ 23) / 23! ≤ 2 / 24!` for
`0 ≤ s ≤ t ≤ π/4`.  Since `t ≤ π/4 < 4/5` we have `s ^ 23, t ^ 23 ≤ (4/5) ^ 23 ≤ 1/24`,
so `s ^ 23 + t ^ 23 ≤ 1/12` and `(1/12) / 23! = 1 / (12 · 23!) = 2 / 24!`. -/
lemma cosP_var_num {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (h1 : t ≤ Real.pi / 4) :
    (s ^ 23 + t ^ 23) / ((23 : ℕ).factorial : ℝ) ≤ 2 * ((Nat.factorial 24 : ℝ))⁻¹ := by
  have hpi : Real.pi / 4 < 4 / 5 := by
    have := Real.pi_lt_d2
    linarith
  have ht : t ≤ 4 / 5 := h1.trans hpi.le
  have hs' : s ≤ 4 / 5 := hst.trans ht
  have hp : ((4 : ℝ) / 5) ^ 23 ≤ 1 / 24 := by norm_num
  have hs23 : s ^ 23 ≤ (1 : ℝ) / 24 := (pow_le_pow_left₀ hs hs' 23).trans hp
  have ht23 : t ^ 23 ≤ (1 : ℝ) / 24 := (pow_le_pow_left₀ (hs.trans hst) ht 23).trans hp
  have hsum : s ^ 23 + t ^ 23 ≤ 1 / 12 := by linarith
  have hfac : ((Nat.factorial 24 : ℝ)) = 24 * ((23 : ℕ).factorial : ℝ) := by
    have h := Nat.factorial_succ 23
    norm_num [Nat.factorial] at h ⊢
  rw [hfac]
  have h23 : (0 : ℝ) < ((23 : ℕ).factorial : ℝ) := by positivity
  rw [show (2 : ℝ) * (24 * ((23 : ℕ).factorial : ℝ))⁻¹ =
      (1 / 12) / ((23 : ℕ).factorial : ℝ) by field_simp; ring]
  exact div_le_div_of_nonneg_right hsum (le_of_lt h23)

theorem CosP_var {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) (h1 : t ≤ Real.pi / 4) :
    (s + t) * (t - s) / 8 - 2 * ((Nat.factorial 24 : ℝ))⁻¹ ≤ cosP s 11 - cosP t 11 := by
  have ht0 : 0 ≤ t := h0.trans hst
  have hcs : |Real.cos s - cosP s 11| ≤ s ^ 23 / ((23 : ℕ).factorial : ℝ) := by
    have := cos_bound s h0 11
    simpa using this
  have hct : |Real.cos t - cosP t 11| ≤ t ^ 23 / ((23 : ℕ).factorial : ℝ) := by
    have := cos_bound t ht0 11
    simpa using this
  rw [abs_le] at hcs hct
  have hdiff := cos_sub_cos_ge h0 hst h1
  have hnum := cosP_var_num h0 hst h1
  have hkey : Real.cos s - Real.cos t - (s ^ 23 + t ^ 23) / ((23 : ℕ).factorial : ℝ) ≤
      cosP s 11 - cosP t 11 := by
    linarith [hcs.1, hcs.2, hct.1, hct.2]
  have heq : (t ^ 2 - s ^ 2) / 8 = (s + t) * (t - s) / 8 := by ring
  linarith [hdiff, hnum, hkey, heq]

end Work.CNum
