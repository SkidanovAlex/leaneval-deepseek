import Mathlib
import Submission.Work.CNum.Jfun_defs
import Submission.Work.CNum.Jfun_chord
import Submission.Work.CNum.chord_Icc
import Submission.Work.CNum.chord
import Submission.Work.CNum.arc_bounds
import Submission.Work.CNum.LL_derivs
import Submission.Work.CNum.tD_bounds
import Submission.Work.CNum.sum_bndJ
import Submission.Work.CNum.DAux.Jfun_hasDerivAt
import Submission.Work.CNum.DAux.JfunD_hasDerivAt
import Submission.Work.CNum.DAux.tD2_tsum_le

/-! # `Work.CNum.DAux.Jlow`

Upper-chord bound: `Jfun ψ ≤ max (Jfun a) (Jfun b) + 1000 (b-a)²` (`Work.CNum.Jfun_chord`).
Lower-chord bound (this file): for `-3.9 ≤ a ≤ b ≤ -2.39`,

`min (Jfun a) (Jfun b) - 1000 (b-a)² ≤ Jfun ψ`   for `ψ ∈ [a,b]`.

The lower bound is the upper bound applied to `-Jfun`: it needs the *second* derivative of
`Jfun` to be bounded above.  Writing `Jfun = log 256 + LL + Σ_m tt m` (see `Jfun_chord.lean`)
one has, on the arc,

`Jfun'' = LLDD + Σ'_k tD2 (k+1)`,

and the two pieces are bounded by `LLDD ≤ 1500` (elementary algebra: `KK ψ ≥ (cJ-uJ)²`)

and `Σ'_k tD2 (k+1) ψ ≤ Σ'_k bndJ (k+1) ≤ 6500` (`Work.CNum.tD_bounds`, `Work.CNum.sum_bndJ`),

so `Jfun'' ≤ 8000` and `Work.CNum.chord_Icc` (with `K = 8000`, `K/8 = 1000`) gives the result.
-/

namespace Work.CNum.DAux

open Work.CNum

/-- `LLDD` is bounded above by `1500` — actually by `cJ·uJ/(cJ-uJ)² ≈ 10.14`.  Indeed
`LLDD ψ = -cJ·uJ·cos ψ/KK ψ - 2(cJ·uJ·sin ψ)²/KK ψ²`; the second term is `≤ 0` and the first
is `≤ cJ·uJ/KK ψ ≤ cJ·uJ/(cJ-uJ)²`, using `KK ψ ≥ (cJ-uJ)²` and `-cos ψ ≤ 1`. -/
lemma LLDD_le (ψ : ℝ) : LLDD ψ ≤ 1500 := by
  have hKpos : 0 < KK ψ := KK_pos ψ
  have hKmin : (169 / 572 : ℝ) ^ 2 ≤ KK ψ := by
    have h1 : KK ψ = (cJ - uJ) ^ 2 + 2 * cJ * uJ * (1 + Real.cos ψ) := by unfold KK; ring
    have h2 : (169 / 572 : ℝ) ^ 2 ≤ (cJ - uJ) ^ 2 := by norm_num [cJ, uJ]
    have h3 : 0 ≤ 2 * cJ * uJ * (1 + Real.cos ψ) := by
      have ha : (0 : ℝ) ≤ 2 * cJ * uJ := by norm_num [cJ, uJ]
      have hb : (0 : ℝ) ≤ 1 + Real.cos ψ := by linarith [Real.neg_one_le_cos ψ]
      exact mul_nonneg ha hb
    rw [h1]; linarith
  have h1 : -cJ * uJ * Real.cos ψ / KK ψ ≤ cJ * uJ / KK ψ := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hKpos)
    nlinarith [Real.neg_one_le_cos ψ, (by norm_num [cJ, uJ] : (0:ℝ) ≤ cJ * uJ)]
  have h2 : 0 ≤ 2 * (cJ * uJ * Real.sin ψ) ^ 2 / (KK ψ) ^ 2 :=
    div_nonneg (by positivity) (by positivity)
  have h3 : cJ * uJ / KK ψ ≤ 1500 := by
    rw [div_le_iff₀ hKpos]
    have hcu : cJ * uJ ≤ 1500 * (169 / 572 : ℝ) ^ 2 := by norm_num [cJ, uJ]
    nlinarith [hKmin]
  rw [LLDD]
  linarith only [h1, h2, h3]

/-- **Assembly.**  If the first two derivatives of `Jfun` on `[a,b]` are
`LLD + Σ'_k tD (k+1)` and `LLDD + Σ'_k tD2 (k+1)`, and the latter is `≤ 8000`
on `[a,b]`, then `Jfun` lies above the minimum of its endpoint values up to
`1000 (b-a)²`.  This is `Work.CNum.chord_Icc` applied to `-Jfun`. -/
theorem Jlow_of_derivs {a b : ℝ} (hab : a ≤ b) (ha : -3.9 ≤ a) (hb : b ≤ -2.39)
    (hd1 : ∀ x ∈ Set.Icc a b,
      HasDerivAt Jfun (LLD x + ∑' k : ℕ, tD (k + 1) x) x)
    (hd2 : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun y : ℝ => LLD y + ∑' k : ℕ, tD (k + 1) y)
        (LLDD x + ∑' k : ℕ, tD2 (k + 1) x) x)
    (hbnd : ∀ x ∈ Set.Icc a b, LLDD x + ∑' k : ℕ, tD2 (k + 1) x ≤ 8000) :
    ∀ ψ ∈ Set.Icc a b, min (Jfun a) (Jfun b) - 1000 * (b - a) ^ 2 ≤ Jfun ψ := by
  intro ψ hψ
  have h := chord_Icc hab (g := fun x : ℝ => -Jfun x)
      (g' := fun x : ℝ => -(LLD x + ∑' k : ℕ, tD (k + 1) x))
      (g'' := fun x : ℝ => -(LLDD x + ∑' k : ℕ, tD2 (k + 1) x))
      (fun x hx => (hd1 x hx).neg) (fun x hx => (hd2 x hx).neg)
      (fun x hx => by have := hbnd x hx; linarith) ψ hψ
  rw [max_neg_neg] at h
  linarith

theorem Jlow {a b : ℝ} (hab : a ≤ b) (ha : -3.9 ≤ a) (hb : b ≤ -2.39) : ∀ ψ ∈ Set.Icc a b, min (Work.CNum.Jfun a) (Work.CNum.Jfun b) - 1000 * (b - a) ^ 2 ≤ Work.CNum.Jfun ψ := by
  have hmem : ∀ x ∈ Set.Icc a b, x ∈ Set.Ioo (-3.905 : ℝ) (-2.385 : ℝ) := by
    intro x hx
    exact ⟨by linarith [hx.1, ha], by linarith [hx.2, hb]⟩
  refine Jlow_of_derivs hab ha hb (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · exact Jfun_hasDerivAt (hmem x hx)
  · exact JfunD_hasDerivAt (hmem x hx)
  · have h1 : LLDD x ≤ 1500 := LLDD_le x
    have h2 : (∑' k : ℕ, tD2 (k + 1) x) ≤ 6500 := tD2_tsum_le (arc_bounds (hmem x hx)).2
    linarith

end Work.CNum.DAux
