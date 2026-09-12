import Submission.AdjustedCheb
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Quantitative margins of the Chebyshev extremal points from the interval ends

For the final `α ± δ` root brackets of Proposition `early_ints_better` we need
every constructed root to lie at distance `≥ δ` from the Serre interval
endpoints.  The roots of the complementary polynomial `Q` lie in the interior
Chebyshev window `[extPoint (r+3) (r+1), extPoint (r+3) 1]` (see
`Submission.CompQEnum`), so this module records the quantitative margins of the
Chebyshev extremal points:

`∃ c > 0, ∀ N ≥ 3, ∀ 1 ≤ k < N :
   c/N² ≤ extPoint N k − aSerre   ∧   c/N² ≤ bSerre − extPoint N k`.

(Here `extPoint N k = chebPoint(cos(kπ/N))` with
`chebPoint t = (a+b)/2 + (b−a)/2·t`, so both margins equal
`(b−a)/2·(1 − cos(kπ/N))` for the two ends and are minimized at `k = 1` /
`k = N−1`; `1 − cos x ≥ 2x²/π²` gives the `N⁻²` decay.  The `c = bSerre−aSerre`
claim below uses `1 − cos(π/N) ≥ 2/N²` for `N ≥ 3`.)
-/

noncomputable section

open scoped Real BigOperators
open Polynomial

namespace Submission.ChebMargin

open Submission.SerreExample
open Submission.ChebSerre
open Submission.AdjustedCheb

private lemma bSerre_sub_aSerre_pos : 0 < bSerre - aSerre := sub_pos.mpr a_lt_b

/-- `extPoint N k − aSerre`, expanded through the affine `chebPoint`. -/
private lemma extPoint_sub_aSerre (N k : ℕ) :
    extPoint N k - aSerre = (bSerre - aSerre) / 2 * (1 + Real.cos (extAngle N k)) := by
  unfold extPoint chebPoint
  ring

/-- `bSerre − extPoint N k`, expanded through the affine `chebPoint`. -/
private lemma bSerre_sub_extPoint (N k : ℕ) :
    bSerre - extPoint N k = (bSerre - aSerre) / 2 * (1 - Real.cos (extAngle N k)) := by
  unfold extPoint chebPoint
  ring

/-- `1 − cos(2u) = 2 sin²u`. -/
private lemma one_sub_cos_two_mul' (u : ℝ) : 1 - Real.cos (2 * u) = 2 * Real.sin u ^ 2 := by
  rw [Real.cos_two_mul]
  have h := Real.sin_sq_add_cos_sq u
  nlinarith

/-- `1 − cos x ≥ 2x²/π²` on `[0, π/2]` (via `sin y ≥ 2y/π`). -/
private lemma one_sub_cos_ge {x : ℝ} (hx0 : 0 ≤ x) (hxπ2 : x ≤ Real.pi / 2) :
    (2 : ℝ) / Real.pi ^ 2 * x ^ 2 ≤ 1 - Real.cos x := by
  have h0 : 0 ≤ x / 2 := div_nonneg hx0 (by norm_num)
  have hle : x / 2 ≤ Real.pi / 2 := by linarith
  have hsin := Real.mul_le_sin (x := x / 2) h0 hle
  have hsinNonneg : 0 ≤ Real.sin (x / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [hxπ2])
  have haNonneg : 0 ≤ (2 / Real.pi) * (x / 2) := by
    exact mul_nonneg (div_nonneg (by norm_num) (le_of_lt Real.pi_pos)) h0
  have hsq : ((2 / Real.pi) * (x / 2)) ^ 2 ≤ Real.sin (x / 2) ^ 2 := by
    have hm := mul_le_mul hsin hsin haNonneg hsinNonneg
    simpa [pow_two, mul_assoc] using hm
  have h1 : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    have hx2 : x = 2 * (x / 2) := by ring
    rw [← one_sub_cos_two_mul' (x / 2), ← hx2]
  have hmul2 : (2 : ℝ) * (((2 / Real.pi) * (x / 2)) ^ 2) ≤ 2 * Real.sin (x / 2) ^ 2 := by
    exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  calc
    (2 : ℝ) / Real.pi ^ 2 * x ^ 2 = (2 : ℝ) * (((2 / Real.pi) * (x / 2)) ^ 2) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ 2 * Real.sin (x / 2) ^ 2 := hmul2
    _ = 1 - Real.cos x := h1.symm

/-- `2/N² ≤ 1 − cos(π/N)` for `N ≥ 3`. -/
private lemma two_div_sq_le_one_sub_cos_pi_div (N : ℕ) (hN : 3 ≤ N) :
    (2 : ℝ) / (N : ℝ) ^ 2 ≤ 1 - Real.cos (Real.pi / (N : ℝ)) := by
  have hN1 : 1 ≤ N := by omega
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN1
  have hα0 : 0 ≤ Real.pi / (N : ℝ) := div_nonneg (le_of_lt Real.pi_pos) (le_of_lt hNpos)
  have hNge2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
  have hαπ2 : Real.pi / (N : ℝ) ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hNpos]
    calc
      Real.pi ≤ (N : ℝ) * (Real.pi / 2) := by
        have hstep : (2 : ℝ) * (Real.pi / 2) ≤ (N : ℝ) * (Real.pi / 2) :=
          mul_le_mul_of_nonneg_right hNge2 (le_of_lt (div_pos Real.pi_pos (by norm_num)))
        have h2 : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
        rwa [h2] at hstep
      _ = Real.pi / 2 * (N : ℝ) := by ring
  have hg := one_sub_cos_ge hα0 hαπ2
  have hrew : (2 : ℝ) / Real.pi ^ 2 * (Real.pi / (N : ℝ)) ^ 2 = (2 : ℝ) / (N : ℝ) ^ 2 := by
    field_simp [Real.pi_ne_zero, ne_of_gt hNpos]
  rwa [hrew] at hg

/-- `extPoint` is decreasing in its index (non-strict). -/
private lemma extPoint_antitone_le {N k l : ℕ} (hN : 1 ≤ N) (hl : l ≤ N) (hkl : k ≤ l) :
    extPoint N l ≤ extPoint N k := by
  rcases lt_or_eq_of_le hkl with hlt | heq
  · exact le_of_lt (extPoint_antitone hN hl hlt)
  · rw [heq]

/-- Left-end margin: `(bSerre−aSerre)/N² ≤ extPoint N k − aSerre` for `1 ≤ k < N`. -/
private lemma margin_left (N : ℕ) (hN : 3 ≤ N) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    (bSerre - aSerre) / (N : ℝ) ^ 2 ≤ extPoint N k - aSerre := by
  have hN1 : 1 ≤ N := by omega
  have hkNm1 : k ≤ N - 1 := by omega
  have he : extPoint N (N - 1) ≤ extPoint N k := by
    exact extPoint_antitone_le hN1 (by omega : N - 1 ≤ N) hkNm1
  have hred : extPoint N (N - 1) - aSerre ≤ extPoint N k - aSerre := by linarith
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  have hangle : extAngle N (N - 1) = Real.pi - Real.pi / (N : ℝ) := by
    unfold extAngle
    rw [hcast]
    field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt hN1)]
  have hval : extPoint N (N - 1) - aSerre =
      (bSerre - aSerre) / 2 * (1 - Real.cos (Real.pi / (N : ℝ))) := by
    rw [extPoint_sub_aSerre N (N - 1)]
    rw [hangle, Real.cos_pi_sub]
    ring
  have h2 : (2 : ℝ) / (N : ℝ) ^ 2 ≤ 1 - Real.cos (Real.pi / (N : ℝ)) :=
    two_div_sq_le_one_sub_cos_pi_div N hN
  have hL2pos : 0 < (bSerre - aSerre) / 2 := div_pos bSerre_sub_aSerre_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left h2 (hL2pos.le)
  have hstep : (bSerre - aSerre) / 2 * ((2 : ℝ) / (N : ℝ) ^ 2) = (bSerre - aSerre) / (N : ℝ) ^ 2 := by
    field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt hN1)]
  calc
    (bSerre - aSerre) / (N : ℝ) ^ 2 ≤ (bSerre - aSerre) / 2 * (1 - Real.cos (Real.pi / (N : ℝ))) := by
      rw [← hstep]
      exact hmul
    _ = extPoint N (N - 1) - aSerre := hval.symm
    _ ≤ extPoint N k - aSerre := hred

/-- Right-end margin: `(bSerre−aSerre)/N² ≤ bSerre − extPoint N k` for `1 ≤ k < N`. -/
private lemma margin_right (N : ℕ) (hN : 3 ≤ N) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    (bSerre - aSerre) / (N : ℝ) ^ 2 ≤ bSerre - extPoint N k := by
  have hN1 : 1 ≤ N := by omega
  have he : extPoint N k ≤ extPoint N 1 := by
    exact extPoint_antitone_le hN1 (by omega : k ≤ N) hk1
  have hred : bSerre - extPoint N 1 ≤ bSerre - extPoint N k := by linarith
  have hangle : extAngle N 1 = Real.pi / (N : ℝ) := by
    unfold extAngle
    norm_num
  have hval : bSerre - extPoint N 1 =
      (bSerre - aSerre) / 2 * (1 - Real.cos (Real.pi / (N : ℝ))) := by
    rw [bSerre_sub_extPoint N 1]
    rw [hangle]
  have h2 : (2 : ℝ) / (N : ℝ) ^ 2 ≤ 1 - Real.cos (Real.pi / (N : ℝ)) :=
    two_div_sq_le_one_sub_cos_pi_div N hN
  have hL2pos : 0 < (bSerre - aSerre) / 2 := div_pos bSerre_sub_aSerre_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left h2 (hL2pos.le)
  have hstep : (bSerre - aSerre) / 2 * ((2 : ℝ) / (N : ℝ) ^ 2) = (bSerre - aSerre) / (N : ℝ) ^ 2 := by
    field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt hN1)]
  calc
    (bSerre - aSerre) / (N : ℝ) ^ 2 ≤ (bSerre - aSerre) / 2 * (1 - Real.cos (Real.pi / (N : ℝ))) := by
      rw [← hstep]
      exact hmul
    _ = bSerre - extPoint N 1 := hval.symm
    _ ≤ bSerre - extPoint N k := hred



/-- Margins of Chebyshev extremal points from both ends of the Serre interval:
`(bSerre − aSerre)/N² ≤ extPoint N k − aSerre` and
`(bSerre − aSerre)/N² ≤ bSerre − extPoint N k` for `1 ≤ k < N`, `3 ≤ N`. -/
theorem extPoint_margin :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 3 ≤ N → ∀ k : ℕ, 1 ≤ k → k < N →
      (c / (N : ℝ) ^ 2) ≤ extPoint N k - aSerre ∧
      (c / (N : ℝ) ^ 2) ≤ bSerre - extPoint N k := by
  refine ⟨bSerre - aSerre, bSerre_sub_aSerre_pos, ?_⟩
  intro N hN k hk1 hkN
  exact ⟨margin_left N hN hk1 hkN, margin_right N hN hk1 hkN⟩

/-- Same margins expressed through the bracket points of `prunedPoly r`
(`bracketPoint r i = extPoint (r+3) (i.val+1)`): all `r+1` bracket points lie
at distance `≥ c/(r+3)²` from both ends. -/
theorem bracketPoint_margin :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 3 ≤ r + 3 → ∀ i : Fin (r + 1),
      (c / ((r : ℝ) + 3) ^ 2) ≤ bracketPoint r i - aSerre ∧
      (c / ((r : ℝ) + 3) ^ 2) ≤ bSerre - bracketPoint r i := by
  refine ⟨bSerre - aSerre, bSerre_sub_aSerre_pos, ?_⟩
  intro r hr i
  have hcast : ((r + 3 : ℕ) : ℝ) = (r : ℝ) + 3 := by norm_num
  have hk1 : 1 ≤ i.val + 1 := by omega
  have hkN : i.val + 1 < r + 3 := by omega
  constructor
  · rw [← hcast]
    simpa [bracketPoint] using (margin_left (r + 3) hr hk1 hkN)
  · rw [← hcast]
    simpa [bracketPoint] using (margin_right (r + 3) hr hk1 hkN)

end Submission.ChebMargin
