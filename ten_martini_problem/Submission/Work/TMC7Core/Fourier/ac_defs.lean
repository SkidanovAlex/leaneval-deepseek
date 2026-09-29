/-
Shared definitions and elementary lemmas for the arithmetic core estimate
`Work.TMC7Core.Fourier.arith_core` (Avila--Jitomirskaya style harmonic-sum bound).

Imported by `arith_core.lean` and by the delegated helpers
(`win_count.lean`, `blk_weighted.lean`, `blk_first.lean`).
-/
import Mathlib
import Submission.Work.TMC7Core.Defs

namespace Work.TMC7Core.Fourier

open Finset

noncomputable section

/-- The weight `x ↦ (1 + (s x)^2)^{-1}` occurring in the arithmetic estimate. -/
def fw (s x : ℝ) : ℝ := (1 + (s * x) ^ 2)⁻¹

/-- Distance from `x` to the nearest multiple of the natural number `q`;
normalised so that `qDist q (q * x) = q * fracDist x`. -/
def qDist (q : ℕ) (x : ℝ) : ℝ := (q : ℝ) * fracDist (x / (q : ℝ))

/-! ## Elementary facts about `fracDist` -/

lemma fracDist_nonneg (x : ℝ) : 0 ≤ fracDist x := abs_nonneg _

lemma fracDist_le_half (x : ℝ) : fracDist x ≤ 1 / 2 := by
  have h := abs_sub_round x
  simpa only [fracDist] using h

lemma fracDist_eq_dist (x : ℝ) : fracDist x = dist x (round x : ℝ) := by
  rw [fracDist, Real.dist_eq]

lemma fracDist_add_intCast (x : ℝ) (n : ℤ) : fracDist (x + n) = fracDist x := by
  rw [fracDist, fracDist, round_add_intCast]
  congr 1
  push_cast
  ring

/-- The nearest multiple of `q` to `q * x` is `q * round x`. -/
lemma round_le_mul (q : ℕ) (hq : 1 ≤ q) (x : ℝ) :
    ∀ z : ℤ,
      dist ((q : ℝ) * x) ((q : ℝ) * (round x : ℤ)) ≤ dist ((q : ℝ) * x) ((q : ℝ) * (z : ℝ)) := by
  intro z
  have hqz : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [Real.dist_eq, Real.dist_eq, ← mul_sub, ← mul_sub, abs_mul, abs_mul,
    abs_of_nonneg (le_of_lt hqz)]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using round_le x z) (le_of_lt hqz)

lemma qDist_nonneg (q : ℕ) (x : ℝ) : 0 ≤ qDist q x := by
  rw [qDist, fracDist]
  positivity

lemma qDist_le (q : ℕ) (x : ℝ) : qDist q x ≤ (q : ℝ) / 2 := by
  have h := fracDist_le_half (x / (q : ℝ))
  have hq : (0 : ℝ) ≤ (q : ℝ) := by positivity
  rw [qDist]
  calc (q : ℝ) * fracDist (x / (q : ℝ)) ≤ (q : ℝ) * (1 / 2) :=
        mul_le_mul_of_nonneg_left h hq
    _ = (q : ℝ) / 2 := by ring

lemma qDist_mul_q (q : ℕ) (x : ℝ) : qDist q ((q : ℝ) * x) = (q : ℝ) * fracDist x := by
  rw [qDist]
  rcases Nat.eq_zero_or_pos q with hq | hq
  · simp [hq]
  · have hq0 : ((q : ℝ)) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hq)
    rw [mul_div_cancel_left₀ x hq0]

/-- `qDist q x` is the distance from `x` to the nearest multiple of `q`. -/
lemma qDist_eq (q : ℕ) (hq : 1 ≤ q) (x : ℝ) :
    qDist q x = dist x ((q : ℝ) * (round (x / (q : ℝ)) : ℤ)) := by
  have hqz : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : ((q : ℝ)) ≠ 0 := ne_of_gt hqz
  set r : ℝ := ((round (x / (q : ℝ)) : ℤ) : ℝ) with hr
  have h1 : qDist q x = (q : ℝ) * |x / (q : ℝ) - r| := by
    rw [qDist, fracDist, hr]
  have h2 : (q : ℝ) * |x / (q : ℝ) - r| = |(q : ℝ) * (x / (q : ℝ) - r)| := by
    rw [abs_mul, abs_of_nonneg (le_of_lt hqz)]
  have h3 : |(q : ℝ) * (x / (q : ℝ) - r)| = |x - (q : ℝ) * r| := by
    congr 1
    rw [mul_sub]
    congr 1
    field_simp
  rw [h1, h2, h3, Real.dist_eq]

/-! ## Elementary facts about the weight `fw` -/

lemma fw_nonneg (s x : ℝ) : 0 ≤ fw s x := by
  rw [fw]; positivity

lemma fw_pos (s x : ℝ) : 0 < fw s x := by
  rw [fw]; positivity

lemma fw_le_one (s x : ℝ) : fw s x ≤ 1 := by
  rw [fw]
  apply inv_le_one_of_one_le₀
  nlinarith [sq_nonneg (s * x)]

/-- `fw s` is antitone on `[0, ∞)`. -/
lemma fw_antitoneOn (s : ℝ) : AntitoneOn (fw s) (Set.Ici 0) := by
  intro a ha b hb hab
  have ha0 : 0 ≤ a := ha
  have hs : 0 ≤ s ^ 2 := sq_nonneg s
  have h : (s * a) ^ 2 ≤ (s * b) ^ 2 := by
    have h2 : (s * a) ^ 2 = s ^ 2 * a ^ 2 := by ring
    have h3 : (s * b) ^ 2 = s ^ 2 * b ^ 2 := by ring
    rw [h2, h3]
    exact mul_le_mul_of_nonneg_left (by nlinarith) hs
  simp only [fw]
  have h1 : (0:ℝ) < 1 + (s * a) ^ 2 := by positivity
  have h1' : (0:ℝ) < 1 + (s * b) ^ 2 := by positivity
  have h2 : 1 + (s * a) ^ 2 ≤ 1 + (s * b) ^ 2 := by linarith
  exact (inv_le_inv₀ h1' h1).mpr h2

/-- `fw s y ≤ fw s x` whenever `0 ≤ x ≤ y`. -/
lemma fw_le_of_le (s : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : fw s y ≤ fw s x :=
  fw_antitoneOn s hx (le_trans hx hxy) hxy

/-- The reciprocal-square bound. -/
lemma fw_le_inv_sq (s x : ℝ) (h : s * x ≠ 0) : fw s x ≤ 1 / (s * x) ^ 2 := by
  rw [fw]
  have h1 : (0:ℝ) < (s * x) ^ 2 := by positivity
  have h2 : (s * x) ^ 2 ≤ 1 + (s * x) ^ 2 := by linarith
  have h1' : (0:ℝ) < 1 + (s * x) ^ 2 := by linarith
  have h3 := (inv_le_inv₀ h1' h1).mpr h2
  simpa only [one_div] using h3

end

end Work.TMC7Core.Fourier
