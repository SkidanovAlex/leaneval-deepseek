import Mathlib
import Submission.Work.Diff.EXT.reactBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The componentwise bound for the symmetrized polarization `rmSym`

`rmSym X Y : Curv4 n` is the symmetrized polarized form of the quadratic reaction `reactionMap`
(see `Submission.Work.Diff.EXT.reactBase`); by definition

`rmSym X Y = (rmPair X Y + rmPair Y X)/2`

with

`rmPair X Y i j k l = ∑_{p,q} (X_{ijpq}Y_{klpq} + 2X_{ipkq}Y_{jplq} − 2X_{iplq}Y_{jpkq})
    − ∑_p (Ric(X)_{ip}Y_{pjkl} + Ric(X)_{jp}Y_{ipkl} + Ric(X)_{lp}Y_{ijkp} + Ric(X)_{kp}Y_{ijpl})`.

Every term is a product of one entry of `X` and one entry of `Y`, so if all entries of `X` are
bounded by `Mx ≥ 0` and all entries of `Y` by `My ≥ 0`, then each component is bounded by
`9 n² Mx My`: there are `n²` quadruples in the first double sum with `5` products each, and `n`
indices in the second single sum with `4` products each, each product contributing
`Mx My` (using `|Ric(X)_{ij}| ≤ n Mx`).  The constant is deliberately not sharp; only its
existence is used.
-/

open Finset
open scoped BigOperators

namespace Work.Diff.EXT.RmPair

/-! ## Elementary absolute-value helpers -/

private lemma abs_add_sub_le (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
  have h1 : |a + b - c| ≤ |a + b| + |c| := by
    rw [sub_eq_add_neg, ← abs_neg c]
    exact abs_add_le _ _
  linarith [abs_add_le a b]

private lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg, ← abs_neg b]
  exact abs_add_le _ _

private lemma abs_sum4_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h2 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

private lemma abs_mul_le_of {x y Mx My : ℝ} (hx : |x| ≤ Mx) (hy : |y| ≤ My) (hMx : 0 ≤ Mx) :
    |x * y| ≤ Mx * My := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) hMx

private lemma abs_smul_mul_le (c x y Mx My : ℝ) (hc : 0 ≤ c) (hx : |x| ≤ Mx) (hy : |y| ≤ My)
    (hMx : 0 ≤ Mx) : |c * x * y| ≤ c * (Mx * My) := by
  rw [mul_assoc, abs_mul, abs_of_nonneg hc, abs_mul]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hx hy (abs_nonneg _) hMx) hc

/-! ## Cardinality bounds for the two sums -/

private lemma sum2_abs_le {n : ℕ} (f : Fin n → Fin n → ℝ) (C : ℝ) (hf : ∀ p q, |f p q| ≤ C) :
    |∑ p, ∑ q, f p q| ≤ (n : ℝ) * ((n : ℝ) * C) := by
  calc |∑ p, ∑ q, f p q| ≤ ∑ p, |∑ q, f p q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, ∑ q, |f p q| := Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, ∑ q, C := Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hf p q
    _ = (n : ℝ) * ((n : ℝ) * C) := by simp [Finset.sum_const]

private lemma sum1_abs_le {n : ℕ} (f : Fin n → ℝ) (C : ℝ) (hf : ∀ p, |f p| ≤ C) :
    |∑ p, f p| ≤ (n : ℝ) * C := by
  calc |∑ p, f p| ≤ ∑ p, |f p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, C := Finset.sum_le_sum fun p _ => hf p
    _ = (n : ℝ) * C := by simp [Finset.sum_const]

/-- The componentwise bound for the Ricci contraction `ricF`: `|Ric(X)_{ij}| ≤ n Mx`. -/
private lemma abs_ricF_le {n : ℕ} {X : Submission.Diff.Alg.Curv4 n} {Mx : ℝ}
    (hX : ∀ i j k l, |X i j k l| ≤ Mx) (i j : Fin n) :
    |Work.Diff.GE.ricF X i j| ≤ (n : ℝ) * Mx := by
  rw [Work.Diff.GE.ricF]
  exact sum1_abs_le _ _ (fun a => hX a i a j)

/-! ## The bounds -/

/-- `|rmPair X Y i j k l| ≤ 9 n² Mx My` whenever the entries of `X` (resp. `Y`) are bounded by
`Mx ≥ 0` (resp. `My ≥ 0`). -/
private lemma rmPair_abs_le {n : ℕ} (X Y : Submission.Diff.Alg.Curv4 n) (Mx My : ℝ)
    (hx0 : 0 ≤ Mx) (_hy0 : 0 ≤ My) (hX : ∀ i j k l, |X i j k l| ≤ Mx)
    (hY : ∀ i j k l, |Y i j k l| ≤ My) (i j k l : Fin n) :
    |Work.Diff.EXT.rmPair X Y i j k l| ≤ 9 * (n : ℝ) * (n : ℝ) * (Mx * My) := by
  -- the first (double) sum: five products of one `X`- and one `Y`-entry each
  have hterm : ∀ p q : Fin n,
      |X i j p q * Y k l p q + 2 * X i p k q * Y j p l q - 2 * X i p l q * Y j p k q|
        ≤ 5 * (Mx * My) := by
    intro p q
    have h1 : |X i j p q * Y k l p q| ≤ Mx * My := abs_mul_le_of (hX i j p q) (hY k l p q) hx0
    have h2 : |2 * X i p k q * Y j p l q| ≤ 2 * (Mx * My) :=
      abs_smul_mul_le 2 (X i p k q) (Y j p l q) Mx My (by norm_num) (hX i p k q) (hY j p l q) hx0
    have h3 : |2 * X i p l q * Y j p k q| ≤ 2 * (Mx * My) :=
      abs_smul_mul_le 2 (X i p l q) (Y j p k q) Mx My (by norm_num) (hX i p l q) (hY j p k q) hx0
    calc |X i j p q * Y k l p q + 2 * X i p k q * Y j p l q - 2 * X i p l q * Y j p k q|
        ≤ |X i j p q * Y k l p q| + |2 * X i p k q * Y j p l q| + |2 * X i p l q * Y j p k q| :=
          abs_add_sub_le _ _ _
      _ ≤ 5 * (Mx * My) := by linarith
  -- the second (single) sum: four products, each of a Ricci contraction with a `Y`-entry
  have hterm2 : ∀ p : Fin n,
      |Work.Diff.GE.ricF X i p * Y p j k l + Work.Diff.GE.ricF X j p * Y i p k l
        + Work.Diff.GE.ricF X l p * Y i j k p + Work.Diff.GE.ricF X k p * Y i j p l|
        ≤ 4 * ((n : ℝ) * (Mx * My)) := by
    intro p
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : |Work.Diff.GE.ricF X i p * Y p j k l| ≤ (n : ℝ) * (Mx * My) := by
      have h := abs_mul_le_of (abs_ricF_le hX i p) (hY p j k l) (mul_nonneg hn0 hx0)
      calc |Work.Diff.GE.ricF X i p * Y p j k l| ≤ (n : ℝ) * Mx * My := h
        _ = (n : ℝ) * (Mx * My) := by ring
    have h2 : |Work.Diff.GE.ricF X j p * Y i p k l| ≤ (n : ℝ) * (Mx * My) := by
      have h := abs_mul_le_of (abs_ricF_le hX j p) (hY i p k l) (mul_nonneg hn0 hx0)
      calc |Work.Diff.GE.ricF X j p * Y i p k l| ≤ (n : ℝ) * Mx * My := h
        _ = (n : ℝ) * (Mx * My) := by ring
    have h3 : |Work.Diff.GE.ricF X l p * Y i j k p| ≤ (n : ℝ) * (Mx * My) := by
      have h := abs_mul_le_of (abs_ricF_le hX l p) (hY i j k p) (mul_nonneg hn0 hx0)
      calc |Work.Diff.GE.ricF X l p * Y i j k p| ≤ (n : ℝ) * Mx * My := h
        _ = (n : ℝ) * (Mx * My) := by ring
    have h4 : |Work.Diff.GE.ricF X k p * Y i j p l| ≤ (n : ℝ) * (Mx * My) := by
      have h := abs_mul_le_of (abs_ricF_le hX k p) (hY i j p l) (mul_nonneg hn0 hx0)
      calc |Work.Diff.GE.ricF X k p * Y i j p l| ≤ (n : ℝ) * Mx * My := h
        _ = (n : ℝ) * (Mx * My) := by ring
    calc |Work.Diff.GE.ricF X i p * Y p j k l + Work.Diff.GE.ricF X j p * Y i p k l
        + Work.Diff.GE.ricF X l p * Y i j k p + Work.Diff.GE.ricF X k p * Y i j p l|
        ≤ |Work.Diff.GE.ricF X i p * Y p j k l| + |Work.Diff.GE.ricF X j p * Y i p k l|
          + |Work.Diff.GE.ricF X l p * Y i j k p| + |Work.Diff.GE.ricF X k p * Y i j p l| :=
          abs_sum4_le _ _ _ _
      _ ≤ 4 * ((n : ℝ) * (Mx * My)) := by linarith
  have hS1 := sum2_abs_le (fun p q : Fin n =>
      X i j p q * Y k l p q + 2 * X i p k q * Y j p l q - 2 * X i p l q * Y j p k q)
      (5 * (Mx * My)) hterm
  have hS2 := sum1_abs_le (fun p : Fin n =>
      Work.Diff.GE.ricF X i p * Y p j k l + Work.Diff.GE.ricF X j p * Y i p k l
        + Work.Diff.GE.ricF X l p * Y i j k p + Work.Diff.GE.ricF X k p * Y i j p l)
      (4 * ((n : ℝ) * (Mx * My))) hterm2
  simp only [Work.Diff.EXT.rmPair]
  calc |(∑ p, ∑ q, (X i j p q * Y k l p q + 2 * X i p k q * Y j p l q
          - 2 * X i p l q * Y j p k q))
        - ∑ p, (Work.Diff.GE.ricF X i p * Y p j k l + Work.Diff.GE.ricF X j p * Y i p k l
          + Work.Diff.GE.ricF X l p * Y i j k p + Work.Diff.GE.ricF X k p * Y i j p l)|
      ≤ |∑ p, ∑ q, (X i j p q * Y k l p q + 2 * X i p k q * Y j p l q
          - 2 * X i p l q * Y j p k q)|
        + |∑ p, (Work.Diff.GE.ricF X i p * Y p j k l + Work.Diff.GE.ricF X j p * Y i p k l
          + Work.Diff.GE.ricF X l p * Y i j k p + Work.Diff.GE.ricF X k p * Y i j p l)| :=
        abs_sub_le_abs_add _ _
    _ ≤ (n : ℝ) * ((n : ℝ) * (5 * (Mx * My))) + (n : ℝ) * (4 * ((n : ℝ) * (Mx * My))) :=
        add_le_add hS1 hS2
    _ ≤ 9 * (n : ℝ) * (n : ℝ) * (Mx * My) := by nlinarith

/-- `|rmSym X Y i j k l| ≤ 9 n² Mx My`: the average of the two `rmPair` bounds. -/
private lemma rmSym_abs_le {n : ℕ} (X Y : Submission.Diff.Alg.Curv4 n) (Mx My : ℝ)
    (hx0 : 0 ≤ Mx) (hy0 : 0 ≤ My) (hX : ∀ i j k l, |X i j k l| ≤ Mx)
    (hY : ∀ i j k l, |Y i j k l| ≤ My) (i j k l : Fin n) :
    |Work.Diff.EXT.rmSym X Y i j k l| ≤ 9 * (n : ℝ) * (n : ℝ) * (Mx * My) := by
  have h1 := rmPair_abs_le X Y Mx My hx0 hy0 hX hY i j k l
  have h2 := rmPair_abs_le Y X My Mx hy0 hx0 hY hX i j k l
  have hcomm : 9 * (n : ℝ) * (n : ℝ) * (My * Mx) = 9 * (n : ℝ) * (n : ℝ) * (Mx * My) := by
    ring
  rw [hcomm] at h2
  have h3 : |(Work.Diff.EXT.rmPair X Y i j k l + Work.Diff.EXT.rmPair Y X i j k l) / 2|
      ≤ (|Work.Diff.EXT.rmPair X Y i j k l| + |Work.Diff.EXT.rmPair Y X i j k l|) / 2 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  simp only [Work.Diff.EXT.rmSym]
  linarith

theorem rmSym_bound (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (X Y : Submission.Diff.Alg.Curv4 n) (Mx My : ℝ), 0 ≤ Mx → 0 ≤ My →
      (∀ i j k l, |X i j k l| ≤ Mx) → (∀ i j k l, |Y i j k l| ≤ My) →
      ∀ i j k l, |Work.Diff.EXT.rmSym X Y i j k l| ≤ C * Mx * My := by
  refine ⟨9 * (n : ℝ) ^ 2, by positivity, ?_⟩
  intro X Y Mx My hx0 hy0 hX hY i j k l
  have h := rmSym_abs_le X Y Mx My hx0 hy0 hX hY i j k l
  calc |Work.Diff.EXT.rmSym X Y i j k l| ≤ 9 * (n : ℝ) * (n : ℝ) * (Mx * My) := h
    _ = 9 * (n : ℝ) ^ 2 * Mx * My := by ring

end Work.Diff.EXT.RmPair
