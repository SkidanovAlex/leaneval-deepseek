import Mathlib
import Submission.Work.Diff.EXT.reactBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The componentwise quadratic bound for the symmetrized reaction `rmSym`

`Work.Diff.EXT.rmSym X Y` is the symmetrized polarization of the quadratic level-`0` reaction
`Q(Rm) = reactionMap`.  Its components are explicit polynomial expressions in the components of
`X` and `Y` (`rmPair X Y i j k l` is a double sum over `p q` plus four Ricci contractions), so if
the components of `X` are bounded by `Mx` and those of `Y` by `My` then

`|rmSym X Y i j k l| ≤ C · Mx · My`

for a constant `C` depending only on `n` (explicitly `C = 9 n²`).  This is the "quadratic
continuity" estimate that lets the bounds on the curvature and its covariant derivatives be
propagated through the reaction term of the evolution equations.

## The proof

`rmSym X Y = (rmPair X Y + rmPair Y X) / 2`, so it suffices to bound `rmPair`.  Unfolding,
`rmPair X Y i j k l = S₁ - S₂` with

* `S₁ = ∑ p ∑ q (X i j p q * Y k l p q + 2 * X i p k q * Y j p l q - 2 * X i p l q * Y j p k q)`,
  whose summand is bounded by `5 * (Mx * My)` by the triangle inequality,
* `S₂ = ∑ p (Ric X i p * Y p j k l + Ric X j p * Y i p k l + Ric X l p * Y i j k p
  + Ric X k p * Y i j p l)`, with `|Ric X i p| ≤ n * Mx`, so each summand is bounded by
  `4 * (n * Mx * My)`.

Bounding a sum of `n` terms each of absolute value `≤ B` by `n * B` (`abs_sum_le_card`) gives
`|S₁| ≤ n * (n * 5 (Mx My))` and `|S₂| ≤ n * (4 n Mx My)`, so `|rmPair| ≤ 9 n² Mx My`.
-/

namespace Work.Diff.EXT.evX

/-- A sum of `m` real numbers, each of absolute value at most `B`, has absolute value at most
`m * B`. -/
lemma rmSym_boundV_abs_sum_le_card {m : ℕ} (f : Fin m → ℝ) (B : ℝ) (h : ∀ x, |f x| ≤ B) :
    |∑ x, f x| ≤ (m : ℝ) * B := by
  calc |∑ x, f x| ≤ ∑ x, |f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : Fin m, B := Finset.sum_le_sum (fun x _ => h x)
    _ = (m : ℝ) * B := by simp [Finset.sum_const, nsmul_eq_mul]

/-- A product of two real numbers bounded by `Mx`, `My` (both nonnegative) is bounded by
`Mx * My`. -/
lemma rmSym_boundV_abs_mul_le {a b Mx My : ℝ} (hMx : 0 ≤ Mx) (ha : |a| ≤ Mx) (hb : |b| ≤ My) :
    |a * b| ≤ Mx * My := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) hMx

/-- Triangle inequality for two terms, with abstract bounds. -/
lemma rmSym_boundV_abs_add_le_of {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a + b| ≤ A + B := by
  linarith [abs_add_le a b]

/-- Triangle inequality for a difference, with abstract bounds. -/
lemma rmSym_boundV_abs_sub_le_of {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a - b| ≤ A + B := by
  have e : a - b = a + (-b) := by ring
  rw [e]
  have h := abs_add_le a (-b)
  rw [abs_neg] at h
  linarith

/-- Triangle inequality for the combination `a + b - c` occurring in `rmPair`. -/
lemma rmSym_boundV_abs_three_le {a b c A B C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B)
    (hc : |c| ≤ C) : |a + b - c| ≤ A + B + C := by
  have h1 : |a + b| ≤ A + B := rmSym_boundV_abs_add_le_of ha hb
  exact rmSym_boundV_abs_sub_le_of h1 hc

/-- Triangle inequality for the four-term Ricci contraction of `rmPair`. -/
lemma rmSym_boundV_abs_four_le {a b c d A B C D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B)
    (hc : |c| ≤ C) (hd : |d| ≤ D) : |a + b + c + d| ≤ A + B + C + D := by
  have h1 := rmSym_boundV_abs_add_le_of ha hb
  have h2 := rmSym_boundV_abs_add_le_of hc hd
  have h3 := rmSym_boundV_abs_add_le_of h1 h2
  have e : a + b + c + d = (a + b) + (c + d) := by ring
  rw [e]; linarith

/-- The components of the Ricci contraction `ricF X i j = ∑ a, X a i a j` are bounded by
`n * Mx` when the components of `X` are bounded by `Mx`. -/
lemma rmSym_boundV_abs_ricF_le {n : ℕ} {X : Submission.Diff.Alg.Curv4 n} {Mx : ℝ}
    (hX : ∀ i j k l, |X i j k l| ≤ Mx) (i j : Fin n) :
    |Work.Diff.GE.ricF X i j| ≤ (n : ℝ) * Mx := by
  rw [show Work.Diff.GE.ricF X i j = ∑ a, X a i a j from rfl]
  exact rmSym_boundV_abs_sum_le_card (fun a => X a i a j) Mx (fun a => hX a i a j)

/-- The componentwise bound for `rmPair`: `|rmPair X Y i j k l| ≤ 9 n² Mx My`. -/
lemma rmSym_boundV_abs_rmPair_le {n : ℕ} {X Y : Submission.Diff.Alg.Curv4 n} {Mx My : ℝ}
    (hMx : 0 ≤ Mx) (_hMy : 0 ≤ My)
    (hX : ∀ i j k l, |X i j k l| ≤ Mx) (hY : ∀ i j k l, |Y i j k l| ≤ My)
    (i j k l : Fin n) :
    |Work.Diff.EXT.rmPair X Y i j k l| ≤ 9 * (n : ℝ)^2 * Mx * My := by
  have hT : ∀ p q : Fin n,
      |X i j p q * Y k l p q + 2 * X i p k q * Y j p l q - 2 * X i p l q * Y j p k q|
        ≤ 5 * (Mx * My) := by
    intro p q
    have hA : |X i j p q * Y k l p q| ≤ Mx * My :=
      rmSym_boundV_abs_mul_le hMx (hX i j p q) (hY k l p q)
    have hB : |2 * X i p k q * Y j p l q| ≤ 2 * (Mx * My) := by
      have h2 : |2 * X i p k q| ≤ 2 * Mx := by
        rw [show (2 : ℝ) * X i p k q = 2 * X i p k q from rfl, abs_mul,
            abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
        linarith [hX i p k q]
      have h := rmSym_boundV_abs_mul_le (mul_nonneg (by norm_num) hMx) h2 (hY j p l q)
      rwa [show (2 * Mx) * My = 2 * (Mx * My) from by ring] at h
    have hC : |2 * X i p l q * Y j p k q| ≤ 2 * (Mx * My) := by
      have h2 : |2 * X i p l q| ≤ 2 * Mx := by
        rw [show (2 : ℝ) * X i p l q = 2 * X i p l q from rfl, abs_mul,
            abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
        linarith [hX i p l q]
      have h := rmSym_boundV_abs_mul_le (mul_nonneg (by norm_num) hMx) h2 (hY j p k q)
      rwa [show (2 * Mx) * My = 2 * (Mx * My) from by ring] at h
    have h := rmSym_boundV_abs_three_le hA hB hC
    linarith
  have hU : ∀ p : Fin n,
      |Work.Diff.GE.ricF X i p * Y p j k l + Work.Diff.GE.ricF X j p * Y i p k l
        + Work.Diff.GE.ricF X l p * Y i j k p + Work.Diff.GE.ricF X k p * Y i j p l|
        ≤ 4 * ((n : ℝ) * Mx * My) := by
    intro p
    have h1 : |Work.Diff.GE.ricF X i p * Y p j k l| ≤ (n : ℝ) * Mx * My :=
      rmSym_boundV_abs_mul_le (mul_nonneg (Nat.cast_nonneg n) hMx)
        (rmSym_boundV_abs_ricF_le hX i p) (hY p j k l)
    have h2 : |Work.Diff.GE.ricF X j p * Y i p k l| ≤ (n : ℝ) * Mx * My :=
      rmSym_boundV_abs_mul_le (mul_nonneg (Nat.cast_nonneg n) hMx)
        (rmSym_boundV_abs_ricF_le hX j p) (hY i p k l)
    have h3 : |Work.Diff.GE.ricF X l p * Y i j k p| ≤ (n : ℝ) * Mx * My :=
      rmSym_boundV_abs_mul_le (mul_nonneg (Nat.cast_nonneg n) hMx)
        (rmSym_boundV_abs_ricF_le hX l p) (hY i j k p)
    have h4 : |Work.Diff.GE.ricF X k p * Y i j p l| ≤ (n : ℝ) * Mx * My :=
      rmSym_boundV_abs_mul_le (mul_nonneg (Nat.cast_nonneg n) hMx)
        (rmSym_boundV_abs_ricF_le hX k p) (hY i j p l)
    have h := rmSym_boundV_abs_four_le h1 h2 h3 h4
    linarith
  have hS1 : |∑ p, ∑ q, (X i j p q * Y k l p q + 2 * X i p k q * Y j p l q
        - 2 * X i p l q * Y j p k q)|
      ≤ (n : ℝ) * ((n : ℝ) * (5 * (Mx * My))) :=
    rmSym_boundV_abs_sum_le_card
      (fun p => ∑ q, (X i j p q * Y k l p q + 2 * X i p k q * Y j p l q
        - 2 * X i p l q * Y j p k q))
      ((n : ℝ) * (5 * (Mx * My)))
      (fun p => rmSym_boundV_abs_sum_le_card
        (fun q => (X i j p q * Y k l p q + 2 * X i p k q * Y j p l q - 2 * X i p l q * Y j p k q))
        (5 * (Mx * My)) (fun q => hT p q))
  have hS2 : |∑ p, (Work.Diff.GE.ricF X i p * Y p j k l + Work.Diff.GE.ricF X j p * Y i p k l
        + Work.Diff.GE.ricF X l p * Y i j k p + Work.Diff.GE.ricF X k p * Y i j p l)|
      ≤ (n : ℝ) * (4 * ((n : ℝ) * Mx * My)) :=
    rmSym_boundV_abs_sum_le_card
      (fun p => (Work.Diff.GE.ricF X i p * Y p j k l + Work.Diff.GE.ricF X j p * Y i p k l
        + Work.Diff.GE.ricF X l p * Y i j k p + Work.Diff.GE.ricF X k p * Y i j p l))
      (4 * ((n : ℝ) * Mx * My)) hU
  have hmain : |Work.Diff.EXT.rmPair X Y i j k l|
      ≤ (n : ℝ) * ((n : ℝ) * (5 * (Mx * My))) + (n : ℝ) * (4 * ((n : ℝ) * Mx * My)) := by
    have h := rmSym_boundV_abs_sub_le_of hS1 hS2
    convert h using 2
    exact rfl
  have htot : (n : ℝ) * ((n : ℝ) * (5 * (Mx * My))) + (n : ℝ) * (4 * ((n : ℝ) * Mx * My))
      = 9 * (n : ℝ)^2 * Mx * My := by ring
  linarith

theorem rmSym_boundV (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (X Y : Submission.Diff.Alg.Curv4 n) (Mx My : ℝ), 0 ≤ Mx → 0 ≤ My →
      (∀ i j k l, |X i j k l| ≤ Mx) → (∀ i j k l, |Y i j k l| ≤ My) →
      ∀ i j k l, |Work.Diff.EXT.rmSym X Y i j k l| ≤ C * Mx * My := by
  refine ⟨9 * (n : ℝ)^2, by positivity, ?_⟩
  intro X Y Mx My hMx hMy hX hY i j k l
  have h1 := rmSym_boundV_abs_rmPair_le (X := X) (Y := Y) (Mx := Mx) (My := My)
    hMx hMy hX hY i j k l
  have h2 := rmSym_boundV_abs_rmPair_le (X := Y) (Y := X) (Mx := My) (My := Mx)
    hMy hMx hY hX i j k l
  have hsym : |Work.Diff.EXT.rmSym X Y i j k l|
      ≤ (|Work.Diff.EXT.rmPair X Y i j k l| + |Work.Diff.EXT.rmPair Y X i j k l|) / 2 := by
    rw [show Work.Diff.EXT.rmSym X Y i j k l
        = (Work.Diff.EXT.rmPair X Y i j k l + Work.Diff.EXT.rmPair Y X i j k l) / 2 from rfl,
      abs_div, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  nlinarith [h1, h2, hsym]

end Work.Diff.EXT.evX
