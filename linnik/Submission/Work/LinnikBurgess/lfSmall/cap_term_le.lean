import Mathlib
import Submission.Work.LinnikBurgess.lfSmall.two_defs
import Submission.Work.LinnikBurgess.lfSmall.capSet2_card_bound

/-!
# The cap term of the `p = 2` counting lemma

This module assembles the *cap term* estimate used in `lfSmall/counting_two`:

```
card (capSet2 e a b) * 2^(T/2) ≤ 10^6 * 2^((m + min J e)/2) * ind (DLp 2 (max T (min J e)) a b),
```

where `m = cubeLevel 2 e`, `T = capLevel 2 e` and `J = padicValNat 2 (contAB a b)`.

The indicator on the right is `1` as soon as the cap set is nonempty: `hcapT` gives `DLp 2 T`,
while `hcoeff` gives `DLp 2 J` (every value of `critN a b` is a combination of its coefficients),
and `max T (min J e)` is either `T` or `min J e ≤ J`.  The cardinality input is

* `capSet2_card_bound` when `J ≤ e`, giving `card ≤ 10^4 · 2^((m - T + 2 + J)/2)`;
* the trivial `card ≤ 2^m` when `e ≤ J`, where `min J e = e` and `m + T/2 = e/2 ≤ (m+e)/2`.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess.lfSmall

open Work.LinnikBurgess

/-! ## Elementary arithmetic of `cubeLevel 2` and `capLevel 2` -/

lemma cubeLevel_two_eq' (e : ℕ) : cubeLevel 2 e = (e + 3) / 3 := by simp [cubeLevel]

lemma two_mul_cubeLevel_le' {e : ℕ} (he : 13 ≤ e) : 2 * cubeLevel 2 e ≤ e := by
  rw [cubeLevel_two_eq']; omega

lemma capLevel_le_self' (e : ℕ) : capLevel 2 e ≤ e := by rw [capLevel]; exact Nat.sub_le _ _

lemma capLevel_cast {e : ℕ} (he : 13 ≤ e) :
    (capLevel 2 e : ℝ) = (e : ℝ) - 2 * (cubeLevel 2 e : ℝ) := by
  have h1 : 2 * cubeLevel 2 e ≤ e := two_mul_cubeLevel_le' he
  have h2 : capLevel 2 e = e - 2 * cubeLevel 2 e := rfl
  rw [h2, Nat.cast_sub h1]
  push_cast
  ring

/-! ## Monotonicity of `DLp` and the trivial cap-set bound -/

/-- `DLp 2 s a b` only gets easier as the level `s` decreases: the same witness works. -/
lemma dlp_mono {s s' : ℕ} {a b : Fin 3 → ℕ} (h : DLp 2 s a b) (hss : s' ≤ s) :
    DLp 2 s' a b := by
  obtain ⟨y, hy, h1, h2⟩ := h
  have hdvd : ((2 ^ s' : ℕ) : ℤ) ∣ ((2 ^ s : ℕ) : ℤ) :=
    by exact_mod_cast (pow_dvd_pow 2 hss : (2 : ℕ) ^ s' ∣ 2 ^ s)
  exact ⟨y, hy, dvd_trans hdvd h1, dvd_trans hdvd h2⟩

/-- If `c` divides every coefficient of `P`, then `c` divides `P.eval z`. -/
lemma eval_dvd_of_coeff_dvd {P : Polynomial ℤ} {c : ℤ} (h : ∀ n, c ∣ P.coeff n) (z : ℤ) :
    c ∣ P.eval z := by
  rw [Polynomial.eval_eq_sum_range]
  exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_left (h i) _)

/-- Coefficient-wise divisibility of `critN a b` by `2^J` at a unit point gives `DLp 2 J a b`. -/
lemma dlp_of_coeff_dvd {J : ℕ} {a b : Fin 3 → ℕ} {y : ℕ} (hy : UnitAt 2 y a b)
    (hcoeff : ∀ n, ((2 ^ J : ℕ) : ℤ) ∣ (critN a b).coeff n) : DLp 2 J a b := by
  refine ⟨y, hy, eval_dvd_of_coeff_dvd hcoeff _, ?_⟩
  apply eval_dvd_of_coeff_dvd _ _
  intro n
  rw [Polynomial.coeff_derivative]
  exact dvd_mul_of_dvd_left (hcoeff (n + 1)) _

/-- The cap set is contained in `[0, 2^m)`, so it has at most `2^m` elements. -/
lemma capSet2_card_le_range (e : ℕ) (a b : Fin 3 → ℕ) :
    (capSet2 e a b).card ≤ 2 ^ cubeLevel 2 e := by
  calc (capSet2 e a b).card ≤ (Finset.range (2 ^ cubeLevel 2 e)).card :=
        Finset.card_le_card (by
          intro y hy
          rw [capSet2] at hy
          exact (Finset.mem_filter.mp hy).1)
    _ = 2 ^ cubeLevel 2 e := Finset.card_range _

/-! ## The cap term estimate -/

theorem cap_term_le {e J : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hJc : padicValNat 2 (contAB a b) = J)
    (hcoeff : ∀ n, ((2 ^ J : ℕ) : ℤ) ∣ (critN a b).coeff n)
    (hi : ∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j)
    (hcapT : (capSet2 e a b).card ≠ 0 → DLp 2 (capLevel 2 e) a b)
    (hcapJ : (capSet2 e a b).card ≠ 0 → J ≤ e → DLp 2 J a b)
    (hJdvd : 2 ^ J ∣ contAB a b) :
    ((capSet2 e a b).card : ℝ) * (2 : ℝ) ^ ((capLevel 2 e : ℝ) / 2)
      ≤ (10 : ℝ) ^ 6 * ((2 : ℝ) ^ (((cubeLevel 2 e : ℝ) + ((min J e : ℕ) : ℝ)) / 2)
          * ind (DLp 2 (max (capLevel 2 e) (min J e)) a b)) := by
  by_cases hcard0 : (capSet2 e a b).card = 0
  · rw [hcard0, Nat.cast_zero, zero_mul]
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (((cubeLevel 2 e : ℝ) + ((min J e : ℕ) : ℝ)) / 2) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    have h3 : (0 : ℝ) ≤ ind (DLp 2 (max (capLevel 2 e) (min J e)) a b) := ind_nonneg _
    nlinarith [h2, h3]
  · have hdlpT : DLp 2 (capLevel 2 e) a b := hcapT hcard0
    have hdlpJ : DLp 2 J a b := by
      obtain ⟨y, hy⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard0)
      have hyU : UnitAt 2 y a b := by
        rw [capSet2] at hy
        exact (Finset.mem_filter.mp hy).2.1
      exact dlp_of_coeff_dvd hyU hcoeff
    have hmono : DLp 2 (max (capLevel 2 e) (min J e)) a b := by
      rcases le_total (min J e) (capLevel 2 e) with h | h
      · rw [max_eq_left h]
        exact hdlpT
      · rw [max_eq_right h]
        exact dlp_mono hdlpJ (min_le_left J e)
    rw [ind_eq_one_of _ hmono, mul_one]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((capLevel 2 e : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rcases lt_or_ge J e with hJlt | hJge
    · -- `J < e`: use the content bound `capSet2_card_bound`.
      rw [min_eq_left (le_of_lt hJlt)]
      have hcardle : ((capSet2 e a b).card : ℝ) ≤ (10 : ℝ) ^ 4 *
          (2 : ℝ) ^ (((cubeLevel 2 e : ℝ) - (capLevel 2 e : ℝ) + 2 + (J : ℝ)) / 2) :=
        capSet2_card_bound he a b i hJc hcoeff hi
      have hstep : ((capSet2 e a b).card : ℝ) * (2 : ℝ) ^ ((capLevel 2 e : ℝ) / 2)
          ≤ ((10 : ℝ) ^ 4
              * (2 : ℝ) ^ (((cubeLevel 2 e : ℝ) - (capLevel 2 e : ℝ) + 2 + (J : ℝ)) / 2))
            * (2 : ℝ) ^ ((capLevel 2 e : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hcardle (le_of_lt h2pos)
      refine le_trans hstep ?_
      have hprod : ((10 : ℝ) ^ 4
              * (2 : ℝ) ^ (((cubeLevel 2 e : ℝ) - (capLevel 2 e : ℝ) + 2 + (J : ℝ)) / 2))
            * (2 : ℝ) ^ ((capLevel 2 e : ℝ) / 2)
          = (10 : ℝ) ^ 4 * (2 : ℝ) ^ (((cubeLevel 2 e : ℝ) + (J : ℝ) + 2) / 2) := by
        rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        have hexp : ((cubeLevel 2 e : ℝ) - (capLevel 2 e : ℝ) + 2 + (J : ℝ)) / 2
            + (capLevel 2 e : ℝ) / 2 = ((cubeLevel 2 e : ℝ) + (J : ℝ) + 2) / 2 := by ring
        rw [hexp]
      rw [hprod]
      have heq : (2 : ℝ) ^ (((cubeLevel 2 e : ℝ) + (J : ℝ) + 2) / 2)
          = 2 * (2 : ℝ) ^ (((cubeLevel 2 e : ℝ) + (J : ℝ)) / 2) := by
        rw [show (((cubeLevel 2 e : ℝ) + (J : ℝ) + 2) / 2)
              = (((cubeLevel 2 e : ℝ) + (J : ℝ)) / 2) + 1 by ring,
            Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
        ring
      rw [heq]
      have hX : (0 : ℝ) ≤ (2 : ℝ) ^ (((cubeLevel 2 e : ℝ) + (J : ℝ)) / 2) :=
        le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
      nlinarith [hX]
    · -- `e ≤ J`: the trivial bound `card ≤ 2^m` suffices, and `min J e = e`.
      rw [min_eq_right hJge]
      have hrange := capSet2_card_le_range e a b
      have hcardle : ((capSet2 e a b).card : ℝ) ≤ (2 : ℝ) ^ ((cubeLevel 2 e : ℕ) : ℝ) := by
        have h1 : ((capSet2 e a b).card : ℝ) ≤ ((2 : ℝ) ^ cubeLevel 2 e : ℝ) := by
          exact_mod_cast hrange
        simpa only [Real.rpow_natCast] using h1
      have hstep : ((capSet2 e a b).card : ℝ) * (2 : ℝ) ^ ((capLevel 2 e : ℝ) / 2)
          ≤ (2 : ℝ) ^ ((cubeLevel 2 e : ℕ) : ℝ) * (2 : ℝ) ^ ((capLevel 2 e : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hcardle (le_of_lt h2pos)
      refine le_trans hstep ?_
      have hprod : (2 : ℝ) ^ ((cubeLevel 2 e : ℕ) : ℝ) * (2 : ℝ) ^ ((capLevel 2 e : ℝ) / 2)
          = (2 : ℝ) ^ ((e : ℝ) / 2) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        have hT := capLevel_cast he
        have hexp : ((cubeLevel 2 e : ℕ) : ℝ) + (capLevel 2 e : ℝ) / 2 = (e : ℝ) / 2 := by
          rw [hT]; ring
        rw [hexp]
      rw [hprod]
      have hle1 : (2 : ℝ) ^ ((e : ℝ) / 2)
          ≤ (2 : ℝ) ^ (((cubeLevel 2 e : ℝ) + (e : ℝ)) / 2) := by
        apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr
        have hm : (0 : ℝ) ≤ (cubeLevel 2 e : ℝ) := by positivity
        linarith
      have hle2 : (2 : ℝ) ^ (((cubeLevel 2 e : ℝ) + (e : ℝ)) / 2)
          ≤ (10 : ℝ) ^ 6 * (2 : ℝ) ^ (((cubeLevel 2 e : ℝ) + (e : ℝ)) / 2) := by
        have hpos : (0 : ℝ) < (2 : ℝ) ^ (((cubeLevel 2 e : ℝ) + (e : ℝ)) / 2) :=
          Real.rpow_pos_of_pos (by norm_num) _
        nlinarith [hpos]
      exact le_trans hle1 hle2

end Work.LinnikBurgess.lfSmall
