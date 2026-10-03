/-
# The final arithmetic of the `ssu` assembly

`ssuArithFinal` is the closing arithmetic estimate of the `ssu` chain: given

* the two size bounds `Qb ≤ 2^{2CπΦ(l)}`, `Nb ≤ Csh² · 2^{2·2^{ρl}}` on the arithmetic
  quantities of the Ionescu--Wainger height bounds,
* the exponent `E` dominating `Kdev·Φ(l) + 2·2^{ρl} + Kdev`,
* and `u` dominating `E + (cI/2)·l + Kerr`,

it bounds the total error

`2CI·(2^{-cI(l-1)} + E^{-cI/ρ}) + 2·2π·(2^E·2^{-3u} + sc·2^{Ed}·2^{-3du}) + 6·Qb·Nb/2^E`

by `(2CI(2^{cI}+1)+2) · 2^{-(cI/2)l}`.  The three terms are handled separately:

* the `CI` term is `≤ 2CI(2^{cI}+1)·2^{-(cI/2)l}` (using `E ≥ 2^{ρl}`);
* the `2π` term is `≤ 2^{-(cI/2)l}` (using `u` and `2^{-Kerr} = 1/(8π(sc+2))`);
* the `Qb·Nb` term is `≤ 2^{-(cI/2)l}` (using `E` and `2^{-logb 2 (6Csh²)} = 1/(6Csh²)`).

The four estimates are split off as private lemmas (`ssuArith_T1`, `ssuArith_T2a`,
`ssuArith_T2b`, `ssuArith_T3`) so that each is proved in a small context; the main
theorem only assembles them.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SsuPhi

namespace Work.KMTPlan.A6

/-- The `CI` term of `ssuArithFinal`: `2 CI (2^{-cI(l-1)} + E^{-cI/ρ}) ≤ 2 CI (2^{cI}+1) 2^{-(cI/2)l}`. -/
private lemma ssuArith_T1 (ρ cI CI : ℝ) (L E : ℕ) (hρ : 0 < ρ) (hcI : 0 < cI) (hCI : 0 ≤ CI)
    (hEρ : (2 : ℝ) ^ (ρ * (L : ℝ)) ≤ (E : ℝ)) :
    2 * CI * ((2 : ℝ) ^ (-(cI * ((L : ℝ) - 1))) + (E : ℝ) ^ (-(cI / ρ)))
      ≤ 2 * CI * (2 ^ cI + 1) * (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h21 : (1 : ℝ) ≤ 2 := by norm_num
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hA0 : (0 : ℝ) < (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := Real.rpow_pos_of_pos h2 _
  have h1 : (2 : ℝ) ^ (-(cI * ((L : ℝ) - 1))) = (2 : ℝ) ^ cI * (2 : ℝ) ^ (-(cI * (L : ℝ))) := by
    rw [← Real.rpow_add h2]
    congr 1; ring
  have hexp1 : -(cI * (L : ℝ)) ≤ -((cI / 2) * (L : ℝ)) := by
    have : (cI / 2) * (L : ℝ) ≤ cI * (L : ℝ) := by nlinarith only [hcI, hL0]
    linarith only [this]
  have h2' : (2 : ℝ) ^ (-(cI * (L : ℝ))) ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le h21 hexp1
  have h1' : (2 : ℝ) ^ (-(cI * ((L : ℝ) - 1)))
      ≤ (2 : ℝ) ^ cI * (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := by
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2' (Real.rpow_nonneg (le_of_lt h2) _)
  have hx : (0 : ℝ) < (2 : ℝ) ^ (ρ * (L : ℝ)) := Real.rpow_pos_of_pos h2 _
  have hz : -(cI / ρ) ≤ 0 := by
    have : 0 < cI / ρ := div_pos hcI hρ
    linarith only [this]
  have hm := Real.rpow_le_rpow_of_nonpos hx hEρ hz
  have hmul : ((2 : ℝ) ^ (ρ * (L : ℝ))) ^ (-(cI / ρ)) = (2 : ℝ) ^ (-(cI * (L : ℝ))) := by
    rw [← Real.rpow_mul (le_of_lt h2) (ρ * (L : ℝ)) (-(cI / ρ))]
    congr 1
    field_simp
  have h2'' : (E : ℝ) ^ (-(cI / ρ)) ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := by
    rw [hmul] at hm
    exact le_trans hm h2'
  have hsum : (2 : ℝ) ^ (-(cI * ((L : ℝ) - 1))) + (E : ℝ) ^ (-(cI / ρ))
      ≤ (2 ^ cI + 1) * (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := by
    have h := add_le_add h1' h2''
    have heq : (2 ^ cI + 1) * (2 : ℝ) ^ (-((cI / 2) * (L : ℝ)))
        = (2 : ℝ) ^ cI * (2 : ℝ) ^ (-((cI / 2) * (L : ℝ)))
          + (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := by ring
    linarith only [h, heq]
  have h := mul_le_mul_of_nonneg_left hsum (by linarith only [hCI] : (0 : ℝ) ≤ 2 * CI)
  calc 2 * CI * ((2 : ℝ) ^ (-(cI * ((L : ℝ) - 1))) + (E : ℝ) ^ (-(cI / ρ)))
      ≤ 2 * CI * ((2 ^ cI + 1) * (2 : ℝ) ^ (-((cI / 2) * (L : ℝ)))) := h
    _ = 2 * CI * (2 ^ cI + 1) * (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := by ring

/-- The first half of the `2π` term of `ssuArithFinal`: `2 (2π · 2^E · 2^{-3u}) ≤ 2^{-(cI/2)l}/2`. -/
private lemma ssuArith_T2a (ρ cI Csh Kerr sc : ℝ) (L E u : ℕ) (hsc : 0 ≤ sc)
    (hKerr : Kerr = Real.logb 2 (8 * Real.pi * (sc + 2)))
    (hEu : (E : ℝ) + (cI / 2) * (L : ℝ) + Kerr ≤ 3 * (u : ℝ)) :
    2 * (2 * Real.pi * ((2 : ℝ) ^ E * (2 : ℝ) ^ (-(3 * (u : ℤ)))))
      ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) / 2 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h21 : (1 : ℝ) ≤ 2 := by norm_num
  have hA0 : (0 : ℝ) < (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := Real.rpow_pos_of_pos h2 _
  have hspos : (0 : ℝ) < 8 * Real.pi * (sc + 2) := by
    have : (0 : ℝ) < sc + 2 := by linarith only [hsc]
    positivity
  have hX : (2 : ℝ) ^ E * (2 : ℝ) ^ (-(3 * (u : ℤ)))
      ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) * (8 * Real.pi * (sc + 2))⁻¹ := by
    have hc1 : (2 : ℝ) ^ E = (2 : ℝ) ^ ((E : ℝ)) := (Real.rpow_natCast 2 E).symm
    have hc2 : (2 : ℝ) ^ (-(3 * (u : ℤ))) = (2 : ℝ) ^ (-(3 * (u : ℝ))) := by
      rw [← Real.rpow_intCast (2 : ℝ) (-(3 * (u : ℤ)))]
      congr 1; push_cast; ring
    have hprod : (2 : ℝ) ^ ((E : ℝ)) * (2 : ℝ) ^ (-(3 * (u : ℝ)))
        = (2 : ℝ) ^ ((E : ℝ) - 3 * (u : ℝ)) := by
      have : (E : ℝ) - 3 * (u : ℝ) = (E : ℝ) + -(3 * (u : ℝ)) := by ring
      rw [this, Real.rpow_add h2]
    have hexp : (E : ℝ) - 3 * (u : ℝ) ≤ -((cI / 2) * (L : ℝ) + Kerr) := by linarith only [hEu]
    have hmono : (2 : ℝ) ^ ((E : ℝ) - 3 * (u : ℝ))
        ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ) + Kerr)) :=
      Real.rpow_le_rpow_of_exponent_le h21 hexp
    have hsplit : (2 : ℝ) ^ (-((cI / 2) * (L : ℝ) + Kerr))
        = (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) * (2 : ℝ) ^ (-Kerr) := by
      have : -((cI / 2) * (L : ℝ) + Kerr) = -((cI / 2) * (L : ℝ)) + -Kerr := by ring
      rw [this, Real.rpow_add h2]
    have hKerrval : (2 : ℝ) ^ (-Kerr) = (8 * Real.pi * (sc + 2))⁻¹ := by
      rw [hKerr]
      rw [Real.rpow_neg (le_of_lt h2) _]
      rw [Real.rpow_logb h2 (by norm_num) hspos]
    calc (2 : ℝ) ^ E * (2 : ℝ) ^ (-(3 * (u : ℤ)))
        = (2 : ℝ) ^ ((E : ℝ) - 3 * (u : ℝ)) := by rw [hc1, hc2, hprod]
      _ ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ) + Kerr)) := hmono
      _ = (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) * (8 * Real.pi * (sc + 2))⁻¹ := by
            rw [hsplit, hKerrval]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hq : 4 * Real.pi * (8 * Real.pi * (sc + 2))⁻¹ ≤ (1 : ℝ) / 2 := by
    rw [inv_eq_one_div]
    rw [show (4 : ℝ) * Real.pi * (1 / (8 * Real.pi * (sc + 2)))
        = 4 * Real.pi / (8 * Real.pi * (sc + 2)) by ring]
    rw [div_le_iff₀ hspos]
    have h1 : (1 : ℝ) ≤ sc + 2 := by linarith only [hsc]
    have heq : (1 : ℝ) / 2 * (8 * Real.pi * (sc + 2)) = 4 * Real.pi * (sc + 2) := by ring
    rw [heq]
    calc 4 * Real.pi = 4 * Real.pi * 1 := by ring
      _ ≤ 4 * Real.pi * (sc + 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hYY : 2 * (2 * Real.pi * ((2 : ℝ) ^ (-((cI / 2) * (L : ℝ)))
        * (8 * Real.pi * (sc + 2))⁻¹))
      ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) / 2 := by
    calc 2 * (2 * Real.pi * ((2 : ℝ) ^ (-((cI / 2) * (L : ℝ)))
          * (8 * Real.pi * (sc + 2))⁻¹))
        = (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) * (4 * Real.pi * (8 * Real.pi * (sc + 2))⁻¹) := by
          ring
      _ ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) * (1 / 2) :=
            mul_le_mul_of_nonneg_left hq (le_of_lt hA0)
      _ = (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) / 2 := by ring
  exact le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hX (by positivity)) (by norm_num)) hYY

/-- The second half of the `2π` term: `2 (2π · sc · 2^{Ed} · 2^{-3du}) ≤ 2^{-(cI/2)l}/2`. -/
private lemma ssuArith_T2b (ρ cI Csh Kerr sc : ℝ) (d L E u : ℕ) (hd : 1 ≤ d) (hcI : 0 < cI)
    (hsc : 0 ≤ sc) (hKerr : Kerr = Real.logb 2 (8 * Real.pi * (sc + 2)))
    (hEu : (E : ℝ) + (cI / 2) * (L : ℝ) + Kerr ≤ 3 * (u : ℝ)) :
    2 * (2 * Real.pi * (sc * ((2 : ℝ) ^ E) ^ d
        * (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ)))))
      ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) / 2 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h21 : (1 : ℝ) ≤ 2 := by norm_num
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hA0 : (0 : ℝ) < (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := Real.rpow_pos_of_pos h2 _
  have hspos : (0 : ℝ) < 8 * Real.pi * (sc + 2) := by
    have : (0 : ℝ) < sc + 2 := by linarith only [hsc]
    positivity
  have hKerrpos : 0 ≤ Kerr := by
    rw [hKerr]
    apply le_of_lt
    apply Real.logb_pos (by norm_num)
    have h2' : (1 : ℝ) < sc + 2 := by linarith only [hsc]
    have h8 : (1 : ℝ) < 8 * Real.pi := by nlinarith only [Real.pi_gt_three]
    nlinarith only [h8, h2']
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hY : sc * ((2 : ℝ) ^ E) ^ d * (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ)))
      ≤ sc * ((2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) * (8 * Real.pi * (sc + 2))⁻¹) := by
    have hc3 : ((2 : ℝ) ^ E) ^ d = (2 : ℝ) ^ ((E : ℝ) * d) := by
      rw [← pow_mul, (Real.rpow_natCast 2 (E * d)).symm]
      congr 1; push_cast; ring
    have hc4 : (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ)))
        = (2 : ℝ) ^ (-(3 * (d : ℝ) * (u : ℝ))) := by
      rw [← Real.rpow_intCast (2 : ℝ) (-(3 * (d : ℤ) * (u : ℤ)))]
      congr 1; push_cast; ring
    have hprod : (2 : ℝ) ^ ((E : ℝ) * d) * (2 : ℝ) ^ (-(3 * (d : ℝ) * (u : ℝ)))
        = (2 : ℝ) ^ ((E : ℝ) * d - 3 * (d : ℝ) * (u : ℝ)) := by
      have : (E : ℝ) * d - 3 * (d : ℝ) * (u : ℝ)
          = (E : ℝ) * d + -(3 * (d : ℝ) * (u : ℝ)) := by ring
      rw [this, Real.rpow_add h2]
    have hexp1 : (E : ℝ) - 3 * (u : ℝ) ≤ -((cI / 2) * (L : ℝ) + Kerr) := by linarith only [hEu]
    have hQnn : (0 : ℝ) ≤ (cI / 2) * (L : ℝ) + Kerr := by
      have h1 : (0 : ℝ) ≤ (cI / 2) * (L : ℝ) := by
        have : (0 : ℝ) ≤ cI / 2 := by linarith only [hcI]
        exact mul_nonneg this hL0
      linarith only [h1, hKerrpos]
    have hdB : (d : ℝ) * ((E : ℝ) - 3 * (u : ℝ)) ≤ -((cI / 2) * (L : ℝ) + Kerr) := by
      have h1 : (d : ℝ) * ((E : ℝ) - 3 * (u : ℝ))
          ≤ (d : ℝ) * (-((cI / 2) * (L : ℝ) + Kerr)) :=
        mul_le_mul_of_nonneg_left hexp1 hd0
      have h2 : (d : ℝ) * (-((cI / 2) * (L : ℝ) + Kerr))
          ≤ -((cI / 2) * (L : ℝ) + Kerr) := by
        have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        nlinarith only [hd1, hQnn]
      linarith only [h1, h2]
    have hexp2 : (E : ℝ) * d - 3 * (d : ℝ) * (u : ℝ) ≤ -((cI / 2) * (L : ℝ) + Kerr) := by
      have heq : (E : ℝ) * d - 3 * (d : ℝ) * (u : ℝ) = (d : ℝ) * ((E : ℝ) - 3 * (u : ℝ)) := by
        ring
      rw [heq]; exact hdB
    have hmono : (2 : ℝ) ^ ((E : ℝ) * d - 3 * (d : ℝ) * (u : ℝ))
        ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ) + Kerr)) :=
      Real.rpow_le_rpow_of_exponent_le h21 hexp2
    have hsplit : (2 : ℝ) ^ (-((cI / 2) * (L : ℝ) + Kerr))
        = (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) * (2 : ℝ) ^ (-Kerr) := by
      have : -((cI / 2) * (L : ℝ) + Kerr) = -((cI / 2) * (L : ℝ)) + -Kerr := by ring
      rw [this, Real.rpow_add h2]
    have hKerrval : (2 : ℝ) ^ (-Kerr) = (8 * Real.pi * (sc + 2))⁻¹ := by
      rw [hKerr]
      rw [Real.rpow_neg (le_of_lt h2) _]
      rw [Real.rpow_logb h2 (by norm_num) hspos]
    have hkey : ((2 : ℝ) ^ E) ^ d * (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ)))
        ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) * (8 * Real.pi * (sc + 2))⁻¹ := by
      calc ((2 : ℝ) ^ E) ^ d * (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ)))
          = (2 : ℝ) ^ ((E : ℝ) * d - 3 * (d : ℝ) * (u : ℝ)) := by rw [hc3, hc4, hprod]
        _ ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ) + Kerr)) := hmono
        _ = (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) * (8 * Real.pi * (sc + 2))⁻¹ := by
              rw [hsplit, hKerrval]
    calc sc * ((2 : ℝ) ^ E) ^ d * (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ)))
        = sc * (((2 : ℝ) ^ E) ^ d * (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ)))) := by ring
      _ ≤ sc * ((2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) * (8 * Real.pi * (sc + 2))⁻¹) :=
            mul_le_mul_of_nonneg_left hkey hsc
  have hqsc : 4 * Real.pi * sc * (8 * Real.pi * (sc + 2))⁻¹ ≤ (1 : ℝ) / 2 := by
    rw [inv_eq_one_div]
    rw [show (4 : ℝ) * Real.pi * sc * (1 / (8 * Real.pi * (sc + 2)))
        = 4 * Real.pi * sc / (8 * Real.pi * (sc + 2)) by ring]
    rw [div_le_iff₀ hspos]
    have h1 : sc ≤ sc + 2 := by linarith only
    have heq : (1 : ℝ) / 2 * (8 * Real.pi * (sc + 2)) = 4 * Real.pi * (sc + 2) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hYY : 2 * (2 * Real.pi * (sc * ((2 : ℝ) ^ (-((cI / 2) * (L : ℝ)))
        * (8 * Real.pi * (sc + 2))⁻¹)))
      ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) / 2 := by
    calc 2 * (2 * Real.pi * (sc * ((2 : ℝ) ^ (-((cI / 2) * (L : ℝ)))
          * (8 * Real.pi * (sc + 2))⁻¹)))
        = (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) * (4 * Real.pi * sc * (8 * Real.pi * (sc + 2))⁻¹) := by
          ring
      _ ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) * (1 / 2) :=
            mul_le_mul_of_nonneg_left hqsc (le_of_lt hA0)
      _ = (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) / 2 := by ring
  exact le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hY (by positivity)) (by norm_num)) hYY

/-- The `Qb·Nb` term of `ssuArithFinal`: `6 Qb Nb / 2^E ≤ 2^{-(cI/2)l}`. -/
private lemma ssuArith_T3 (ρ cI Cπ Csh Kdev Qb Nb : ℝ) (L E : ℕ) (hCπ : 0 ≤ Cπ) (hCsh : 1 ≤ Csh)
    (hcI : 0 < cI) (hQb0 : 0 ≤ Qb) (hNb0 : 0 ≤ Nb)
    (hQb : Qb ≤ (2 : ℝ) ^ (2 * Cπ * ssuPhi ρ L))
    (hNb : Nb ≤ Csh ^ 2 * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (L : ℝ))))
    (hKdev : Kdev = 2 * Cπ + Real.logb 2 (6 * Csh ^ 2) + cI / 2)
    (hEdev : Kdev * ssuPhi ρ L + 2 * (2 : ℝ) ^ (ρ * (L : ℝ)) + Kdev ≤ (E : ℝ)) :
    6 * Qb * Nb / (2 : ℝ) ^ E ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h21 : (1 : ℝ) ≤ 2 := by norm_num
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  set Φ : ℝ := ssuPhi ρ L with hΦdef
  have hΦ1 : 1 ≤ Φ := by rw [hΦdef]; exact one_le_ssuPhi ρ L
  have hΦL1 : (L : ℝ) + 1 ≤ Φ := by
    rw [hΦdef]
    have hB : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (L : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    simp only [ssuPhi]; linarith only [hL0, hB, mul_nonneg hL0 hB]
  have h6Cgt1 : (1 : ℝ) < 6 * Csh ^ 2 := by nlinarith only [hCsh]
  have h6C1 : (1 : ℝ) ≤ 6 * Csh ^ 2 := le_of_lt h6Cgt1
  have h6Cpos : (0 : ℝ) < 6 * Csh ^ 2 := by linarith only [h6Cgt1]
  have hlogval : (2 : ℝ) ^ (Real.logb 2 (6 * Csh ^ 2)) = 6 * Csh ^ 2 :=
    Real.rpow_logb h2 (by norm_num) h6Cpos
  have hKdevnonneg : 0 ≤ Kdev := by
    rw [hKdev]
    have h0 := Real.logb_pos (by norm_num : (1 : ℝ) < 2) h6Cgt1
    have h1 : (0 : ℝ) ≤ cI / 2 := by linarith only [hcI]
    have h2' : (0 : ℝ) ≤ 2 * Cπ := by
      have : (0 : ℝ) ≤ Cπ := by linarith only [hCπ]
      linarith only [this]
    linarith only [h0, h1, h2']
  have hnum : Qb * Nb ≤ Csh ^ 2 * (2 : ℝ) ^ (2 * Cπ * Φ + 2 * (2 : ℝ) ^ (ρ * (L : ℝ))) := by
    have h1 : (2 : ℝ) ^ (2 * Cπ * Φ) * (Csh ^ 2 * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (L : ℝ))))
        = Csh ^ 2 * (2 : ℝ) ^ (2 * Cπ * Φ + 2 * (2 : ℝ) ^ (ρ * (L : ℝ))) := by
      rw [Real.rpow_add h2]; ring
    calc Qb * Nb ≤ (2 : ℝ) ^ (2 * Cπ * Φ) * (Csh ^ 2 * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (L : ℝ)))) :=
          mul_le_mul hQb hNb hNb0 (Real.rpow_nonneg (le_of_lt h2) _)
      _ = Csh ^ 2 * (2 : ℝ) ^ (2 * Cπ * Φ + 2 * (2 : ℝ) ^ (ρ * (L : ℝ))) := h1
  have hEposR : (0 : ℝ) < (2 : ℝ) ^ E := by positivity
  have hratio : (2 : ℝ) ^ (2 * Cπ * Φ + 2 * (2 : ℝ) ^ (ρ * (L : ℝ))) / (2 : ℝ) ^ E
      ≤ (2 : ℝ) ^ ((2 * Cπ - Kdev) * Φ - Kdev) := by
    have hEq : (2 : ℝ) ^ (2 * Cπ * Φ + 2 * (2 : ℝ) ^ (ρ * (L : ℝ))) / (2 : ℝ) ^ E
        = (2 : ℝ) ^ (2 * Cπ * Φ + 2 * (2 : ℝ) ^ (ρ * (L : ℝ)) - (E : ℝ)) := by
      rw [(Real.rpow_natCast 2 E).symm, ← Real.rpow_sub h2]
    have hexp : 2 * Cπ * Φ + 2 * (2 : ℝ) ^ (ρ * (L : ℝ)) - (E : ℝ)
        ≤ (2 * Cπ - Kdev) * Φ - Kdev := by
      linarith only [hEdev]
    rw [hEq]
    exact Real.rpow_le_rpow_of_exponent_le h21 hexp
  have hcombine : 6 * Qb * Nb / (2 : ℝ) ^ E
      ≤ 6 * Csh ^ 2 * (2 : ℝ) ^ ((2 * Cπ - Kdev) * Φ - Kdev) := by
    have hb1 : 6 * Qb * Nb ≤ 6 * (Csh ^ 2 * (2 : ℝ) ^ (2 * Cπ * Φ + 2 * (2 : ℝ) ^ (ρ * (L : ℝ)))) := by
      calc 6 * Qb * Nb = 6 * (Qb * Nb) := by ring
        _ ≤ 6 * (Csh ^ 2 * (2 : ℝ) ^ (2 * Cπ * Φ + 2 * (2 : ℝ) ^ (ρ * (L : ℝ)))) :=
              mul_le_mul_of_nonneg_left hnum (by norm_num)
    have hstep1 : 6 * Qb * Nb / (2 : ℝ) ^ E
        ≤ 6 * (Csh ^ 2 * (2 : ℝ) ^ (2 * Cπ * Φ + 2 * (2 : ℝ) ^ (ρ * (L : ℝ)))) / (2 : ℝ) ^ E :=
      div_le_div_of_nonneg_right hb1 (le_of_lt hEposR)
    have hstep2 : 6 * (Csh ^ 2 * (2 : ℝ) ^ (2 * Cπ * Φ + 2 * (2 : ℝ) ^ (ρ * (L : ℝ)))) / (2 : ℝ) ^ E
        = 6 * Csh ^ 2 * ((2 : ℝ) ^ (2 * Cπ * Φ + 2 * (2 : ℝ) ^ (ρ * (L : ℝ))) / (2 : ℝ) ^ E) := by
      ring
    have hstep3 : 6 * Csh ^ 2 * ((2 : ℝ) ^ (2 * Cπ * Φ + 2 * (2 : ℝ) ^ (ρ * (L : ℝ))) / (2 : ℝ) ^ E)
        ≤ 6 * Csh ^ 2 * (2 : ℝ) ^ ((2 * Cπ - Kdev) * Φ - Kdev) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    linarith only [hstep1, hstep2, hstep3]
  have hfinal : 6 * Csh ^ 2 * (2 : ℝ) ^ ((2 * Cπ - Kdev) * Φ - Kdev)
      ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := by
    have hexp : (2 * Cπ - Kdev) * Φ - Kdev
        = -(Real.logb 2 (6 * Csh ^ 2)) * Φ - (cI / 2) * Φ - Kdev := by
      rw [hKdev]; ring
    rw [hexp]
    have hsplit : (2 : ℝ) ^ (-(Real.logb 2 (6 * Csh ^ 2)) * Φ - (cI / 2) * Φ - Kdev)
        = (2 : ℝ) ^ (-(Real.logb 2 (6 * Csh ^ 2)) * Φ) * (2 : ℝ) ^ (-(cI / 2) * Φ - Kdev) := by
      rw [← Real.rpow_add h2]; congr 1; ring
    rw [hsplit]
    have hA1 : (2 : ℝ) ^ (-(Real.logb 2 (6 * Csh ^ 2)) * Φ) = (6 * Csh ^ 2) ^ (-Φ) := by
      rw [show -(Real.logb 2 (6 * Csh ^ 2)) * Φ = (Real.logb 2 (6 * Csh ^ 2)) * (-Φ) by ring]
      rw [Real.rpow_mul (le_of_lt h2), hlogval]
    have hprod : 6 * Csh ^ 2 * (6 * Csh ^ 2) ^ (-Φ) ≤ 1 := by
      have hle : (6 * Csh ^ 2) ^ (-Φ) ≤ (6 * Csh ^ 2)⁻¹ := by
        convert Real.rpow_le_rpow_of_exponent_le h6C1
          (show -Φ ≤ -(1 : ℝ) by linarith only [hΦ1]) using 1
        rw [Real.rpow_neg (le_of_lt h6Cpos), Real.rpow_one]
      calc 6 * Csh ^ 2 * (6 * Csh ^ 2) ^ (-Φ) ≤ 6 * Csh ^ 2 * (6 * Csh ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left hle (by linarith only [h6Cgt1])
        _ = 1 := by exact mul_inv_cancel₀ (ne_of_gt h6Cpos)
    have hA2 : (2 : ℝ) ^ (-(cI / 2) * Φ - Kdev) ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := by
      apply Real.rpow_le_rpow_of_exponent_le h21
      have hΦL : (L : ℝ) ≤ Φ := by linarith only [hΦL1]
      have hcI0 : (0 : ℝ) ≤ cI / 2 := by linarith only [hcI]
      have h1 : (cI / 2) * (L : ℝ) ≤ (cI / 2) * Φ := mul_le_mul_of_nonneg_left hΦL hcI0
      have h2' : (0 : ℝ) ≤ (cI / 2) * (L : ℝ) := mul_nonneg hcI0 hL0
      linarith only [h1, h2', hKdevnonneg]
    calc 6 * Csh ^ 2 * ((2 : ℝ) ^ (-(Real.logb 2 (6 * Csh ^ 2)) * Φ) * (2 : ℝ) ^ (-(cI / 2) * Φ - Kdev))
        = (6 * Csh ^ 2 * (6 * Csh ^ 2) ^ (-Φ)) * (2 : ℝ) ^ (-(cI / 2) * Φ - Kdev) := by
          rw [hA1]; ring
      _ ≤ 1 * (2 : ℝ) ^ (-(cI / 2) * Φ - Kdev) :=
            mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg (le_of_lt h2) _)
      _ ≤ 1 * (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := mul_le_mul_of_nonneg_left hA2 (by norm_num)
      _ = (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := by ring
  exact le_trans hcombine hfinal

/-- The arithmetic that closes the `ssu` assembly. -/
theorem ssuArithFinal (ρ cI CI Cπ Csh Kdev Kerr Qb Nb sc : ℝ) (d L E u : ℕ)
    (hρ : 0 < ρ) (hcI : 0 < cI) (hCI : 0 ≤ CI) (hCπ : 0 ≤ Cπ) (hCsh : 1 ≤ Csh)
    (hsc : 0 ≤ sc) (hQb0 : 0 ≤ Qb) (hNb0 : 0 ≤ Nb) (hd : 1 ≤ d)
    (hQb : Qb ≤ (2 : ℝ) ^ (2 * Cπ * Work.KMTPlan.A6.ssuPhi ρ L))
    (hNb : Nb ≤ Csh ^ 2 * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (L : ℝ))))
    (hE2 : 2 ≤ E)
    (hEρ : (2 : ℝ) ^ (ρ * (L : ℝ)) ≤ (E : ℝ))
    (hKdev : Kdev = 2 * Cπ + Real.logb 2 (6 * Csh ^ 2) + cI / 2)
    (hKerr : Kerr = Real.logb 2 (8 * Real.pi * (sc + 2)))
    (hEdev : Kdev * Work.KMTPlan.A6.ssuPhi ρ L + 2 * (2 : ℝ) ^ (ρ * (L : ℝ)) + Kdev ≤ (E : ℝ))
    (hEu : (E : ℝ) + (cI / 2) * (L : ℝ) + Kerr ≤ 3 * (u : ℝ)) :
    2 * CI * ((2 : ℝ) ^ (-(cI * ((L : ℝ) - 1))) + (E : ℝ) ^ (-(cI / ρ)))
      + 2 * (2 * Real.pi * (((2 : ℝ) ^ E) * (2 : ℝ) ^ (-(3 * (u : ℤ)))
            + sc * (((2 : ℝ) ^ E) ^ d) * (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ)))))
      + 6 * Qb * Nb / (2 : ℝ) ^ E
    ≤ (2 * CI * (2 ^ cI + 1) + 2) * (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := by
  have hT1 := ssuArith_T1 ρ cI CI L E hρ hcI hCI hEρ
  have hTA := ssuArith_T2a ρ cI Csh Kerr sc L E u hsc hKerr hEu
  have hTB := ssuArith_T2b ρ cI Csh Kerr sc d L E u hd hcI hsc hKerr hEu
  have hT3 := ssuArith_T3 ρ cI Cπ Csh Kdev Qb Nb L E hCπ hCsh hcI hQb0 hNb0 hQb hNb hKdev hEdev
  have hT2 : 2 * (2 * Real.pi * (((2 : ℝ) ^ E) * (2 : ℝ) ^ (-(3 * (u : ℤ)))
        + sc * (((2 : ℝ) ^ E) ^ d) * (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ)))))
      ≤ (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := by
    have heq : 2 * (2 * Real.pi * (((2 : ℝ) ^ E) * (2 : ℝ) ^ (-(3 * (u : ℤ)))
          + sc * (((2 : ℝ) ^ E) ^ d) * (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ)))))
        = 2 * (2 * Real.pi * ((2 : ℝ) ^ E * (2 : ℝ) ^ (-(3 * (u : ℤ)))))
          + 2 * (2 * Real.pi * (sc * ((2 : ℝ) ^ E) ^ d
              * (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ))))) := by ring
    have h2 : (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) / 2 + (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) / 2
        = (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := by ring
    linarith only [hTA, hTB, heq, h2]
  have hsum : 2 * CI * ((2 : ℝ) ^ (-(cI * ((L : ℝ) - 1))) + (E : ℝ) ^ (-(cI / ρ)))
      + 2 * (2 * Real.pi * (((2 : ℝ) ^ E) * (2 : ℝ) ^ (-(3 * (u : ℤ)))
            + sc * (((2 : ℝ) ^ E) ^ d) * (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ)))))
      + 6 * Qb * Nb / (2 : ℝ) ^ E
      ≤ 2 * CI * (2 ^ cI + 1) * (2 : ℝ) ^ (-((cI / 2) * (L : ℝ)))
        + ((2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) + (2 : ℝ) ^ (-((cI / 2) * (L : ℝ)))) := by
    linarith only [hT1, hT2, hT3]
  have hfin : 2 * CI * (2 ^ cI + 1) * (2 : ℝ) ^ (-((cI / 2) * (L : ℝ)))
      + ((2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) + (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))))
      = (2 * CI * (2 ^ cI + 1) + 2) * (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := by ring
  linarith only [hsum, hfin]

end Work.KMTPlan.A6
