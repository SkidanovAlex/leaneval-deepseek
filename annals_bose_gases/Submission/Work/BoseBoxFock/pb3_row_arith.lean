import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pb3_row_arith` — the pure-real arithmetic of the block-III row

The block-III row comparison of `Work.BoseBoxFock.pairRowB3_le_massWord` ends in the following
elementary estimate: with the deficit payers

* `pin ≤ Cp·(kin + nv·nb)`  (the `pinDirChi` bound),
* `kin ≤ Ck·av·μv²·ℓ³·nb`   (the `kinFormB` bound at a low state),
* `nv ≤ 2·μv·ℓ³`            (the particle-number window),
* `β ≤ μv·Cw·av`            (the mass coefficient),

and the two threshold inequalities

* `4·Cw·Cd·Cp·(Ck+2)·ℓ²/X ≤ N²`,
* `8·Cw·Cd/X ≤ N²`,

one has

    β·[Cd·((ℓ/(2πN))²·pin + nv·nb/N²)] ≤ (1/2)·(μv²·av·ℓ³·X)·nb .

The two thresholds are exactly the ones the `Nmin μ` of the target implements (with
`X = √(dil v μ)·K_ℓ^{-3}`).
-/

namespace Work.BoseBoxFock

theorem pb3_row_arith {ℓ X nv nb pin kin β μv av Cw Cd Cp Ck : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hℓ : 0 < ℓ) (hX : 0 < X) (hnb : 0 ≤ nb)
    (hCw0 : 0 ≤ Cw) (hCd0 : 0 ≤ Cd) (hCp0 : 0 ≤ Cp) (hCk0 : 0 ≤ Ck)
    (hav0 : 0 ≤ av) (hμv0 : 0 ≤ μv) (haμ1 : av * μv ≤ 1)
    (hnv0 : 0 ≤ nv) (hnv : nv ≤ 2 * μv * ℓ ^ 3)
    (hβ0 : 0 ≤ β) (hβ : β ≤ μv * Cw * av)
    (hpin0 : 0 ≤ pin) (hpin : pin ≤ Cp * (kin + nv * nb))
    (hkin : kin ≤ Ck * av * μv ^ 2 * ℓ ^ 3 * nb)
    (hN2 : 4 * Cw * Cd * Cp * (Ck + 2) * ℓ ^ 2 / X ≤ (N : ℝ) ^ 2)
    (hN3 : 8 * Cw * Cd / X ≤ (N : ℝ) ^ 2) :
    β * (Cd * ((ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin + nv * nb / (N : ℝ) ^ 2))
      ≤ (1 / 2) * (μv ^ 2 * av * ℓ ^ 3 * X) * nb := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have hN2r : (0 : ℝ) < (N : ℝ) ^ 2 := pow_pos hNr 2
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hℓ3 : (0 : ℝ) ≤ ℓ ^ 3 := pow_nonneg hℓ.le 3
  have hmass0 : (0 : ℝ) ≤ μv * ℓ ^ 3 * nb := mul_nonneg (mul_nonneg hμv0 hℓ3) hnb
  -- the two payers, cleared of the `X`-division
  have hA1 : Cw * Cd * Cp * (Ck + 2) * ℓ ^ 2 / (N : ℝ) ^ 2 ≤ X / 4 := by
    have h := hN2
    rw [div_le_iff₀ hX] at h
    rw [div_le_iff₀ hN2r]
    linarith
  have hA2 : 2 * Cw * Cd / (N : ℝ) ^ 2 ≤ X / 4 := by
    have h := hN3
    rw [div_le_iff₀ hX] at h
    rw [div_le_iff₀ hN2r]
    linarith
  -- the scale comparison `(ℓ/(2πN))² ≤ ℓ²/N²`
  have hζ : (ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 ≤ ℓ ^ 2 / (N : ℝ) ^ 2 := by
    rw [div_pow]
    refine div_le_div_of_nonneg_left (sq_nonneg ℓ) (by positivity) ?_
    have h1 : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
    calc (N : ℝ) ^ 2 = 1 * (N : ℝ) ^ 2 := by ring
      _ ≤ (2 * Real.pi) ^ 2 * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = (2 * Real.pi * (N : ℝ)) ^ 2 := by ring
  -- the `pin` and `n` payers, with the `kin`- and `n`-budgets substituted
  have hpin' : pin ≤ Cp * (Ck * av * μv ^ 2 * ℓ ^ 3 + 2 * μv * ℓ ^ 3) * nb := by
    have h1 : kin + nv * nb ≤ Ck * av * μv ^ 2 * ℓ ^ 3 * nb + 2 * μv * ℓ ^ 3 * nb := by
      have h2 : nv * nb ≤ 2 * μv * ℓ ^ 3 * nb := mul_le_mul_of_nonneg_right hnv hnb
      linarith [hkin, h2]
    calc pin ≤ Cp * (kin + nv * nb) := hpin
      _ ≤ Cp * (Ck * av * μv ^ 2 * ℓ ^ 3 * nb + 2 * μv * ℓ ^ 3 * nb) :=
          mul_le_mul_of_nonneg_left h1 hCp0
      _ = Cp * (Ck * av * μv ^ 2 * ℓ ^ 3 + 2 * μv * ℓ ^ 3) * nb := by ring
  have h3 : Ck * av * μv ^ 2 * ℓ ^ 3 + 2 * μv * ℓ ^ 3 ≤ (Ck + 2) * (μv * ℓ ^ 3) := by
    have h2 : Ck * av * μv ^ 2 ≤ Ck * μv := by
      have h4 : Ck * (av * μv) * μv ≤ Ck * 1 * μv :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haμ1 hCk0) hμv0
      nlinarith [h4]
    have h5 := mul_le_mul_of_nonneg_right h2 hℓ3
    nlinarith [h5]
  have hbr : (0 : ℝ) ≤ Cd * ((ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin + nv * nb / (N : ℝ) ^ 2) := by
    refine mul_nonneg hCd0 (add_nonneg (mul_nonneg (sq_nonneg _) hpin0) ?_)
    exact div_nonneg (mul_nonneg hnv0 hnb) hN2r.le
  -- the kernel of the estimate
  have hcore : Cw * (Cd * ((ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin + nv * nb / (N : ℝ) ^ 2))
      ≤ μv * ℓ ^ 3 * nb * (Cw * Cd * Cp * (Ck + 2) * ℓ ^ 2 / (N : ℝ) ^ 2 + 2 * Cw * Cd / (N : ℝ) ^ 2) := by
    have h1 : (ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin
        ≤ ℓ ^ 2 / (N : ℝ) ^ 2 * (Cp * (Ck * av * μv ^ 2 * ℓ ^ 3 + 2 * μv * ℓ ^ 3) * nb) := by
      calc (ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin
          ≤ (ℓ ^ 2 / (N : ℝ) ^ 2) * pin := mul_le_mul_of_nonneg_right hζ hpin0
        _ ≤ (ℓ ^ 2 / (N : ℝ) ^ 2) * (Cp * (Ck * av * μv ^ 2 * ℓ ^ 3 + 2 * μv * ℓ ^ 3) * nb) :=
            mul_le_mul_of_nonneg_left hpin' (by positivity)
    have h2 : nv * nb / (N : ℝ) ^ 2 ≤ 2 * μv * ℓ ^ 3 * nb / (N : ℝ) ^ 2 := by
      refine div_le_div_of_nonneg_right ?_ hN2r.le
      exact mul_le_mul_of_nonneg_right hnv hnb
    have h4 : ℓ ^ 2 / (N : ℝ) ^ 2 * (Cp * (Ck * av * μv ^ 2 * ℓ ^ 3 + 2 * μv * ℓ ^ 3) * nb)
        ≤ ℓ ^ 2 / (N : ℝ) ^ 2 * (Cp * ((Ck + 2) * (μv * ℓ ^ 3)) * nb) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hCp0) hnb
    have h5 : (ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin
        ≤ ℓ ^ 2 / (N : ℝ) ^ 2 * (Cp * ((Ck + 2) * (μv * ℓ ^ 3)) * nb) := le_trans h1 h4
    have hsum : (ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin + nv * nb / (N : ℝ) ^ 2
        ≤ ℓ ^ 2 / (N : ℝ) ^ 2 * (Cp * ((Ck + 2) * (μv * ℓ ^ 3)) * nb)
          + 2 * μv * ℓ ^ 3 * nb / (N : ℝ) ^ 2 := add_le_add h5 h2
    calc Cw * (Cd * ((ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin + nv * nb / (N : ℝ) ^ 2))
        = Cw * Cd * ((ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin + nv * nb / (N : ℝ) ^ 2) := by ring
      _ ≤ Cw * Cd * (ℓ ^ 2 / (N : ℝ) ^ 2 * (Cp * ((Ck + 2) * (μv * ℓ ^ 3)) * nb)
            + 2 * μv * ℓ ^ 3 * nb / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = μv * ℓ ^ 3 * nb
            * (Cw * Cd * Cp * (Ck + 2) * ℓ ^ 2 / (N : ℝ) ^ 2 + 2 * Cw * Cd / (N : ℝ) ^ 2) := by
          simp only [div_eq_mul_inv]
          ring
  have hthr : Cw * Cd * Cp * (Ck + 2) * ℓ ^ 2 / (N : ℝ) ^ 2 + 2 * Cw * Cd / (N : ℝ) ^ 2 ≤ X / 2 := by
    linarith [hA1, hA2]
  calc β * (Cd * ((ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin + nv * nb / (N : ℝ) ^ 2))
      ≤ μv * av * (Cw * (Cd * ((ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin + nv * nb / (N : ℝ) ^ 2))) := by
        have h := mul_le_mul_of_nonneg_right hβ hbr
        linarith [h]
    _ ≤ μv * av * (μv * ℓ ^ 3 * nb * (X / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hμv0 hav0)
        exact le_trans hcore (mul_le_mul_of_nonneg_left hthr hmass0)
    _ = (1 / 2) * (μv ^ 2 * av * ℓ ^ 3 * X) * nb := by ring

end Work.BoseBoxFock
