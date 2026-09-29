import Mathlib
import Submission.Work.Haupt.thetaCore

/-!
# The functional equation of the two-variable theta product

`ThetaProd x z = ∏'_{n ≥ 0} (1 + x^{2n+1} z)(1 + x^{2n+1}/z)` satisfies, for `z ≠ 0`,

`ThetaProd x (x² z) = (x z)⁻¹ ThetaProd x z`,

i.e. `ThetaProd x (x² z) = ThetaProd x z / (x z)`.

Substituting `z ↦ x² z` shifts the first family of factors `(1 + x^{2n+1} z)` up by one index
and the last family `(1 + x^{2n+1}/z)` down by one index; the two corrections combine through
`(x z)⁻¹ (1 + x z) = 1 + x⁻¹/z`.

The argument mirrors `Work.Haupt.jtpLHS_functional` with the third ("Jacobi") family
`∏' (1 - x^{2(n+1)})` removed.
-/

namespace Work.Haupt

open scoped BigOperators

set_option maxHeartbeats 1000000

theorem ThetaProd_functional (x : ℂ) (hx : ‖x‖ < 1) (hx0 : x ≠ 0) :
    ∀ z : ℂ, z ≠ 0 → ThetaProd x (x ^ 2 * z) = ThetaProd x z / (x * z) := by
  intro z hz0
  have hx2 : ‖x ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  have g := summable_geometric_of_norm_lt_one hx2
  have sB : Summable (fun n : ℕ => x ^ (2 * n + 1) * z) :=
    (g.mul_left (z * x)).congr (fun n => by rw [← pow_mul, pow_succ]; ring)
  have sC : Summable (fun n : ℕ => x ^ (2 * n + 1) / z) :=
    (g.mul_left (z⁻¹ * x)).congr (fun n => by rw [← pow_mul, pow_succ]; ring)
  have sB2 : Summable (fun n : ℕ => x ^ (2 * n + 1) * (x ^ 2 * z)) :=
    (g.mul_left (x ^ 2 * z * x)).congr (fun n => by rw [← pow_mul, pow_succ]; ring)
  have sC2 : Summable (fun n : ℕ => x ^ (2 * n + 1) / (x ^ 2 * z)) :=
    (g.mul_left ((x ^ 2 * z)⁻¹ * x)).congr (fun n => by rw [← pow_mul, pow_succ]; ring)
  have mB : Multipliable (fun n : ℕ => 1 + x ^ (2 * n + 1) * z) :=
    Complex.multipliable_one_add_of_summable sB
  have mC : Multipliable (fun n : ℕ => 1 + x ^ (2 * n + 1) / z) :=
    Complex.multipliable_one_add_of_summable sC
  have mB2 : Multipliable (fun n : ℕ => 1 + x ^ (2 * n + 1) * (x ^ 2 * z)) :=
    Complex.multipliable_one_add_of_summable sB2
  have mC2 : Multipliable (fun n : ℕ => 1 + x ^ (2 * n + 1) / (x ^ 2 * z)) :=
    Complex.multipliable_one_add_of_summable sC2
  -- power identities used to compare the shifted families
  have hpow1 : ∀ n : ℕ, x ^ (2 * n + 1) * x ^ 2 = x ^ (2 * n + 3) := fun n => by
    rw [← pow_add]
  have hpow2 : ∀ n : ℕ, x ^ (2 * n + 1) * (x ^ 2 * z) = x ^ (2 * n + 3) * z := fun n => by
    rw [← mul_assoc, hpow1 n]
  have hpow3 : ∀ n : ℕ, x ^ (2 * n + 3) / x ^ 2 / z = x ^ (2 * n + 1) / z := fun n => by
    rw [← hpow1 n]
    field_simp
  set PB : ℂ := ∏' n : ℕ, (1 + x ^ (2 * n + 1) * z) with hPB
  set PC : ℂ := ∏' n : ℕ, (1 + x ^ (2 * n + 1) / z) with hPC
  set PB2 : ℂ := ∏' n : ℕ, (1 + x ^ (2 * n + 1) * (x ^ 2 * z)) with hPB2
  set PC2 : ℂ := ∏' n : ℕ, (1 + x ^ (2 * n + 1) / (x ^ 2 * z)) with hPC2
  set PB3 : ℂ := ∏' n : ℕ, (1 + x ^ (2 * n + 3) * z) with hPB3
  -- splitting `ThetaProd` into its two constituent products
  have hsplit : ThetaProd x z = PB * PC := by
    rw [hPB, hPC, ThetaProd]
    rw [Multipliable.tprod_mul mB mC]
  have hsplit2 : ThetaProd x (x ^ 2 * z) = PB2 * PC2 := by
    rw [hPB2, hPC2, ThetaProd]
    rw [Multipliable.tprod_mul mB2 mC2]
  -- the first family, shifted
  have hPB23 : PB2 = PB3 := by
    rw [hPB2, hPB3]
    exact tprod_congr (fun n => by rw [hpow2 n])
  have hBshift : Multipliable (fun n : ℕ => 1 + x ^ (2 * (n + 1) + 1) * z) :=
    mB2.congr (fun n => by
      show 1 + x ^ (2 * n + 1) * (x ^ 2 * z) = 1 + x ^ (2 * (n + 1) + 1) * z
      rw [hpow2 n, show 2 * (n + 1) + 1 = 2 * n + 3 from by ring])
  have hBrel : PB = (1 + x * z) * PB3 := by
    rw [hPB, hPB3]
    rw [tprod_eq_zero_mul' (f := fun n : ℕ => 1 + x ^ (2 * n + 1) * z) hBshift]
    simp only [Nat.mul_zero, Nat.zero_add, pow_one]
    congr 1
  -- the last family, shifted
  have mjs : Multipliable (fun n : ℕ => 1 + x ^ (2 * (n + 1) + 1) / x ^ 2 / z) :=
    mC.congr (fun n => by
      show 1 + x ^ (2 * n + 1) / z = 1 + x ^ (2 * (n + 1) + 1) / x ^ 2 / z
      rw [show 2 * (n + 1) + 1 = 2 * n + 3 from by ring, ← hpow3 n])
  have hCrel : PC2 = (1 + x⁻¹ / z) * PC := by
    rw [hPC2, hPC, tprod_congr (fun n => by rw [div_mul_eq_div_div]),
      tprod_eq_zero_mul' (f := fun n : ℕ => 1 + x ^ (2 * n + 1) / x ^ 2 / z) mjs]
    congr 1
    · simp only [Nat.mul_zero, Nat.zero_add, pow_one]; field_simp
    · refine tprod_congr (fun n => ?_)
      rw [show 2 * (n + 1) + 1 = 2 * n + 3 from by ring, hpow3 n]
  have hK : (x * z)⁻¹ * (1 + x * z) = 1 + x⁻¹ / z := by
    rw [mul_add, mul_one, inv_mul_cancel₀ (mul_ne_zero hx0 hz0), mul_inv]
    ring
  calc ThetaProd x (x ^ 2 * z)
      = PB2 * PC2 := hsplit2
    _ = PB3 * PC2 := by rw [hPB23]
    _ = PB3 * ((1 + x⁻¹ / z) * PC) := by rw [hCrel]
    _ = PB3 * ((x * z)⁻¹ * (1 + x * z) * PC) := by rw [hK]
    _ = (x * z)⁻¹ * (PB3 * (1 + x * z) * PC) := by ac_rfl
    _ = (x * z)⁻¹ * (PB * PC) := by rw [hBrel]; ac_rfl
    _ = (x * z)⁻¹ * ThetaProd x z := by rw [← hsplit]
    _ = ThetaProd x z / (x * z) := by rw [div_eq_mul_inv]; ring

end Work.Haupt
