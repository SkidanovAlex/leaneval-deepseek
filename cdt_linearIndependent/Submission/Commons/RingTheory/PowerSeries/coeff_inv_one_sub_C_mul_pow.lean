import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open PowerSeries

namespace Commons.RingTheory.PowerSeries

/-- The coefficient of `((1 - aX)⁻¹) ^ (e + 1)` is `(n + e).choose e * a ^ n`. -/
lemma coeff_inv_one_sub_C_mul_pow (K : Type*) [Field K] (a : K) (n e : ℕ) :
    PowerSeries.coeff n ((((1 : PowerSeries K) - PowerSeries.C a * PowerSeries.X)⁻¹) ^ (e + 1)) =
      ((Nat.choose (n + e) e : ℕ) : K) * a ^ n := by
  have hsub : (rescale a) (((1 : PowerSeries K) - X)) = (1 : PowerSeries K) - C a * X := by
    rw [map_sub, map_one, rescale_X]
  have hF : constantCoeff ((1 : PowerSeries K) - C a * X) ≠ 0 := by
    simp
  have hG : constantCoeff ((1 : PowerSeries K) - X) ≠ 0 := by
    simp
  have rescaleGinv : (rescale a) (((1 : PowerSeries K) - X)⁻¹) =
      (((1 : PowerSeries K) - C a * X)⁻¹) := by
    refine (eq_inv_iff_mul_eq_one hF).mpr ?_
    rw [← hsub]
    rw [← map_mul]
    rw [PowerSeries.inv_mul_cancel ((1 : PowerSeries K) - X) hG]
    exact map_one (rescale a)
  have Ginv : (((1 : PowerSeries K) - X)⁻¹) = (mk (fun _ : ℕ => (1 : K)) : PowerSeries K) := by
    refine ((eq_inv_iff_mul_eq_one hG).mpr ?_).symm
    exact mk_one_mul_one_sub_eq_one K
  have hSeries : (((1 : PowerSeries K) - X)⁻¹) ^ (e + 1) =
      (mk (fun m : ℕ => (((e + m).choose e : ℕ) : K)) : PowerSeries K) := by
    rw [Ginv]
    exact mk_one_pow_eq_mk_choose_add K e
  calc
    coeff n ((((1 : PowerSeries K) - C a * X)⁻¹) ^ (e + 1))
        = coeff n (((rescale a) (((1 : PowerSeries K) - X)⁻¹)) ^ (e + 1)) := by
            rw [← rescaleGinv]
    _ = coeff n ((rescale a) ((((1 : PowerSeries K) - X)⁻¹) ^ (e + 1))) := by
            rw [← map_pow]
    _ = a ^ n * coeff n ((((1 : PowerSeries K) - X)⁻¹) ^ (e + 1)) := by
            rw [coeff_rescale]
    _ = a ^ n * coeff n (mk (fun m : ℕ => (((e + m).choose e : ℕ) : K)) : PowerSeries K) := by
            rw [hSeries]
    _ = a ^ n * ((((e + n).choose e : ℕ) : K)) := by
            rw [coeff_mk]
    _ = ((Nat.choose (n + e) e : ℕ) : K) * a ^ n := by
            rw [Nat.add_comm e n, mul_comm]

end Commons.RingTheory.PowerSeries