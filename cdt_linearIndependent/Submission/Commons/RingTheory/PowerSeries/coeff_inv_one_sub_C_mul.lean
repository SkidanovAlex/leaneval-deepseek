import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.RingTheory.PowerSeries

/-- The power series `(1 - a·X)⁻¹` has coefficients `a^n` — the formal
geometric series `∑ n, a^n · X^n`. -/
lemma coeff_inv_one_sub_C_mul (K : Type*) [Field K] (a : K) (n : ℕ) :
    PowerSeries.coeff n (((1 : PowerSeries K) - PowerSeries.C a * PowerSeries.X)⁻¹) = a ^ n := by
  let φ : PowerSeries K := (1 : PowerSeries K) - PowerSeries.C a * PowerSeries.X
  let g : PowerSeries K := φ⁻¹
  have hφ_ne : PowerSeries.constantCoeff φ ≠ 0 := by
    simp [φ]
  have h_mul : φ * g = 1 := by
    simpa [g] using (PowerSeries.mul_inv_cancel φ hφ_ne)
  have hcg : ∀ k, PowerSeries.coeff (k + 1) g = a * PowerSeries.coeff k g := by
    intro k
    have hk := congrArg (PowerSeries.coeff (k + 1)) h_mul
    dsimp [φ] at hk
    rw [sub_mul, one_mul, map_sub] at hk
    have hx : PowerSeries.coeff (k + 1) ((PowerSeries.C a * PowerSeries.X) * g) =
        a * PowerSeries.coeff k g := by
      rw [mul_assoc, PowerSeries.coeff_C_mul]
      have hxg : PowerSeries.coeff (k + 1) ((PowerSeries.X : PowerSeries K) * g) =
          PowerSeries.coeff k g := by
        rw [mul_comm (PowerSeries.X : PowerSeries K) g, PowerSeries.coeff_succ_mul_X]
      rw [hxg]
    rw [hx] at hk
    have hk1 : PowerSeries.coeff (k + 1) (1 : PowerSeries K) = 0 := by simp
    rw [hk1] at hk
    exact sub_eq_zero.mp hk
  have hc0 : PowerSeries.coeff 0 g = 1 := by
    have h0 := congrArg (PowerSeries.coeff 0) h_mul
    dsimp [φ] at h0
    rw [sub_mul, one_mul, map_sub] at h0
    have hx : PowerSeries.coeff 0 ((PowerSeries.C a * PowerSeries.X) * g) = 0 := by
      simp
    rw [hx, sub_zero] at h0
    simp [h0]
  induction n with
  | zero =>
      simp [g, φ, hc0]
  | succ k ih =>
      rw [hcg k, ih, pow_succ]
      ring

end Commons.RingTheory.PowerSeries