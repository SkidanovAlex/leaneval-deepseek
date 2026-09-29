import Mathlib
import Submission.Commons.NumberTheory.PrimeNumberTheorem.psi_isEquivalent

open Filter Asymptotics
open scoped Topology

namespace Commons.NumberTheory.PrimeNumberTheorem

/-- `√y = o(y)` as `y → ∞`. -/
private lemma sqrt_isLittleO_id :
    (fun y : ℝ => Real.sqrt y) =o[Filter.atTop] (fun y : ℝ => y) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [Filter.eventually_ge_atTop (max 1 ((1 / c) ^ 2))] with y hy
  have hy1 : (1 : ℝ) ≤ y := le_trans (le_max_left _ _) hy
  have hy0 : 0 ≤ y := by linarith
  have hc2 : (1 / c) ^ 2 ≤ y := le_trans (le_max_right _ _) hy
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  have hle : 1 / c ≤ Real.sqrt y := (Real.le_sqrt (by positivity) hy0).mpr hc2
  have h1 : 1 ≤ c * Real.sqrt y := by
    have h := (div_le_iff₀ hc).mp hle
    rwa [mul_comm] at h
  have hmul : Real.sqrt y ≤ c * y :=
    calc Real.sqrt y = 1 * Real.sqrt y := (one_mul _).symm
      _ ≤ (c * Real.sqrt y) * Real.sqrt y := mul_le_mul_of_nonneg_right h1 (le_of_lt hs)
      _ = c * y := by rw [mul_assoc, Real.mul_self_sqrt hy0]
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg y), abs_of_nonneg hy0]
    using hmul

/-- `θ y - y = o(y)` as `y → ∞` over the reals (the prime number theorem in
Chebyshev `θ` form). -/
theorem theta_sub_id_isLittleO :
    (fun y : ℝ => Chebyshev.theta y - y) =o[Filter.atTop] (fun y : ℝ => y) := by
  have hpsi : (fun y : ℝ => Chebyshev.psi y - y) =o[Filter.atTop] (fun y : ℝ => y) :=
    psi_isEquivalent
  have hbig : (fun y : ℝ => Chebyshev.theta y - Chebyshev.psi y) =O[Filter.atTop]
      (fun y : ℝ => Real.sqrt y) := by
    refine (Chebyshev.isBigO_psi_sub_theta_sqrt.neg_left).congr_left (fun y => ?_)
    simp only [Pi.sub_apply, neg_sub]
  have h1 : (fun y : ℝ => Chebyshev.theta y - Chebyshev.psi y) =o[Filter.atTop]
      (fun y : ℝ => y) := hbig.trans_isLittleO sqrt_isLittleO_id
  refine (h1.add hpsi).congr (fun y => ?_) (fun _ => rfl)
  show (Chebyshev.theta y - Chebyshev.psi y) + (Chebyshev.psi y - y) = Chebyshev.theta y - y
  ring

theorem theta_band_sub_id_isLittleO :
    Asymptotics.IsLittleO Filter.atTop
      (fun X : ℕ => Chebyshev.theta ((2 * X : ℕ) : ℝ) - Chebyshev.theta (X : ℝ) - (X : ℝ))
      (fun X : ℕ => (X : ℝ)) := by
  have hθ := theta_sub_id_isLittleO
  have hcast2 : Tendsto (fun X : ℕ => ((2 * X : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    have h : Tendsto (fun X : ℕ => (2 : ℝ) * (X : ℝ)) Filter.atTop Filter.atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    simpa [Nat.cast_mul] using h
  have hA : (fun X : ℕ => Chebyshev.theta ((2 * X : ℕ) : ℝ) - ((2 * X : ℕ) : ℝ)) =o[Filter.atTop]
      (fun X : ℕ => ((2 * X : ℕ) : ℝ)) := hθ.comp_tendsto hcast2
  have hO : (fun X : ℕ => ((2 * X : ℕ) : ℝ)) =O[Filter.atTop] (fun X : ℕ => (X : ℝ)) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards with X
    have h2X : (0 : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by positivity
    have hX : (0 : ℝ) ≤ (X : ℝ) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h2X, abs_of_nonneg hX]
    push_cast
    linarith
  have hA' : (fun X : ℕ => Chebyshev.theta ((2 * X : ℕ) : ℝ) - ((2 * X : ℕ) : ℝ)) =o[Filter.atTop]
      (fun X : ℕ => (X : ℝ)) := hA.trans_isBigO hO
  have hB : (fun X : ℕ => Chebyshev.theta (X : ℝ) - (X : ℝ)) =o[Filter.atTop]
      (fun X : ℕ => (X : ℝ)) :=
    hθ.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  refine (hA'.sub hB).congr (fun X => ?_) (fun _ => rfl)
  push_cast
  ring

end Commons.NumberTheory.PrimeNumberTheorem
