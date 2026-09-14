import ChallengeDeps
import Submission.NBody.Energy
import Mathlib

/-!
# The potential vanishes along an escaping motion

Seventh stone.  If a motion escapes along a collision-free limit shape `a` with positive speed
`c > 0`, i.e. `y(t) = (c·t) • a + o(t)` with `o(t) = o(t)` as `t → +∞`, then the Newtonian
potential tends to zero: the bodies separate at least linearly, so every `rᵢⱼ(y(t)) → +∞` and
`U(y(t)) → 0`.

This is the first half of identifying the energy first integral (`energy_eq_of_pos`) with the
prescribed level `h` for a hyperbolic motion with `‖a‖ₘ = 1` and `c = √(2h)`.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators
open scoped Topology

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The potential vanishes along an escaping motion.**  If `y t = (c*t) • a + o(t)` with
`c > 0`, `a` collision-free and `o =o[atTop] (·)`, then `U m (y t) → 0`. -/
theorem tendsto_U_atTop_zero (m : Fin N → ℝ) (a : EN E N) (a_nc : WithoutCollisions a)
    {c : ℝ} (hc : 0 < c) {y : ℝ → EN E N} {o : ℝ → EN E N}
    (ho : o =o[atTop] fun t : ℝ => t)
    (hasym : ∀ᶠ t in atTop, y t = (c * t) • a + o t) :
    Tendsto (fun t : ℝ => U m (y t)) atTop (𝓝 0) := by
  -- each pair contributes a vanishing inverse distance
  have hpair : ∀ i j : Fin N, i ≠ j →
      Tendsto (fun t : ℝ => (r (y t) i j)⁻¹) atTop (𝓝 0) := by
    intro i j hij
    have hne : ‖a i - a j‖ ≠ 0 := by
      have h0 := a_nc i j hij
      rwa [r_eq_norm_sub] at h0
    have hδ : 0 < ‖a i - a j‖ := lt_of_le_of_ne (norm_nonneg _) hne.symm
    -- the distance grows at least like `(c‖aᵢ-aⱼ‖/2) t`
    have hlower : ∀ᶠ t : ℝ in atTop, (c * ‖a i - a j‖ / 2) * t ≤ r (y t) i j := by
      have hfour : 0 < c * ‖a i - a j‖ / 4 := by positivity
      filter_upwards [hasym, ho.bound hfour, Filter.eventually_ge_atTop (0 : ℝ)]
        with t hyt hb ht
      have hb' : ‖o t‖ ≤ (c * ‖a i - a j‖ / 4) * t := by
        rw [Real.norm_eq_abs, abs_of_nonneg ht] at hb
        exact hb
      rw [r_eq_norm_sub, hyt]
      have hcomp : ((c * t) • a + o t) i - ((c * t) • a + o t) j
          = (c * t) • (a i - a j) + ((o t) i - (o t) j) := by
        rw [show ((c * t) • a + o t) i = (c * t) • a i + o t i by simp,
            show ((c * t) • a + o t) j = (c * t) • a j + o t j by simp]
        rw [show (c * t) • a i + o t i - ((c * t) • a j + o t j)
            = ((c * t) • a i - (c * t) • a j) + (o t i - o t j) by abel]
        rw [← smul_sub]
      rw [hcomp]
      have h1 : ‖(o t) i - (o t) j‖ ≤ 2 * ‖o t‖ := by
        calc ‖(o t) i - (o t) j‖ ≤ ‖(o t) i‖ + ‖(o t) j‖ := norm_sub_le _ _
          _ ≤ ‖o t‖ + ‖o t‖ := add_le_add (PiLp.norm_apply_le (o t) i) (PiLp.norm_apply_le (o t) j)
          _ = 2 * ‖o t‖ := by ring
      have h2 : ‖(c * t) • (a i - a j)‖ = c * t * ‖a i - a j‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h3 : ‖(c * t) • (a i - a j) + ((o t) i - (o t) j)‖ ≥
          ‖(c * t) • (a i - a j)‖ - ‖(o t) i - (o t) j‖ := by
        have h := abs_norm_sub_norm_le ((c * t) • (a i - a j)) (-((o t) i - (o t) j))
        rw [sub_neg_eq_add, norm_neg] at h
        exact (abs_le.mp h).2
      calc (c * ‖a i - a j‖ / 2) * t
          = c * t * ‖a i - a j‖ - 2 * ((c * ‖a i - a j‖ / 4) * t) := by ring
        _ ≤ c * t * ‖a i - a j‖ - 2 * ‖o t‖ := by linarith
        _ = ‖(c * t) • (a i - a j)‖ - 2 * ‖o t‖ := by rw [h2]
        _ ≤ ‖(c * t) • (a i - a j)‖ - ‖(o t) i - (o t) j‖ := by linarith
        _ ≤ ‖(c * t) • (a i - a j) + ((o t) i - (o t) j)‖ := h3
    -- hence `r → ∞`, so its inverse tends to `0`
    have htop : Tendsto (fun t : ℝ => r (y t) i j) atTop atTop :=
      Filter.tendsto_atTop_mono' atTop hlower
        (Filter.Tendsto.const_mul_atTop (by positivity : 0 < c * ‖a i - a j‖ / 2) tendsto_id)
    exact htop.inv_tendsto_atTop
  -- sum over the (finite) pairs
  have hinner : ∀ j : Fin N, Tendsto
      (fun t : ℝ => ∑ i ∈ Finset.Iio j, m i * m j * (r (y t) i j)⁻¹) atTop (𝓝 0) := by
    intro j
    have := tendsto_finsetSum (Finset.Iio j) (fun i hi => by
      have hij : i ≠ j := ne_of_lt (Finset.mem_Iio.mp hi)
      simpa using (hpair i j hij).const_mul (m i * m j))
    simpa using this
  have houter : Tendsto (fun t : ℝ => ∑ j : Fin N, ∑ i ∈ Finset.Iio j, m i * m j * (r (y t) i j)⁻¹)
      atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin N)) (fun j _ => hinner j)
    simpa using this
  simpa [U] using houter

end Submission.NBody
