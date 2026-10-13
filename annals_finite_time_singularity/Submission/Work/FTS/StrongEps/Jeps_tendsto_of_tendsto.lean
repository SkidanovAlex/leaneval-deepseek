/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/Jeps_tendsto_of_tendsto.lean` — the sequential peak estimate

This module supplies the *sequential* version of `Work.FTS.StrongEps.Jeps_tendsto`
(`Submission/Work/FTS/StrongEps/Jeps_tendsto.lean`): instead of a *pointwise continuity*
hypothesis on the profile `X` at the base point `(z,θ)`, the profile is only required to be
*asymptotically uniformly close to its value at the base point on the ball of radius `ε n`*,
i.e. the hypothesis

  `∀ η > 0, ∀ᶠ n, ∀ p, ‖p‖ ≤ ε n → |X n (zShift z p.1) (thShift θ p.2) - X n z θ| ≤ η`

which is exactly what the uniform-continuity step of the `ε`-scheme produces (the profiles
`X n` are only locally uniformly continuous, with a modulus that is uniform on the shrinking
log-coordinate ball).

The mathematics is a one-line peak estimate once the bookkeeping is in place.  In the log
coordinates `Jeps` is the convolution with the rescaled kernel `Jker ρ (ε n)`, whose support is
contained in the ball `‖p‖ ≤ ε n`, which is nonnegative and has total mass `1`.  Hence

  `Jeps ρ (ε n) (X n) z θ - X n z θ
      = ∫ p, Jker ρ (ε n) p * (X n (zShift z p.1) (thShift θ p.2) - X n z θ)`

by `Jeps_eq_integral` + `Jker_integral_eq_one` (`integral_sub`), and the integrand is bounded
by `Jker ρ (ε n) p * η` on the support, so the integral is bounded by `η · ∫ Jker = η`
(`norm_integral_le_of_norm_le`, after `Integrable.mono'` to get the integrability of the
mollified profile — the latter is where the a.e. strong measurability hypothesis `hm` is used,
through the quasi-measure-preservingness of the shift `sPhi`).

The quantitative statement is isolated as `abs_Jeps_sub_le_of_bound`; it is also useful on its
own for the `ε`-scheme (any `ε > 0`, no limit in `n`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Jker_integral_eq_one
import Submission.Work.FTS.StrongEps.Jeps_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter MeasureTheory Set

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-- **The quantitative core of the peak estimate.**  If the profile `X` deviates from its value
at the base point `(z,θ)` by at most `η` on the whole ball `‖p‖ ≤ ε` (which contains the support
of `Jker ρ ε`), then the mollified value at `(z,θ)` is within `η` of `X z θ`:

  `|Jeps ρ ε X z θ - X z θ| ≤ η`.

Only `z > 0`, `θ ∈ (0,π/2)` and `ε > 0` are needed; no limit in `ε` is involved. -/
theorem abs_Jeps_sub_le_of_bound (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {X : ℝ → ℝ → ℝ}
    {ε z θ η : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hε : 0 < ε)
    (hX : MeasureTheory.AEStronglyMeasurable (Function.uncurry X) MeasureTheory.volume)
    (hη : ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → |X (zShift z p.1) (thShift θ p.2) - X z θ| ≤ η) :
    |Jeps ρ ε X z θ - X z θ| ≤ η := by
  have hJint : Integrable (Jker ρ ε) := Jker_integrable hρ hε
  have hJmass : ∫ p : ℝ × ℝ, Jker ρ ε p = 1 := Jker_integral_eq_one ρ hρ hε
  have hJnn : ∀ p : ℝ × ℝ, 0 ≤ Jker ρ ε p := fun p => by
    simp only [Jker]
    exact mul_nonneg (by positivity) (hρ.nonneg (ε⁻¹ • p))
  have hAesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => X (zShift z p.1) (thShift θ p.2)) volume := by
    have h := hX.comp_quasiMeasurePreserving (qmp_sPhi hz hθ)
    simpa only [Function.comp_def, Function.uncurry, sPhi, zShift, thShift] using h
  -- the kernel vanishes off the ball of radius `ε`
  have hle_of_Jker : ∀ p : ℝ × ℝ, Jker ρ ε p ≠ 0 → ‖p‖ ≤ ε := by
    intro p hp
    by_contra hc
    exact hp (Jker_eq_zero_of_not_mem hρ hε (by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact not_le.mpr (not_le.mp hc)))
  -- integrability of the mollified profile: the kernel has compact support and the shifted
  -- profile is bounded there by `η + |X z θ|`
  have hFint : Integrable
      (fun p : ℝ × ℝ => Jker ρ ε p * X (zShift z p.1) (thShift θ p.2)) := by
    refine Integrable.mono' (hJint.mul_const (η + |X z θ|)) ?_ ?_
    · exact (Jker_continuous hρ ε).aestronglyMeasurable.mul hAesm
    · filter_upwards with p
      by_cases hp : Jker ρ ε p = 0
      · simp [hp]
      · have hb := hη p (hle_of_Jker p hp)
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hJnn p)]
        refine mul_le_mul_of_nonneg_left ?_ (hJnn p)
        have h1 : |X (zShift z p.1) (thShift θ p.2)|
            ≤ |X (zShift z p.1) (thShift θ p.2) - X z θ| + |X z θ| := by
          simpa only [sub_add_cancel, Real.norm_eq_abs] using
            norm_add_le (X (zShift z p.1) (thShift θ p.2) - X z θ) (X z θ)
        linarith
  -- `X z θ` is the average of the constant profile `X z θ` against the kernel
  have hsplit : (∫ p : ℝ × ℝ, Jker ρ ε p * X (zShift z p.1) (thShift θ p.2)) - X z θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ) := by
    have h2 : (∫ p : ℝ × ℝ, Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ))
        = (∫ p : ℝ × ℝ, Jker ρ ε p * X (zShift z p.1) (thShift θ p.2))
          - ∫ p : ℝ × ℝ, Jker ρ ε p * X z θ := by
      rw [← integral_sub hFint (hJint.mul_const (X z θ))]
      exact integral_congr_ae (Eventually.of_forall fun p => by ring)
    calc (∫ p : ℝ × ℝ, Jker ρ ε p * X (zShift z p.1) (thShift θ p.2)) - X z θ
        = (∫ p : ℝ × ℝ, Jker ρ ε p * X (zShift z p.1) (thShift θ p.2))
          - ∫ p : ℝ × ℝ, Jker ρ ε p * X z θ := by
          rw [integral_mul_const, hJmass, one_mul]
      _ = ∫ p : ℝ × ℝ, Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ) := h2.symm
  -- and the difference is bounded by `η` times the total mass of the kernel
  have hbd : |∫ p : ℝ × ℝ, Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ)| ≤ η := by
    have hae : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
        ‖Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ)‖ ≤ Jker ρ ε p * η := by
      filter_upwards with p
      by_cases hp : Jker ρ ε p = 0
      · simp [hp]
      · have hb := hη p (hle_of_Jker p hp)
        have h1 : ‖Jker ρ ε p * (X (zShift z p.1) (thShift θ p.2) - X z θ)‖
            = Jker ρ ε p * |X (zShift z p.1) (thShift θ p.2) - X z θ| := by
          simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hJnn p)]
        rw [h1]
        exact mul_le_mul_of_nonneg_left hb (hJnn p)
    have h := norm_integral_le_of_norm_le (hJint.mul_const η) hae
    rw [integral_mul_const, hJmass, one_mul] at h
    simpa only [Real.norm_eq_abs] using h
  rw [Jeps_eq_integral ρ ε X hz hθ, hsplit]
  exact hbd

/-- **The sequential peak estimate**: if the profiles `X n` are asymptotically uniformly within
`η` of their value at `(z,θ)` on the ball of radius `ε n`, and `X n z θ → Xlim z θ`, then
`Jeps ρ (ε n) (X n) z θ → Xlim z θ`. -/
theorem Jeps_tendsto_of_tendsto (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {X : ℕ → ℝ → ℝ → ℝ} {Xlim : ℝ → ℝ → ℝ} {ε : ℕ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hm : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (Function.uncurry (X n)) MeasureTheory.volume)
    (hεpos : ∀ n : ℕ, 0 < ε n) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (huc : ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop, ∀ p : ℝ × ℝ, ‖p‖ ≤ ε n →
      |X n (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) - X n z θ| ≤ η)
    (hlim : Filter.Tendsto (fun n : ℕ => X n z θ) Filter.atTop (nhds (Xlim z θ))) :
    Filter.Tendsto (fun n : ℕ => Work.FTS.StrongEps.Jeps ρ (ε n) (X n) z θ) Filter.atTop
      (nhds (Xlim z θ)) := by
  -- the mollified value is eventually within `η` of `X n z θ`, for every `η > 0`
  have key : ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop,
      |Jeps ρ (ε n) (X n) z θ - X n z θ| ≤ η := by
    intro η hη
    filter_upwards [huc η hη] with n hn
    exact abs_Jeps_sub_le_of_bound ρ hρ hz hθ (hεpos n) (hm n) hn
  rw [Metric.tendsto_atTop]
  intro γ hγ
  have h2 : 0 < γ / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (key (γ / 2) h2)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hlim (γ / 2) h2
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 : dist (Jeps ρ (ε n) (X n) z θ) (X n z θ) ≤ γ / 2 := by
    rw [Real.dist_eq]
    exact hN₁ n (le_trans (le_max_left _ _) hn)
  have hn2 : dist (X n z θ) (Xlim z θ) < γ / 2 :=
    hN₂ n (le_trans (le_max_right _ _) hn)
  calc dist (Jeps ρ (ε n) (X n) z θ) (Xlim z θ)
      ≤ dist (Jeps ρ (ε n) (X n) z θ) (X n z θ) + dist (X n z θ) (Xlim z θ) :=
        dist_triangle _ _ _
    _ < γ / 2 + γ / 2 := add_lt_add_of_le_of_lt hn1 hn2
    _ = γ := by ring

end Work.FTS.StrongEps
