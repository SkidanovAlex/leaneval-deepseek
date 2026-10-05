import Mathlib
import Submission.Work.RPCore.Port.Whitney.noRetraction_unit_odd
import Submission.Work.RPCore.Port.Whitney.exists_retraction_succ

/-!
# No retraction of a closed ball onto its boundary sphere

`Work.RPCore.Port.Whitney.noRetractionBallSphere`: the closed ball `closedBall c r` (`0 < r`) of
`EuclideanSpace ℝ (Fin N)` admits no continuous retraction onto its boundary sphere `sphere c r`.

## Strategy

1. *Normalisation* (`exists_unit_retraction_of_ball`): the similarity `x ↦ r⁻¹ • (x - c)` carries the
   problem to the unit ball of `EuclideanSpace ℝ (Fin N)`, i.e. to a continuous `F₀` with
   `F₀ = id` on the unit sphere and `‖F₀ x‖ = 1` for `‖x‖ ≤ 1`.

2. *Odd dimension* (`Work.RPCore.Port.Whitney.noRetraction_unit_odd`): for odd `N` such an `F₀` gives the
   sphere-valued homotopy `(t, x) ↦ F₀ ((1 - 2 * smoothTransition t) • x)` from the identity to the
   antipodal map, contradicting the workspace degree theorem
   `Work.RPCore.Port.PushDisc.no_continuous_homotopy_of_odd`.

3. *Even dimension* (`Work.RPCore.Port.Whitney.exists_retraction_succ`): a retraction of the closed unit
   ball of `ℝ^N` suspends to a retraction of the closed unit ball of `ℝ^(N+1)`, which is odd, so
   step 2 applies in dimension `N + 1`.

Note that `N = 0` needs no separate treatment: there `Even 0` holds, the suspension produces a
retraction in dimension `1`, and step 2 refutes it.
-/

namespace Work.RPCore.Port.Whitney

open Set Metric
open scoped Topology

/-- **Similarity normalisation.**  A continuous retraction of the closed ball `closedBall c r`
(`0 < r`) onto its boundary sphere yields a continuous retraction of the closed unit ball of
`EuclideanSpace ℝ (Fin N)` onto its unit sphere, via `x ↦ r⁻¹ • (F (c + r • x) - c)`. -/
lemma exists_unit_retraction_of_ball {N : ℕ} (c : EuclideanSpace ℝ (Fin N)) {r : ℝ} (hr : 0 < r)
    (F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hcont : Continuous F)
    (hfix : ∀ z ∈ Metric.sphere c r, F z = z)
    (hball : ∀ z ∈ Metric.closedBall c r, F z ∈ Metric.sphere c r) :
    ∃ F₀ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N),
      Continuous F₀ ∧ (∀ x, ‖x‖ = 1 → F₀ x = x) ∧ (∀ x, ‖x‖ ≤ 1 → ‖F₀ x‖ = 1) := by
  refine ⟨fun x => r⁻¹ • (F (c + r • x) - c), ?_, ?_, ?_⟩
  · exact ((hcont.comp (continuous_const.add (continuous_id.const_smul r))).sub
      continuous_const).const_smul (r⁻¹)
  · intro x hx
    have hsub : c + r • x - c = r • x := by abel
    have hmem : c + r • x ∈ Metric.sphere c r := by
      rw [Metric.mem_sphere, dist_eq_norm, hsub, norm_smul, Real.norm_of_nonneg hr.le, hx, mul_one]
    change r⁻¹ • (F (c + r • x) - c) = x
    rw [hfix _ hmem, hsub, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  · intro x hx
    have hsub : c + r • x - c = r • x := by abel
    have hmem : c + r • x ∈ Metric.closedBall c r := by
      rw [Metric.mem_closedBall, dist_eq_norm, hsub, norm_smul, Real.norm_of_nonneg hr.le]
      exact mul_le_of_le_one_right hr.le hx
    have h2 : ‖F (c + r • x) - c‖ = r := by
      have := hball _ hmem
      rwa [Metric.mem_sphere, dist_eq_norm] at this
    change ‖r⁻¹ • (F (c + r • x) - c)‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), h2, inv_mul_cancel₀ hr.ne']

theorem noRetractionBallSphere {N : ℕ} (c : EuclideanSpace ℝ (Fin N)) {r : ℝ} (hr : 0 < r) :
    ¬ ∃ F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N),
        Continuous F ∧ (∀ z ∈ Metric.sphere c r, F z = z) ∧
        (∀ z ∈ Metric.closedBall c r, F z ∈ Metric.sphere c r) := by
  rintro ⟨F, hcont, hfix, hball⟩
  obtain ⟨F₀, hc₀, hfx₀, hbl₀⟩ := exists_unit_retraction_of_ball c hr F hcont hfix hball
  rcases Nat.even_or_odd N with hev | hod
  · -- even dimension: suspend to the odd dimension `N + 1`
    have hodd' : Odd (N + 1) := by
      obtain ⟨k, hk⟩ := hev
      exact ⟨k, by omega⟩
    obtain ⟨G, hGc, hGfx, hGbl⟩ := exists_retraction_succ F₀ hc₀ hfx₀ hbl₀
    exact noRetraction_unit_odd hodd' ⟨G, hGc, hGfx, hGbl⟩
  · -- odd dimension: the degree obstruction
    exact noRetraction_unit_odd hod ⟨F₀, hc₀, hfx₀, hbl₀⟩

end Work.RPCore.Port.Whitney
