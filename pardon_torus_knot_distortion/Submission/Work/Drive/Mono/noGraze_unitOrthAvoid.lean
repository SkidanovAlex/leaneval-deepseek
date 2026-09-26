import Mathlib
import Submission.Work.Drive.Mono.NoGrazeDefs

/-!
# A unit direction orthogonal to `e` avoiding the non-vertical crossings

`Work.Drive.Mono.exists_avoid_vertVel` produces *some* vector `Ñ` which is not orthogonal
to the orthogonal velocity `vertVel K e t` at any crossing `t` where that velocity is
non-zero.  Here we additionally force `Ñ` to be a **unit** vector **orthogonal to `e`**.

Geometrically the bad set is the union of the hyperplanes `{Ñ | ⟪Ñ, vertVel K e t⟫ = 0}`
over the finite set of crossings with `vertVel K e t ≠ 0`.  Every such velocity lies in
`e^⊥`, so the orthogonal projection `x = Ñ - ⟪e,Ñ⟫ • e ∈ e^⊥` of an avoiding `Ñ` is again
avoiding (projecting along `e` keeps the pairing with vectors of `e^⊥`) and is non-zero;
normalising it lands on the unit circle of `e^⊥`.  When there is no crossing with non-zero
vertical velocity the hypothesis is vacuous and the given unit vector `e₂ ⟂ e` is a witness.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology RealInnerProductSpace

noncomputable section

/-- A vector of `e^⊥` (for unit `e`) is annihilated by `e` on the left as well. -/
theorem inner_perpProj_left (e x : R3) (he : ‖e‖ = 1) : inner ℝ e (perpProj e x) = 0 := by
  rw [real_inner_comm, inner_perpProj_eq_zero e x he]

/-- The orthogonal velocity is orthogonal to `e`, in either argument order. -/
theorem inner_e_vertVel (K : Knot) (e : R3) (he : ‖e‖ = 1) (t : ℝ) :
    inner ℝ e (vertVel K e t) = 0 := by
  rw [vertVel, real_inner_comm, inner_perpProj_eq_zero e (deriv K.curve t) he]

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
theorem noGraze_unitOrthAvoid (K : Knot) (e e₂ : R3) (he : ‖e‖ = 1) (he₂ : ‖e₂‖ = 1)
    (horth : inner ℝ e₂ e = 0) {c : R3} {σ : Equiv.Perm (Fin 3)} {s u : ℝ}
    (hcut : Work.Drive.Mono.CutTransverse K s c σ u) :
    ∃ Ñ : R3, ‖Ñ‖ = 1 ∧ inner ℝ Ñ e = 0 ∧
      ∀ t ∈ Work.Drive.Mono.crossingSet K c σ s u hcut, Work.Drive.Mono.vertVel K e t ≠ 0 →
        inner ℝ Ñ (Work.Drive.Mono.vertVel K e t) ≠ 0 := by
  classical
  by_cases hne : ∃ t ∈ crossingSet K c σ s u hcut, vertVel K e t ≠ 0
  · -- Some crossing has non-zero vertical velocity: project the avoiding vector onto `e^⊥`.
    obtain ⟨t₀, ht₀, hw₀⟩ := hne
    obtain ⟨Ñ, hÑ⟩ := exists_avoid_vertVel K e hcut
    set x := Ñ - inner ℝ e Ñ • e with hx
    -- The projection pairs with `e^⊥` exactly as `Ñ` does.
    have hx_eq : ∀ t ∈ crossingSet K c σ s u hcut,
        inner ℝ x (vertVel K e t) = inner ℝ Ñ (vertVel K e t) := by
      intro t ht
      rw [hx, inner_sub_left, real_inner_smul_left, inner_e_vertVel K e he t, mul_zero, sub_zero]
    have hx_ne : x ≠ 0 := by
      intro h0
      have h1 : inner ℝ Ñ (vertVel K e t₀) ≠ 0 := hÑ t₀ ht₀ hw₀
      have h2 : inner ℝ Ñ (vertVel K e t₀) = 0 := by
        rw [← hx_eq t₀ ht₀, h0, inner_zero_left]
      exact h1 h2
    refine ⟨unitDir x, unitDir_norm x hx_ne, ?_, ?_⟩
    · -- `unitDir x` is orthogonal to `e`.
      rw [inner_unitDir]
      have hxe : inner ℝ x e = 0 := by
        rw [hx, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he, one_pow,
          mul_one, real_inner_comm e Ñ, sub_self]
      rw [hxe, mul_zero]
    · -- Normalising preserves avoidance on `e^⊥`.
      intro t ht hz
      rw [inner_unitDir]
      have h2 : inner ℝ Ñ (vertVel K e t) ≠ 0 := hÑ t ht hz
      rw [hx_eq t ht]
      exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hx_ne)) h2
  · -- No crossing has non-zero vertical velocity: the condition is vacuous, `e₂` works.
    refine ⟨e₂, he₂, horth, fun t ht hz => ?_⟩
    exact absurd ⟨t, ht, hz⟩ hne

end

end Work.Drive.Mono
