import Mathlib
import Submission.Work.PTGeometric.AmbientPerturbation
import Submission.Work.PTGeometric.hinj_nhds_of_hinj

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.PTGeometric

/-- **Injectivity of `ℓ` on the planes of a continuous family is an open condition.**

`Q : X → EndOp n` is a continuous family of orthogonal rank-`k` projections and `ℓ : ℝⁿ → ℝᵏ`
is linear.  The set of `x` at which `ℓ` is injective on the plane `im (Q x)` — i.e. at which
`Q x z = z` and `ℓ z = 0` force `z = 0` — is open: by `hinj_nhds_of_hinj` injectivity at a point
`x` persists on an operator-norm ball around `Q x`, and that ball is the preimage under the
continuous `Q` of an open ball, hence is a neighbourhood of `x`. -/
theorem isOpen_setOf_injOn_gr {n k : ℕ}
    (ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k))
    {X : Type} [TopologicalSpace X]
    {Q : X → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hQc : Continuous Q) (hQ : ∀ x : X, Q x ∈ Work.PTGeometric.Gr n k) :
    IsOpen {x : X | ∀ z : EuclideanSpace ℝ (Fin n), Q x z = z → ℓ z = 0 → z = 0} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨ε, hε, hεh⟩ := hinj_nhds_of_hinj (M := X) Q hQc hQ ℓ x hx
  have hopen : IsOpen {y : X | ‖Q y - Q x‖ < ε} :=
    isOpen_lt (hQc.sub continuous_const).norm continuous_const
  have hmem : x ∈ {y : X | ‖Q y - Q x‖ < ε} := by
    simpa using hε
  exact Filter.mem_of_superset (hopen.mem_nhds hmem) fun y hy => hεh y hy

end Work.PTGeometric
