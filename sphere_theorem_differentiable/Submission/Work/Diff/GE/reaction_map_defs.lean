import Mathlib
import Submission.Diff.Alg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The reaction map `F` of the fixed-vector curvature evolution

This module defines the *explicit* quadratic map on curvature arrays

`reactionMap R = Q R − (the four Ricci-action terms)`

that appears as the reaction term of Hamilton's evolution equation for the curvature tensor in the
*fixed-vector* form.  See `Work.Diff.GE.curvature_evolution` for the statement it serves.

## Normalisation

* `R : Curv4 n = Fin n → Fin n → Fin n → Fin n → ℝ` is the curvature array in an orthonormal frame,
  `R i j k l = ⟪R(eᵢ,eⱼ)e_l, e_k⟫` (the workspace convention, see `Submission/Diff/Alg.lean`);
* `ricF R i j = ∑ a, R a i a j` is the Ricci tensor of the array (`Ric_{ij} = ∑_a R_{aiaj}`);
* `Q` is Hamilton's quadratic term (Brendle–Schoen's `Q(R)_{ijkl} = R_{ijpq}R_{klpq} +
  2R_{ipkq}R_{jplq} − 2R_{iplq}R_{jpkq}`).

The correction terms are the action of the Ricci tensor on each of the four slots; they arise when
one converts the Uhlenbeck-frame (moving orthonormal frame) statement `∂ₜR = ΔR + Q(R)` into the
statement for the components in *fixed* vectors, where the frame-rotation terms `∂ₜeᵢ = Ric(eᵢ)^♯`
have to be absorbed.

## Calibration

On the round sphere `R = K · Iso` (with `Q(Iso) = 2(n−1)·Iso`, `rel/PP/Q_Iso`) one has
`ricF (K·Iso) = (n−1)K·δ`, so each of the four correction terms equals `(n−1)K²·Iso` and
`reactionMap (K·Iso) = (2(n−1) − 4(n−1))K²·Iso = −2(n−1)K²·Iso`.
This is exactly `∂ₜ⟨R(a,b)d,c⟩` for the family `g(t) = (1 − 2(n−1)t)g₀` (the curvature (1,3)-tensor
of a round sphere is scale invariant, so `⟨R(a,b)d,c⟩_{g(t)} = c(t)⟨R₀(a,b)d,c⟩_{g₀}` and
`c' = −2(n−1)`; with `K = 1/c` this gives `−2(n−1)K²·Iso`, matching `ΔR = 0` for the sphere).
-/

namespace Work.Diff.GE

open Submission.Diff.Alg

/-- The Ricci tensor of a curvature array: `ricF R i j = ∑ a, R a i a j`. -/
noncomputable def ricF {n : ℕ} (R : Curv4 n) : Fin n → Fin n → ℝ := fun i j => ∑ a, R a i a j

/-- **The reaction map of the fixed-vector curvature evolution**:
`reactionMap R = Q R − ∑ₚ (Ric_{ip}R_{pjkl} + Ric_{jp}R_{ipkl} + Ric_{lp}R_{ijkp} + Ric_{kp}R_{ijpl})`.
-/
noncomputable def reactionMap {n : ℕ} (R : Curv4 n) : Curv4 n := fun i j k l =>
  Q R i j k l
    - ∑ p, (ricF R i p * R p j k l + ricF R j p * R i p k l
              + ricF R l p * R i j k p + ricF R k p * R i j p l)

end Work.Diff.GE
