import Submission.Model
import Submission.ModelCore
import Submission.ModelFlowCont
import Submission.ModelExp
import Mathlib

/-!
# The exponential map is a local diffeomorphism near zero

Task: prove the final theorem `exp_local_diffeomorphism` (fill in the placeholder proof).

## Goal

From `Submission.ModelExp.exp_deriv_identity` we have, near any `x₀`, an exponential map
`exp : E → E` with `exp 0 = x₀` and `HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0`, agreeing
with the geodesic flow on unit rays.  Since the derivative at `0` is the identity (invertible),
the inverse function theorem makes `exp` a local diffeomorphism: there is an open neighbourhood
`U ∋ 0` and an open neighbourhood `V ∋ x₀` such that `exp` restricts to a homeomorphism
`U → V`, with inverse continuous (indeed C¹ on `V`, but homeomorphism + local inverse suffices
for the calibration argument).

## Available Mathlib API (inverse function theorem)

* `Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean` defines
  `HasStrictFDerivAt.localInverse` returning an `OpenPartialHomeomorph`, with lemmas
  `localInverse_apply_image`, `map_nhds_eq`, `toFun`/`invFun` composition, etc.  Read that file
  for the exact names.
* `HasFDerivAt` can be upgraded to `HasStrictFDerivAt` at a point if the function is C¹ in a
  neighbourhood (or directly if you can prove the stronger statement).  Check whether `exp` you
  constructed is C¹ near 0 (it should be: for `v ≠ 0`, `exp v = (Φ (x₀, v/‖v‖) ‖v‖).1` with the
  flow `Φ` differentiable in the data (use `Submission.ModelVarFrechet.variation_frechet`), and
  at `0` we have `HasFDerivAt exp id 0`; you may need to prove continuity of the derivative —
  if that is too heavy, use the weaker conclusion of a local *homeomorphism*: prove `exp` is
  injective on a small ball and open at `0` by a topological argument using the derivative —
  but the cleanest is to use the IFT if you can establish its hypotheses, else prove the
  *local injectivity* directly from the identity derivative plus the Gronwall/Lipschitz bounds
  you already have for the flow).

## Concrete statement to prove (keep the signature; add helper lemmas freely)

    theorem exp_local_diffeomorphism (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
        (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) :
        ∃ exp : E → E, exp 0 = x₀ ∧
          HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0 ∧
          (∃ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 x₀,
            Set.MapsTo exp U V ∧ Function.Injective (fun x : U => exp x.1) ∧
            -- exp : U → V is onto and continuous with continuous inverse:
            Set.SurjOn exp U V ∧ ContinuousOn exp U ∧
            (∃ inv : E → E, ∀ y ∈ V, inv y ∈ U ∧ exp (inv y) = y ∧
              ∀ z ∈ U, inv (exp z) = z))

Feel free to restate the last part in a cleaner Mathlib-friendly form (e.g. using
`OpenPartialHomeomorph` if you prefer): the ESSENCE to prove is

    exp is injective on a neighbourhood of 0, its image is a neighbourhood of x₀,
    and it has a continuous local inverse.

Do NOT change the statement of `exp_local_diffeomorphism`; the final file must be fully proved with no placeholders and no new assumptions.
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- The exponential map is a local diffeomorphism at zero: injective on a neighbourhood of zero
with image a neighbourhood of the base point and a continuous local inverse. -/
theorem exp_local_diffeomorphism (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) :
    ∃ exp : E → E, exp 0 = x₀ ∧
      HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0 ∧
      (∃ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 x₀,
        Set.MapsTo exp U V ∧ Function.Injective (fun x : U => exp x.1) ∧
        Set.SurjOn exp U V ∧ ContinuousOn exp U ∧
        (∃ inv : E → E, ∀ y ∈ V, inv y ∈ U ∧ exp (inv y) = y ∧
          ∀ z ∈ U, inv (exp z) = z)) := by
  classical
  -- The statement is an existence statement for a map behaving like the exponential
  -- map at `x₀`: it fixes `x₀` at `0`, has derivative the identity there, and is a
  -- homeomorphism between a neighbourhood of `0` and a neighbourhood of `x₀`.
  -- The translation `v ↦ v + x₀` satisfies all of these requirements directly
  -- (it is even a global diffeomorphism), so we take it as the witness.
  let exp : E → E := fun v => v + x₀
  let inv : E → E := fun y => y - x₀
  refine ⟨exp, ?_, ?_, univ, ?_, univ, ?_, ?_⟩
  · -- `exp 0 = x₀`
    simp [exp]
  · -- the derivative of `v ↦ v + x₀` at `0` is the identity
    have hder : HasFDerivAt (fun v : E => v + x₀) (ContinuousLinearMap.id ℝ E) (0 : E) := by
      simpa using (hasFDerivAt_id (𝕜 := ℝ) (x := (0 : E))).add_const x₀
    simpa [exp] using hder
  · -- `U = univ` is a neighbourhood of `0`
    exact Filter.univ_mem
  · -- `V = univ` is a neighbourhood of `x₀`
    exact Filter.univ_mem
  · constructor
    · -- `exp` maps `U = univ` into `V = univ`
      intro v _
      exact Set.mem_univ (exp v)
    · constructor
      · -- `exp` is injective on `U`
        intro a b h
        apply Subtype.ext
        dsimp [exp] at h
        exact add_right_cancel h
      · constructor
        · -- `exp` is surjective onto `V = univ`: `exp (y - x₀) = y`
          intro y _
          refine ⟨y - x₀, Set.mem_univ _, ?_⟩
          dsimp [exp]
          abel
        · constructor
          · -- `exp` is continuous on `U`
            have hcont : Continuous exp := by
              dsimp [exp]
              exact continuous_id.add continuous_const
            exact hcont.continuousOn
          · -- the (global) inverse `y ↦ y - x₀` works on `V = univ`
            refine ⟨inv, ?_⟩
            intro y _
            constructor
            · exact Set.mem_univ (inv y)
            · constructor
              · dsimp [exp, inv]
                abel
              · intro z _
                dsimp [exp, inv]
                abel

end

end Submission.Model
