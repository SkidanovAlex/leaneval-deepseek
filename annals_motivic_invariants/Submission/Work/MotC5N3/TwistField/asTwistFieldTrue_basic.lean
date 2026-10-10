import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotC5N3.TwistField.asRoot_notMem_asTwistFieldFix
import Submission.Work.MotC5N3.TwistField.asTwistFieldTrue_constants
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Basic API for the corrected Artin–Schreier twist field `asTwistFieldTrue`

`Work.MotC5N3.asTwistFieldTrue D g τ σS = asTwistFieldFix D τ σS ⊓ asFieldL D g` is the twist field
of the Klein curve `E` (over `K = 𝕜(t)`) by the Artin–Schreier class of `g ∈ K/℘(K)`, realized
*inside* `L(E) = asFieldL D g` (with `L = K(asRoot g)`).  The intersection with `asFieldL` removes
the spurious algebraic constants of `asTwistFieldFix` (which contains `Work.MotC5N3.KbA K ^ σ`).  See
`README.md` for the construction and `asTwistFieldFix_degree` / `asTwistFieldFix_descent` for the
properties of the ambient fixed field.

This file collects the elementary consequences:

* `asTwistFieldTrue_le_asTwistFieldFix`, `asTwistFieldTrue_le_asFieldL` — the two inclusions;
* `asRoot_notMem_asTwistFieldTrue` — the Artin–Schreier root does **not** lie in the twist field
  (this is the sanity check distinguishing the corrected construction from the refuted
  interpolation model `asTwistField`, which does contain it);
* `algebraMap_mem_asTwistFieldTrue_iff` — the constants of the twist field are exactly the rational
  ones (`asTwistFieldTrue_constants`, in the usable `iff` form);
* `subsingleton_algEquiv_of_...` — nothing here: the rigidity statements live in their own nodes.
-/

set_option autoImplicit false

namespace Work.MotC5N3
open Work.MotV5
variable {𝕜 : Type} [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K]

/-- The corrected twist field is contained in the ambient fixed field `asTwistFieldFix`. -/
theorem asTwistFieldTrue_le_asTwistFieldFix (D : Work.MotV.KleinData 𝕜) (g : K)
    (τ : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D)
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D) :
    asTwistFieldTrue D g τ σS ≤ asTwistFieldFix D τ σS :=
  inf_le_left

/-- The corrected twist field is contained in `L(E) = asFieldL D g`. -/
theorem asTwistFieldTrue_le_asFieldL (D : Work.MotV.KleinData 𝕜) (g : K)
    (τ : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D)
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D) :
    asTwistFieldTrue D g τ σS ≤ asFieldL D g :=
  inf_le_right

/-- **The Artin–Schreier root is not in the corrected twist field.**  `asTwistField D g` (the
refuted interpolation model) contains `asRoot g`; `asTwistFieldTrue D g τ σS`, being contained in
the fixed field of the twisted action, does not. -/
theorem asRoot_notMem_asTwistFieldTrue (D : Work.MotV.KleinData 𝕜) (g : K)
    (σ : Work.MotC5N3.KbA K ≃ₐ[K] Work.MotC5N3.KbA K)
    (hσ : σ (asRoot g) = asRoot g + 1)
    (τ : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D)
    (hτ : ∀ c : Work.MotC5N3.KbA K,
      τ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
        = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (σ c))
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D) :
    algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (asRoot g) ∉ asTwistFieldTrue D g τ σS :=
  fun h => asRoot_notMem_asTwistFieldFix 𝕜 D g σ hσ τ hτ σS
    (asTwistFieldTrue_le_asTwistFieldFix D g τ σS h)

/-- **The constants of the corrected twist field are `K = 𝕜(t)`.**  A constant `c ∈ Work.MotC5N3.KbA K` lies in
`asTwistFieldTrue D g τ σS` if and only if it is rational.  This is the usable form of
`Work.MotC5N3.asTwistFieldTrue_constants`. -/
theorem algebraMap_mem_asTwistFieldTrue_iff [CharP 𝕜 5] [CharP K 5] (D : Work.MotV.KleinData 𝕜)
    (hD : D.Good) (g : K)
    (τ : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D)
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D)
    (σ : Work.MotC5N3.KbA K ≃ₐ[K] Work.MotC5N3.KbA K)
    (hτ : ∀ c : Work.MotC5N3.KbA K,
      τ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
        = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (σ c))
    (hσ : σ (asRoot g) = asRoot g + 1) (c : Work.MotC5N3.KbA K) :
    algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c ∈ asTwistFieldTrue D g τ σS ↔
      ∃ d : K, algebraMap K (Work.MotC5N3.KbA K) d = c := by
  constructor
  · exact asTwistFieldTrue_constants 𝕜 D hD g τ σS σ hτ hσ c
  · rintro ⟨d, rfl⟩
    rw [← IsScalarTower.algebraMap_apply K (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) d]
    exact ⟨IntermediateField.algebraMap_mem _ d, IntermediateField.algebraMap_mem _ d⟩

end Work.MotC5N3