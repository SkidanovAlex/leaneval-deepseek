import Mathlib
import Submission.Work.MotV5.RigAS.PlaceData
import Submission.Work.MotV5.RigAS.placeExtension_e1
import Submission.Work.MotV5.RigAS.residueLift_e1

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace Work.MotV5.RigAS

open scoped WithZero

/-!
# The local place datum `IsPlaceData` at a pole of `t` (the `e = 1` case)

This is the assembly of the two halves of the local chapter of the Artin–Schreier bridge:

* `Work.MotV5.RigAS.placeExtension_e1` — a prolongation `V` of `v` to `L = asFieldL D g` with
  `V|_F = v` and the same value group (`e = 1`), i.e. §10.2 of `STATUS.md`:
  the tower `𝕜(t) ⊆ K(E) ⊆ L`, the proved `5 ∣ e(P/∞)` (`Nodes/fifthPowAtPoles_AS`) and
  the étaleness of the Klein translation quotient (`RigAS/kleinQuotient_etale`);
* `Work.MotV5.RigAS.residueLift_e1` — `e = 1` implies the inertia is trivial on the residue field.

Putting them together gives `IsPlaceData` at every pole of `t`; feeding that into the PROVED
`Work.MotV5.RigAS.bridge_twist_of_placeData` yields the bridge `BR_AS`
(`Work.MotV5.Nodes.bridge_AS`) for the two classes `g ∈ {fAS 𝕜, 2 • fAS 𝕜}`.
-/

/-- **The local place datum at a pole of `t`.**  For every `𝕜`-valuation `v` of the AS twist
field `F = asTwistFieldTrue D g τ σS` at which `t = RatFunc.X` has a pole, there is a
`ℤᵐ⁰`-valued place `V` of `L = asFieldL D g` above `v` with trivial ramification and trivial
inertia (`IsPlaceData`). -/
theorem placeData_e1 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) :
    ∀ v : Valuation ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ℤᵐ⁰,
      Work.MotV.TrivOn 𝕜 v →
      1 < v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X) →
      ∃ V : Valuation ↥(Work.MotV5.asFieldL D g) ℤᵐ⁰,
        IsPlaceData D g τ σS σ h v V := by
  intro v htriv ht
  obtain ⟨V, hV⟩ := placeExtension_e1 𝕜 D hD g hg τ σS σ h v htriv ht
  exact ⟨V, hV, residueLift_e1 𝕜 D hD g hg τ σS σ h v htriv ht V hV⟩

end Work.MotV5.RigAS
