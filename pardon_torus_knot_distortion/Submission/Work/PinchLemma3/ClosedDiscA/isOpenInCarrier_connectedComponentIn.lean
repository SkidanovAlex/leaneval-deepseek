import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.TorusCover.ParamTorus_exists_liftOf
import Submission.Work.TorusCover.Basic
import Submission.Work.PinchLemma3.ClosedDiscA.isPathConnected_connectedComponentIn_carrier

/-!
# Components of a surface-open set are open in the surface

`Work.PinchLemma3.ClosedDiscA.isOpenInCarrier_connectedComponentIn`:
if `K ⊆ ℝ³` is a subset of the surface `F = P.carrier` of a parametrised torus `P` which is
**open in that surface**, then for every `x : ℝ³` the connected component of `x` inside `K`
is again open in the surface.

The proof is the standard `IsOpen.connectedComponentIn` argument for the open subspace
`↥(P.carrier ∩ K)` of the (locally connected) surface, transported through the canonical
homeomorphism `↥K ≃ₜ ↥(P.carrier ∩ K)`.
-/

-- The local instance below is genuinely used as a typeclass instance, so `haveI` (rather than
-- the `have` suggested by this linter) is the correct binder.
set_option linter.style.haveILetI false

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.PinchLemma3.ClosedDiscA

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- The surface of a parametrised torus is locally connected: it is locally path connected
(`locallyPathConnected_carrier`) and locally path connected spaces are locally connected. -/
theorem locallyConnected_carrier (P : Work.CoreTopology.ParamTorus) :
    LocallyConnectedSpace ↥P.carrier := by
  haveI : LocallyPathConnectedSpace ↥P.carrier := locallyPathConnected_carrier P
  infer_instance

/-- For `K ⊆ P.carrier` and `S ⊆ ↥K`, the preimage under `↥P.carrier → ℝ³` of the image of `S`
under `↥K → ℝ³` is the image of `S` under the inclusion `↥K → ↥P.carrier`. -/
theorem preimage_val_image_eq {K : Set R3} (hKc : K ⊆ P.carrier) (S : Set ↥K) :
    (Subtype.val : ↥P.carrier → R3) ⁻¹' ((Subtype.val : ↥K → R3) '' S)
      = (fun w : ↥K => (⟨(w : R3), hKc w.2⟩ : ↥P.carrier)) '' S := by
  have himg : (Subtype.val : ↥K → R3) '' S
      = (Subtype.val : ↥P.carrier → R3) ''
        ((fun w : ↥K => (⟨(w : R3), hKc w.2⟩ : ↥P.carrier)) '' S) := by
    rw [← Set.image_comp]
    congr 1
  rw [himg, Set.preimage_image_eq _ Subtype.val_injective]

theorem isOpenInCarrier_connectedComponentIn {P : Work.CoreTopology.ParamTorus}
    {K : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hK : Work.SurgeryInvariance.IsOpenInCarrier P K)
    (hKc : K ⊆ P.carrier) (x : LeanEval.KnotTheory.PardonDistortion.R3) :
    Work.SurgeryInvariance.IsOpenInCarrier P (connectedComponentIn K x) := by
  rw [Work.SurgeryInvariance.IsOpenInCarrier]
  by_cases hx : x ∈ K
  · haveI : LocallyConnectedSpace ↥P.carrier := locallyConnected_carrier P
    -- the open subset `A = P.carrier ∩ K` of the surface
    have hAopen : IsOpen (Subtype.val ⁻¹' K : Set ↥P.carrier) := hK
    -- the two canonical maps
    let i : ↥K → ↥P.carrier := fun w => ⟨(w : R3), hKc w.2⟩
    let e : ↥K ≃ₜ ↥(Subtype.val ⁻¹' K : Set ↥P.carrier) :=
      subtypePreimageHomeo (P := P) hKc
    let xK : ↥K := ⟨x, hx⟩
    let y : ↥P.carrier := ⟨x, hKc hx⟩
    have hyA : y ∈ (Subtype.val ⁻¹' K : Set ↥P.carrier) := hx
    -- `e` sends `xK` to `⟨y, hyA⟩`
    have hex : e xK = (⟨y, hyA⟩ : ↥(Subtype.val ⁻¹' K : Set ↥P.carrier)) := rfl
    -- the preimage of the component is the image of the component of `xK` under `i`
    have hpre : (Subtype.val ⁻¹' (connectedComponentIn K x) : Set ↥P.carrier)
        = i '' connectedComponent xK := by
      rw [connectedComponentIn_eq_image hx]
      have h1 : (Subtype.val : ↥P.carrier → R3) ⁻¹'
            ((Subtype.val : ↥K → R3) '' connectedComponent (⟨x, hx⟩ : ↥K))
          = i '' connectedComponent (⟨x, hx⟩ : ↥K) :=
        preimage_val_image_eq (P := P) hKc _
      exact h1
    -- the component of `y` in `A` is the image of the component of `xK` under `i`
    have hcomp : connectedComponentIn (Subtype.val ⁻¹' K : Set ↥P.carrier) y
        = i '' connectedComponent xK := by
      rw [connectedComponentIn_eq_image hyA]
      have heS : e '' connectedComponent xK = connectedComponent (e xK) := by
        have h := e.image_connectedComponentIn (s := Set.univ) (x := xK) (Set.mem_univ xK)
        simpa [connectedComponentIn_univ] using h
      rw [hex] at heS
      have hcoe : (Subtype.val : ↥(Subtype.val ⁻¹' K : Set ↥P.carrier) → ↥P.carrier) ∘ e = i := rfl
      rw [← heS, ← Set.image_comp, hcoe]
    rw [hpre, ← hcomp]
    exact hAopen.connectedComponentIn
  · rw [connectedComponentIn_eq_empty hx]
    simp

end

end Work.PinchLemma3.ClosedDiscA
