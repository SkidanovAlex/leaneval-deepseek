import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFT.GaloisIdeles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFT.Galois

open NK.GlobalCFT
open scoped NumberField RestrictedProduct

/-- The group `Gal(L/K)` acts on the idèle group `𝕀 L` by
`(σ · x)_w = σ_*(x_{σ⁻¹ w})`, where `σ_* : L_w ≃+* L_{σ w}` is the canonical isomorphism of
local fields.  For the action to be well defined on the restricted product one needs that this
operation preserves the restricted product: this is the statement below, that the component
`(σ · x)_w` is a local unit for all but finitely many places `w`.

Indeed, `x` itself is a local unit outside a finite set `S` of places, and a local isomorphism
maps local units to local units; hence `(σ · x)_w` fails to be a local unit only for the finitely
many `w` with `σ⁻¹ • w ∈ S`. -/
theorem globalCFT_eventually_smul_mem {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L) (x : NK.GlobalCFT.Idele L) :
    ∀ᶠ w in Filter.cofinite,
      Units.map (NK.GlobalCFT.Place.localRingEquiv σ⁻¹ w).symm.toMonoidHom
        (x (σ⁻¹ • w)) ∈ NK.GlobalCFT.Place.localUnits L w := by
  -- `x` is a local unit at all but finitely many places.
  have hx : ∀ᶠ v in Filter.cofinite,
      x v ∈ NK.GlobalCFT.Place.localUnits L v := x.2
  rw [Filter.eventually_cofinite] at hx ⊢
  -- The bad places of `σ · x` are contained in the image of the bad places of `x` under `σ`.
  refine (hx.image (fun v : NK.GlobalCFT.Place L => σ • v)).subset ?_
  intro w hw
  refine ⟨σ⁻¹ • w, ?_, by simp⟩
  -- If `x` were a local unit at `σ⁻¹ • w`, then `(σ · x)_w` would be a local unit at `w`,
  -- because the local isomorphism maps local units to local units.
  intro hgood
  exact hw ((NK.GlobalCFT.Place.localRingEquiv_mem_localUnits σ⁻¹ w _).2 (by
    have hcomp : Units.map (NK.GlobalCFT.Place.localRingEquiv σ⁻¹ w).toMonoidHom
        (Units.map (NK.GlobalCFT.Place.localRingEquiv σ⁻¹ w).symm.toMonoidHom
          (x (σ⁻¹ • w))) = x (σ⁻¹ • w) := by
      ext
      simp
    rw [hcomp]
    exact hgood))

end NK.GlobalCFT.Galois
