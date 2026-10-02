import Submission.Work.PTGeometric.LastMile

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: from the ambient collapse-end data to the local level-set data

The bridge between the ambient form of the last mile (`Work.PTGeometric.AmbientCollapseEnd`) and the
local preimage theorem (G4, `Work.PTGeometric.LocalLevelPreimageTheorem`): the zero set of the
ambient vector field carries local level-set data.

This is the step at which the *ambient* coordinates of the Pontryagin–Thom construction (a
projection-valued matrix `P` and a vector `v` with `v x ∈ im (P x)`) are turned into the chart-wise
data that `Work.PTGeometric.localPreimageTheorem` consumes, without ever constructing a map into the
abstract total space of `γ_k`: at a point `x` with `v x = 0`, the chart of the Grassmannian at the
plane `im (P x)` (carried by the linear map `ℓ` of `AmbientCollapseEnd.transverse`, injective on
*every* plane `im (P y)` for `y` in an open neighbourhood of `x`, which is what a trivialisation of
the bundle over an open set of the Grassmannian gives) supplies the defining function `ℓ ∘ v`, and
its zero set coincides with `{y | v y = 0}` on that neighbourhood because `v y` lies in the plane
`im (P y)` and `ℓ` is injective there.

## Main result

* `Work.PTGeometric.localLevelData_of_ambientCollapseEnd`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

/-- **The zero set of the ambient data carries local level-set data.**

`W := {x | v x = 0}` (the transverse zero set of the ambient vector field) is closed, its boundary
part is exactly the collapse end's preimage of the zero section (`S ∩ {v = 0}`, which
`AmbientCollapseEnd.endHomeo` identifies with the pieces), and it carries the local level-set data
`LocalLevelData k M W` with the defining functions `ℓ ∘ v` read in the Grassmannian charts. -/
theorem localLevelData_of_ambientCollapseEnd {n k : ℕ} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} (D : AmbientCollapseEnd n k ι Fam) :
    ∃ W : Set D.M, IsClosed W ∧ Nonempty (LocalLevelData k D.M W) ∧
      W ∩ (𝓡∂ ((8 + k) + 1)).boundary D.M = D.S ∩ {x : D.M | D.v x = 0} := by
  classical
  refine ⟨{x : D.M | D.v x = 0}, ?_, ?_, ?_⟩
  · rw [show {x : D.M | D.v x = 0} = D.v ⁻¹' ({0} : Set (EuclideanSpace ℝ (Fin n))) from rfl]
    exact isClosed_singleton.preimage D.continuous_v
  · have hchoice : ∀ x : ↥({x : D.M | D.v x = 0} : Set D.M),
        ∃ (U : Set D.M) (g : D.M → EuclideanSpace ℝ (Fin k)),
          IsOpen U ∧ (x : D.M) ∈ U ∧
          ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ g ∧
          (∀ y : D.M, y ∈ U → (g y = 0 ↔ y ∈ ({x : D.M | D.v x = 0} : Set D.M))) ∧
          IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ g (x : D.M) ∧
          (∀ hx : (x : D.M) ∈ (𝓡∂ ((8 + k) + 1)).boundary D.M,
            IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
              (fun z : ↥((𝓡∂ ((8 + k) + 1)).boundary D.M) => g (z : D.M)) ⟨x, hx⟩) := by
      intro x
      have hvx : D.v (x : D.M) = 0 := x.2
      have hzeros : ∀ (ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k))
          (U : Set D.M), (∀ y ∈ U, ∀ z : EuclideanSpace ℝ (Fin n), D.P y z = z → ℓ z = 0 → z = 0) →
          ∀ y : D.M, y ∈ U → (ℓ (D.v y) = 0 ↔ y ∈ ({x : D.M | D.v x = 0} : Set D.M)) := by
        intro ℓ U hinj y hy
        constructor
        · intro hgy
          exact hinj y hy (D.v y) (D.mem y) hgy
        · intro hy'
          rw [show D.v y = 0 from hy', map_zero ℓ]
      by_cases hx : (x : D.M) ∈ (𝓡∂ ((8 + k) + 1)).boundary D.M
      · obtain ⟨ℓ, U, hUopen, hxU, hinj, hsub, hbsub⟩ := D.bndTransverse (x : D.M) hx hvx
        exact ⟨U, fun y => ℓ (D.v y), hUopen, hxU, ℓ.contMDiff.comp D.contMDiff_v,
          hzeros ℓ U hinj, hsub, fun hy => by
            have h : (⟨x, hy⟩ : ↥((𝓡∂ ((8 + k) + 1)).boundary D.M)) = ⟨x, hx⟩ :=
              Subtype.ext rfl
            rwa [h]⟩
      · obtain ⟨ℓ, U, hUopen, hxU, hinj, hsub⟩ := D.transverse (x : D.M) hvx
        exact ⟨U, fun y => ℓ (D.v y), hUopen, hxU, ℓ.contMDiff.comp D.contMDiff_v,
          hzeros ℓ U hinj, hsub, fun hy => absurd hy hx⟩
    choose U g hUopen hxU hgsm hg0 hgsub hgbnd using hchoice
    exact ⟨{ U := U, isOpen_U := hUopen, mem_U := hxU, g := g, contMDiff_g := hgsm, zero_iff := hg0, isSubmersion_g := hgsub, bndSubmersion := hgbnd }⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨hv, hbd⟩ : x ∈ ({x : D.M | D.v x = 0} : Set D.M) ∧
          x ∈ (𝓡∂ ((8 + k) + 1)).boundary D.M := hx
      exact ⟨by_contra (fun hxS => D.avoid x hbd hxS hv), hv⟩
    · intro hx
      obtain ⟨hS, hv⟩ : x ∈ D.S ∧ x ∈ ({x : D.M | D.v x = 0} : Set D.M) := hx
      exact ⟨hv, D.S_subset_bdry hS⟩

end

end Work.PTGeometric
