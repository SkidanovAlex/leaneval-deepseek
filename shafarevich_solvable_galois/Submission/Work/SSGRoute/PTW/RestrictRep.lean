import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
import Submission.Work.SSGRoute.PTW.NontrivialEigenspace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The restriction of the regular representation to an invariant subspace

For a `regRep`-invariant submodule `E ≤ Lp ℂ 2 μ`, the regular representation restricts to a monoid
homomorphism `Q →* (E ≃ₗᵢ[ℂ] E)` into linear isometry equivalences.  This is the input needed by
`finiteDim_rep_exists_weight`, and hence the bridge between the spectral step and the character
`χ : Q →* ℂˣ` with `χ y ≠ 1` from which the open index-`p` subgroup is built.

## How to use it (next steps)

Given `lam ≠ 0` and `E := Module.End.eigenspace ((avgOp ξ : _ →L[ℂ] _) : _ →ₗ[ℂ] _) lam`
with a vector `v ∈ E`, `v ≠ 0`, `regRep y v ≠ v` (produced by
`Work.SSGRoute.PTW.exists_eigenspace_regRep_ne_one` in `NontrivialEigenspace.lean`):

* `hE : ∀ h, ∀ w ∈ E, regRep h w ∈ E` is
  `Work.SSGRoute.PTW.avgOp_regRep_mem_eigenspace` (`Spectral.lean`);
* `FiniteDimensional ℂ E` is
  `ContinuousLinearMap.finite_dimensional_eigenspace` (needs compactness of `avgOp ξ`);
* `restrictRepHom E hE : Q →* (E ≃ₗᵢ[ℂ] E)` is the representation; `restrictRepHom E hE y ≠ 1`
  because it moves `⟨v, hv⟩`;
* `Work.SSGRoute.PTW.finiteDim_rep_exists_weight` then yields `χ : Q →* ℂˣ` with `χ y ≠ 1` and a
  nonzero eigenvector `w : E` with `regRep g w = χ g • w` for all `g`;
* `χ` is continuous: for `w ≠ 0`, `(χ g : ℂ) = ⟪regRep g w, w⟫ / ‖w‖²` (with the conjugate-linearity
  convention), and `g ↦ regRep g w` is continuous by
  `Work.SSGRoute.PTW.continuous_regRep_apply`;
* finally `χ(Q) ⊆ μ_p` (exponent `p`), `χ y ≠ 1`, so `ker χ` is closed of finite index, hence
  open (`Subgroup.isOpen_of_isClosed_of_finiteIndex`); refining inside the finite quotient
  `Q ⧸ ker χ` (an `𝔽_p`-vector space via `AddCommGroup.zmodModule`) by a hyperplane avoiding the
  class of `y` gives the open index-`p` subgroup — the same device as steps 3–4 of the sibling file
  `Submission/Work/SSGRoute/PTW/openIndexPSubgroup.lean`.
-/

namespace Work.SSGRoute.PTW

open MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [T2Space Q] [MeasurableSpace Q] [BorelSpace Q] {μ : Measure Q}
  [Measure.IsMulLeftInvariant μ] [IsProbabilityMeasure μ] [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop]

/-- The restricted regular representation, as a linear map on an invariant submodule. -/
noncomputable def restrictRepLin (E : Submodule ℂ (Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, regRep (μ := μ) h v ∈ E) (g : Q) : E →ₗ[ℂ] E :=
  ((regRep (μ := μ) g : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ).restrict
    (fun v hv => hE g v hv)

@[simp]
theorem restrictRepLin_apply (E : Submodule ℂ (Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, regRep (μ := μ) h v ∈ E) (g : Q) (v : E) :
    ((restrictRepLin (μ := μ) E hE g v : E) : Lp ℂ 2 μ) = regRep (μ := μ) g (v : Lp ℂ 2 μ) :=
  rfl

theorem restrictRepLin_injective (E : Submodule ℂ (Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, regRep (μ := μ) h v ∈ E) (g : Q) :
    Function.Injective (restrictRepLin (μ := μ) E hE g) := by
  intro u v huv
  apply Subtype.ext
  apply regRep_injective (μ := μ) g
  have := congrArg (fun w : E => (w : Lp ℂ 2 μ)) huv
  simpa using this

theorem restrictRepLin_leftInverse (E : Submodule ℂ (Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, regRep (μ := μ) h v ∈ E) (g : Q) :
    Function.LeftInverse (restrictRepLin (μ := μ) E hE g⁻¹) (restrictRepLin (μ := μ) E hE g) := by
  intro v
  apply Subtype.ext
  show regRep (μ := μ) g⁻¹ (regRep (μ := μ) g (v : Lp ℂ 2 μ)) = (v : Lp ℂ 2 μ)
  rw [← regRep_mul_apply, inv_mul_cancel, regRep_one]
  rfl

theorem restrictRepLin_surjective (E : Submodule ℂ (Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, regRep (μ := μ) h v ∈ E) (g : Q) :
    Function.Surjective (restrictRepLin (μ := μ) E hE g) := by
  intro w
  refine ⟨restrictRepLin (μ := μ) E hE g⁻¹ w, ?_⟩
  apply Subtype.ext
  show regRep (μ := μ) g (regRep (μ := μ) g⁻¹ (w : Lp ℂ 2 μ)) = (w : Lp ℂ 2 μ)
  rw [← regRep_mul_apply, mul_inv_cancel, regRep_one]
  rfl

/-- The regular representation restricted to an invariant submodule, as a linear isometry
equivalence. -/
noncomputable def restrictRep (E : Submodule ℂ (Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, regRep (μ := μ) h v ∈ E) (g : Q) : E ≃ₗᵢ[ℂ] E where
  toLinearEquiv := LinearEquiv.ofBijective (restrictRepLin (μ := μ) E hE g)
    ⟨restrictRepLin_injective (μ := μ) E hE g, restrictRepLin_surjective (μ := μ) E hE g⟩
  norm_map' v := by
    show ‖regRep (μ := μ) g ((v : E) : Lp ℂ 2 μ)‖ = ‖((v : E) : Lp ℂ 2 μ)‖
    rw [norm_regRep_apply]

/-- The restricted regular representation as a monoid homomorphism. -/
noncomputable def restrictRepHom (E : Submodule ℂ (Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, regRep (μ := μ) h v ∈ E) : Q →* (E ≃ₗᵢ[ℂ] E) where
  toFun := restrictRep (μ := μ) E hE
  map_one' := by
    refine LinearIsometryEquiv.ext fun v => ?_
    exact Subtype.ext (by
      show regRep (μ := μ) 1 ((v : E) : Lp ℂ 2 μ) = ((v : E) : Lp ℂ 2 μ)
      rw [regRep_one]
      rfl)
  map_mul' g h := by
    refine LinearIsometryEquiv.ext fun v => ?_
    exact Subtype.ext (by
      show regRep (μ := μ) (g * h) ((v : E) : Lp ℂ 2 μ)
        = regRep (μ := μ) g (regRep (μ := μ) h ((v : E) : Lp ℂ 2 μ))
      rw [regRep_mul_apply])
