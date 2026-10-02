import Submission.Work.ThomBordism.CofAtlas.Defs
import Submission.Work.ThomBordism.CofAtlas.det_section_prod
import Submission.Work.ThomBordism.CofAtlas.reflOph_mem_contDiffGroupoid

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The signs of the `Lvl` charts of a coframed level set, and the corrected atlas

Vocabulary for the proof of `Work.ThomBordism.levelSet_positiveAtlas_of_coframing`
(cf. `CofAtlas/NOTES.md`).

Let `D : Cof k n M` be the bundled data: a smooth level function `v : M → ℝⁿ` with a projection
field `P` onto its derivative along `W = v⁻¹(0)`, local level-set data `L` for `W` (whose `Lvl`
charts are `chartAt S x`), and a positively cocycled coframing `(ℓ j, e j)` of the kernel
`range P`.

For `x ∈ W` and `p ∈ M` we define

* `Delta D x p` — the derivative of the chart change `domChartAt x ∘ (extChartAt x)⁻¹` (normal-form
  coordinates versus ambient coordinates), `DeltaInv` its inverse;
* `Tex D x y p` — the derivative of the *ambient* chart change, whose determinant is positive by
  `hMdet`;
* `Tdom D x y p` — the derivative of the change of *normal-form* charts;
* `Omega D x p` — the coframing of the level set in normal-form coordinates,
  `ℓ (jx x) ∘ dv_p ∘ (d domChartAt x)⁻¹`.

Then `sgn D x p` and `tau D x p` are the signs of `det (σ ∘ (β_x, Ω))` and of `det (Delta x p)`;
both are constant on the connected source `src x` of the chart at `x`, so
`flipSign D x := sgn D x x * tau D x x` (the value at the centre) is the correct correction, and
`newChart D x` is the chart at `x` post-composed with the reflection `reflOph` of the half-space
when `flipSign D x = -1` and restricted to the connected source `src x`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Work.PTGeometric
open Work.PTGeometric.Lvl

namespace Work.ThomBordism.CofAtlas

noncomputable section

/-- The ambient (half-space model) manifold dimension. -/
abbrev NN (k : ℕ) : ℕ := (8 + k) + 1

/-- The ambient model space `ℝ ^ N`. -/
abbrev ModN (k : ℕ) : Type := EuclideanSpace ℝ (Fin (NN k))

/-- A fixed linear equivalence `ℝ⁹ × ℝᵏ ≅ ℝ ^ N`. -/
noncomputable def sigma (k : ℕ) : (E9 × EuclideanSpace ℝ (Fin k)) ≃ₗ[ℝ] ModN k :=
  Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (by
    rw [Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace,
      finrank_euclideanSpace]
    simp only [NN, Fintype.card_fin]
    omega))

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (NN k)) M]
  [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]

namespace Cof

/-! ## The charts and their changes of coordinates -/

/-- The ambient chart at `x` of the given charted-space structure on `M`. -/
abbrev ambChart (D : Cof k n M) (x : D.S.Pre) :
    OpenPartialHomeomorph M (EuclideanHalfSpace (NN k)) :=
  chartAt (EuclideanHalfSpace (NN k)) (x : M)

/-- The normal-form domain chart at `x`. -/
abbrev domChart (D : Cof k n M) (x : D.S.Pre) :
    OpenPartialHomeomorph M (EuclideanHalfSpace (NN k)) :=
  D.S.domChartAt x

/-- The extended normal-form chart at `x`. -/
abbrev domExt (D : Cof k n M) (x : D.S.Pre) : PartialEquiv M (ModN k) :=
  (D.domChart x).extend (𝓡∂ (NN k))

/-- The extended ambient chart at `x`. -/
abbrev ambExt (D : Cof k n M) (x : D.S.Pre) : PartialEquiv M (ModN k) :=
  (D.ambChart x).extend (𝓡∂ (NN k))

/-- The `Lvl` chart of the level set at `x`. -/
abbrev lvlChart (D : Cof k n M) (x : D.S.Pre) :
    OpenPartialHomeomorph D.S.Pre (EuclideanHalfSpace 9) :=
  Work.PTGeometric.Lvl.Setup.chartAt D.S x

/-- The extended `Lvl` chart of the level set at `x`. -/
abbrev lvlExt (D : Cof k n M) (x : D.S.Pre) :
    PartialEquiv D.S.Pre (EuclideanSpace ℝ (Fin 9)) :=
  (D.lvlChart x).extend (𝓡∂ 9)

/-- **The change of coordinates from the normal-form chart at `x` to the normal-form chart at `y`**,
as a partial equivalence of the ambient model space. -/
abbrev domChange (D : Cof k n M) (x y : D.S.Pre) : PartialEquiv (ModN k) (ModN k) :=
  (𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.domChart y)

/-- **The change of coordinates from the ambient chart at `x` to the ambient chart at `y`**. -/
abbrev ambChange (D : Cof k n M) (x y : D.S.Pre) : PartialEquiv (ModN k) (ModN k) :=
  (𝓡∂ (NN k)).extendCoordChange (D.ambChart x) (D.ambChart y)

/-- **The change of coordinates from the ambient chart at `x` to the normal-form chart at `x`**. -/
abbrev ambDomChange (D : Cof k n M) (x : D.S.Pre) : PartialEquiv (ModN k) (ModN k) :=
  (𝓡∂ (NN k)).extendCoordChange (D.ambChart x) (D.domChart x)

/-- **The change of coordinates from the normal-form chart at `x` to the ambient chart at `x`**. -/
abbrev domAmbChange (D : Cof k n M) (x : D.S.Pre) : PartialEquiv (ModN k) (ModN k) :=
  (𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.ambChart x)

/-- **The chart change from the ambient chart to the normal-form chart** at `x`, as a linear map. -/
noncomputable def Delta (D : Cof k n M) (x : D.S.Pre) (p : M) : ModN k →L[ℝ] ModN k :=
  fderiv ℝ (D.ambDomChange x) (D.ambExt x p)

/-- The inverse chart change, as a linear map. -/
noncomputable def DeltaInv (D : Cof k n M) (x : D.S.Pre) (p : M) : ModN k →L[ℝ] ModN k :=
  fderiv ℝ (D.domAmbChange x) (D.domExt x p)

/-- **The derivative of the ambient chart change** at `p`, from the chart at `x` to the chart at
`y`. -/
noncomputable def Tex (D : Cof k n M) (x y : D.S.Pre) (p : M) : ModN k →L[ℝ] ModN k :=
  fderiv ℝ (D.ambChange x y) (D.ambExt x p)

/-- **The derivative of the change of normal-form charts** at `p`. -/
noncomputable def Tdom (D : Cof k n M) (x y : D.S.Pre) (p : M) : ModN k →L[ℝ] ModN k :=
  fderiv ℝ (D.domChange x y) (D.domExt x p)

/-- The change of coordinates from the normal-form chart at `x` to the **ambient chart at `p`**. -/
abbrev domChangeToPt (D : Cof k n M) (x : D.S.Pre) (p : M) : PartialEquiv (ModN k) (ModN k) :=
  (𝓡∂ (NN k)).extendCoordChange (D.domChart x) (chartAt (EuclideanHalfSpace (NN k)) p)

/-- The derivative at `domExt x p` of the change of coordinates from the normal-form chart at `x`
to the ambient chart at `p`: it transports normal-form coordinates to the coordinates in which
`mfderiv v p` is written. -/
noncomputable def Cx (D : Cof k n M) (x : D.S.Pre) (p : M) : ModN k →L[ℝ] ModN k :=
  fderiv ℝ (D.domChangeToPt x p) (D.domExt x p)

/-- **The coframing of the level set in normal-form coordinates** at `p`: `mfderiv v p` (written in
the coordinates of the ambient chart at `p`) transported to the normal-form coordinates at `x` and
read through the coframing `ℓ (jx x)`. -/
noncomputable def Omega (D : Cof k n M) (x : D.S.Pre) (p : M) :
    ModN k →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (D.ℓ (D.jx x)).comp ((mfderiv (𝓡∂ (NN k)) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v p).comp
    (D.Cx x p))

/-- The pair `(β_x, Ω)` of the normal-form splitting and the coframing, as a single linear map. -/
noncomputable def phiD (D : Cof k n M) (x : D.S.Pre) (p : M) :
    ModN k →L[ℝ] (E9 × EuclideanSpace ℝ (Fin k)) :=
  (D.S.chartBeta x).prod (D.Omega x p)

/-- **The sign of the chart at `x`** at the point `p`, relative to the sigma-fixed model
orientation: the sign of `det (σ ∘ (β_x, Ω_x(p)))`. -/
noncomputable def sgn (D : Cof k n M) (x : D.S.Pre) (p : M) : SignType :=
  SignType.sign (LinearMap.det ((sigma k).toLinearMap.comp (D.phiD x p).toLinearMap))

/-- **The sign of the chart change** at `p`: `sign (det (Delta D x p))`. -/
noncomputable def tau (D : Cof k n M) (x : D.S.Pre) (p : M) : SignType :=
  SignType.sign (LinearMap.det (D.Delta x p).toLinearMap)

/-- **The correction sign of the chart at `x`**: the sign of the chart at its own centre. -/
noncomputable def flipSign (D : Cof k n M) (x : D.S.Pre) : SignType :=
  D.sgn x (x : M) * D.tau x (x : M)

/-- The coframing transition `ℓ (jx y) ∘ e (jx x) p : ℝᵏ → ℝᵏ`. -/
noncomputable abbrev gLin (D : Cof k n M) (x y : D.S.Pre) (p : M) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (D.ℓ (D.jx y)).comp (D.e (D.jx x) p)

/-- Whether the chart at `x` has to be flipped. -/
noncomputable def flipBool (D : Cof k n M) (x : D.S.Pre) : Bool :=
  decide (D.flipSign x = -1)

/-- The reflection (or the identity) used to correct the chart at `x`. -/
noncomputable def reflectMap (D : Cof k n M) (x : D.S.Pre) :
    OpenPartialHomeomorph (EuclideanHalfSpace 9) (EuclideanHalfSpace 9) :=
  if D.flipBool x then reflOph
  else OpenPartialHomeomorph.refl (EuclideanHalfSpace 9)

/-- **The corrected chart at `x`**: the `Lvl` chart at `x`, post-composed with the reflection if the
chart sign is negative, restricted to the connected source `src x`. -/
noncomputable def newChart (D : Cof k n M) (x : D.S.Pre) :
    OpenPartialHomeomorph D.S.Pre (EuclideanHalfSpace 9) :=
  ((D.lvlChart x).trans (D.reflectMap x)).restr (D.src x)

/-- The atlas of corrected charts. -/
def newAtlas (D : Cof k n M) : Set (OpenPartialHomeomorph D.S.Pre (EuclideanHalfSpace 9)) :=
  Set.range (D.newChart)

end Cof

end

end Work.ThomBordism.CofAtlas
