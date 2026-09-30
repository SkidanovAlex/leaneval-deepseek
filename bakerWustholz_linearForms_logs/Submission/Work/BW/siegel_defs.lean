import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the Vaaler-free Siegel step over a number field

This file collects the vocabulary used by `Work.BW.siegel_mixed_short_vector`:

* `Work.BW.kerVecs F a` : the integral kernel vectors `x ∈ (𝓞 F)^N` of the matrix `a`;
* `Work.BW.coord` : the coordinate functional of the mixed space w.r.t. `mixedEmbedding.stdBasis`;
* `Work.BW.kerLattice F a` : the kernel lattice, i.e. the `ℤ`-span of the coordinate vectors of the
  mixed images of `kerVecs`, inside `(index F → ℝ)^N ≅ ℝ^{dN}` (the standard coordinates of the
  mixed space);
* `Work.BW.covolumeOf v` : the covolume `√|det Gram v|` of a `ℤ`-independent family `v`.

The `ℤ`-lattice `kerLattice F a` is the object whose covolume the Bombieri–Vaaler step bounds.
-/

namespace Work.BW

open NumberField MeasureTheory

variable {F : Type*} [Field F] [NumberField F]

/-- The integral vectors killed by the matrix `a`. -/
def kerVecs {M N : ℕ} (a : Fin M → Fin N → F) : Set (Fin N → RingOfIntegers F) :=
  {x | ∀ i, ∑ j, a i j * ((x j : RingOfIntegers F) : F) = 0}

/-- The coordinate functional of the mixed space with respect to the standard basis. -/
noncomputable def coord (v : NumberField.mixedEmbedding.mixedSpace F) :
    NumberField.mixedEmbedding.index F → ℝ :=
  (NumberField.mixedEmbedding.stdBasis F).repr v

/-- The coordinate vector of an integral vector `x : (𝓞 F)^N` in the mixed space, as a point of
`(index F → ℝ)^N`. -/
noncomputable def coordVec {N : ℕ} (x : Fin N → RingOfIntegers F) :
    Fin N → (NumberField.mixedEmbedding.index F → ℝ) :=
  fun j => coord (F := F) (NumberField.mixedEmbedding F ((x j : RingOfIntegers F) : F))

/-- The kernel lattice: the `ℤ`-span of the coordinate vectors of the mixed images of the integral
kernel vectors, inside `(index F → ℝ)^N`. -/
noncomputable def kerLattice {M N : ℕ} (a : Fin M → Fin N → F) :
    Submodule ℤ (Fin N → (NumberField.mixedEmbedding.index F → ℝ)) :=
  Submodule.span ℤ (coordVec (F := F) '' kerVecs a)

/-- The Gram determinant of a finite family of vectors of `(index F → ℝ)^N`, in the standard
(product) inner product. -/
noncomputable def gramDet {N k : ℕ}
    (v : Fin k → (Fin N → (NumberField.mixedEmbedding.index F → ℝ))) : ℝ := by
  classical
  exact (Matrix.of (fun i j => ∑ t : Fin N, ∑ s : NumberField.mixedEmbedding.index F,
      v i t s * v j t s)).det

/-- The covolume `√|det Gram v|` of a finite family of vectors. -/
noncomputable def covolumeOf {N k : ℕ}
    (v : Fin k → (Fin N → (NumberField.mixedEmbedding.index F → ℝ))) : ℝ :=
  Real.sqrt |gramDet (F := F) v|

end Work.BW
