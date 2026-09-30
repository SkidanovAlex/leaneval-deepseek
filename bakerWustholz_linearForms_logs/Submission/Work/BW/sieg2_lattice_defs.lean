import Mathlib
import Submission.Work.BW.sieg2KernelDefs
import Submission.Work.BW.sieg2_PhiE_aux
import Submission.Work.BW.sieg2_intLatE_basis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The product model of `(KE F)^N` and the lattice `intLatE`

This file sets up the vocabulary used by `Work.BW.sieg2_lattice_instances` and the lemmas it
delegates.

* `pe F N` is the `ℝ`-linear equivalence between the Euclidean coordinate model
  `EuclideanSpace ℝ (Fin N × index F)` (in which `PhiE`, `intLatE`, `kerLatE`, `imgLatE` live)
  and the product model `Fin N → KE F` (in which `Phi` and its algebra live); it sends a family
  of coordinates to the family of vectors of `KE F` obtained by expanding in the orthonormal
  basis `stdOrthonormalBasis F`.

* `PLat F N = (euclidean.integerLattice F)^N` is the product lattice in the product model; it is
  the image of `intLatE F N` under `pe F N`.
-/

open scoped Classical
open NumberField

namespace Work.BW

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The `ℝ`-linear equivalence between the Euclidean coordinate model and the product model. -/
def pe (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) ≃ₗ[ℝ] (Fin N → KE F) :=
  (WithLp.linearEquiv 2 ℝ (Fin N × NumberField.mixedEmbedding.index F → ℝ)).trans
    (psiEquiv (F := F) N)

@[simp]
theorem pe_apply (N : ℕ) (x : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F))
    (j : Fin N) :
    pe F N x j = ∑ c, x (j, c) • NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c :=
  rfl

/-- The product lattice `(𝓞 F)^N` in the product model. -/
def PLat (F : Type*) [Field F] [NumberField F] (N : ℕ) : Submodule ℤ (Fin N → KE F) :=
  Submodule.pi Set.univ (fun _ : Fin N => NumberField.mixedEmbedding.euclidean.integerLattice F)

@[simp]
theorem mem_PLat {N : ℕ} (y : Fin N → KE F) :
    y ∈ PLat F N ↔ ∀ j, y j ∈ NumberField.mixedEmbedding.euclidean.integerLattice F := by
  simp [PLat, Submodule.mem_pi]

end

end Work.BW
