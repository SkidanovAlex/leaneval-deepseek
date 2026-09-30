import Mathlib
import Submission.Work.BW.sieg2Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Objects for the sharp Bombieri–Vaaler kernel-lattice bound

This file fixes the vocabulary used by `Work.BW.sieg2_kernel_family` (the sharp
kernel-lattice covolume bound) and by the lemmas it delegates.

* `KE F` is the Euclidean mixed space `ℝ^{r₁} × ℂ^{r₂}` of `F` (as an inner product space),
  and `meK a` is the image of `a : F`;
* `mulK a` is the `ℝ`-linear "multiplication by `meK a`";
* `Phi a : (Fin N → KE F) →ₗ[ℝ] (Fin M → KE F)` is the linear map
  `y ↦ (∑_j meK (a i j) * y j)_i` (the `ℝ`-linear extension of the `F`-linear map given by the
  rows `a i`); `PhiL a` is its continuous version;
* `intLat F N` is the integral lattice `(meK '' 𝓞 F)^N ⊆ (KE F)^N`.
-/

open scoped Classical
open NumberField

namespace Work.BW

noncomputable section

/-- The Euclidean mixed space of `F` (an inner product space of dimension `[F : ℚ]`). -/
abbrev KE (F : Type*) [Field F] [NumberField F] :=
  NumberField.mixedEmbedding.euclidean.mixedSpace F

/-- The image of `a : F` in the Euclidean mixed space. -/
def meK {F : Type*} [Field F] [NumberField F] (a : F) : KE F :=
  (NumberField.mixedEmbedding.euclidean.toMixed F).symm (NumberField.mixedEmbedding F a)

/-- Multiplication by `meK a` as an `ℝ`-linear map of the Euclidean mixed space. -/
def mulK {F : Type*} [Field F] [NumberField F] (a : F) : KE F →ₗ[ℝ] KE F :=
  (NumberField.mixedEmbedding.euclidean.toMixed F).symm.toLinearMap.comp
    ((LinearMap.mulLeft ℝ (NumberField.mixedEmbedding F a)).comp
      (NumberField.mixedEmbedding.euclidean.toMixed F).toLinearMap)

@[simp]
theorem mulK_apply {F : Type*} [Field F] [NumberField F] (a : F) (y : KE F) :
    mulK a y = (NumberField.mixedEmbedding.euclidean.toMixed F).symm
      (NumberField.mixedEmbedding F a *
        (NumberField.mixedEmbedding.euclidean.toMixed F) y) := rfl

@[simp]
theorem mulK_one {F : Type*} [Field F] [NumberField F] : mulK (F := F) 1 = LinearMap.id := by
  ext y
  simp [mulK]

/-- The map `y ↦ (∑_j meK (a i j) * y j)_i`. -/
def Phi {F : Type*} [Field F] [NumberField F] {M N : ℕ} (a : Fin M → Fin N → F) :
    (Fin N → KE F) →ₗ[ℝ] (Fin M → KE F) where
  toFun y := fun i => ∑ j, mulK (a i j) (y j)
  map_add' y z := by
    ext i
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c y := by
    ext i
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

@[simp]
theorem Phi_apply {F : Type*} [Field F] [NumberField F] {M N : ℕ} (a : Fin M → Fin N → F)
    (y : Fin N → KE F) (i : Fin M) :
    Phi a y i = ∑ j, mulK (a i j) (y j) := rfl

/-- The continuous version of `Phi a`. -/
def PhiL {F : Type*} [Field F] [NumberField F] {M N : ℕ} (a : Fin M → Fin N → F) :
    (Fin N → KE F) →L[ℝ] (Fin M → KE F) :=
  (Phi a).toContinuousLinearMap

@[simp]
theorem PhiL_apply {F : Type*} [Field F] [NumberField F] {M N : ℕ} (a : Fin M → Fin N → F)
    (y : Fin N → KE F) :
    PhiL a y = Phi a y := rfl

/-- The integral lattice `(meK '' 𝓞 F)^N ⊆ (KE F)^N`. -/
def intLat (F : Type*) [Field F] [NumberField F] (N : ℕ) : Submodule ℤ (Fin N → KE F) :=
  Submodule.pi Set.univ (fun _ : Fin N => NumberField.mixedEmbedding.euclidean.integerLattice F)

@[simp]
theorem mem_intLat {F : Type*} [Field F] [NumberField F] {N : ℕ} (y : Fin N → KE F) :
    y ∈ intLat F N ↔ ∀ j, y j ∈ NumberField.mixedEmbedding.euclidean.integerLattice F := by
  simp [intLat, Submodule.mem_pi]

/-- The covolume of the integral lattice of `F` in the Euclidean mixed space. -/
theorem covolume_integerLattice {F : Type*} [Field F] [NumberField F] :
    ZLattice.covolume (NumberField.mixedEmbedding.euclidean.integerLattice F) =
      (1 / 2 : ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces F) *
        Real.sqrt |((NumberField.discr F : ℤ) : ℝ)| := by
  rw [NumberField.mixedEmbedding.euclidean.integerLattice]
  rw [ZLattice.covolume_comap (L := NumberField.mixedEmbedding.integerLattice F)
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (NumberField.mixedEmbedding.mixedSpace F)))
    (ν := (MeasureTheory.volume :
      MeasureTheory.Measure (NumberField.mixedEmbedding.euclidean.mixedSpace F)))
    (e := NumberField.mixedEmbedding.euclidean.toMixed F)
    (NumberField.mixedEmbedding.euclidean.volumePreserving_toMixed F)]
  simpa only [one_div] using NumberField.mixedEmbedding.covolume_integerLattice F

end

end Work.BW

/-! ## The coordinate model of `(KE F)^N`

The lists above live on `(Fin N → KE F)`, which carries no inner-product-space structure (the
product norm is the sup norm).  For the covolume arguments we use instead the isometric model
`EuclideanSpace ℝ (Fin N × index F)`, together with the matrix of `Phi a` in the orthonormal
basis and the integral lattice in these coordinates. -/

namespace Work.BW

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The matrix of `Phi a` in the orthonormal basis of `(KE F)^N`. -/
noncomputable def PhiMat {M N : ℕ} (a : Fin M → Fin N → F) :
    Matrix (Fin M × NumberField.mixedEmbedding.index F)
      (Fin N × NumberField.mixedEmbedding.index F) ℝ :=
  fun p q => inner ℝ (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F p.2)
    (((Phi a) (Pi.single q.1
      (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F q.2))) p.1)

/-- The `ℝ`-linear map on the coordinate Euclidean spaces corresponding to `Phi a`. -/
noncomputable def PhiE {M N : ℕ} (a : Fin M → Fin N → F) :
    EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F) :=
  Matrix.toEuclideanLin (PhiMat a)

/-- `PhiE a` as a continuous linear map.  Its underlying linear map is definitionally `PhiE a`,
so that the kernel `LinearMap.ker (PhiE a)` and the kernel appearing in the covolume
transference coincide. -/
noncomputable def PhiEL {M N : ℕ} (a : Fin M → Fin N → F) :
    EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →L[ℝ]
      EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F) :=
  { toLinearMap := PhiE a
    cont := (PhiE a).continuous_of_finiteDimensional }

/-- The integral lattice `(meK '' 𝓞 F)^N`, in the orthonormal coordinates of `(KE F)^N`. -/
noncomputable def intLatE (F : Type*) [Field F] [NumberField F] (N : ℕ) : Submodule ℤ
    (EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) :=
  Submodule.span ℤ (Set.range (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 F) =>
    WithLp.toLp 2 (fun p : Fin N × NumberField.mixedEmbedding.index F =>
      if p.1 = q.1 then ((NumberField.mixedEmbedding.stdBasis F).repr
        (NumberField.mixedEmbedding F ((NumberField.integralBasis F) q.2))) p.2
      else 0)))

end

end Work.BW

/-! ## Decidability of the real/complex place predicates

The index type `mixedEmbedding.index F = {w : InfinitePlace F // IsReal w} ⊕
({w // IsComplex w} × Fin 2)` and hence the Euclidean coordinate spaces carry `Fintype` and
`MeasureSpace` instances only through decidability of `IsReal`/`IsComplex`.  These are registered
globally here so that statements about the coordinate spaces elaborate without a local
`open scoped Classical`. -/

namespace Work.BW

noncomputable instance instDecidableIsReal {F : Type*} [Field F] [NumberField F]
    (w : NumberField.InfinitePlace F) : Decidable w.IsReal := Classical.propDecidable _

noncomputable instance instDecidableIsComplex {F : Type*} [Field F] [NumberField F]
    (w : NumberField.InfinitePlace F) : Decidable w.IsComplex := Classical.propDecidable _

end Work.BW

namespace Work.BW

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The kernel lattice of `a`: the integral lattice intersected with the kernel of `PhiE a`. -/
noncomputable def kerLatE {M N : ℕ} (a : Fin M → Fin N → F) :
    Submodule ℤ (EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) :=
  intLatE F N ⊓ ((PhiE a).ker).restrictScalars ℤ

end

end Work.BW

namespace Work.BW

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The kernel lattice, viewed as a `ℤ`-submodule of the kernel of `PhiE a`. -/
noncomputable def kerLatK {M N : ℕ} (a : Fin M → Fin N → F) : Submodule ℤ
    ↥(LinearMap.ker (PhiE a : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F))) :=
  Submodule.comap (((LinearMap.ker (PhiE a)).subtype).restrictScalars ℤ) (kerLatE a)

/-- The image lattice `PhiE a '' (𝓞 F)^N`. -/
noncomputable def imgLatE {M N : ℕ} (a : Fin M → Fin N → F) :
    Submodule ℤ (EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)) :=
  Submodule.map ((PhiE a).restrictScalars ℤ) (intLatE F N)

end

end Work.BW

namespace Work.BW

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The ambient vector of a point of the kernel lattice. -/
noncomputable def kerLatEval {M N : ℕ} (a : Fin M → Fin N → F)
    (x : ↥(kerLatK (F := F) a)) : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) :=
  ((x : ↥(LinearMap.ker (PhiE a : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)))) :
    EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F))

end

end Work.BW
