import Mathlib
import Submission.Work.BW.sieg2KernelDefs
import Submission.Work.BW.sieg2_intLatE_basis
import Submission.Work.BW.covolume_sqrt_gram_det_arb
import Submission.Work.BW.sieg2_gram_det_intLatEBasis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The covolume of `(𝓞 F)^N` in the Euclidean coordinate model

`Work.BW.intLatE F N` is the integral lattice `(𝓞 F)^N` inside the Euclidean coordinate model
`EuclideanSpace ℝ (Fin N × index F)` of `(KE F)^N`, defined in
`Submission.Work.BW.sieg2KernelDefs` as the `ℤ`-span of the vectors obtained by placing the mixed
coordinates of an integral basis in the `N` slots.

Here we compute its covolume:

  `covolume (intLatE F N) = ((1/2)^{r₂} · √|disc F|)^N`,  `r₂ = nrComplexPlaces F`.

Equivalently, the covolume of `(𝓞 F)^N` is the `N`-th power of the covolume of `𝓞 F` itself, whose
value `(1/2)^{r₂} √|disc F|` is Minkowski's theorem (as formalized in Mathlib as
`NumberField.mixedEmbedding.covolume_integerLattice`, restated for the Euclidean model of the
mixed space by `Work.BW.covolume_integerLattice`).  This is the reason the answer is a pure
`N`-th power: the covolume of a product of `N` copies of a lattice is the `N`-th power of its
covolume.

The argument has three structural inputs, and one genuine computation (the one-factor value),
which is carried out here.

* `Work.BW.covolume_sqrt_gram_det_arb`: the covolume of the `ℤ`-span of an `ℝ`-basis indexed by an
  arbitrary finite type is `√|det Gram|`.
* `Work.BW.sieg2_gram_det_intLatEBasis`: in the product basis `intLatEBasis F N` the Gram matrix
  is block diagonal with `N` identical blocks `gram (intLatBasis F)`, hence
  `det Gram (intLatEBasis F N) = (det Gram (intLatBasis F))^N`; taking square roots turns the
  `N` blocks into an `N`-th power.
* The one-factor value `√|det Gram (intLatBasis F)| = (1/2)^{r₂} √|disc F|`: the vectors of
  `intLatBasis F` are the orthonormal coordinates of the images `meK (integralBasis F i)` of the
  integral basis (`repr_meK_integralBasis`), so their `ℤ`-span is the image of the Euclidean
  integer lattice of `F` under the orthonormal-coordinate isomorphism (`coordEquiv`); covolumes
  are preserved by that isomorphism (`ZLattice.covolume_comap`), and the covolume of the Euclidean
  integer lattice of `F` is Minkowski's value (`Work.BW.covolume_integerLattice`).

Finally `intLatE F N` is the `ℤ`-span of the `ℝ`-basis `intLatEBasis F N`, so it is a discrete
`ℤ`-lattice and the covolume formula applies (this is not needed for the statement, in which the
covolume is the measure-theoretic one, but it identifies the two).
-/

open NumberField MeasureTheory
open scoped Classical

namespace Work.BW.TV

noncomputable section

/-- `intLatE F N` is the `ℤ`-span of the `ℝ`-basis `intLatEBasis F N`. -/
theorem intLatE_eq_span_intLatEBasis {F : Type*} [Field F] [NumberField F] (N : ℕ) :
    Submodule.span ℤ (Set.range ⇑(Work.BW.intLatEBasis F N)) = Work.BW.intLatE F N := by
  have hb : ⇑(Work.BW.intLatEBasis F N) = (fun q : Fin N ×
      Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F) =>
      WithLp.toLp 2 (fun p : Fin N × NumberField.mixedEmbedding.index F =>
        if p.1 = q.1 then ((NumberField.mixedEmbedding.stdBasis F).repr
          (NumberField.mixedEmbedding F ((NumberField.integralBasis F) q.2))) p.2 else 0)) :=
    funext (Work.BW.intLatEBasis_apply F N)
  rw [hb]
  rfl

/-- `intLatE F N` is discrete: it is the `ℤ`-span of an `ℝ`-basis. -/
theorem discreteTopology_intLatE {F : Type*} [Field F] [NumberField F] (N : ℕ) :
    DiscreteTopology ↥(Work.BW.intLatE F N) := by
  rw [← intLatE_eq_span_intLatEBasis (F := F) N]
  infer_instance

/-- The orthonormal coordinates of `meK` of the integral basis are the vectors `intLatBasis F`. -/
theorem repr_meK_integralBasis {F : Type*} [Field F] [NumberField F]
    (i : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F)) :
    (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F).repr
        (Work.BW.meK ((NumberField.integralBasis F) i)) = Work.BW.intLatBasis F i := by
  rw [Work.BW.intLatBasis_apply, WithLp.ext_iff]
  funext p
  rw [← OrthonormalBasis.coe_toBasis_repr_apply,
    ← NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis_map_eq F]
  simp [Work.BW.meK, Module.Basis.map]

/-- `√|x ^ n| = (√|x|) ^ n`. -/
theorem sqrt_abs_pow (x : ℝ) (n : ℕ) :
    Real.sqrt |x ^ n| = (Real.sqrt |x|) ^ n := by
  have hx : 0 ≤ |x| := abs_nonneg x
  rw [abs_pow]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n) |x|, ih, pow_succ]

/-- The orthonormal-coordinate model of the Euclidean mixed space of `F`. -/
noncomputable def coordEquiv (F : Type*) [Field F] [NumberField F] :
    EuclideanSpace ℝ (NumberField.mixedEmbedding.index F) ≃L[ℝ]
      NumberField.mixedEmbedding.euclidean.mixedSpace F :=
  ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F).repr.symm).toContinuousLinearEquiv

/-- The Euclidean integer lattice of `F` is the image, under `toMixed.symm`, of the `ℤ`-span of
the mixed images of the integral basis. -/
theorem euclidean_integerLattice_eq_map (F : Type*) [Field F] [NumberField F] :
    NumberField.mixedEmbedding.euclidean.integerLattice F
      = Submodule.map
          (((NumberField.mixedEmbedding.euclidean.toMixed F).symm.toLinearMap).restrictScalars ℤ)
          (Submodule.span ℤ (Set.range ⇑(NumberField.mixedEmbedding.latticeBasis F))) := by
  rw [NumberField.mixedEmbedding.euclidean.integerLattice,
    ← NumberField.mixedEmbedding.span_latticeBasis]
  change Submodule.comap
      (((NumberField.mixedEmbedding.euclidean.toMixed F).toLinearMap).restrictScalars ℤ)
      (Submodule.span ℤ (Set.range ⇑(NumberField.mixedEmbedding.latticeBasis F)))
    = Submodule.map
      (((NumberField.mixedEmbedding.euclidean.toMixed F).symm.toLinearMap).restrictScalars ℤ)
      (Submodule.span ℤ (Set.range ⇑(NumberField.mixedEmbedding.latticeBasis F)))
  ext x
  rw [Submodule.mem_comap, Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨(NumberField.mixedEmbedding.euclidean.toMixed F) x, hx, by simp⟩
  · rintro ⟨y, hy, hyx⟩
    rw [← hyx]
    simpa using hy

/-- The `ℤ`-span of the vectors `intLatBasis F` is the image of the Euclidean integer lattice of
`F` under the inverse of the orthonormal-coordinate isomorphism `coordEquiv`. -/
theorem span_intLatBasis_eq_map_coordEquiv_symm (F : Type*) [Field F] [NumberField F] :
    Submodule.map (((coordEquiv F).symm.toLinearMap).restrictScalars ℤ)
        (NumberField.mixedEmbedding.euclidean.integerLattice F)
      = Submodule.span ℤ (Set.range ⇑(Work.BW.intLatBasis F)) := by
  have hleft : Submodule.span ℤ (Set.range ⇑(Work.BW.intLatBasis F))
      = Submodule.span ℤ (Set.range (fun i : Module.Free.ChooseBasisIndex ℤ
            (NumberField.RingOfIntegers F) =>
          (coordEquiv F).symm ((NumberField.mixedEmbedding.euclidean.toMixed F).symm
            ((NumberField.mixedEmbedding.latticeBasis F) i)))) := by
    refine congrArg (Submodule.span ℤ) (congrArg Set.range (funext fun i => ?_))
    rw [← repr_meK_integralBasis (F := F) i, Work.BW.meK,
      NumberField.mixedEmbedding.latticeBasis_apply]
    rfl
  have hR : Submodule.map (((coordEquiv F).symm.toLinearMap).restrictScalars ℤ)
        (NumberField.mixedEmbedding.euclidean.integerLattice F)
      = Submodule.span ℤ (Set.range (fun i : Module.Free.ChooseBasisIndex ℤ
            (NumberField.RingOfIntegers F) =>
          (coordEquiv F).symm ((NumberField.mixedEmbedding.euclidean.toMixed F).symm
            ((NumberField.mixedEmbedding.latticeBasis F) i)))) := by
    rw [euclidean_integerLattice_eq_map F, ← Submodule.map_comp, Submodule.map_span,
      ← Set.range_comp]
    rfl
  exact hR.trans hleft.symm

/-- The `ℤ`-span of the vectors `intLatBasis F` is the pullback of the Euclidean integer lattice
of `F` along the orthonormal-coordinate isomorphism `coordEquiv`. -/
theorem comap_coordEquiv_integerLattice (F : Type*) [Field F] [NumberField F] :
    ZLattice.comap ℝ (NumberField.mixedEmbedding.euclidean.integerLattice F)
        (coordEquiv F).toLinearMap
      = Submodule.span ℤ (Set.range ⇑(Work.BW.intLatBasis F)) := by
  rw [← span_intLatBasis_eq_map_coordEquiv_symm F]
  change (NumberField.mixedEmbedding.euclidean.integerLattice F).comap
      (((coordEquiv F).toLinearMap).restrictScalars ℤ)
    = Submodule.map (((coordEquiv F).symm.toLinearMap).restrictScalars ℤ)
        (NumberField.mixedEmbedding.euclidean.integerLattice F)
  ext x
  rw [Submodule.mem_comap, Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨(coordEquiv F) x, hx, by simp⟩
  · rintro ⟨y, hy, hyx⟩
    rw [← hyx]
    simpa using hy

/-- **The one-factor value.**  The covolume of the `ℤ`-span of `intLatBasis F` — the lattice
`𝓞 F` in the orthonormal coordinates of the mixed space — is `(1/2)^{r₂} √|disc F|`. -/
theorem sqrt_gram_det_intLatBasis {F : Type*} [Field F] [NumberField F] :
    Real.sqrt |(Matrix.gram ℝ (⇑(Work.BW.intLatBasis F))).det| =
      (1 / 2 : ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces F) *
        Real.sqrt |((NumberField.discr F : ℤ) : ℝ)| := by
  rw [← Work.BW.covolume_sqrt_gram_det_arb (Work.BW.intLatBasis F)]
  rw [← comap_coordEquiv_integerLattice F]
  rw [ZLattice.covolume_comap
    (L := NumberField.mixedEmbedding.euclidean.integerLattice F)
    (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
    (e := coordEquiv F) (OrthonormalBasis.measurePreserving_repr_symm _)]
  exact Work.BW.covolume_integerLattice

/-- **The covolume of the integral lattice `(𝓞 F)^N` in the Euclidean coordinate model.** -/
theorem covolume_intLatE {F : Type*} [Field F] [NumberField F] (N : ℕ) :
    ZLattice.covolume (Work.BW.intLatE F N) (μ := MeasureTheory.volume) =
      ((1 / 2 : ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces F) *
        Real.sqrt |((NumberField.discr F : ℤ) : ℝ)|) ^ N := by
  have h1 : ZLattice.covolume (Work.BW.intLatE F N) MeasureTheory.volume
      = Real.sqrt |(Matrix.gram ℝ (⇑(Work.BW.intLatEBasis F N))).det| := by
    rw [← intLatE_eq_span_intLatEBasis (F := F) N]
    exact Work.BW.covolume_sqrt_gram_det_arb (Work.BW.intLatEBasis F N)
  have h2 : Real.sqrt |(Matrix.gram ℝ (⇑(Work.BW.intLatEBasis F N))).det|
      = (Real.sqrt |(Matrix.gram ℝ (⇑(Work.BW.intLatBasis F))).det|) ^ N := by
    rw [Work.BW.sieg2_gram_det_intLatEBasis (F := F) N, sqrt_abs_pow]
  rw [h1, h2, sqrt_gram_det_intLatBasis (F := F)]

end

end Work.BW.TV
