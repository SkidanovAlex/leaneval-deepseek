import Mathlib
import Submission.Work.BW.kcb_lat_defs
import Submission.Work.BW.sieg2_covolume_pi
import Submission.Work.BW.sieg2KernelDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Covolume of the coordinate lattice `kcbIdealCoord`

Let `F` be a number field and `I : Fin M → (FractionalIdeal (𝓞 F)⁰ F)ˣ` a finite family of
fractional ideals.  `Work.BW.kcbIdealCoord I` is the model of `∏ᵢ Iᵢ ⊆ (F^M)` in the Euclidean
coordinate space `EuclideanSpace ℝ (Fin M × index F)`, obtained from the product lattice
`kcbIdealProd I ⊆ (Fin M → KE F)` by transporting along the coordinate equivalence `kcbEquiv F M`.

The main result of this file computes its covolume:

  `covolume (kcbIdealCoord I) = (∏ᵢ N(Iᵢ)) · c^M`,
  `c = 2^{-r₂}·√|disc F|` being the covolume of the ring of integers (`r₂` = number of complex
  places).

The proof has three independent inputs:

* `covolume_kcbIdealE`: the covolume of a single ideal lattice `kcbIdealE J` in `KE F` is
  `N(J) · c`; this is `NumberField.mixedEmbedding.covolume_idealLattice` combined with the
  invariance of the covolume under the volume-preserving map `toMixed`.
* `sieg2_covolume_pi`: the covolume of a product of `ℤ`-lattices is the product of the covolumes
  (`Work.BW.sieg2_covolume_pi`), applied to `kcbIdealProd I`.
* `kcbEquiv_measurePreserving`: the coordinate equivalence `kcbEquiv F M` is volume preserving,
  so `ZLattice.covolume_comap` shows that passing from the product model to the coordinates does
  not change the covolume.  The measure-theoretic content is that currying
  `(ι × κ → ℝ) → (ι → κ → ℝ)` preserves the product Lebesgue measure
  (`volume_preserving_curry`) together with the fact that the standard orthonormal-basis
  equivalence and the `WithLp`-casts are measure preserving.
-/

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors

namespace Work.BW

noncomputable section

/-! ## The currying map preserves the product Lebesgue measure -/

lemma volume_map_uncurry {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasureSpace X]
    [SigmaFinite (volume : Measure X)] :
    Measure.map (Function.uncurry : (ι → κ → X) → (ι × κ → X)) volume = volume := by
  change Measure.map Function.uncurry
      (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => (volume : Measure X))))
    = Measure.pi (fun _ : ι × κ => (volume : Measure X))
  refine (Measure.pi_eq (μ := fun _ : ι × κ => (volume : Measure X)) fun s hs => ?_).symm
  rw [Measure.map_apply measurable_uncurry (MeasurableSet.pi Set.countable_univ (fun p _ => hs p))]
  rw [show Function.uncurry ⁻¹' Set.pi Set.univ s
      = Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s (i, j))) by
    ext f; simp [Function.uncurry, Set.mem_pi]]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun p : ι × κ => (volume : Measure X) (s p))).symm

lemma volume_preserving_curry {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasureSpace X]
    [SigmaFinite (volume : Measure X)] :
    MeasurePreserving (Function.curry : (ι × κ → X) → (ι → κ → X)) volume volume := by
  have h : Measure.map (Function.uncurry : (ι → κ → X) → (ι × κ → X)) volume = volume :=
    volume_map_uncurry
  refine ⟨measurable_curry, ?_⟩
  have h' : (Measure.pi (fun _ : ι × κ => (volume : Measure X)))
      = Measure.map (⇑(MeasurableEquiv.curry ι κ X).symm)
          (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => (volume : Measure X)))) := by
    rw [MeasurableEquiv.coe_curry_symm]
    exact h.symm
  exact (MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq (MeasurableEquiv.curry ι κ X)).mpr h'

/-! ## Discreteness of a product of lattices -/

/-- The product `Submodule.pi Set.univ L` of discrete `ℤ`-submodules of `E` is discrete in the
product topology on `ι → E`. -/
lemma discreteTopology_submodulePi {E : Type*} [NormedAddCommGroup E] {ι : Type*} [Fintype ι]
    (L : ι → Submodule ℤ E) [∀ i, DiscreteTopology ↥(L i)] :
    DiscreteTopology ↥(Submodule.pi Set.univ L) := by
  have hφ : Continuous
      (fun x : ↥(Submodule.pi Set.univ L) => fun i => (⟨x.1 i, x.2 i trivial⟩ : ↥(L i))) :=
    continuous_pi fun i =>
      Continuous.subtype_mk ((continuous_apply i).comp continuous_subtype_val) _
  have hφi : Function.Injective
      (fun x : ↥(Submodule.pi Set.univ L) => fun i => (⟨x.1 i, x.2 i trivial⟩ : ↥(L i))) := by
    intro a b h
    exact Subtype.ext (funext fun i => congrArg (fun f => (f i : E)) h)
  exact DiscreteTopology.of_continuous_injective hφ hφi

/-! ## `kcbEquiv` is volume preserving -/

lemma kcbEquiv_measurePreserving {F : Type*} [Field F] [NumberField F] (N : ℕ) :
    MeasurePreserving (kcbEquiv F N) volume volume := by
  have hcurry : MeasurePreserving
      (Function.curry : (Fin N × NumberField.mixedEmbedding.index F → ℝ) →
        (Fin N → NumberField.mixedEmbedding.index F → ℝ)) volume volume :=
    volume_preserving_curry
  have h1 : MeasurePreserving (WithLp.ofLp : kcbE F N →
      (Fin N × NumberField.mixedEmbedding.index F → ℝ)) volume volume :=
    PiLp.volume_preserving_ofLp _
  let H : (NumberField.mixedEmbedding.index F → ℝ) → KE F :=
    fun b => (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F).repr.symm
      (WithLp.toLp 2 b)
  have hH : MeasurePreserving H volume volume :=
    (OrthonormalBasis.measurePreserving_repr_symm
      (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F)).comp
    (PiLp.volume_preserving_toLp (NumberField.mixedEmbedding.index F))
  have hsf : ∀ _ : Fin N, SigmaFinite
      (Measure.map (fun b : NumberField.mixedEmbedding.index F → ℝ => H b)
        (volume : Measure (NumberField.mixedEmbedding.index F → ℝ))) :=
    fun _ => by
      rw [show Measure.map (fun b : NumberField.mixedEmbedding.index F → ℝ => H b)
          (volume : Measure (NumberField.mixedEmbedding.index F → ℝ)) = volume from hH.map_eq]
      infer_instance
  have h3 : MeasurePreserving (fun (g : Fin N → NumberField.mixedEmbedding.index F → ℝ) =>
      fun i : Fin N => H (g i)) volume volume := by
    refine ⟨?_, ?_⟩
    · exact measurable_pi_iff.mpr (fun i => hH.measurable.comp (measurable_pi_apply i))
    · show Measure.map
          (fun (g : Fin N → NumberField.mixedEmbedding.index F → ℝ) (i : Fin N) => H (g i))
          (Measure.pi (fun _ : Fin N =>
            (volume : Measure (NumberField.mixedEmbedding.index F → ℝ))))
        = Measure.pi (fun _ : Fin N => (volume : Measure (KE F)))
      have key := Measure.pi_map_pi
        (μ := fun _ : Fin N => (volume : Measure (NumberField.mixedEmbedding.index F → ℝ)))
        (Y := fun _ : Fin N => KE F)
        (f := fun (_ : Fin N) (b : NumberField.mixedEmbedding.index F → ℝ) => H b)
        (hμ := hsf)
        (fun _ => hH.aemeasurable)
      rw [key]
      exact congrArg Measure.pi (funext fun _ => hH.map_eq)
  have hcomp := h3.comp (hcurry.comp h1)
  have hfun : ⇑(kcbEquiv F N) =
      (fun (g : Fin N → NumberField.mixedEmbedding.index F → ℝ) =>
        fun i : Fin N => H (g i)) ∘
      (Function.curry : (Fin N × NumberField.mixedEmbedding.index F → ℝ) →
        (Fin N → NumberField.mixedEmbedding.index F → ℝ)) ∘ WithLp.ofLp := by
    funext x
    simp only [Function.comp_apply, kcbEquiv, LinearEquiv.trans_apply]
    rfl
  rw [hfun]
  exact hcomp

/-! ## Covolume of a single ideal lattice -/

lemma covolume_kcbIdealE {F : Type*} [Field F] [NumberField F]
    (J : (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)ˣ) :
    ZLattice.covolume (kcbIdealE (F := F) J) MeasureTheory.volume =
      ((FractionalIdeal.absNorm (J : FractionalIdeal
          (nonZeroDivisors (NumberField.RingOfIntegers F)) F) : ℚ) : ℝ) *
        ((1 / 2 : ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces F) *
          Real.sqrt |((NumberField.discr F : ℤ) : ℝ)|) := by
  rw [kcbIdealE, ZLattice.covolume_comap
      (L := NumberField.mixedEmbedding.idealLattice F J)
      (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
      (e := NumberField.mixedEmbedding.euclidean.toMixed F)
      (NumberField.mixedEmbedding.euclidean.volumePreserving_toMixed F)]
  rw [NumberField.mixedEmbedding.covolume_idealLattice]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  ring

/-! ## The main theorem -/

theorem sic_covolume_kcbIdealCoord {F : Type*} [Field F] [NumberField F] {M : ℕ}
    (I : Fin M → (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)ˣ) :
    ZLattice.covolume (Work.BW.kcbIdealCoord (F := F) I) MeasureTheory.volume =
      (∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) : ℚ) : ℝ)) *
        ((1 / 2 : ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces F) *
          Real.sqrt |((NumberField.discr F : ℤ) : ℝ)|) ^ M := by
  haveI hEdisc : ∀ i : Fin M, DiscreteTopology ↥(kcbIdealE (F := F) (I i)) := fun i =>
    ZLattice.comap_discreteTopology ℝ (NumberField.mixedEmbedding.idealLattice F (I i))
      (NumberField.mixedEmbedding.euclidean.toMixed F).continuous
      (NumberField.mixedEmbedding.euclidean.toMixed F).injective
  haveI hEzl : ∀ i : Fin M, IsZLattice ℝ (kcbIdealE (F := F) (I i)) := fun i =>
    inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ
      (NumberField.mixedEmbedding.idealLattice F (I i))
      (NumberField.mixedEmbedding.euclidean.toMixed F).toLinearMap))
  haveI hPdisc : DiscreteTopology
      ↥(Submodule.pi Set.univ (fun i => kcbIdealE (F := F) (I i))) :=
    discreteTopology_submodulePi (fun i => kcbIdealE (F := F) (I i))
  haveI hPzl : IsZLattice ℝ
      (Submodule.pi Set.univ (fun i => kcbIdealE (F := F) (I i))) :=
    ⟨pi_span_top (fun i => kcbIdealE (F := F) (I i)) (fun i => (hEzl i).span_top)⟩
  haveI hPdisc' : DiscreteTopology ↥(kcbIdealProd (F := F) I) := hPdisc
  haveI hPzl' : IsZLattice ℝ (kcbIdealProd (F := F) I) := hPzl
  haveI hBor : BorelSpace (Fin M → KE F) := inferInstance
  haveI hHaar : Measure.IsAddHaarMeasure (volume : Measure (Fin M → KE F)) := by
    change Measure.IsAddHaarMeasure
      (Measure.pi (fun _ : Fin M => (volume : Measure (KE F))))
    exact Measure.pi.isAddHaarMeasure _
  have hmp : MeasurePreserving (kcbEquiv F M) volume volume := kcbEquiv_measurePreserving M
  have hstep1 : ZLattice.covolume (kcbIdealCoord (F := F) I) volume
      = ZLattice.covolume (kcbIdealProd (F := F) I) volume := by
    rw [kcbIdealCoord]
    exact ZLattice.covolume_comap (L := kcbIdealProd (F := F) I) (μ := volume) (ν := volume)
      (e := (kcbEquiv F M).toContinuousLinearEquiv) hmp
  have hstep2 : ZLattice.covolume (kcbIdealProd (F := F) I) volume
      = ∏ i, ZLattice.covolume (kcbIdealE (F := F) (I i)) volume :=
    sieg2_covolume_pi (E := KE F) (fun i => kcbIdealE (F := F) (I i))
  rw [hstep1, hstep2]
  rw [Finset.prod_congr rfl (fun i _ => covolume_kcbIdealE (F := F) (I i))]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end

end Work.BW
