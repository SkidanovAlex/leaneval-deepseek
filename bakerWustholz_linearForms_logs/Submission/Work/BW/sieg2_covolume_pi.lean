import Mathlib
import Submission.Work.BW.pi_span_top
import Submission.Work.BW.pi_existsUnique_vadd_mem_fundamentalDomain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Covolume of a product of `ℤ`-lattices

Let `L i` (`i : ι`, `ι` finite) be full `ℤ`-lattices in a finite-dimensional real inner product
space `E`.  Then the product lattice `∏ i, L i ⊆ ι → E` (Mathlib's `Submodule.pi Set.univ L`) is
again a full `ℤ`-lattice, and its covolume is the product of the covolumes of the factors:

  `covolume (∏ i, L i) = ∏ i, covolume (L i)`.

This is the `ι`-ary form of the multiplicativity of the covolume for split products (the binary
case is `Work.BW.covolume_prod`).

Proof outline.  For each `i` choose a `ℤ`-basis `b i` of `L i` and let
`F i := ZSpan.fundamentalDomain ((b i).ofZLatticeBasis ℝ) ⊆ E` be the associated fundamental
domain, so that `covolume (L i) = volume.real (F i)`.

* Each point `x : ι → E` has a *unique* representative modulo `L i` inside `F i`; hence
  `F := ∏ i, F i` is an additive fundamental domain of `∏ i, L i` in `ι → E`
  (`Work.BW.pi_existsUnique_vadd_mem_fundamentalDomain` and
  `MeasureTheory.IsAddFundamentalDomain.mk'`).  The product lattice spans `ι → E` over `ℝ`
  (`Work.BW.pi_span_top`), so `IsZLattice` applies and the covolume is the volume of `F`.
* The volume on `ι → E` *is* the product measure: `MeasureTheory.volume_pi` holds by `rfl`.  So
  `volume.real (∏ i, F i) = ∏ i, volume.real (F i)` by `Measure.pi_pi` and
  `ENNReal.toReal_prod`.

Note that the `volumes` are not finite, so one cannot use a finiteness argument: the identity
`Measure.real (pi univ F) = ∏ i, Measure.real (F i)` is proved by `ENNReal.toReal_prod`, which
needs no finiteness hypothesis.
-/

set_option linter.style.haveILetI false

open MeasureTheory

namespace Work.BW

theorem sieg2_covolume_pi {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] (L : ι → Submodule ℤ E)
    [∀ i, DiscreteTopology (L i)] [∀ i, IsZLattice ℝ (L i)]
    [DiscreteTopology ↥(Submodule.pi Set.univ L)] :
    ZLattice.covolume (Submodule.pi Set.univ L) = ∏ i, ZLattice.covolume (L i) := by
  classical
  -- The product lattice spans the whole space over `ℝ`, hence is a full `ℤ`-lattice.
  haveI : IsZLattice ℝ (Submodule.pi Set.univ L) :=
    ⟨pi_span_top L fun i => (inferInstance : IsZLattice ℝ (L i)).span_top⟩
  -- A `ℤ`-basis of each factor and the attached `ZSpan` fundamental domain.
  let b : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex ℤ (L i)) ℤ (L i) :=
    fun i => Module.Free.chooseBasis ℤ (L i)
  let F : ι → Set E := fun i => ZSpan.fundamentalDomain ((b i).ofZLatticeBasis ℝ)
  have hF : ∀ i, IsAddFundamentalDomain ↥(L i) (F i) (volume : Measure E) :=
    fun i => ZLattice.isAddFundamentalDomain (b i) volume
  -- The product of the fundamental domains is a fundamental domain of the product lattice.
  have huniq : ∀ x : ι → E, ∃! g : ↥(Submodule.pi Set.univ L), g +ᵥ x ∈ Set.pi Set.univ F :=
    fun x => pi_existsUnique_vadd_mem_fundamentalDomain L b x
  have hmeas : MeasurableSet (Set.pi Set.univ F) :=
    MeasurableSet.pi Set.countable_univ fun i _ =>
      ZSpan.fundamentalDomain_measurableSet ((b i).ofZLatticeBasis ℝ)
  have hprod : IsAddFundamentalDomain ↥(Submodule.pi Set.univ L) (Set.pi Set.univ F)
      (volume : Measure (ι → E)) :=
    IsAddFundamentalDomain.mk' hmeas.nullMeasurableSet huniq
  -- The covolume is the volume of any fundamental domain.
  have hcov : ZLattice.covolume (Submodule.pi Set.univ L)
      = (volume : Measure (ι → E)).real (Set.pi Set.univ F) :=
    ZLattice.covolume_eq_measure_fundamentalDomain (Submodule.pi Set.univ L) volume hprod
  -- `volume` on `ι → E` is the product measure, and `real` commutes with the product.
  have hreal : (volume : Measure (ι → E)).real (Set.pi Set.univ F)
      = ∏ i, (volume : Measure E).real (F i) := by
    rw [Measure.real, volume_pi, Measure.pi_pi, ENNReal.toReal_prod]
    simp [Measure.real]
  have hfac : ∀ i, (volume : Measure E).real (F i) = ZLattice.covolume (L i) := fun i =>
    (ZLattice.covolume_eq_measure_fundamentalDomain (L i) volume (hF i)).symm
  rw [hcov, hreal]
  exact Finset.prod_congr rfl fun i _ => hfac i

end Work.BW
