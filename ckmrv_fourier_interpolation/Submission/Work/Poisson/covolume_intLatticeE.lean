import Mathlib
import Submission.Work.Modular.Poisson.Std

/-!
# Covolume of the standard integer lattice in `EuclideanSpace ℝ ι`

`Work.Modular.intLatticeE ι` is the lattice `ℤ^ι` inside `EuclideanSpace ℝ ι`, i.e. the lattice
of vectors all of whose coordinates are integers. The main result of this file,
`Work.Poisson.covolume_intLatticeE`, computes its covolume as `1`.

The argument is a transport along the measure preserving linear isometry
`EuclideanSpace.equiv ι ℝ : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ)`: it identifies `intLatticeE ι`
with the image of the standard lattice `Work.Modular.stdLattice ι = ℤ^ι ⊆ (ι → ℝ)`, whose
covolume is `1` because the half-open unit cube `[0,1)^ι` is a fundamental domain of volume `1`
(`ZSpan.isAddFundamentalDomain`).

Along the way we register the discreteness and lattice instances for `Work.Modular.stdLattice ι`
(the standard lattice is *definitionally* `Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))`, a
form for which Mathlib's instances apply, but instance search does not unfold the definition).
-/

noncomputable section

open MeasureTheory

namespace Work.Poisson

instance instDiscreteTopologyStdLattice (ι : Type*) [Fintype ι] :
    DiscreteTopology (Work.Modular.stdLattice ι) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))))

instance instIsZLatticeStdLattice (ι : Type*) [Fintype ι] :
    IsZLattice ℝ (Work.Modular.stdLattice ι) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))))

/-- The map `EuclideanSpace ℝ ι → (ι → ℝ)` forgetting the `L²`-structure is measure preserving
for the Lebesgue measure on both sides. -/
theorem measurePreserving_euclideanSpaceEquiv (ι : Type*) [Fintype ι] :
    MeasurePreserving (EuclideanSpace.equiv ι ℝ) volume volume :=
  PiLp.volume_preserving_ofLp ι

/-- **The covolume of `ℤ^ι ⊆ EuclideanSpace ℝ ι` is one.** -/
theorem covolume_intLatticeE {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ZLattice.covolume (Work.Modular.intLatticeE ι) MeasureTheory.volume = 1 := by
  have h₁ : ZLattice.covolume (Work.Modular.intLatticeE ι) volume
      = ZLattice.covolume (Work.Modular.stdLattice ι) volume :=
    ZLattice.covolume_comap (Work.Modular.stdLattice ι) volume volume
      (measurePreserving_euclideanSpaceEquiv ι)
  have hfund : IsAddFundamentalDomain (Work.Modular.stdLattice ι)
      (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) volume :=
    ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) volume
  rw [h₁,
    ZLattice.covolume_eq_measure_fundamentalDomain (Work.Modular.stdLattice ι) volume hfund,
    ZSpan.volume_real_fundamentalDomain (Pi.basisFun ℝ ι)]
  have hmat : (Matrix.of ⇑(Pi.basisFun ℝ ι)) = (1 : Matrix ι ι ℝ) := by
    ext i j; simp [Pi.basisFun_apply, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [hmat, Matrix.det_one, abs_one]

end Work.Poisson
