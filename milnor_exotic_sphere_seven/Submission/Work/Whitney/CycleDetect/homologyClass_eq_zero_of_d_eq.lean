import Mathlib
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.relCochainDual
import Submission.Work.Cohomology.relCupH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A cycle that is a boundary has vanishing class

For a `ℕ`-indexed cochain complex `K` of `R`-modules, a cycle `z ∈ Zⁿ(K)` whose underlying element
is the differential of a degree `n-1` cochain has zero class in `Hⁿ(K)`: this is the elementary
fact that `homologyπ` vanishes on the image of the incoming differential (`toCycles`).

The corollary is the form in which the fact is used for the relative complex `C^*(X,A)`: a relative
cocycle whose class in `H^n(X,A)` is nonzero is **not** a coboundary.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

-- The module structure on a submodule of a `ℤ`-module is the one induced from the ambient module,
-- rather than `AddCommGroup.toIntModule`: this matches `Submission/Work/Cohomology/uctDefs.lean`.
attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory CategoryTheory.Limits

namespace Work.Whitney.CycleDetect

noncomputable section

/-- **A cycle that is a boundary has vanishing class.** -/
theorem homologyClass_eq_zero_of_d_eq {R : Type} [CommRing R] (K : CochainComplex (ModuleCat R) ℕ)
    [∀ i, HomologicalComplex.HasHomology K i] {n : ℕ} (z : K.cycles n) (y : K.X (n - 1))
    (h : (K.iCycles n).hom z = (K.d (n - 1) n).hom y) : K.homologyπ n z = 0 := by
  have h1 : z = K.toCycles (n - 1) n y := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    rw [h]
    have h3 := congrArg (fun (g : K.X (n - 1) ⟶ K.X n) => g.hom y)
      (HomologicalComplex.toCycles_i K (n - 1) n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h3.symm
  rw [h1]
  have h2 := congrArg (fun (g : K.X (n - 1) ⟶ K.homology n) => g.hom y)
    (HomologicalComplex.toCycles_comp_homologyπ K (n - 1) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h2

/-- **A relative cocycle of nonzero class is not a coboundary.** -/
theorem notMem_range_relDiffLM_of_relClassOf_ne_zero (X : TopCat) (A : Set X) (m : ℕ)
    (a : ↥(Work.Cohomology.relKern ℤ X A (m + 1)))
    (ha : Work.Cohomology.relDiffLM ℤ X A (m + 1) a = 0)
    (h : Work.Cohomology.relClassOf ℤ X A a ha ≠ 0) :
    ¬ ∃ v : ↥(Work.Cohomology.relKern ℤ X A m),
      Work.Cohomology.relDiffLM ℤ X A m v = a := by
  rintro ⟨v, hv⟩
  have ha' : ((Work.Cohomology.relComplex ℤ X A).d (m + 1) (m + 1 + 1)).hom a = 0 := by
    rw [Work.Cohomology.relComplex_d]
    exact ha
  have hIm : (Work.Cohomology.relComplex ℤ X A).homologyπ (m + 1)
      (Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex ℤ X A) (n := m + 1) a ha') = 0 := by
    refine homologyClass_eq_zero_of_d_eq (K := Work.Cohomology.relComplex ℤ X A) (n := m + 1)
      (Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex ℤ X A) (n := m + 1) a ha') v ?_
    rw [Work.Cohomology.iCycles_cocycleOfK]
    show a = ((Work.Cohomology.relComplex ℤ X A).d m (m + 1)).hom v
    rw [Work.Cohomology.relComplex_d]
    exact hv.symm
  rw [← Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK ℤ X A a ha ha'] at hIm
  exact h hIm

end

end Work.Whitney.CycleDetect
