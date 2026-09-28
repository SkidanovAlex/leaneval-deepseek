import Mathlib
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.AlexanderWhitney
import Submission.Work.Cohomology.relCapHHom

/-!
# The universal coefficient theorem over `ℚ`: the rational Kronecker pairing is non-degenerate

`Work.Cohomology.kronH ℚ X n : H^n(X;ℚ) →ₗ[ℚ] (H_n(X;ℚ) →ₗ[ℚ] ℚ)` is the Kronecker pairing, fixed
by the computation rule `Work.Cohomology.kronH_apply` (on the class of a cocycle and the class of a
cycle it is the evaluation `α z`).

Over a *field* the dualisation `Hom(-,ℚ)` is exact, so
`H^n(X;ℚ) ≅ Hom_ℚ(H_n(X;ℚ),ℚ)` and the pairing is the evaluation pairing, which is
non-degenerate in its second variable.  This file proves that statement for an arbitrary simplicial
set (no finiteness hypotheses, in contrast with the `ℤ`-coefficient statement
`Work.Cohomology.kronH_kernel_eq_torsion`, whose radical is the torsion subgroup and which needs
finite generation).

The proof is direct and avoids the universal coefficient theorem: given `z ≠ 0` in `H_n(X;ℚ)`,
lift it to a cycle `c`; its underlying chain is not a boundary
(`Work.Cohomology.homologyπ_eq_zero_of_iCycles_eq_d`), so there is a `ℚ`-linear functional `w` on
`C_n(X;ℚ)` vanishing on the boundaries with `w (iCycles c) ≠ 0` (quotient + a coordinate
functional).  Such a `w` is a cocycle (`cochainDiff = w ∘ d`), and its class pairs with `z` to
`w (iCycles c) ≠ 0`.

This is the input that makes the "Detection" step of the reduction
`Detection + KerPhiZero ⟹ BoundaryMaximalIsotropic` available *over ℚ coefficients*, with no
finiteness hypothesis (see `Submission/Work/ThomBordism/STATUS_boundarySigma.md`, §2b).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology
open scoped TensorProduct

namespace Work.ThomBordism

noncomputable section

/-- **A nonzero vector of a `ℚ`-vector space is detected by a linear functional.** -/
theorem exists_linearMap_ne_zero_of_ne_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : V) (hv : v ≠ 0) : ∃ φ : V →ₗ[ℚ] ℚ, φ v ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, (Module.Free.chooseBasis ℚ V).repr v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv ((Module.Free.chooseBasis ℚ V).repr.injective (Finsupp.ext (by simpa using h)))
  refine ⟨(Finsupp.lapply i).comp ((Module.Free.chooseBasis ℚ V).repr : V →ₗ[ℚ] _), ?_⟩
  rw [LinearMap.comp_apply, Finsupp.lapply_apply]
  exact hi

/-- **A linear functional vanishing on a submodule, nonzero on an element outside it.** -/
theorem exists_linearMap_eq_zero_on_of_not_mem {V : Type*} [AddCommGroup V] [Module ℚ V]
    (W : Submodule ℚ V) (v : V) (hv : v ∉ W) :
    ∃ φ : V →ₗ[ℚ] ℚ, (∀ w ∈ W, φ w = 0) ∧ φ v ≠ 0 := by
  have hne : (Submodule.mkQ W) v ≠ 0 := by
    rw [Submodule.mkQ_apply]
    exact fun h => hv ((Submodule.Quotient.mk_eq_zero W).mp h)
  obtain ⟨φ, hφ⟩ := exists_linearMap_ne_zero_of_ne_zero ((Submodule.mkQ W) v) hne
  refine ⟨φ.comp (Submodule.mkQ W), ?_, ?_⟩
  · intro w hw
    rw [LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero W).mpr hw, map_zero]
  · simpa [LinearMap.comp_apply] using hφ

/-- **The universal coefficient theorem over `ℚ`** (second-variable non-degeneracy of the
Kronecker pairing), for an arbitrary simplicial set. -/
theorem detectionOfSSetRat (X : SSet) (n : ℕ) :
    ∀ z : (Work.Cohomology.chainC ℚ X).homology n,
      (∀ u : (Work.Cohomology.cochainC ℚ X).homology n,
        (Work.Cohomology.kronH ℚ X n) u z = 0) → z = 0 := by
  intro z hz
  by_contra hz0
  -- lift `z` to a cycle
  obtain ⟨c, hc⟩ : ∃ c : (Work.Cohomology.chainC ℚ X).cycles n,
      ((Work.Cohomology.chainC ℚ X).homologyπ n).hom c = z :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance z
  -- the underlying chain of `c` is not a boundary
  have hnotbd : ((Work.Cohomology.chainC ℚ X).iCycles n).hom c ∉
      LinearMap.range ((Work.Cohomology.chainC ℚ X).d (n + 1) n).hom := by
    rintro ⟨y, hy⟩
    refine hz0 ?_
    rw [← hc]
    exact Work.Cohomology.homologyπ_eq_zero_of_iCycles_eq_d ℚ _ n c y hy.symm
  -- a functional vanishing on the boundaries, nonzero on the cycle
  obtain ⟨w, hw0, hwv⟩ := exists_linearMap_eq_zero_on_of_not_mem
    (LinearMap.range ((Work.Cohomology.chainC ℚ X).d (n + 1) n).hom)
    (((Work.Cohomology.chainC ℚ X).iCycles n).hom c) hnotbd
  -- it is a cocycle
  have hw : Work.Cohomology.cochainDiff ℚ X w = 0 := by
    apply LinearMap.ext
    intro x
    exact hw0 _ ⟨x, rfl⟩
  -- and its class pairs nontrivially with `z`
  have hpair := hz (Work.Cohomology.cohomologyClassOf ℚ X w hw)
  rw [← hc] at hpair
  rw [Work.Cohomology.kronH_apply ℚ X w hw c] at hpair
  exact hwv hpair

end

end Work.ThomBordism
