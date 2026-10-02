import Mathlib
import Submission.Work.Whitney.RelABComplex
import Submission.Work.Whitney.relCycleKron
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.Sd_isSmallChain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The `pdABCohR`-spelling of the vanishing of the pairing on small chains

Item 2 of `rankOne_cup_model_NOTES.md` §57: the hypothesis consumed by the pairing trick
(`tcmSuspAux.kronecker_tcmRelCup_apply`) is stated on the `A+C` **complex** `pdABCohR X A C`, namely
`∀ ξ : (pdABCohR X A C).X n, ⟨ξ.1, c⟩ = 0`, while `IsSmallChain` speaks about chains.  This file
converts: an `(A,C)`-small chain is annihilated by every element of `pdABKernR X A C`, by (★) applied
to each of the two factors.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **`IsSmallChain A C` ⟹ the `pdABCohR`-spelling of the pairing-trick hypothesis.** -/
theorem kronecker_eq_zero_of_pdABKern_of_isSmallChain (X : TopCat) (A C : Set X) {n : ℕ}
    (ξ : ↥(Work.Whitney.pdABKernR (R := ℤ) X A C n))
    (c : (singularChains ℤ X).X n) (hc : IsSmallChain A C c) :
    kronecker ℤ (TopCat.toSSet.obj X) (show Cochain ℤ (TopCat.toSSet.obj X) n from ξ.1) c = 0 := by
  classical
  obtain ⟨c', hc'⟩ := hc
  rw [← hc']
  let Q : Submodule ℤ ↥((smallChains A C).X n) :=
    Submodule.comap ((smallToSing A C).f n).hom
      (LinearMap.ker (show Cochain ℤ (TopCat.toSSet.obj X) n from ξ.1))
  have hQ : Q = ⊤ := by
    refine mem_of_genSSet (smallSSet A C) n Q ?_
    intro τ
    show ((smallToSing A C).f n).hom (genSSet (smallSSet A C) n τ)
      ∈ LinearMap.ker (show Cochain ℤ (TopCat.toSSet.obj X) n from ξ.1)
    rw [smallToSing_gen τ, LinearMap.mem_ker]
    rcases τ.2 with h | h
    · have h1 := genEval_eq_zero_of_mem_relKern_of_isSmall X
        (⟨ξ.1, (Submodule.mem_inf.mp ξ.2).1⟩ : ↥(relKern ℤ X A n))
        ((Or.inl h))
      have hgoal : (show Cochain ℤ (TopCat.toSSet.obj X) n from ξ.1) (gen X n τ.1) = 0 := h1
      exact hgoal
    · have h1 := genEval_eq_zero_of_mem_relKern_of_isSmall X
        (⟨ξ.1, (Submodule.mem_inf.mp ξ.2).2⟩ : ↥(relKern ℤ X C n))
        (show IsSmall C (∅ : Set X) τ.1 from (Or.inl h))
      have hgoal : (show Cochain ℤ (TopCat.toSSet.obj X) n from ξ.1) (gen X n τ.1) = 0 := h1
      exact hgoal
  have hmem : c' ∈ Q := by rw [hQ]; exact Submodule.mem_top
  exact hmem

end

end Work.Cohomology

#print axioms Work.Cohomology.kronecker_eq_zero_of_pdABKern_of_isSmallChain
