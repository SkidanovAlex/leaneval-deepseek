import Mathlib
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.kronH_isIso
import Submission.Work.Cohomology.CompatTrans.sphere3DiscPairHomology
import Submission.Work.Cohomology.uctDefs

/-!
# Detecting a cohomology class of `H⁶(S³ × S³; ℤ)` by a `6`-cycle

The singular homology of `A = S³ × S³` being degreewise free, the Kronecker pairing
`H⁶(A;ℤ) →ₗ (H₆(A;ℤ) →ₗ ℤ)` is injective; hence the class of a `6`-cocycle `α` is nonzero if and
only if `α` does not vanish on all `6`-cycles.  This is the `A = S³ × S³` instance of the standard
universal-coefficient detection, and it is the passage from the cohomological Künneth statement to
the evaluated chain-level one.
-/

set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology.Kunneth

noncomputable section

open Work.Cohomology

/-- The space `A = S³ × S³` (the sphere bundle `PairAT`), as an opaque `TopCat` (so that the
definitional equalities used in this file do not unfold it). -/
def kunnethA : TopCat := TopCat.of PairAT

/-- The singular homology of `A = PairAT = S³ × S³` is degreewise free. -/
theorem free_homology_PairAT_kunneth (n : ℕ) :
    Module.Free ℤ ↥((singularChains ℤ kunnethA).homology n) := by
  obtain ⟨e⟩ := HA_iso_expo n
  haveI : Module.Free ℤ ↥(ModuleCat.of ℤ (Fin (expo 3 3 n) → ℤ)) := inferInstance
  exact Module.Free.of_equiv (σ := RingHom.id ℤ) (σ' := RingHom.id ℤ)
    (uctIsoToLinearEquiv e).symm

/-- **A nonzero class of `H⁶(S³ × S³; ℤ)` is detected by a `6`-cycle.**  The singular homology of
`A = S³ × S³` is degreewise free, so the Kronecker pairing `H⁶(A;ℤ) →ₗ (H₆(A;ℤ) →ₗ ℤ)` is
injective, and a nonzero functional on `H₆(A;ℤ)` does not vanish identically. -/
theorem exists_cycle_eval_ne_zero (α : Cochain ℤ (TopCat.toSSet.obj kunnethA) 6)
    (hα : cochainDiff ℤ (TopCat.toSSet.obj kunnethA) α = 0)
    (hγ : cohomologyClassOf ℤ (TopCat.toSSet.obj kunnethA) α hα ≠ 0) :
    ∃ a : (chainC ℤ (TopCat.toSSet.obj kunnethA)).X 6,
      (chainC ℤ (TopCat.toSSet.obj kunnethA)).d 6 5 a = 0 ∧ α a ≠ 0 := by
  have hfree : ∀ n, Module.Free ℤ ↥((singularChains ℤ kunnethA).homology n) :=
    free_homology_PairAT_kunneth
  have hbij := kronH_isIso kunnethA hfree 6
  have hkne : kronH ℤ (TopCat.toSSet.obj kunnethA) 6
      (cohomologyClassOf ℤ (TopCat.toSSet.obj kunnethA) α hα) ≠ 0 := by
    intro h
    refine hγ (hbij.1 ?_)
    simp [h]
  obtain ⟨v, hv⟩ : ∃ v, (kronH ℤ (TopCat.toSSet.obj kunnethA) 6
      (cohomologyClassOf ℤ (TopCat.toSSet.obj kunnethA) α hα)) v ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hkne (LinearMap.ext hh)
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((chainC ℤ (TopCat.toSSet.obj kunnethA)).homologyπ 6)).mp inferInstance v
  refine ⟨(chainC ℤ (TopCat.toSSet.obj kunnethA)).iCycles 6 z, ?_, ?_⟩
  · have h := congrArg (fun (g : (chainC ℤ (TopCat.toSSet.obj kunnethA)).cycles 6 ⟶
        (chainC ℤ (TopCat.toSSet.obj kunnethA)).X 5) => g.hom z)
      (HomologicalComplex.iCycles_d (chainC ℤ (TopCat.toSSet.obj kunnethA)) 6 5)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h
    exact h
  · rw [← kronH_apply ℤ (TopCat.toSSet.obj kunnethA) α hα z]
    exact hv

end

end Work.Cohomology.Kunneth
