import Mathlib
import Submission.Work.Thom.MixedCup
import Submission.Work.Thom.localThomMap_cup_zero
import Submission.Work.Cohomology.cupAssoc
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Thom.mixedCupC_oneH_zero

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Work.StemsB

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

/-- **Associativity of the mixed cup product with a degree-zero factor**:
`(a ⌣ c) ⌣ z = a ⌣ (c ⌣ z)` for `c ∈ H^0`.  The two sides live in the degrees `(m+0)+k = m+k`
and `m+(0+k)`, compared by the cast `Nat.add_assoc m 0 k`. -/
theorem mixedCupC_assoc_zero {X : Type} [TopologicalSpace X] (A : Set X) (m k : ℕ)
    (a : Work.Thom.Coh ℤ m X) (c : Work.Thom.Coh ℤ 0 X) (z : Work.Thom.RelCoh ℤ k X A) :
    (Work.Thom.mixedCupC ℤ A m (0 + k)) a ((Work.Thom.mixedCupC ℤ A 0 k) c z)
      = (Nat.add_assoc m 0 k) ▸
          ((Work.Thom.mixedCupC ℤ A m k)
            ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of X)) m 0) a c) z) := by
  obtain ⟨α, hα, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of X)) m a
  obtain ⟨β, hβ, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of X)) 0 c
  obtain ⟨ζ, hζ, rfl⟩ := Work.Cohomology.exists_relClassOf ℤ (TopCat.of X) A k z
  simp only [Work.Thom.mixedCupC_eq_mixedCup]
  -- the left-hand side
  obtain ⟨hmem1, hcoc1, h1⟩ :=
    Work.Cohomology.mixedCup_apply (TopCat.of X) A 0 k β ζ hβ hζ
  rw [h1]
  obtain ⟨hmem2, hcoc2, h2⟩ :=
    Work.Cohomology.mixedCup_apply (TopCat.of X) A m (0 + k) α
      ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of X)) β ζ.1, hmem1⟩ hα hcoc1
  rw [h2]
  -- the right-hand side, under the cast
  rw [Work.Cohomology.cupH'_apply' ℤ (TopCat.toSSet.obj (TopCat.of X)) α β hα hβ]
  obtain ⟨hmem3, hcoc3, h3⟩ :=
    Work.Cohomology.mixedCup_apply (TopCat.of X) A m k
      (Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of X)) α β) ζ
      (Work.Cohomology.cochainDiff_cup_of_cocycles ℤ (TopCat.toSSet.obj (TopCat.of X)) α β hα hβ)
      hζ
  rw [h3]
  -- push the cast inside
  let u3 : Work.Cohomology.relKern ℤ (TopCat.of X) A (m + k) :=
    ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of X))
        (Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of X)) α β) ζ.1, hmem3⟩
  have hu3 : Work.Cohomology.relDiffLM ℤ (TopCat.of X) A (m + k) u3 = 0 := hcoc3
  have hu3' : Work.Cohomology.relDiffLM ℤ (TopCat.of X) A (m + (0 + k))
      (((Work.Cohomology.relComplex ℤ (TopCat.of X) A).XIsoOfEq (Nat.add_assoc m 0 k)).hom u3) = 0 := by
    rw [← Work.Cohomology.relComplex_d_apply]
    exact Work.Thom.cocycle_transport_K (K := Work.Cohomology.relComplex ℤ (TopCat.of X) A)
      (Nat.add_assoc m 0 k) u3 (by rw [Work.Cohomology.relComplex_d_apply]; exact hu3)
  rw [Work.Thom.relClassOf_cast (Y := TopCat.of X) (A := A) (Nat.add_assoc m 0 k) u3 hu3 hu3']
  -- the cochain identity
  refine Work.Cohomology.relClassOf_congr ℤ (TopCat.of X) A hcoc2 _ (Subtype.ext ?_)
  rw [Work.Thom.relComplex_XIsoOfEq_coe (Y := TopCat.of X) (B := A) (Nat.add_assoc m 0 k)]
  simpa only [Subtype.coe_mk, Subtype.coe_eta] using
    (Work.Cohomology.cupAssoc ℤ (TopCat.toSSet.obj (TopCat.of X)) α β ζ.1).symm

end

end Work.StemsB
