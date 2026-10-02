import Mathlib
import Submission.Work.Agree.crux
import Submission.Work.Agree.cLine
import Submission.Work.Agree.rankTwoShiftIso
import Submission.Work.Thom.sumEps
import Submission.Work.Thom.sumStableCorollaries
import Submission.Work.Thom.realification
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.nonempty_bundleIso_sumEps_whitneySum
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm
import Submission.Work.LerayHirsch.WhitneySumAssoc
import Submission.Work.Gen.WhitneySumRegroup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The rank-two shift `ℂ(L^a) ≅ cLine (2a) ⊕ ε²`

This module assembles `Work.Agree.shiftToRankTwo` from

* `Work.Agree.complexificationCore_iso_whitneySum` (`ℂ(L^a) ≅ cLine a ⊕ cLine a`),
* `Work.Agree.rankTwoShiftIso` (`cLine a ⊕ cLine a ≅ cLine (2a) ⊕ ε²`), and
* the presentation bridge `Z ⊕ ε² ≅ sumEps (sumEps Z)` (`Work.Agree.sumEpsRegroupC` below),
  proved here from the associativity/functoriality/commutativity lemmas of the Whitney sum and the
  rigidity of the trivial bundle.
-/

open Work.TangentClasses

namespace Work.Agree

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## §1. Rigidity of the trivial gluing data -/

/-- **A bundle all of whose transition functions are `1` and all of whose base sets are `univ` is
isomorphic to any other such bundle with the same model fibre** — the constant gauge `1`. -/
theorem nonempty_bundleIso_of_trivial {k : ℕ} {ι ι' : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin k)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin k)) ι')
    (hZ : ∀ i j x, Z.coordChange i j x = 1) (hZ' : ∀ i j x, Z'.coordChange i j x = 1) :
    Nonempty (Work.Thom.BundleIso Z Z') := by
  refine Work.Thom.nonempty_bundleIso_of_gauge Z Z'
    (fun _ _ _ => 1) (fun _ _ _ => 1) (fun i i' => continuousOn_const)
    (fun i i' => continuousOn_const) ?_ ?_ ?_ ?_ ?_ ?_
  · intro i t t' b _ _ _
    rw [hZ' t t' b]
    ext v
    simp
  · intro i t i' b _ _ _
    rw [hZ i' i b]
    ext v
    simp
  · intro i t t' b _ _ _
    rw [hZ' t' t b]
    ext v
    simp
  · intro i t i' b _ _ _
    rw [hZ i i' b]
    ext v
    simp
  · intro i i' b x _
    simp
  · intro i i' b y _
    simp

/-! ## §2. Functoriality of the Whitney sum in its second argument -/

/-- **Functoriality of the complex direct sum in its *second* argument**, obtained from
`Work.LerayHirsch.nonempty_bundleIso_whitneySum_first` and the commutativity of the sum. -/
theorem nonempty_bundleIso_whitneySum_second {m₁ m₂ m₂' : ℕ} {ι₁ ι₂ ι₂' : Type}
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (Z₂' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂')) ι₂')
    (e : Work.Thom.BundleIso Z₂ Z₂') :
    Nonempty (Work.Thom.BundleIso (Whitney.whitneySum Z₁ Z₂)
      (Whitney.whitneySum Z₁ Z₂')) := by
  obtain ⟨c1⟩ := Whitney.nonempty_bundleIso_whitneySum_comm Z₁ Z₂
  obtain ⟨c2⟩ := LerayHirsch.nonempty_bundleIso_whitneySum_first Z₂ Z₂' Z₁ e
  obtain ⟨c3⟩ := Whitney.nonempty_bundleIso_whitneySum_comm Z₂' Z₁
  exact ⟨c1.trans (c2.trans c3)⟩

/-! ## §3. The rigidity facts for the two trivial presentations -/

section TrivialFacts

/-- The rank-`1` trivial bundle over the index type `Bool`. -/
abbrev trivC1 : VectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 1)) Bool :=
  trivialVectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 1)) Bool

@[simp] theorem T1_coordChange (i j : Bool) (x : S4) :
    trivC1.coordChange i j x = 1 :=
  rfl

@[simp] theorem whitneySum_T1_coordChange (i j : Bool × Bool) (x : S4) :
    (Whitney.whitneySum trivC1 trivC1).coordChange i j x = 1 := by
  rw [Whitney.whitneySum_coordChange, T1_coordChange, T1_coordChange]
  ext v
  simp

@[simp] theorem trivTwo_coordChange (i j : Bool) (x : S4) :
    (trivialVectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 2)) Bool).coordChange i j x = 1 :=
  rfl

end TrivialFacts

/-! ## §4. The presentation bridge `Z ⊕ ε² ≅ sumEps (sumEps Z)` -/

/-- **The presentation bridge.** `Z ⊕ ε²` (in the `Work.Whitney.whitneySum` presentation, with the
trivial summand indexed by `Bool`) is `sumEps Bool (sumEps Bool Z)`.  The proof is the chain
`Z ⊕ ε² ≅ Z ⊕ (ε¹ ⊕ ε¹) ≅ (Z ⊕ ε¹) ⊕ ε¹ ≅ (sumEps Z) ⊕ ε¹ ≅ sumEps (sumEps Z)`. -/
theorem sumEpsRegroupC {m : ℕ} {ι : Type}
    (Z : VectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin m)) ι) :
    Nonempty (Work.Thom.BundleIso
      (Whitney.whitneySum Z (trivialVectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 2)) Bool))
      (Work.Thom.sumEps Bool (Work.Thom.sumEps Bool Z))) := by
  -- (1) `sumEps (sumEps Z) ≅ (sumEps Z) ⊕ ε¹`
  obtain ⟨f1⟩ := Whitney.nonempty_bundleIso_sumEps_whitneySum (ι₀ := Bool) (Z := Work.Thom.sumEps Bool Z)
  -- (2) `sumEps Z ≅ Z ⊕ ε¹`
  obtain ⟨f2⟩ := Whitney.nonempty_bundleIso_sumEps_whitneySum (ι₀ := Bool) (Z := Z)
  -- (3) functoriality in the first argument
  obtain ⟨f3⟩ := LerayHirsch.nonempty_bundleIso_whitneySum_first
    (Work.Thom.sumEps Bool Z) (Whitney.whitneySum Z trivC1) trivC1 f2
  -- (4) associativity
  obtain ⟨f4⟩ := LerayHirsch.nonempty_bundleIso_whitneySum_assoc Z trivC1 trivC1
  -- (5) `ε¹ ⊕ ε¹ ≅ ε²`
  obtain ⟨f5⟩ := nonempty_bundleIso_of_trivial (Whitney.whitneySum trivC1 trivC1)
    (trivialVectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 2)) Bool)
    (fun i j x => whitneySum_T1_coordChange i j x) (fun i j x => trivTwo_coordChange i j x)
  -- (6) functoriality in the second argument
  obtain ⟨f6⟩ := nonempty_bundleIso_whitneySum_second Z (Whitney.whitneySum trivC1 trivC1)
    (trivialVectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 2)) Bool) f5
  -- assemble: `whitneySum Z ε² ≅ sumEps (sumEps Z)`
  exact ⟨(f1.trans (f3.trans (f4.trans f6))).symm⟩

/-! ## §5. The rank-two shift -/

/-- **The rank-two shift**: the complexification of Milnor's quaternionic line `L^a = L^a R^0` is
`cLine (2a) ⊕ ε¹ ⊕ ε¹`.  This is the brick that replaces the degree-`2` Whitney formula in
`Work.Agree.RankTwoShift`: `c₂(ℂ(L^a)) = c₂(cLine (2a)) = ±2a·G` by stability. -/
theorem shiftToRankTwo (a : ℤ) :
    Nonempty (Work.Thom.BundleIso (Work.Thom.complexificationCore (Work.Agree.clutchBundle a 0))
      (Work.Thom.sumEps Bool (Work.Thom.sumEps Bool (Work.Agree.cLine (2 * a))))) := by
  obtain ⟨e1⟩ := complexificationCore_iso_whitneySum a
  obtain ⟨e2⟩ := rankTwoShiftIso a
  obtain ⟨e3⟩ := sumEpsRegroupC (cLine (2 * a))
  exact ⟨e1.trans (e2.trans e3)⟩

end

end Work.Agree
