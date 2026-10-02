import Mathlib
import Submission.Work.Thom.stepDefs
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.Kronecker
import Submission.Work.Whitney.Cup
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.relCochainDual
import Submission.Work.Cohomology.relIncl_relCupH
import Submission.Work.Cohomology.relCupH
import Submission.Work.Cohomology.Sd_isSmallChain
import Submission.Work.Thom.naturalModelClass
import Submission.Work.Thom.discFullA
import Submission.Work.Thom.chartCoeffAux
import Submission.Work.Thom.mixedCupC_oneH_zero
import Submission.Work.Whitney.relCycleKron
import Submission.Work.Whitney.exists_chain_relClassOf_ne_zero
import Submission.Work.Whitney.isZero_relHomology_discB

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial
open Work.Thom Work.Cohomology

noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The nonzero-ness of the model class of the disc pair

The transfer of the model class `Mn n Y` to the disc pair `(Y × Dⁿ, Y × Sⁿ⁻¹)` is nonzero: the
transfer along the inclusion of pairs `discFullMap` preserves the model property
(`Work.Thom.cupMap_transfer_fwdA`), and the model property says that the map
`x ↦ π^*(x) ⌣ stepDisc` is bijective `H⁰(Y) → H^n(Y × Dⁿ, Y × Sⁿ⁻¹)`; since `1 ≠ 0` in `H⁰(Y)`
for `Y` nonempty (`Work.Thom.oneH_ne_zero`) the class `stepDisc` cannot vanish. -/

/-- **The transferred model Thom class of the disc pair is nonzero.** -/
theorem stepDisc_ne_zero (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y] (n : ℕ)
    (hn : 1 ≤ n) : Work.Thom.stepDisc Y n (Work.Thom.Mn n Y) ≠ 0 := by
  intro h0
  have hbij := (Work.Thom.cupMap_transfer_fwdA (Work.Thom.CleanA.discFullMap Y n)
      (Work.Thom.Sph Y n) (Work.Thom.DiscB Y n) (Work.Thom.CleanA.discFullMap_mem Y n)
      (Work.Thom.bijective_relCohMap_discFull Y n) (Work.Thom.projFstA Y n)
      ⟨Prod.fst, continuous_fst⟩ (by ext q; rfl) n (Work.Thom.Mn n Y)
      (Work.Thom.Mn_isModel n Y)) 0
  have hstep : (Work.Thom.relCohMap (Work.Thom.CleanA.discFullMap Y n) (Work.Thom.DiscB Y n)
      (Work.Thom.Sph Y n) (Work.Thom.CleanA.discFullMap_mem Y n) ℤ n).hom (Work.Thom.Mn n Y)
      = Work.Thom.stepDisc Y n (Work.Thom.Mn n Y) := rfl
  have hone : (Work.Cohomology.oneH ℤ (Work.Whitney.ssB Y)) ≠ 0 :=
    Work.Thom.oneH_ne_zero
  refine hone (hbij.1 ?_)
  rw [hstep, h0]
  simp

/-! ## The ball chain of the disc pair

The chain of the statement is produced by the (Ext-free) universal coefficient non-degeneracy of the
pair `(Y × Dⁿ, Y × Sⁿ⁻¹)`: since `Y` is a point and the relative homology of the disc pair vanishes
below the top degree (`Work.Whitney.isZero_relHomology_discB`, the transport of
`Work.Cohomology.diskPairHomologyZero`), a nonzero relative cohomology class is detected by a
relative cycle (`Work.Whitney.exists_chain_relClassOf_ne_zero`), and the detecting chain satisfies
the two conclusions. -/

/-- **The ball chain of the disc pair over a point.**  There is a chain `B ∈ C_n(Y × Dⁿ)` whose
boundary is carried by the sphere bundle `DiscB Y n = Y × Sⁿ⁻¹`, and which pairs nontrivially with
every relative cocycle representing the model Thom class `stepDisc Y n (Mn n Y)`. -/
theorem exists_ballChain (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y]
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ B : (Work.Cohomology.singularChains ℤ (TopCat.of (Y × Work.Thom.MBall n))).X n,
      Work.Cohomology.IsSmallChain (Work.Thom.DiscB Y n) ∅
        ((Work.Cohomology.singularChains ℤ (TopCat.of (Y × Work.Thom.MBall n))).d n (n - 1) B)
      ∧ ∀ (w : ↥(Work.Cohomology.relKern ℤ (TopCat.of (Y × Work.Thom.MBall n))
            (Work.Thom.DiscB Y n) n))
          (hw : Work.Cohomology.relDiffLM ℤ (TopCat.of (Y × Work.Thom.MBall n))
            (Work.Thom.DiscB Y n) n w = 0)
          (hcl : Work.Cohomology.relClassOf ℤ (TopCat.of (Y × Work.Thom.MBall n))
            (Work.Thom.DiscB Y n) w hw = Work.Thom.stepDisc Y n (Work.Thom.Mn n Y)),
          Work.Cohomology.kronecker ℤ (Work.Whitney.ssB (Y × Work.Thom.MBall n)) w.1 B ≠ 0 := by
  have hne : Work.Thom.stepDisc Y n (Work.Thom.Mn n Y) ≠ 0 := stepDisc_ne_zero Y n hn
  have hk : n - 1 ≠ n := by omega
  have hZ : CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains (TopCat.of (Y × Work.Thom.MBall n))
        (Work.Thom.DiscB Y n)).homology (n - 1)) :=
    isZero_relHomology_discB Y n (n - 1) hn hk
  exact exists_chain_relClassOf_ne_zero (TopCat.of (Y × Work.Thom.MBall n))
    (Work.Thom.DiscB Y n) n hn hZ (Work.Thom.stepDisc Y n (Work.Thom.Mn n Y)) hne

end

end Work.Whitney
