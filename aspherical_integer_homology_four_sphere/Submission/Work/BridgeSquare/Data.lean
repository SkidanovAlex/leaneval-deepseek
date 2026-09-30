/-
# `BridgeSquare/Data.lean` — the vocabulary of the surjectivity `(c)` of the bridge

This file collects the *definitions* through which the remaining input of the Mayer–Vietoris bridge
is stated (see `Submission/Work/NOTES_LEAD_aspherical_bridge.md` §2–§3 and
`Submission/Work/BridgeSquare/NOTES.md` §0.0):

* `bdryGen` / `bdryWit` — the truncation-supported generators of `H_k(Gen.mbarCx)` in degrees
  `1, 2, 3`, with their homology witnesses (`Gen/BdryGen.lean`, generated);
* `bdryGen_cycle` / `bdryGen_hom` / `bdryGen_supp` — the generated certificates;
* `mbarCx_cycles_gen` — every cycle of `Gen.mbarCx` in degrees `1, 2, 3` is a ℤ-combination of the
  `bdryGen` plus a boundary (the SDR identity);
* `PsiM` and its quasi-isomorphism (`PsiM.lean`);
* `singCxFun` — the singular chain complex as a functor, for the lifting statement.

Nothing here is a hypothesis of the final theorem: the file exists so that the lemmas about these
objects can be stated (and delegated) in this area's own vocabulary.
-/
import Mathlib
import Submission.Work.BridgeSquare.PsiM
import Submission.Work.BridgeSquare.Spaces
import Submission.Work.BridgeSquare.FinalInputsP
import Submission.Work.RTOwed.FinalInstance
import Submission.Work.BridgeSquare.Gen.BdryGen
import Submission.Work.HomologyExtra.CycleClass

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.BridgeSquare

noncomputable section

open Work.Certificates
open Work.HomologyIso.Gen (mbarDim mbarB mbarZ mbarBd mbarRho mbarH mbarSDR)

/-- **The truncation-supported generators of `H_k(M̄)`, in every degree**: the generated data of
`Gen/BdryGen.lean` in degrees `1, 2, 3`, and the zero operator in the other degrees (where the
statement is not used). -/
def bdryGen : ∀ k, SOp (mbarDim k) (mbarB k)
  | 1 => Gen.bdryGenone
  | 2 => Gen.bdryGentwo
  | 3 => Gen.bdryGenthree
  | _ => SOp.zero _ _

/-- The witnesses of `bdryGen`: `bdryGen k - mbarZ k = mbarBd k * bdryWit k`. -/
def bdryWit : ∀ k, SOp (mbarDim (k+1)) (mbarB k)
  | 1 => Gen.bdryWitone
  | 2 => Gen.bdryWittwo
  | 3 => Gen.bdryWitthree
  | _ => SOp.zero _ _

/-- The boundary `∂_k : C_k → C_{k-1}` in degrees `1, 2, 3`, exposed as a single family so that
the statements about `bdryGen` can be written with one index. -/
def bdryGenBd : ∀ k, SOp (mbarDim (k - 1)) (mbarDim k)
  | 1 => mbarBd 0
  | 2 => mbarBd 1
  | 3 => mbarBd 2
  | _ => SOp.zero _ _

/-- The columns of `bdryGen` are cycles (in degrees `1, 2, 3`). -/
theorem bdryGen_cycle (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 3) :
    ((bdryGenBd k).mul (bdryGen k)).eqb
      (SOp.zero (mbarDim (k - 1)) (mbarB k)) = true := by
  obtain ⟨h1, h3⟩ := hk
  interval_cases k
  · exact Gen.bdryGenone_cycle
  · exact Gen.bdryGentwo_cycle
  · exact Gen.bdryGenthree_cycle

/-- Each column of `bdryGen` is homologous to the corresponding SDR generator. -/
theorem bdryGen_hom (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 3) :
    ((bdryGen k).sub (mbarZ k)).eqb ((mbarBd k).mul (bdryWit k)) = true := by
  obtain ⟨h1, h3⟩ := hk
  interval_cases k
  · exact Gen.bdryGenone_hom
  · exact Gen.bdryGentwo_hom
  · exact Gen.bdryGenthree_hom

/-- The generators are supported on the truncation cells. -/
theorem bdryGen_supp (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 3) (j : Fin (mbarB k)) :
    ((bdryGen k).img j).all (fun p => isTruncCell k p.1) = true := by
  obtain ⟨h1, h3⟩ := hk
  interval_cases k
  · exact Gen.bdryGenone_supp j
  · exact Gen.bdryGentwo_supp j
  · exact Gen.bdryGenthree_supp j

/-- The concrete assembled datum `Work.RTOwed.rtData`, in the vocabulary of this area (it is the
`rt` of the final wiring). -/
noncomputable abbrev rtConcrete : Work.Space.RTData := Work.RTOwed.rtData

/-- **The singular chain complex, as a functor** (so that `singCxFun.map f` is available). -/
abbrev singCxFun : TopCat ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

end

end Work.BridgeSquare
