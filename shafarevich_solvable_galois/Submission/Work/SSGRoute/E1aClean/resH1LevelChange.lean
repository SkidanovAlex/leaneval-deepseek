import Mathlib
import Submission.Work.SSGRoute.PT.H1Transfer
import Submission.Work.SSGRoute.PT.akH2Setup
import Submission.Work.SSGRoute.PTembedding.homeomorph_fixedField_fixingSubgroup
import Submission.Work.SSGRoute.E1aClean.levelChange_lift_transport
import Submission.Work.SSGRoute.E1aClean.restrictScalarsContinuous
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# **(BC)** at the level of `H¹`: the `resH1` of the level-`1` class is the level-`2` class

`levelTwoCocycle_agrees` (`E1aClean/levelTwoCocycleAgrees.lean`) compares the *cocycles* attached to
the two levels.  To compare the *dictionary values* one still has to identify the two `H¹`-groups:
`resH1_{D_A}` lands in `H¹(D_A, M)` with the coefficient carrying the *subgroup* action
(`Subgroup.instDistribMulActionSubtypeMem`), while the level-`2` dictionary lives in
`H¹(Gal(Ω/k^h), M)` with the *native* level-`2` action.  The two actions agree pointwise by
`homCoind_levelChange_smul`, so the two `H¹` are canonically identified — this file writes that
identification down as the composite

    H¹(Gal(Ω/k), M) --resH1--> H¹((k^h).fixingSubgroup, M) --h1TransferAddHom--> H¹(Gal(Ω/k^h), M)

along the homeomorphism `IntermediateField.fixingSubgroupEquiv (decompField k Ω A)`, and proves

    T (H¹π^{(k)} c) = H¹π^{(k^h)} (c ∘ AlgEquiv.restrictScalars k) .

With the level-`1` cocycle formula (`E1aClean.e1cMapCocycleFormula`), `PT.H2Fin.resH1_H1π` and the
level-`2` formula (`E1aClean.e1cMap_hensel_cocycle_formula`), this turns
`levelTwoCocycle_agrees` into the statement that the *global* `E1c` dictionary, restricted to `D_A`,
is the *henselian* `E1c` dictionary — i.e. the remaining mathematical content of the comparison
square of `localDictionary_natural_family_arch` (the (BC) of
`E1aClean/PING_BC_complete_route_2026-10-06.md`).
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped Topology

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-- **The two level coefficients as one additive group.**

`homCoind k Ω K R` (the level-`1` coefficient, with the `Gal(Ω/k)`-action) and the level-`2`
coefficient `homCoind ↥k^h Ω K^h (Rep.res φ R)` (with the `Gal(Ω/k^h)`-action) are the *same*
underlying additive group; writing the identity map as an `AddEquiv` between the two syntactically
different terms is what lets the two `DistribMulAction` instances of the level change be named
separately (and so found by type class search). -/
def levelTwoCoeffEquiv (A : ValuationSubring Ω)
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (φ : (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)) →*
      (K ≃ₐ[k] K))
    [CharZero ↥(decompField k Ω A)] [IsAlgClosure ↥(decompField k Ω A) Ω]
    [FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    [IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)] :
    Work.SSGRoute.homCoind k Ω K R ≃+
      Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A) (Rep.res φ R) where
  toFun m := m
  invFun m := m
  left_inv m := rfl
  right_inv m := rfl
  map_add' a b := rfl

/-- **The comparison map of the level change on `H¹`.**

The composite

    H¹(Gal(Ω/k), M) --resH1--> H¹((k^h).fixingSubgroup, M) --transfer--> H¹(Gal(Ω/k^h), M)

of the restriction to `D_A = (k^h).fixingSubgroup` with the transport along the homeomorphism
`fixingSubgroupEquiv : ↥((k^h).fixingSubgroup) ≃* Gal(Ω/k^h)`.  The two coefficient instances are
named explicitly (`Subgroup.instDistribMulActionSubtypeMem` on the source side, the native level-`2`
action on the target side), which is the whole content of the "(B1)" instance identification. -/
noncomputable def levelChangeTransfer (A : ValuationSubring Ω)
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (φ : (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)) →*
      (K ≃ₐ[k] K))
    [CharZero ↥(decompField k Ω A)] [IsAlgClosure ↥(decompField k Ω A) Ω]
    [FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    [IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    (hφres : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      φ (SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g)) :
    Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) →+
      Work.AbsoluteKummer.H1 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
        (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A)
          (Rep.res φ R)) := by
  haveI : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  exact (@Work.SSGRoute.PT.h1TransferAddHom (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
      (↥((decompField k Ω A).fixingSubgroup))
      _ _ _ _
      (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A) (Rep.res φ R))
      (Work.SSGRoute.homCoind k Ω K R)
      _
      (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv
        (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) (Rep.res φ R))
      _
      (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)
        _ _ (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (k := k) (Ω := Ω) (K := K) R)
        ((decompField k Ω A).fixingSubgroup))
      (IntermediateField.fixingSubgroupEquiv (decompField k Ω A))
      (Work.SSGRoute.PT.continuous_symm_of_isHomeomorph_mulEquiv _
        (Work.SSGRoute.PTembedding.isHomeomorph_fixingSubgroupEquiv (decompField k Ω A)))
      (levelTwoCoeffEquiv A R φ)
      (by
        intro g' m'
        rw [Subgroup.smul_def]
        convert (Work.SSGRoute.E1aClean.homCoind_levelChange_smul A R φ hφres
          ((IntermediateField.fixingSubgroupEquiv (decompField k Ω A)) g') m').symm using 1
        · rw [show ((↑g' : Ω ≃ₐ[k] Ω))
              = AlgEquiv.restrictScalars k
                ((IntermediateField.fixingSubgroupEquiv (decompField k Ω A)) g') from
              AlgEquiv.ext (fun x => rfl)]
          rfl
        · rfl)).comp
      (@Work.SSGRoute.PT.H2Fin.resH1 (Ω ≃ₐ[k] Ω) _ _ _ ((decompField k Ω A).fixingSubgroup)
        (Work.SSGRoute.homCoind k Ω K R) _
        (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (k := k) (Ω := Ω) (K := K) R))

/-- **`(BC)` at the level of `H¹`**: the restriction of the level-`1` class to
`D_A = (k^h).fixingSubgroup`, transported to `Gal(Ω/k^h)` along `fixingSubgroupEquiv`, is the class
of the pointwise-transported cocycle. -/
theorem levelChangeTransfer_H1π (A : ValuationSubring Ω)
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (φ : (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)) →*
      (K ≃ₐ[k] K))
    [CharZero ↥(decompField k Ω A)] [IsAlgClosure ↥(decompField k Ω A) Ω]
    [FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    [IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    (hφres : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      φ (SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g))
    (hψc : Continuous (fun g : Ω ≃ₐ[↥(decompField k Ω A)] Ω => AlgEquiv.restrictScalars k g))
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R))) :
    levelChangeTransfer A R φ hφres
        (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) c)
      = Work.AbsoluteKummer.H1π (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
          (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A) (Rep.res φ R))
          ⟨fun g : Ω ≃ₐ[↥(decompField k Ω A)] Ω => c.1 (AlgEquiv.restrictScalars k g),
            levelChange_mem_Z1 A R φ hφres hψc c⟩ := by
  unfold levelChangeTransfer
  rw [AddMonoidHom.comp_apply]
  rw [Work.SSGRoute.PT.H2Fin.resH1_H1π]
  rw [Work.SSGRoute.PT.h1TransferAddHom_mk]
  congr 1

end

end Work.SSGRoute.E1aClean
