import Submission.Work.SSGRoute.E1aClean.BaseChangeResH1Explicit
import Submission.Work.SSGRoute.E1aClean.BaseChangeExtTransport
import Submission.Work.SSGRoute.E1aClean.continuous_galOMulEquiv_symm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The level-change square, stated

## Prover's plan (no re-derivation needed)

Discharge the `sorry` below by wiring the four naturality steps of
`NOTE_levelChangeRoute.md` §2, each **already proved** in this workspace:

1. **cover comparison** — `Work.SSGRoute.PT.PhiEgen_res_compat`
   (`PT/PhiEgen_compat.lean`) and
   `Work.SSGRoute.SSGStage.extClass_freeCoverSES_res_comparison`
   (`PT/e1a_localComparison_bricks.lean`): relates `PhiE` at the two levels through the comparison
   `Φ` of the canonical covers.  (This is the only step where the two cover choices differ; note
   `PhiEgen_res_compat` is stated with the direction `F.mapExtAddHom (PhiE_X w) =
   PhiE_{FX} (mk₀ Φ.τ₁ ∘ F.mapExtAddHom w)`.)
2. **computation rule** — `Work.SSGRoute.PT.e1cMap_PhiE_eq_delta_gen`
   (`PT/e1cDelta_beta_relation_gen.lean`), with the *same* `e1cMap` as `ExtChain` uses
   (`ExtChain.e1cMap` = `E1cGeneric.e1cMap`): on `PhiE`-generators the dictionary is
   `(e1aSESgen V).delta ∘ PsiEMap`.  Because `PhiE` is surjective it suffices to prove the square on
   the generators, i.e. replace both sides by `δ ∘ ΨE`.
3. **δ-naturality under restriction** — `Work.SSGRoute.PT.delta_restrictSES`
   (`PT/delta_restrictSES.lean`), plus the two transports `extTransport`/`resH1_fixing'`'
   computation rules.
4. **`ΨE`-step** — `Work.SSGRoute.toCoindH0_apply` (`homRepFormulaAux.lean`): `ΨE` is "push values
   along `K ↪ Ω`", so the level-change compatibility is a `funext` + `rfl` computation; the only
   input is `PING_localField_subfield_place_compat`-style coherence at the level of the embeddings,
   which here is just `rfl` because both sides use `algebraMap` through the same coercion.

Wiring aids already on disk, matching the statement's terms:
* `resH1_fixing'` (`BaseChangeResH1Explicit.lean`) — the restriction with explicit coefficient
  instances; its computation rule is `PT.H2Fin.resH1_H1π` at the instance levels used above.
* `extTransport` (`BaseChangeExtTransport.lean`) and its rules `resMulEquiv_mk₀`,
  `resMulEquiv_comp_mk₀` (`E1cGeneric/ext_res_mulEquiv_n_rules.lean`) and `extCongrLeft_mk₀`
  (`BaseChangeExtCongr.lean`).
* `res_res_eq` (`BaseChangeTransport.lean`) and `res_galOIncl`
  (`BaseChangeResGalOIncl.lean`) for the two module/group identifications.
* `homCoind_action_compat` (`BaseChangeAction.lean`, `rfl`) for the `hΨ` slot.
* `continuous_galOMulEquiv_symm` for the `hΦc` slot.

Instance-argument facts that cost builds to learn (see §2l): `AbsoluteKummer.H1` takes **four**
instance arguments `[TopologicalSpace] [Group] [AddCommGroup] [DistribMulAction]` (no
`IsTopologicalGroup`), while `PT.H2Fin.resH1` takes `[Group] [TopologicalSpace] [IsTopologicalGroup]`
before its `N`, `P` and then `[AddCommGroup P] [DistribMulAction Γ P]`.  Read them with
`#check @Name` before writing any `@`-application; `E1aClean/_chk.lean` is the scratch with them.

§2j/§2l.  The left-hand ingredient is `resH1_fixing'` with the coefficient instances passed
explicitly (`homCoind.instAddCommGroup`, `homCoind.instDistribMulActionAlgEquiv` — the latter being
the instance `ExtChain.e1cMap` itself was declared against, which is why the explicit wrapper is
needed).  The right-hand side is the base-changed dictionary applied to the `extRes`-then-`extTransport`
image of `z`.  The proof is the four naturality steps of `NOTE_levelChangeRoute.md` §2
(`PhiEgen_res_compat`, `e1cMap_PhiE_eq_delta_gen`, `delta_restrictSES`, the `ΨE`-step). -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]

/-- **The level-change naturality square of the `E1c` dictionary.** -/
theorem e1cMap_levelChange_square (L : IntermediateField k K)
    [FiniteDimensional ↥L (Kover L)] [IsGalois ↥L (Kover L)] [NumberField (Kover L)]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] [Finite R.V]
    (z : CategoryTheory.Abelian.Ext.{0} R (SSGRoute.PTExt.unitsK k K) 1) :
    resH1_fixing' L R (Work.SSGRoute.homCoind.instAddCommGroup R)
        (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv R)
        (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K) R z)
      = Work.SSGRoute.PT.h1TransferAddHom (galOMulEquiv L)
          (continuous_galOMulEquiv_symm L) (AddEquiv.refl _) (fun _ _ => rfl)
          (e1cMap_baseChanged L (Rep.res (galKIncl L) R)
            (extTransport L R 1
              (SSGRoute.PTExt.extRes (L.fixingSubgroup).subtype z))) := by
  sorry

end

end Work.SSGRoute.E1aClean
