import Mathlib
import Submission.Work.SSGRoute.E1aClean.globalDictionaryCanonDefs
import Submission.Work.SSGRoute.E1aClean.localDictFromFamily
import Submission.Work.SSGRoute.E1aClean.levelTwoDatum
import Submission.Work.SSGRoute.E1aClean.resH1LevelChange
import Submission.Work.SSGRoute.E1aClean.henselUnits_push_iso
import Submission.Work.SSGRoute.E1aClean.e1cMap_hensel_cocycle_formula
import Submission.Work.SSGRoute.LTDDefs.DecompAction
import Submission.Work.SSGRoute.PT.e1a_localComparison_bricks
import Submission.Work.SSGRoute.E1aClean.decompFieldHenselEmb_relAlgClosed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The finite-place dictionary of `localDictionary_natural_family_arch`, as a *definable* chain

Per the lead's ruling `_lead_design/ssg_natwit_0820.md` §(c) FIN: the per-place finite dictionary

  `Φcan E : H1loc(D_A,E) ≃+ Ext¹_{D_q}(res E′, K_qˣ)`

is built as the chain

  `push_θ ∘ extResEquivExplicit ∘ e1cEquiv₂ ∘ levelChangeTransferD ∘ h1AddEquiv(Φd) ∘ bridge`

with every factor **definable** (no `Classical.choice` of `ext_res_mulEquiv`, of `Ψfam`, or of
`hiso`): `push_θ` is pinned by `θ u = Units.map φ u`, `Φd = e1aCoeffNat` is the *same* coefficient
transport as the one used by `globalDictionaryCanon`, and the two remaining choices (`e`,
`θ`) are pinned by their specs.  This is what makes the comparison square provable: both sides
of the square use the *same* `h1AddEquiv Φd`, so the square is a statement about the `E1c`
dictionaries alone, exactly as in §10 of `E1aClean/NOTE_localDict_finite_route_sessionN5.md`.

This module is deliberately **leaf-free** (it imports no module that imports
`E1aClean.localDictionary_natural_family`), so that the leaf can import it.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## 1. Transport of `H1loc` along an equality of subgroups -/

section H1locCongr

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : IntermediateField k Ω}
  [FiniteDimensional k K] [IsGalois k K]

/-- `IsCocycleOn`/`IsLocConstOn` only depend on the subgroup as a set, so the local `H¹` of equal
subgroups is the same group. -/
noncomputable def h1locSubgroupEqEquiv (p : ℕ) [Fact p.Prime] (M : Type)
    [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    {H H' : Subgroup (Ω ≃ₐ[k] Ω)} (h : H = H') :
    H1loc p k Ω K M H ≃+ H1loc p k Ω K M H' := by
  rw [h]

end H1locCongr

/-! ## 2. The level-change transfer, at the decomposition subgroup itself

`E1aClean.levelChangeTransfer` is `h1TransferAddHom ∘ resH1`, i.e. it starts from `H¹(Gal(Ω/k),·)`.
The dictionary chain of §(c) FIN applies `h1AddEquiv` at the decomposition subgroup `D_A` first, so
the `resH1` has already been taken and only the `h1TransferAddHom` half is needed.  This is that
half, verbatim from `levelChangeTransfer` minus the `.comp resH1`. -/

/-- **The transfer half of `(BC)`**: the additive equivalence from the decomposition subgroup to
`Gal(Ω/k^h)`.  This is `Work.SSGRoute.PT.h1Transfer` at the level-change datum of
`E1aClean.levelChangeTransfer` (which is the same statement with `resH1` precomposed). -/
noncomputable def levelChangeTransferD
    (p : ℕ) (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω)
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (φ : (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
            ↥(henselOverDecomp k Ω K A)) →* (K ≃ₐ[k] K))
    [CharZero ↥(decompField k Ω A)]
    [IsAlgClosure ↥(decompField k Ω A) Ω]
    [FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    [IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    (hφres : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      φ (SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g)) :
    Work.AbsoluteKummer.H1 ↥((decompField k Ω A).fixingSubgroup)
        (Work.SSGRoute.homCoind k Ω K R) ≃+
      Work.AbsoluteKummer.H1 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
        (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A) (Rep.res φ R)) := by
  haveI : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  exact @Work.SSGRoute.PT.h1Transfer (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
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
      (Work.SSGRoute.PTembedding.isHomeomorph_fixingSubgroupEquiv (decompField k Ω A))
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
        · rfl)

/-! ## 3. The explicit form of `ext_res_mulEquiv`

`ext_res_mulEquiv` is only a `Nonempty`, so it may not be used through `Classical.choice` (the
square would not follow).  This is the explicit, `rfl`-computed form; see
`_lead_design/ssg_natwit_0820.lean` §(3). -/

/-! ## `DualMod` is `p`-torsion

The coefficient modules of the local dictionaries are `DualMod p (E ⊗ T)`, which are `ZMod p`-modules,
so they are `p`-torsion.  This is the hypothesis `(∀ x, p • x = 0)` of the PUSH bijectivity. -/

/-- `DualMod p W` is `p`-torsion. -/
theorem dualMod_p_smul_eq_zero (p : ℕ) (W : Type) [AddCommGroup W] [Module (ZMod p) W]
    (x : Work.SSGRoute.DualMod p W) : p • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) p x, ZMod.natCast_self, zero_smul]

/-- The explicit form of `ext_res_mulEquiv`. -/
noncomputable def extResEquivExplicit {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X Y : Rep.{0} SSGRoute.PTExt.Coeff G) :
    CategoryTheory.Abelian.Ext (Rep.res e.symm.toMonoidHom X) (Rep.res e.symm.toMonoidHom Y) 1 ≃+
      CategoryTheory.Abelian.Ext X Y 1 :=
  haveI : (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).IsEquivalence :=
    Work.SSGRoute.resFunctor_isEquivalence e
  (AddEquiv.ofBijective
    ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).mapExtAddHom X Y 1)
    (Functor.mapExt_bijective_of_preservesProjectiveObjects
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom) X Y 1)).symm

/-- Its computation rule: the inverse *is* `res`-functoriality on `Ext`. -/
theorem extResEquivExplicit_symm_apply {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X Y : Rep.{0} SSGRoute.PTExt.Coeff G) (x : CategoryTheory.Abelian.Ext X Y 1) :
    (extResEquivExplicit e X Y).symm x =
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).mapExtAddHom X Y 1 x := rfl

end

end Work.SSGRoute.E1aClean
