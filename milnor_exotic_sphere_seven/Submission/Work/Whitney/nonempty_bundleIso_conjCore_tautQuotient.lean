import Mathlib
import Submission.Work.Whitney.ConjDefs
import Submission.Work.Whitney.ConjTopology
import Submission.Work.Whitney.ConjQuotient
import Submission.Work.Thom.tautQuotientCore_defs
import Submission.Work.Thom.QuotientLin
import Submission.Work.Thom.Iso
import Submission.Work.Thom.complexPullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type}

/-!
**THE TAUTOLOGICAL QUOTIENT OF A CONJUGATE BUNDLE IS THE CONJUGATE OF THE TAUTOLOGICAL QUOTIENT.**

This is the geometric input of the sign rule `c_j(Z̄) = (-1)^j c_j(Z)` for the conjugate bundle
`Work.Whitney.conjCore Z` of `Submission/Work/Whitney/ConjDefs.lean`.  Both sides are cores over
`X = ↥(zeroComplement (realification Z))` with model fibre `EuclideanSpace ℂ (Fin m)` and index type
`ι × Fin (m+1)`; and the two cores have the *same* `baseSet`, the *same* `indexAt` and the *same*
transition functions, so by `Work.Thom.bundleCore_ext` they are **equal**, whence the isomorphism.

The three comparisons are:

* `Work.Whitney.localTriv_snd_conjCore_conjPunct` — the `j`-th fibre coordinate of the
  conjugation `Φ = conjPunct Z` is the conjugate of the `j`-th coordinate of `Z`;
* `Work.Whitney.mem_tqBaseSet_conjCore_conjPunct` — the base sets agree, using
  `star x ≠ 0 ↔ x ≠ 0` (`conjC_coord`);
* `Work.Whitney.tqCoord_conjCore_conjPunct` — the *chosen* non-vanishing coordinate of `Z̄` at
  `Φ p` equals that of `Z` at `p`.  This is the delicate point: both sides are `Classical.choose`s
  over *propositionally equal* predicates on the same type `Fin (m+1)`
  (`Classical.choose.congr_simp` + proof irrelevance), exactly as in
  `Work.Thom.tqCoord_comap` of `Submission/Work/Thom/tautQuotientComap.lean`.

Finally `Work.Whitney.bundleComap_tautQuotient_conjCore` is the equality of cores, and the required
`BundleIso` is `Work.Thom.BundleIso.ofEq` of it (both sides are cores of rank `m` over `X` with
index type `ι × Fin (m+1)`), whose fibrewise map is the identity.
-/

/-- **The fibre coordinate of the conjugation in a chart.**  The `j`-th chart coordinate of the
point `conjPunct Z p` of the conjugate bundle is the conjugate (`conjC`) of the `j`-th chart
coordinate of `p`. -/
theorem localTriv_snd_conjCore_conjPunct
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (j : ι)
    (p : ↥(zeroComplement (realification Z))) :
    ((conjCore Z).localTriv j
        (conjPunct Z p : (realification (conjCore Z)).TotalSpace)).2
      = conjC (m + 1) ((Z.localTriv j (p : (realification Z).TotalSpace)).2) := by
  rw [← localTriv_snd_eq (conjCore Z) j
    (conjPunct Z p : (realification (conjCore Z)).TotalSpace)]
  rw [conjPunct_coe, localTriv_realification_conjRealTotalSpace]
  exact congrArg (conjC (m + 1)) (localTriv_snd_eq Z j (p : (realification Z).TotalSpace))

/-- **The chosen non-vanishing coordinate of the tautological section is compatible with
conjugation.**  `tqCoord` is a `Classical.choose`, so this needs the transport argument: the two
predicates ("the `k`-th coordinate does not vanish") are equal by
`Work.Whitney.localTriv_snd_conjCore_conjPunct` and `conjC_coord` + `star_ne_zero`. -/
theorem tqCoord_conjCore_conjPunct
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) :
    tqCoord (conjCore Z) (conjPunct Z p) = tqCoord Z p := by
  have hL := exists_coord_ne_zero_localTriv (conjCore Z) (conjPunct Z p)
  have hR := exists_coord_ne_zero_localTriv Z p
  change Classical.choose hL = Classical.choose hR
  have hpred : (fun k : Fin (m + 1) =>
        (((conjCore Z).localTriv ((conjCore Z).indexAt
            (conjPunct Z p : (realification (conjCore Z)).TotalSpace).proj)
          (conjPunct Z p : (realification (conjCore Z)).TotalSpace))).2 k ≠ 0)
      = (fun k : Fin (m + 1) =>
        ((Z.localTriv (Z.indexAt (p : (realification Z).TotalSpace).proj)
          (p : (realification Z).TotalSpace))).2 k ≠ 0) := by
    funext k
    have hidx : ((conjPunct Z p : (realification (conjCore Z)).TotalSpace)).proj
        = (p : (realification Z).TotalSpace).proj := by
      rw [conjPunct_coe, conjRealTotalSpace_apply]
    rw [conjCore_indexAt, hidx, localTriv_snd_conjCore_conjPunct, conjC_coord]
    exact propext star_ne_zero
  calc Classical.choose hL = Classical.choose (hpred ▸ hL) :=
        Classical.choose.congr_simp hpred hL
    _ = Classical.choose hR := congrArg Classical.choose (Subsingleton.elim _ _)

/-- **The base sets of the tautological quotients of `Z̄` and of `Z` agree under conjugation**:
`conjPunct Z p` lies in the `(i,k)`-piece of the tautological quotient of `conjCore Z` exactly when
`p` lies in the `(i,k)`-piece of the tautological quotient of `Z`.  Sets of the *two different*
punctured total spaces, compared through `conjPunct`. -/
theorem mem_tqBaseSet_conjCore_conjPunct
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (i : ι) (k : Fin (m + 1))
    (p : ↥(zeroComplement (realification Z))) :
    conjPunct Z p ∈ tqBaseSet (conjCore Z) i k ↔ p ∈ tqBaseSet Z i k := by
  have hbase : ((conjPunct Z p : (realification (conjCore Z)).TotalSpace)).proj
      = (p : (realification Z).TotalSpace).proj := by
    rw [conjPunct_coe, conjRealTotalSpace_apply]
  rw [tqBaseSet, tqBaseSet, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    rw [conjCore_baseSet, hbase] at h1
    refine ⟨h1, ?_⟩
    rw [localTriv_snd_conjCore_conjPunct, conjC_coord] at h2
    exact star_ne_zero.mp h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [conjCore_baseSet]
      exact hbase ▸ h1
    · rw [localTriv_snd_conjCore_conjPunct, conjC_coord]
      exact star_ne_zero.mpr h2

/-- **The tautological quotient of the conjugate bundle is the conjugate of the tautological
quotient**: an equality of gluing data over `↥(zeroComplement (realification Z))`, with index type
`ι × Fin (m+1)`.  The proof is `Work.Thom.bundleCore_ext` applied to the three comparisons
`baseSet` (via `Work.Whitney.mem_tqBaseSet_conjCore_conjPunct`), `indexAt` (via
`Work.Whitney.tqCoord_conjCore_conjPunct`) and `coordChange` (the substitution
`Work.Whitney.conjC_fillFun` / `Work.Whitney.conjC_quoFun`). -/
theorem bundleComap_tautQuotient_conjCore
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    bundleComap (tautQuotient (conjCore Z)) (conjPunctCM Z) = conjCore (tautQuotient Z) := by
  refine bundleCore_ext ?_ ?_ ?_
  · -- the base sets
    funext ik
    obtain ⟨i, k⟩ := ik
    ext p
    rw [bundleComap_baseSet, Set.mem_preimage, conjPunctCM_apply, conjCore_baseSet,
      tautQuotient_baseSet (conjCore Z), tautQuotient_baseSet Z]
    exact mem_tqBaseSet_conjCore_conjPunct Z i k p
  · -- the index maps
    funext p
    simp only [bundleComap_indexAt, conjPunctCM_apply, conjCore_indexAt]
    rw [tautQuotient_indexAt_eq (conjCore Z) (conjPunct Z p), tautQuotient_indexAt_eq Z p]
    refine Prod.ext ?_ ?_
    · have hidx : ((conjPunct Z p : (realification (conjCore Z)).TotalSpace)).proj
          = (p : (realification Z).TotalSpace).proj := by
        rw [conjPunct_coe, conjRealTotalSpace_apply]
      rw [conjCore_indexAt, hidx]
    · exact tqCoord_conjCore_conjPunct Z p
  · -- the transition functions
    rintro ⟨i, k⟩ ⟨j, l⟩ p
    apply ContinuousLinearMap.ext
    intro z
    have hb : ((conjPunct Z p : (realification (conjCore Z)).TotalSpace)).1 = p.1.1 := by
      rw [conjPunct_coe, conjRealTotalSpace_apply]
    rw [bundleComap_coordChange, conjPunctCM_apply,
      tautQuotient_coordChange (conjCore Z) i j k l (conjPunct Z p) z,
      hb, localTriv_snd_conjCore_conjPunct, conjCore_coordChange, conjCLM_apply,
      conjC_fillFun, conjCore_coordChange, conjCLM_apply,
      tautQuotient_coordChange Z i j k l p (conjC m z), ← conjC_quoFun]

/-- **THE TAUTOLOGICAL QUOTIENT OF A CONJUGATE BUNDLE IS THE CONJUGATE OF THE TAUTOLOGICAL
QUOTIENT.**  The two cores are equal (`Work.Whitney.bundleComap_tautQuotient_conjCore`), so the
identity is an isomorphism of bundles with `hom = 1`, `inv = 1`
(`Work.Thom.BundleIso.ofEq`). -/
theorem nonempty_bundleIso_conjCore_tautQuotient {m : ℕ} {B : Type} [TopologicalSpace B]
    {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.bundleComap (Work.Thom.tautQuotient (conjCore Z)) (conjPunctCM Z))
      (conjCore (Work.Thom.tautQuotient Z))) :=
  ⟨BundleIso.ofEq (bundleComap_tautQuotient_conjCore Z)⟩

end

end Work.Whitney
