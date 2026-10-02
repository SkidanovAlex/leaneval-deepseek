import Mathlib
import Submission.Work.ThomBordism.KeyLocal.tubeCompareDefs
import Submission.Work.ThomBordism.KeyLocal.pointLocalisation
import Submission.Work.ThomBordism.someOpen_relCohMap_injective
import Submission.Work.Thom.step_natural
import Submission.Work.Whitney.tcmRelCup_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory

/-!
# From the chart-level comparison to the point-relative comparison on the tube

This is the *pair-mismatch* bookkeeping step of the last-mile plan
(`Submission/Work/ThomBordism/_kl/NOTE_SESSION10.md` §3): the four geometric pieces of the plan
(`tubeTanReadingO`, `tubeNormReading`, `chartProductFormula`, `gmTubeProduct`) assemble into
`ChartCompareAll k hk`, a comparison of classes living on a *chart piece*
`tubeBaseSet E C ND i` of the tube with relative sets `tubeFootPunct` and `tubeBaseSetPunct`,
whereas the consumer (`Submission/Work/ThomBordism/_kl/perDatum.lean`) needs the comparison on the
whole closed tube `C.U`, relative to the *point* `E.e x`:

  `TubePointRelativeAll k hk`.

## The proof

Fix the datum and the point `x`.  Put `i := ND.D.indexAt x`, so `x ∈ ND.D.baseSet i`
(`ND.D.mem_baseSet_at`).  The two sets

  `tubeBaseSet E C ND i`  and  `tubeFootPunctCU E C x ∪ tubeInvPunct E C`

are open and cover the closed tube (`tubeBaseSet_union_punct`), so the pullback along the inclusion

  `incl : ↥(tubeBaseSet E C ND i) → ↥C.U`

is *injective* on relative cohomology in the point-relative pair (excision;
`relCohMap_subtypeIncl_injective`).  Hence it suffices to prove the identity after restricting
along `incl`, and there the two sides are computed by *naturality of the relative–relative cup*
(`Work.Whitney.relRelCupOpen_natural`) and *functoriality of the pullback*
(`Work.Thom.relCohMap_compA_apply`):

* the relative–relative cup `relRelCupOpen (normalPunctAt E x) (normalNonzero E) (π^*(o)) Ucan`
  restricts along the tube inverse `tubeInvMap E C` (with source sets `tubeFootPunctCU` and
  `tubeInvPunct`) and then along `incl` (with source sets `tubeFootPunct` and `tubeBaseSetPunct`) to
  the relative–relative cup of the two chart-level factors of `ChartCompareAll`;
* the two factors themselves are the pullbacks of `o` and `Ucan` along the composites
  `π ∘ tubeInvMap ∘ incl = (srcIncl V i.1) ∘ tubeFootSrc` and
  `tubeInvMap ∘ incl = tubeBaseSetIncl`, which are *definitional* identities of continuous maps
  (proved here by `ContinuousMap.ext` plus `rfl`);
* the right-hand side restricts to the same translation reading as `ChartCompareAll`'s right-hand
  side (the translation `y ↦ (y : ℝ^{8+k}) - E.e x` commutes with the inclusion definitionally),

after which `H` (i.e. `ChartCompareAll k hk`) at the chart index `i` and the point `x` closes the
goal.

**A technical remark on the spellings.**  The relative set of the chart piece in the *hypothesis*
`ChartCompareAll` is the union `tubeFootPunct E C ND i x ∪ tubeBaseSetPunct E C ND i`, whereas the
pullback along `incl` carries the relative set `{y | (y : ↥C.U) ∈ tubeFootPunctCU E C x ∪
tubeInvPunct E C}`.  The two are *definitionally* equal (they only differ by the unfolding of the
definitions of the four sets and of `Set.union`), but not syntactically, and `rw` unifies at a
transparency too low to see this.  The proof therefore states the injectivity of the restricted
pullback (`hinj'` below) directly in the union spelling: the ascription is checked by `isDefEq` at
the default transparency, which does unfold those definitions.  Likewise all the set- and
map-comparisons in the proof are performed through `ContinuousMap.ext` + `rfl` or through the
type-ascribed `have`s, never through a rewrite at low transparency.
-/
namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.FrameSigns

/-- **From the chart-level comparison to the tube-level point-relative comparison.** -/
theorem tubePointRelative (k : ℕ) (hk : 1 ≤ k) (H : ChartCompareAll k hk) :
    TubePointRelativeAll k hk := by
  intro V hV E ND G hgm hbp hvec ε C x o ho
  let I : CoverIdx V k := ND.D.indexAt x
  have hxI : x ∈ ND.D.baseSet I := ND.D.mem_baseSet_at x
  -- the chart piece and the two punctured sets are open and cover the closed tube
  have hU : IsOpen (tubeBaseSet E C ND I) :=
    (ND.D.isOpen_baseSet I).preimage (tubeFoot E C).continuous
  have hA : IsOpen (tubeFootPunctCU E C x ∪ tubeInvPunct E C) :=
    (isOpen_tubeFootPunctCU E C x).union (isOpen_tubeInvPunct E C)
  have hcov : tubeBaseSet E C ND I ∪ (tubeFootPunctCU E C x ∪ tubeInvPunct E C) = Set.univ :=
    tubeBaseSet_union_punct E C ND I x hxI
  -- localisation at the point `E.e x`: the restriction to the chart piece is injective
  have hinj := relCohMap_subtypeIncl_injective (tubeBaseSet E C ND I)
    (tubeFootPunctCU E C x ∪ tubeInvPunct E C) hU hA hcov (8 + k)
  -- the same statement, with the source relative set written as the union of the two chart-level
  -- punctured sets (definitionally the same set; see the module docstring)
  have hinj' : Function.Injective (fun z : Work.Thom.RelCoh ℤ (8 + k) ↥C.U
        (tubeFootPunctCU E C x ∪ tubeInvPunct E C) =>
      (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(tubeBaseSet E C ND I), ↥C.U))
        (tubeFootPunct E C ND I x ∪ tubeBaseSetPunct E C ND I)
        (tubeFootPunctCU E C x ∪ tubeInvPunct E C) (fun y hy => hy) ℤ (8 + k)).hom z) := hinj
  apply hinj'
  simp only []
  -- ## naturality of the relative–relative cup along the tube inverse
  have hmT1 : ∀ z ∈ tubeFootPunctCU E C x, tubeInvMap E C z ∈ normalPunctAt E x := fun z hz => hz
  have hmT2 : ∀ z ∈ tubeInvPunct E C, tubeInvMap E C z ∈ normalNonzero E := fun z hz => hz
  have hmTU : ∀ z ∈ tubeFootPunctCU E C x ∪ tubeInvPunct E C,
      tubeInvMap E C z ∈ normalPunctAt E x ∪ normalNonzero E := fun z hz => hz
  rw [Work.Whitney.relRelCupOpen_natural (tubeInvMap E C) (normalPunctAt E x) (normalNonzero E)
      (tubeFootPunctCU E C x) (tubeInvPunct E C)
      (isOpen_normalPunctAt E x) (isOpen_normalNonzero E)
      (isOpen_tubeFootPunctCU E C x) (isOpen_tubeInvPunct E C)
      hmT1 hmT2 hmTU 8 k _ _]
  -- ## naturality of the relative–relative cup along the chart inclusion
  have hmI1 : ∀ y ∈ tubeFootPunct E C ND I x,
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(tubeBaseSet E C ND I), ↥C.U)) y
        ∈ tubeFootPunctCU E C x := fun y hy => hy
  have hmI2 : ∀ y ∈ tubeBaseSetPunct E C ND I,
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(tubeBaseSet E C ND I), ↥C.U)) y
        ∈ tubeInvPunct E C := fun y hy => hy
  have hmIU : ∀ y ∈ tubeFootPunct E C ND I x ∪ tubeBaseSetPunct E C ND I,
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(tubeBaseSet E C ND I), ↥C.U)) y
        ∈ tubeFootPunctCU E C x ∪ tubeInvPunct E C := fun y hy => hy
  rw [Work.Whitney.relRelCupOpen_natural
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(tubeBaseSet E C ND I), ↥C.U))
      (tubeFootPunctCU E C x) (tubeInvPunct E C)
      (tubeFootPunct E C ND I x) (tubeBaseSetPunct E C ND I)
      (isOpen_tubeFootPunctCU E C x) (isOpen_tubeInvPunct E C)
      (isOpen_tubeFootPunct E C ND I x) (isOpen_tubeBaseSetPunct E C ND I)
      hmI1 hmI2 hmIU 8 k _ _]
  -- ## functoriality of the pullback in the two factors
  have hmC1 : ∀ y ∈ tubeFootPunct E C ND I x,
      tubeInvMap E C ((⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(tubeBaseSet E C ND I), ↥C.U)) y) ∈ normalPunctAt E x :=
    fun y hy => hmT1 _ (hmI1 y hy)
  have hmC2 : ∀ y ∈ tubeBaseSetPunct E C ND I,
      tubeInvMap E C ((⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(tubeBaseSet E C ND I), ↥C.U)) y) ∈ normalNonzero E :=
    fun y hy => hmT2 _ (hmI2 y hy)
  rw [Work.Thom.relCohMap_compA_apply (A := tubeFootPunct E C ND I x)
      (B := tubeFootPunctCU E C x) (C := normalPunctAt E x)
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(tubeBaseSet E C ND I), ↥C.U)) (tubeInvMap E C)
      hmI1 hmT1 hmC1 ℤ 8 _]
  rw [Work.Thom.relCohMap_compA_apply (A := tubeFootPunct E C ND I x)
      (B := normalPunctAt E x) (C := FrameSigns.punct V x)
      ((tubeInvMap E C).comp (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(tubeBaseSet E C ND I), ↥C.U)))
      (⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ : C(NormalTotal E, V.pt))
      hmC1 (fun p hp => hp) (fun y hy => hmC1 y hy) ℤ 8 o]
  -- `π ∘ tubeInvMap ∘ incl = srcIncl ∘ tubeFootSrc` (definitional)
  have hmapPi : (⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ : C(NormalTotal E, V.pt)).comp
      ((tubeInvMap E C).comp (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(tubeBaseSet E C ND I), ↥C.U)))
      = (FrameSigns.srcIncl V I.1).comp (tubeFootSrc E C ND I) := by
    apply ContinuousMap.ext; intro y; rfl
  rw [Work.Thom.relCohMap_congrA (tubeFootPunct E C ND I x) (FrameSigns.punct V x) hmapPi
      (fun y hy => hmC1 y hy) (fun y hy => hmC1 y hy) ℤ 8]
  rw [Work.Thom.relCohMap_compA_apply (A := tubeBaseSetPunct E C ND I)
      (B := tubeInvPunct E C) (C := normalNonzero E)
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(tubeBaseSet E C ND I), ↥C.U)) (tubeInvMap E C)
      hmI2 hmT2 hmC2 ℤ k _]
  -- `tubeInvMap ∘ incl = tubeBaseSetIncl` (definitional)
  have hmapT : (tubeInvMap E C).comp (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(tubeBaseSet E C ND I), ↥C.U)) = tubeBaseSetIncl E C ND I := by
    apply ContinuousMap.ext; intro y; rfl
  rw [Work.Thom.relCohMap_congrA (tubeBaseSetPunct E C ND I) (normalNonzero E) hmapT
      (fun y hy => hmC2 y hy) (fun y hy => hy) ℤ k]
  -- ## the right-hand side: push the scalar through and compose the translations
  rw [map_zsmul]
  rw [Work.Thom.relCohMap_compA_apply (A := tubeFootPunct E C ND I x ∪ tubeBaseSetPunct E C ND I)
      (B := tubeFootPunctCU E C x ∪ tubeInvPunct E C) (C := ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))))
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(tubeBaseSet E C ND I), ↥C.U))
      (⟨fun y : ↥C.U => (y : Work.Tubular.Euc (8 + k)) - E.e x, by fun_prop⟩ :
        C(↥C.U, Work.Tubular.Euc (8 + k)))
      hmIU (fun z hz => tubePoint_neCU E C x z hz) (fun y hy => tubePoint_neCU E C x (y : ↥C.U) hy)
      ℤ (8 + k) (stdModelGen (8 + k))]
  -- the translation on the chart piece is the restriction of the translation on the tube
  have hmapPsi : ((⟨fun y : ↥C.U => (y : Work.Tubular.Euc (8 + k)) - E.e x, by fun_prop⟩ :
        C(↥C.U, Work.Tubular.Euc (8 + k)))).comp
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(tubeBaseSet E C ND I), ↥C.U))
      = (⟨fun y : ↥(tubeBaseSet E C ND I) => (y : Work.Tubular.Euc (8 + k)) - E.e x,
          by fun_prop⟩ : C(↥(tubeBaseSet E C ND I), Work.Tubular.Euc (8 + k))) := by
    apply ContinuousMap.ext; intro y; rfl
  rw [Work.Thom.relCohMap_congrA (tubeFootPunct E C ND I x ∪ tubeBaseSetPunct E C ND I)
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmapPsi
      (fun y hy => tubePoint_neCU E C x (y : ↥C.U) hy) (tubePoint_ne E C ND I x hxI) ℤ (8 + k)]
  -- ## the two spellings of the relative–relative cup, and the chart-level comparison
  rw [← Work.Whitney.tcmRelCup_eq_relRelCupOpen (tubeFootPunct E C ND I x)
      (tubeBaseSetPunct E C ND I) (isOpen_tubeFootPunct E C ND I x)
      (isOpen_tubeBaseSetPunct E C ND I) 8 k _ _]
  exact H E ND G hgm hbp hvec C I x hxI o ho

end

end Work.ThomBordism.KeyLocal
