import Mathlib
import Submission.Work.LerayHirsch.TautLine
import Submission.Work.Thom.Iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The tautological quotient descends to the projectivisation

Let `Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι` be a complex bundle of rank
`m + 1` and `P(E) = Work.LerayHirsch.ProjSpace Z = (E∖0)/ℂˣ` its projectivisation.  Over the
punctured total space `E∖0` the **tautological quotient** `Q_Z = π^*Z / ℂ·s` of the Thom chapter
(`Work.Thom.tautQuotient Z`) is a complex bundle of rank `m`, and the quotient map
`mkProj Z : E∖0 → P(E)` is a map of bundles: **`Q_Z` is the pullback along `mkProj Z` of a bundle
`Q` on `P(E)`**, which is the cokernel in the tautological sequence
`0 → ℓ → π^*Z → Q → 0` over the projectivisation.

This module proves that descent.  The cover of `Q` is the image of the cover of `Q_Z` (the pieces
`(i,k)`, `i` a chart of `Z` and `k` a non-vanishing coordinate), its transition functions are the
`ℂˣ`-descended transition functions `quoFun` of `Q_Z`, and the descent is possible because both the
index map and the transition functions of `Q_Z` are **invariant under the `ℂˣ`-action**:

* `Work.LerayHirsch.tqCoord_smul` — the chosen non-vanishing coordinate `Work.Thom.tqCoord` is
  invariant (`Classical.choose` of two predicates that are *equal as functions*, since scaling by a
  unit does not change which coordinates vanish);
* `Work.LerayHirsch.tautQuotient_indexAt_smul`, `Work.LerayHirsch.tautQuotient_coordChange_smul` —
  hence the index map and the transition functions of `tautQuotient Z` are invariant, because
  `quoFun l (c • w) u = quoFun l w u` (`quoFun_smul_unit`).

The final equality `bundleComap Q ⟨mkProj Z, _⟩ = tautQuotient Z` is a comparison of gluing data
(`Work.Thom.bundleCore_ext`): base sets by `preimage_tautBaseSetProj`, index map and transition
functions by the definition of the descended data.

## Main results

* `Work.LerayHirsch.quotientBundle` — the descended bundle `Q` over `P(E)`;
* `Work.LerayHirsch.bundleComap_quotientBundle` —
  `bundleComap (quotientBundle Z) ⟨mkProj Z, _⟩ = tautQuotient Z`;
* `Work.LerayHirsch.exists_quotientBundle_descend` — the statement requested by the Leray–Hirsch
  chapter.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## The chart of the tautological quotient is the chart of the tautological line bundle -/

/-- The chart `Work.Thom.tqBaseSet` of the tautological quotient is the chart `tautBaseSet` of the
tautological line bundle (both are "the `k`-th chart coordinate over `Z.baseSet i` does not
vanish"). -/
theorem tqBaseSet_eq_tautBaseSet (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (i : ι) (k : Fin (m + 1)) : Work.Thom.tqBaseSet Z i k = tautBaseSet Z i k := by
  ext p
  rfl

/-- The base set of the tautological quotient is the chart `tautBaseSet` of the tautological line
bundle.  (The statement of `Work.Thom.tautQuotient_baseSet` is the defining set-builder, so this is
the form in which the cover of the quotient is used below.) -/
theorem tautQuotient_baseSet_eq (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (ik : ι × Fin (m + 1)) :
    (tautQuotient Z).baseSet ik = tautBaseSet Z ik.1 ik.2 := by
  rw [tautQuotient_baseSet]
  ext p
  exact Iff.rfl

/-- Membership in the base set of the tautological quotient, in the form of a chart of the
tautological line bundle. -/
theorem mem_baseSet_tautQuotient (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (i : ι) (k : Fin (m + 1)) (p : ↥(zeroComplement (realification Z))) :
    p ∈ (tautQuotient Z).baseSet (i, k) ↔ p ∈ tautBaseSet Z i k := by
  rw [tautQuotient_baseSet_eq]

/-! ## The invariance of the gluing data of the tautological quotient under `ℂˣ` -/

/-- **`quoFun` is homogeneous of degree zero in the line it projects along**: the quotient
projection `u ↦ u - (u l / w l) • w` depends only on the line `ℂ·w`. -/
theorem quoFun_smul_unit {n : ℕ} (l : Fin (n + 1)) (c : ℂˣ)
    (w u : EuclideanSpace ℂ (Fin (n + 1))) :
    Work.Thom.quoFun l ((c : ℂ) • w) u = Work.Thom.quoFun l w u := by
  ext k
  rw [Work.Thom.quoFun_apply, Work.Thom.quoFun_apply]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- **The chosen non-vanishing coordinate of the tautological section is invariant under the
`ℂˣ`-action.**  `tqCoord Z p` is `Classical.choose` of the predicate "the `k`-th chart coordinate of
`p` does not vanish"; scaling `p` by a unit scales that vector by the unit
(`chartCoord_smulPunct`), so the predicates are *equal as functions*, and `Classical.choose` of two
proofs of two equal predicates agrees (`Classical.choose.congr_simp`, then proof irrelevance). -/
theorem tqCoord_smul (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (c : ℂˣ)
    (p : ↥(zeroComplement (realification Z))) :
    Work.Thom.tqCoord Z (smulPunct Z c p) = Work.Thom.tqCoord Z p := by
  have hL := Work.Thom.exists_coord_ne_zero_localTriv Z (smulPunct Z c p)
  have hR := Work.Thom.exists_coord_ne_zero_localTriv Z p
  change Classical.choose hL = Classical.choose hR
  have hpred : (fun k : Fin (m + 1) =>
        ((Z.localTriv (Z.indexAt ((smulPunct Z c p) : (realification Z).TotalSpace).proj)
          ((smulPunct Z c p) : (realification Z).TotalSpace))).2 k ≠ 0)
      = (fun k : Fin (m + 1) =>
        ((Z.localTriv (Z.indexAt (p : (realification Z).TotalSpace).proj)
          (p : (realification Z).TotalSpace))).2 k ≠ 0) := by
    funext k
    have h1 : (Z.localTriv (Z.indexAt (smulPunct Z c p).1.proj)
          ((smulPunct Z c p) : (realification Z).TotalSpace)).2 k
        = (c : ℂ) * (Z.localTriv (Z.indexAt p.1.proj)
            (p : (realification Z).TotalSpace)).2 k := by
      have h2 : chartCoord Z (Z.indexAt p.1.proj) (smulPunct Z c p)
          = (c : ℂ) • chartCoord Z (Z.indexAt p.1.proj) p := chartCoord_smulPunct Z _ c p
      have h3 := congrArg (fun v : EuclideanSpace ℂ (Fin (m + 1)) => v.ofLp k) h2
      simpa [chartCoord, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] using h3
    rw [h1]
    exact propext ⟨fun h => (mul_ne_zero_iff.mp h).2, fun h => mul_ne_zero (Units.ne_zero c) h⟩
  calc Classical.choose hL = Classical.choose (hpred ▸ hL) :=
        Classical.choose.congr_simp hpred hL
    _ = Classical.choose hR := congrArg Classical.choose (Subsingleton.elim _ _)

/-- **The index map of the tautological quotient is invariant under the `ℂˣ`-action.**  By
`Work.Thom.tautQuotient_indexAt_eq` it is the pair of the base index (`rfl`-invariant, since
`smulPunct` does not move the base point) and of `tqCoord` (`tqCoord_smul`). -/
theorem tautQuotient_indexAt_smul (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (c : ℂˣ) (p : ↥(zeroComplement (realification Z))) :
    (tautQuotient Z).indexAt (smulPunct Z c p) = (tautQuotient Z).indexAt p := by
  rw [tautQuotient_indexAt_eq, tautQuotient_indexAt_eq, tqCoord_smul, smulPunct_proj]

/-- **The transition functions of the tautological quotient are invariant under the `ℂˣ`-action.**
By `Work.Thom.tautQuotient_coordChange` both sides are `quoFun jl.2 w u` where `w` is the `jl.1`-th
chart coordinate of the point and `u = Z.coordChange ik.1 jl.1 b (fillFun ik.2 z)`; scaling the
point by `c` scales `w` by `c` (`chartCoord_smulPunct`) and leaves `u` alone (`smulPunct` does not
move the base point), and `quoFun` is homogeneous of degree zero in `w` (`quoFun_smul_unit`). -/
theorem tautQuotient_coordChange_smul (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (c : ℂˣ) (ik jl : ι × Fin (m + 1)) (p : ↥(zeroComplement (realification Z))) :
    (tautQuotient Z).coordChange ik jl (smulPunct Z c p) = (tautQuotient Z).coordChange ik jl p := by
  apply ContinuousLinearMap.ext
  intro z
  rw [tautQuotient_coordChange, tautQuotient_coordChange]
  have hw : (Z.localTriv jl.1 ((smulPunct Z c p) : (realification Z).TotalSpace)).2
      = (c : ℂ) • (Z.localTriv jl.1 (p : (realification Z).TotalSpace)).2 :=
    chartCoord_smulPunct Z jl.1 c p
  rw [hw]
  exact quoFun_smul_unit jl.2 c _ _

/-- The transition functions of the tautological quotient, in the form of the continuous linear
maps `quoCLM`/`fillCLM` used to prove their continuity
(`Work.Thom.continuousOn_coordChange_tq`). -/
theorem tautQuotient_coordChange_eq (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (ik jl : ι × Fin (m + 1)) (p : ↥(zeroComplement (realification Z))) :
    (tautQuotient Z).coordChange ik jl p
      = (Work.Thom.quoCLM jl.2 ((Z.localTriv jl.1 (p : (realification Z).TotalSpace)).2)).comp
          ((Z.coordChange ik.1 jl.1 ((p : (realification Z).TotalSpace)).1).comp
            (Work.Thom.fillCLM ik.2)) := by
  apply ContinuousLinearMap.ext
  intro z
  rw [tautQuotient_coordChange, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Work.Thom.quoCLM_apply, Work.Thom.fillCLM_apply]

/-! ## The descended bundle over the projectivisation -/

/-- The **index map of the descended bundle**: the `ℂˣ`-invariant index map of the tautological
quotient, read on the projectivisation. -/
def quotientIndexAt (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    ProjSpace Z → ι × Fin (m + 1) :=
  Quotient.lift (fun p => (tautQuotient Z).indexAt p) (fun p q h => by
    obtain ⟨c, hc⟩ := h
    rw [← hc]
    exact tautQuotient_indexAt_smul Z c q)

theorem quotientIndexAt_mk (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) :
    quotientIndexAt Z (mkProj Z p) = (tautQuotient Z).indexAt p := rfl

/-- The **transition functions of the descended bundle**: the `ℂˣ`-invariant transition functions
of the tautological quotient, read on the projectivisation. -/
def quotientCoord (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (ik jl : ι × Fin (m + 1)) :
    ProjSpace Z → (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) :=
  Quotient.lift (fun p => (tautQuotient Z).coordChange ik jl p) (fun p q h => by
    obtain ⟨c, hc⟩ := h
    rw [← hc]
    exact tautQuotient_coordChange_smul Z c ik jl q)

theorem quotientCoord_mk (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (ik jl : ι × Fin (m + 1)) (p : ↥(zeroComplement (realification Z))) :
    quotientCoord Z ik jl (mkProj Z p) = (tautQuotient Z).coordChange ik jl p := rfl

/-- The chosen index of the descended bundle is a legitimate index: the point lies in the
corresponding chart. -/
theorem mem_tautBaseSetProj_quotientIndexAt
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (x : ProjSpace Z) :
    x ∈ tautBaseSetProj Z (quotientIndexAt Z x) := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  rw [quotientIndexAt_mk, mem_tautBaseSetProj_mk]
  exact (mem_baseSet_tautQuotient Z _ _ p).mp ((tautQuotient Z).mem_baseSet_at p)

/-- The transition functions of the descended bundle are those of the tautological quotient. -/
theorem quotientCoord_self (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (ik : ι × Fin (m + 1)) (x : ProjSpace Z) (hx : x ∈ tautBaseSetProj Z ik)
    (v : EuclideanSpace ℂ (Fin m)) :
    quotientCoord Z ik ik x v = v := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  rw [quotientCoord_mk]
  have hp : p ∈ tautBaseSet Z ik.1 ik.2 := (mem_tautBaseSetProj_mk Z ik p).mp hx
  exact (tautQuotient Z).coordChange_self ik p
    ((mem_baseSet_tautQuotient Z ik.1 ik.2 p).mpr hp) v

/-- The transition functions of the descended bundle satisfy the cocycle condition. -/
theorem quotientCoord_comp (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (ik jm jl : ι × Fin (m + 1)) (x : ProjSpace Z)
    (hx : x ∈ tautBaseSetProj Z ik ∩ tautBaseSetProj Z jm ∩ tautBaseSetProj Z jl)
    (v : EuclideanSpace ℂ (Fin m)) :
    quotientCoord Z jm jl x (quotientCoord Z ik jm x v) = quotientCoord Z ik jl x v := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  rw [quotientCoord_mk, quotientCoord_mk, quotientCoord_mk]
  have h1 : p ∈ tautBaseSet Z ik.1 ik.2 := (mem_tautBaseSetProj_mk Z ik p).mp hx.1.1
  have h2 : p ∈ tautBaseSet Z jm.1 jm.2 := (mem_tautBaseSetProj_mk Z jm p).mp hx.1.2
  have h3 : p ∈ tautBaseSet Z jl.1 jl.2 := (mem_tautBaseSetProj_mk Z jl p).mp hx.2
  exact (tautQuotient Z).coordChange_comp ik jm jl p
    ⟨⟨(mem_baseSet_tautQuotient Z ik.1 ik.2 p).mpr h1,
      (mem_baseSet_tautQuotient Z jm.1 jm.2 p).mpr h2⟩,
      (mem_baseSet_tautQuotient Z jl.1 jl.2 p).mpr h3⟩ v

/-- The transition functions of the descended bundle are continuous on the overlaps. -/
theorem continuousOn_quotientCoord (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (ik jl : ι × Fin (m + 1)) :
    ContinuousOn (fun x : ProjSpace Z => quotientCoord Z ik jl x)
      (tautBaseSetProj Z ik ∩ tautBaseSetProj Z jl) := by
  have hq : Topology.IsQuotientMap (mkProj Z) := isQuotientMap_quotient_mk'
  refine (Topology.IsQuotientMap.continuousOn_isOpen_iff hq
    ((isOpen_tautBaseSetProj Z ik).inter (isOpen_tautBaseSetProj Z jl))).mpr ?_
  have hpre : mkProj Z ⁻¹' (tautBaseSetProj Z ik ∩ tautBaseSetProj Z jl)
      = tautBaseSet Z ik.1 ik.2 ∩ tautBaseSet Z jl.1 jl.2 := by
    rw [Set.preimage_inter, preimage_tautBaseSetProj, preimage_tautBaseSetProj]
  rw [hpre]
  have hcont : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      (Work.Thom.quoCLM jl.2 ((Z.localTriv jl.1 (p : (realification Z).TotalSpace)).2)).comp
        ((Z.coordChange ik.1 jl.1 ((p : (realification Z).TotalSpace)).1).comp
          (Work.Thom.fillCLM ik.2)))
      (tautBaseSet Z ik.1 ik.2 ∩ tautBaseSet Z jl.1 jl.2) := by
    rw [← tqBaseSet_eq_tautBaseSet, ← tqBaseSet_eq_tautBaseSet]
    exact continuousOn_coordChange_tq Z ik.1 jl.1 ik.2 jl.2
  refine hcont.congr (fun p hp => ?_)
  rw [Function.comp_apply, quotientCoord_mk]
  exact tautQuotient_coordChange_eq Z ik jl p

/-- **The descended bundle** `Q` over the projectivisation `P(E) = (E∖0)/ℂˣ`, whose pullback along
`mkProj Z : E∖0 → P(E)` is the tautological quotient `π^*Z / ℂ·s` (`bundleComap_quotientBundle`). -/
def quotientBundle (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    VectorBundleCore ℂ (ProjSpace Z) (EuclideanSpace ℂ (Fin m)) (ι × Fin (m + 1)) where
  baseSet ik := tautBaseSetProj Z ik
  isOpen_baseSet ik := isOpen_tautBaseSetProj Z ik
  indexAt := quotientIndexAt Z
  mem_baseSet_at := mem_tautBaseSetProj_quotientIndexAt Z
  coordChange ik jl := quotientCoord Z ik jl
  coordChange_self := quotientCoord_self Z
  continuousOn_coordChange := continuousOn_quotientCoord Z
  coordChange_comp := quotientCoord_comp Z

theorem quotientBundle_baseSet (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (ik : ι × Fin (m + 1)) : (quotientBundle Z).baseSet ik = tautBaseSetProj Z ik := rfl

theorem quotientBundle_indexAt (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (x : ProjSpace Z) : (quotientBundle Z).indexAt x = quotientIndexAt Z x := rfl

theorem quotientBundle_coordChange (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (ik jl : ι × Fin (m + 1)) (x : ProjSpace Z) :
    (quotientBundle Z).coordChange ik jl x = quotientCoord Z ik jl x := rfl

/-! ## The pullback of the descended bundle is the tautological quotient -/

/-- **The descent**: the pullback of the descended bundle `Q` along `mkProj Z` is *equal* to the
tautological quotient `π^*Z / ℂ·s` as gluing data over `E∖0` (same cover, same index map, same
transition functions). -/
theorem bundleComap_quotientBundle
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    bundleComap (quotientBundle Z) ⟨mkProj Z, continuous_mkProj Z⟩ = tautQuotient Z := by
  refine Work.Thom.bundleCore_ext ?_ ?_ ?_
  · funext ik
    simp only [bundleComap_baseSet, quotientBundle_baseSet, ContinuousMap.coe_mk]
    rw [preimage_tautBaseSetProj, tautQuotient_baseSet_eq]
  · funext p
    simp only [bundleComap_indexAt, quotientBundle_indexAt, ContinuousMap.coe_mk]
    exact quotientIndexAt_mk Z p
  · intro ik jl p
    simp only [bundleComap_coordChange, quotientBundle_coordChange, ContinuousMap.coe_mk]
    exact quotientCoord_mk Z ik jl p

/-! ## The requested statement -/

theorem exists_quotientBundle_descend {m : ℕ} {B : Type} [TopologicalSpace B]
    {ι : Type} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    ∃ Q : VectorBundleCore ℂ (Work.LerayHirsch.ProjSpace Z) (EuclideanSpace ℂ (Fin m)) (ι × Fin (m + 1)),
      Nonempty (Work.Thom.BundleIso
        (Work.Thom.bundleComap Q ⟨Work.LerayHirsch.mkProj Z, Work.LerayHirsch.continuous_mkProj Z⟩)
        (Work.Thom.tautQuotient Z)) :=
  ⟨quotientBundle Z, ⟨BundleIso.ofEq (bundleComap_quotientBundle Z)⟩⟩

end

end Work.LerayHirsch
