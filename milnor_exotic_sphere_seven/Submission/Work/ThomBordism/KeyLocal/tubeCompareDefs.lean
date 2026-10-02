import Mathlib
import Submission.Work.ThomBordism.KeyLocal._assAux
import Submission.Work.ThomBordism.KeyLocal.mixedCupLift

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory

namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.FrameSigns

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The foot-punctured set on the closed tube: the tube points whose foot is not `x`. -/
def tubeFootPunctCU (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) (x : V.pt) :
    Set ↥C.U :=
  {y | tubeFoot E C y ≠ x}

theorem isOpen_tubeFootPunctCU (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (x : V.pt) : IsOpen (tubeFootPunctCU E C x) := by
  have h : tubeFootPunctCU E C x = tubeFoot E C ⁻¹' ({x}ᶜ : Set V.pt) := rfl
  rw [h]
  exact isClosed_singleton.isOpen_compl.preimage (tubeFoot E C).continuous

theorem isOpen_tubeInvPunct (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) :
    IsOpen (Work.ThomBordism.tubeInvPunct E C) := by
  have h : Work.ThomBordism.tubeInvPunct E C
      = (fun y : ↥C.U => C.inv y.1) ⁻¹' (normalNonzero E) := rfl
  rw [h]
  exact (isOpen_normalNonzero E).preimage
    (C.continuousOn_inv.comp_continuous continuous_subtype_val (fun y => y.2))

theorem tubeBaseSet_union_punct (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    tubeBaseSet E C ND i
      ∪ (tubeFootPunctCU E C x ∪ Work.ThomBordism.tubeInvPunct E C) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro y
  by_cases hy : tubeFoot E C y = x
  · exact Or.inl (by
      rw [mem_tubeBaseSet, ← tubeFoot_apply E C y, hy]
      exact hx)
  · exact Or.inr (Or.inl hy)

/-- The point `E.e x` of the tube is not in the two punctured sets. -/
theorem tubePoint_notMem_CU (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) (x : V.pt) :
    (⟨E.e x, C.zero_mem_U x⟩ : ↥C.U)
      ∉ tubeFootPunctCU E C x ∪ Work.ThomBordism.tubeInvPunct E C := by
  intro h
  have hf : tubeFoot E C (⟨E.e x, C.zero_mem_U x⟩ : ↥C.U) = x := by
    rw [tubeFoot_apply, Work.ThomBordism.inv_embed E C x, zeroSectionNormal_proj]
  rcases h with h | h
  · exact h hf
  · exact zeroSectionNormal_notMem_normalNonzero E x
      (Work.ThomBordism.inv_embed E C x ▸ h)

theorem tubePoint_neCU (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) (x : V.pt) :
    ∀ y ∈ tubeFootPunctCU E C x ∪ Work.ThomBordism.tubeInvPunct E C,
      (y : Work.Tubular.Euc (8 + k)) - E.e x ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := by
  intro y hy
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h0
  exact tubePoint_notMem_CU E C x (by
    have hyU : y = (⟨E.e x, C.zero_mem_U x⟩ : ↥C.U) := Subtype.ext (sub_eq_zero.mp h0)
    rwa [hyU] at hy)

/-- The definitional membership of `tubeInvPunct` in `normalNonzero`. -/
theorem tubeInvPunct_mem_normalNonzero (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) :
    ∀ y ∈ Work.ThomBordism.tubeInvPunct E C,
      (Work.ThomBordism.tubeInvMap E C) y ∈ normalNonzero E := fun y hy => hy

/-- **The chart-level comparison**: on a chart piece `tubeBaseSet E C ND i` of the tube, the
relative–relative cup of the two readings of the canonical class is the `tauSign`-multiple of the
translation reading.  This is the conclusion of the assembly of the four pieces
`tubeTanReadingO`, `tubeNormReading`, `chartProductFormula`, `gmTubeProduct`. -/
def ChartCompareAll (k : ℕ) (hk : 1 ≤ k) : Prop :=
  ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    {ε : ℝ} (C : TubeChart E ε)
    (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i)
    (o : Work.Thom.RelCoh ℤ 8 V.pt (FrameSigns.punct V x))
    (ho : Work.Tubular.relKronH (TopCat.of V.pt) (FrameSigns.punct V x) 8 o
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x) = 1),
    Work.Whitney.tcmRelCup (tubeFootPunct E C ND i x) (tubeBaseSetPunct E C ND i)
        (isOpen_tubeFootPunct E C ND i x) (isOpen_tubeBaseSetPunct E C ND i) 8 k
      ((Work.Thom.relCohMap ((FrameSigns.srcIncl V i.1).comp (tubeFootSrc E C ND i))
          (tubeFootPunct E C ND i x) (FrameSigns.punct V x)
          (tubeFootPunct_mem_srcIncl E C ND i x) ℤ 8).hom o)
      ((Work.Thom.relCohMap (tubeBaseSetIncl E C ND i) (tubeBaseSetPunct E C ND i)
          (Work.Tubular.normalNonzero E) (fun y hy => hy) ℤ k).hom
        (Work.ThomBordism.gtdUWith E ND G hgm
          (Work.Thom.realThomClassOf hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.tautologicalBundle_horiO k))))
    = tauSign •
      (Work.Thom.relCohMap
        (⟨fun y : ↥(tubeBaseSet E C ND i) => (y : Work.Tubular.Euc (8 + k)) - E.e x,
          by fun_prop⟩ : C(↥(tubeBaseSet E C ND i), Work.Tubular.Euc (8 + k)))
        (tubeFootPunct E C ND i x ∪ tubeBaseSetPunct E C ND i)
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (tubePoint_ne E C ND i x hx) ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k))

/-! ## How `TubePointRelativeAll` is obtained from `ChartCompareAll`

This is the *pair-mismatch* bookkeeping step of the last-mile plan
(`Submission/Work/ThomBordism/_kl/NOTE_SESSION10.md` §3).  Four *definitional* facts (each `rfl` in
these spellings) make it short:

1. `({y : ↥(tubeBaseSet E C ND i) | (y : ↥C.U) ∈ (tubeFootPunctCU E C x ∪ tubeInvPunct E C)}
      : Set ↥(tubeBaseSet E C ND i)) = tubeFootPunct E C ND i x ∪ tubeBaseSetPunct E C ND i`;
2. `(tubeInvMap E C).comp (⟨Subtype.val, _⟩ : C(↥(tubeBaseSet E C ND i), ↥C.U)) = tubeBaseSetIncl E C ND i`;
3. `(⟨NormalTotal.proj, _⟩ : C(NormalTotal E, V.pt)).comp
      ((tubeInvMap E C).comp (⟨Subtype.val, _⟩ : C(↥(tubeBaseSet E C ND i), ↥C.U)))
    = (FrameSigns.srcIncl V i.1).comp (tubeFootSrc E C ND i)`;
4. the two spellings `y ↦ (y : ↥C.U) - E.e x` and `y ↦ (y : ℝ^{8+k}) - E.e x` of the translation
   (and likewise for the point-relative membership proofs, which are proof-irrelevant).

**Proof.**  Take `i := ND.D.indexAt x`, so `hx : x ∈ ND.D.baseSet i` is `ND.D.mem_baseSet_at x`.
Localise at the point `E.e x` using `Work.ThomBordism.relCohMap_subtypeIncl_injective`
(or `KeyLocal.pointLocalisation_injective`) with `U := tubeBaseSet E C ND i` and
`A := tubeFootPunctCU E C x ∪ tubeInvPunct E C`: both are open
(`isOpen_tubeFootPunctCU`, `isOpen_tubeInvPunct`) and they cover the tube
(`tubeBaseSet_union_punct`, needing `x ∈ ND.D.baseSet i`).  So it suffices to prove the identity
after restricting along the inclusion `incl := ⟨Subtype.val, _⟩ : C(↥(tubeBaseSet E C ND i), ↥C.U)`.

The restriction of the left-hand side is computed in three steps, all with the tools
`Work.Thom.relCohMap_compA_apply` (functoriality, applied facts 2 and then 3/π-association) and
`Work.Whitney.relRelCupOpen_natural` (naturality of the relative–relative cup, whose source sets may
be taken to be `tubeFootPunct E C ND i x` and `tubeBaseSetPunct E C ND i` thanks to fact 1), plus
`Work.Whitney.tcmRelCup_eq_relRelCupOpen` if one prefers the `tcmRelCup` spelling of
`ChartCompareAll`.  The result is exactly the two factors of `ChartCompareAll`'s left-hand side.

The restriction of the right-hand side is the pullback of `stdModelGen (8+k)` along
`(y ↦ y - E.e x) ∘ incl`, which is fact 4.

Then `H E ND G hgm hbp hvec C i x hx o ho` closes the goal. -/

/-- **The point-relative comparison on the closed tube**: the pullback along the tube inverse of the
relative–relative cup of `π^*(o)` with the canonical Thom class is the `tauSign`-multiple of the
translation reading.  Its restriction to a chart of the normal datum is `ChartCompareAll`. -/
def TubePointRelativeAll (k : ℕ) (hk : 1 ≤ k) : Prop :=
  ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    {ε : ℝ} (C : TubeChart E ε) (x : V.pt)
    (o : Work.Thom.RelCoh ℤ 8 V.pt (FrameSigns.punct V x))
    (ho : Work.Tubular.relKronH (TopCat.of V.pt) (FrameSigns.punct V x) 8 o
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x) = 1),
    (Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C)
        (tubeFootPunctCU E C x ∪ Work.ThomBordism.tubeInvPunct E C)
        (normalPunctAt E x ∪ normalNonzero E) (fun y hy => hy) ℤ (8 + k)).hom
      (Work.Whitney.relRelCupOpen (normalPunctAt E x) (normalNonzero E)
        (isOpen_normalPunctAt E x) (isOpen_normalNonzero E) 8 k
        ((Work.Thom.relCohMap (⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ :
            C(NormalTotal E, V.pt)) (normalPunctAt E x) (FrameSigns.punct V x)
          (fun p hp => hp) ℤ 8).hom o)
        (Work.ThomBordism.gtdUWith E ND G hgm
          (Work.Thom.realThomClassOf hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.tautologicalBundle_horiO k))))
    = tauSign •
      (Work.Thom.relCohMap
        (⟨fun y : ↥C.U => (y : Work.Tubular.Euc (8 + k)) - E.e x, by fun_prop⟩ :
          C(↥C.U, Work.Tubular.Euc (8 + k)))
        (tubeFootPunctCU E C x ∪ Work.ThomBordism.tubeInvPunct E C)
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (tubePoint_neCU E C x) ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k))

/-! ## Pitfalls (found while assembling the consumers of these definitions)

1. `rw` elaborates its argument list at a *low* transparency, so whenever an argument of
   `Work.Thom.relCohMap_compA_apply` is a membership proof whose *type* needs a `def` unfolded
   (`tubeInvPunct`, `tubeFootPunctCU`, `normalPunctAt`, `tubeInvMap`, …), give it a name first with
   an explicitly ascribed type -- `have hm : ∀ z ∈ …, f z ∈ S := fun z hz => …` -- and then pass the
   name.  Elaborating the type of a `have` (or of a top-level `theorem`) uses the full transparency
   and succeeds; writing the same lambda inline as a `rw`-argument does not.
2. The membership argument `hgf` of `Work.Thom.relCohMap_compA_apply` is stated with `g (f x)`
   (the evaluation form), not with the composite `(g.comp f) x`; `ContinuousMap.comp` is not
   unfolded by the low-transparency matching of `rw`.
3. The facts
   `({y : ↥(tubeBaseSet E C ND i) | (y : ↥C.U) ∈ (tubeFootPunctCU E C x ∪ tubeInvPunct E C)})
      = tubeFootPunct E C ND i x ∪ tubeBaseSetPunct E C ND i`,
   `(tubeInvMap E C).comp ⟨Subtype.val, _⟩ = tubeBaseSetIncl E C ND i` and
   `(π).comp ((tubeInvMap E C).comp ⟨Subtype.val, _⟩) = (srcIncl V i.1).comp (tubeFootSrc E C ND i)`
   are all `rfl` (`Work.ThomBordism.KeyLocal` probes in this file's history).
-/

end

end Work.ThomBordism.KeyLocal
