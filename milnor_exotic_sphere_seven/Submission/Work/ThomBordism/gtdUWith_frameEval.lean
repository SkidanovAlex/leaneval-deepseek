import Mathlib
import Submission.Work.ThomBordism.fibreRes_gtdU_geom
import Submission.Work.ThomBordism.tautologicalClassSensitivity

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibre restriction of `gtdUWith U` is the frame reading of `U`

`Work.ThomBordism.nfRes_gtdU_eq_frameClass` (`Submission/Work/ThomBordism/fibreRes_gtdU_geom.lean`)
proves, for the *tautological* Thom class `τ = Grassmann.tautologicalThomClass k 10`,

  `nfRes E x k (gtdU E ND G hgm) = L (frameClass k (datumFrame E ND x))`,

where `L = (relCohMap (nfRead E ND x))` and `frameClass k σ = (frameEvalMap k σ)^* τ`.  Its proof —
`nfRes`-functoriality, `Work.ThomBordism.G_eq_frameEval` (the plane/vector clauses pin `G` to the
frame evaluation on each fibre), and `relCohMap`-functoriality again — uses **no property of `τ`**.
This file performs the verbatim generalisation: for an *arbitrary* class `a` of the Thom pair of the
tautological bundle,

  `nfRes E x k (gtdUWith E ND G hgm ⟨a, isThom⟩) = L ((frameEvalMap k (datumFrame E ND x))^* a)`.

This is the first half of `(A2)` of `Submission/Work/ThomBordism/NOTE_CANONICAL_SHARP.md`: applying it
to `a := (Work.Thom.realThomClassOf hk (tautologicalBundle k 10) horiO).τ` reduces the frame half of
`canonicalGauss_isLocalDegreeClass` to the *pure frame* statement

  `(frameEvalMap k (datumFrame E ND x))^* (realThomClassOf …).τ = stdModelGen k`,

i.e. to the comparison of the *chart* trivialisation of the tautological bundle at the Gauss plane
with the σ-corrected coorientation frame — with no `Nonempty`-choice and no `nfGen` in sight.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

open Work.ThomBordism.Grassmann
open Work.ThomBordism.PontryaginThom

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The fibre restriction of `gtdUWith U` is the frame reading of `U`.**  For any class `a` of the
Thom pair of the tautological bundle, the restriction of the pulled-back class
`gtdUWith E ND G hgm ⟨a, _⟩` to the fibre of the normal bundle over `x` is the pullback of `a`
along the frame evaluation of the σ-corrected (coorientation) frame of the datum, read through
`nfRead E ND x`. -/
theorem nfRes_gtdUWith_eq_frameEval (hk : 1 ≤ k)
    (E : PontryaginThom.EmbeddingData V (8 + k))
    (ND : PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10))
    (hbp : ∀ p, (tautologicalBundle k 10).proj (G p) = Grassmann.padGaussFun E ND p.1)
    (hvec : ∀ p, Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    (x : V.pt) {U : Work.Thom.ThomClass (tautologicalBundle k 10) k} :
    nfRes E x k (gtdUWith E ND G hgm U)
      = (Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x) (framePunct k)
          (fun p hp => (mem_framePunct k _).mpr (nfRead_ne_zero hk E ND x p hp)) ℤ k).hom
        ((Work.Thom.relCohMap (frameEvalMap k (datumFrame E ND x)) (framePunct k)
          (Work.Thom.zeroComplement (tautologicalBundle k 10))
          (frameEvalMap_mem k (datumFrame E ND x)) ℤ k).hom U.τ) := by
  classical
  have hΨreq : ∀ p ∈ nfPunct E x, nfRead E ND x p ∈ framePunct k :=
    fun p hp => (mem_framePunct k _).mpr (nfRead_ne_zero hk E ND x p hp)
  have hcomp1 : ∀ q ∈ nfPunct E x,
      ((Work.Tubular.eucNormalHomeomorph E ND).symm : C(Work.Tubular.NormalTotal E,
        (Work.Tubular.normalBundle E ND).TotalSpace)).comp (nfIncl E x) q
        ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND) :=
    fun q hq => gtd_mem E ND (nfIncl E x q) (nfIncl_mem E x q hq)
  have hcomp2 : ∀ q ∈ nfPunct E x,
      G (((Work.Tubular.eucNormalHomeomorph E ND).symm : C(Work.Tubular.NormalTotal E,
        (Work.Tubular.normalBundle E ND).TotalSpace)).comp (nfIncl E x) q)
        ∈ Work.Thom.zeroComplement (tautologicalBundle k 10) :=
    fun q hq => hgm _ (hcomp1 q hq)
  have hcomp3 : ∀ q ∈ nfPunct E x,
      ((frameEvalMap k (datumFrame E ND x)).comp (nfRead E ND x)) q
        ∈ Work.Thom.zeroComplement (tautologicalBundle k 10) :=
    fun q hq => frameEvalMap_mem k (datumFrame E ND x) _ (hΨreq q hq)
  -- step 1: `nfRes (gtdUWith U)` is the pullback of `U.τ` along the composite
  have hstep1 : nfRes E x k (gtdUWith E ND G hgm U)
      = (Work.Thom.relCohMap
          (G.comp (((Work.Tubular.eucNormalHomeomorph E ND).symm : C(Work.Tubular.NormalTotal E,
            (Work.Tubular.normalBundle E ND).TotalSpace)).comp (nfIncl E x)))
          (nfPunct E x) (Work.Thom.zeroComplement (tautologicalBundle k 10)) hcomp2 ℤ k).hom
        U.τ := by
    show (Work.Thom.relCohMap (nfIncl E x) (nfPunct E x) (Work.Tubular.normalNonzero E)
        (nfIncl_mem E x) ℤ k).hom
        ((Work.Thom.relCohMap ((Work.Tubular.eucNormalHomeomorph E ND).symm :
            C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace))
          (Work.Tubular.normalNonzero E) (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
          (gtd_mem E ND) ℤ k).hom
        ((Work.Thom.relCohMap G (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
          (Work.Thom.zeroComplement (tautologicalBundle k 10)) hgm ℤ k).hom U.τ))
      = _
    rw [Work.Thom.relCohMap_compA_apply (A := nfPunct E x)
      (B := Work.Tubular.normalNonzero E)
      (C := Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
      (f := nfIncl E x)
      (g := ((Work.Tubular.eucNormalHomeomorph E ND).symm : C(Work.Tubular.NormalTotal E,
        (Work.Tubular.normalBundle E ND).TotalSpace)))
      (nfIncl_mem E x) (gtd_mem E ND) (hcomp1) ℤ k _]
    exact Work.Thom.relCohMap_compA_apply (A := nfPunct E x)
      (B := Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
      (C := Work.Thom.zeroComplement (tautologicalBundle k 10))
      (f := ((Work.Tubular.eucNormalHomeomorph E ND).symm : C(Work.Tubular.NormalTotal E,
        (Work.Tubular.normalBundle E ND).TotalSpace)).comp (nfIncl E x))
      (g := G) (hcomp1) hgm (hcomp2) ℤ k _
  -- step 2: the composite map is the frame evaluation composed with the frame reading
  have hmap : G.comp (((Work.Tubular.eucNormalHomeomorph E ND).symm : C(Work.Tubular.NormalTotal E,
        (Work.Tubular.normalBundle E ND).TotalSpace)).comp (nfIncl E x))
      = (frameEvalMap k (datumFrame E ND x)).comp (nfRead E ND x) := by
    refine ContinuousMap.ext fun q => ?_
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
    show G ((Work.Tubular.eucNormalHomeomorph E ND).symm (nfIncl E x q))
      = frameEval k (datumFrame E ND x) (nfRead E ND x q)
    rw [show (Work.Tubular.eucNormalHomeomorph E ND).symm (nfIncl E x q)
      = Work.Tubular.normalToBundle E ND q.1 from
        gtdEucNormalHomeomorph_symm_apply E ND q.1]
    exact G_eq_frameEval E ND G hbp hvec x q
  -- step 3: replace the composite by the frame evaluation composed with the frame reading
  have hrepl : (Work.Thom.relCohMap
        (G.comp (((Work.Tubular.eucNormalHomeomorph E ND).symm : C(Work.Tubular.NormalTotal E,
          (Work.Tubular.normalBundle E ND).TotalSpace)).comp (nfIncl E x)))
        (nfPunct E x) (Work.Thom.zeroComplement (tautologicalBundle k 10)) hcomp2 ℤ k).hom U.τ
      = (Work.Thom.relCohMap ((frameEvalMap k (datumFrame E ND x)).comp (nfRead E ND x))
          (nfPunct E x) (Work.Thom.zeroComplement (tautologicalBundle k 10)) hcomp3 ℤ k).hom U.τ :=
    congrArg (fun (φ : Work.Thom.RelCoh ℤ k (tautologicalBundle k 10).TotalSpace
        (Work.Thom.zeroComplement (tautologicalBundle k 10)) ⟶
        Work.Thom.RelCoh ℤ k ↥(nfSet E x) (nfPunct E x)) => φ.hom U.τ)
      (Work.Thom.relCohMap_congrA (A := nfPunct E x)
        (B := Work.Thom.zeroComplement (tautologicalBundle k 10)) hmap hcomp2 hcomp3 ℤ k)
  -- step 4: functoriality of the pullback
  have hstep4 : (Work.Thom.relCohMap ((frameEvalMap k (datumFrame E ND x)).comp (nfRead E ND x))
        (nfPunct E x) (Work.Thom.zeroComplement (tautologicalBundle k 10)) hcomp3 ℤ k).hom U.τ
      = (Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x) (framePunct k)
          hΨreq ℤ k).hom
        ((Work.Thom.relCohMap (frameEvalMap k (datumFrame E ND x)) (framePunct k)
          (Work.Thom.zeroComplement (tautologicalBundle k 10))
          (frameEvalMap_mem k (datumFrame E ND x)) ℤ k).hom U.τ) :=
    (Work.Thom.relCohMap_compA_apply (A := nfPunct E x) (B := framePunct k)
      (C := Work.Thom.zeroComplement (tautologicalBundle k 10)) (f := nfRead E ND x)
      (g := frameEvalMap k (datumFrame E ND x)) hΨreq
      (frameEvalMap_mem k (datumFrame E ND x)) hcomp3 ℤ k U.τ).symm
  rw [hstep1, hrepl, hstep4]

end

end Work.ThomBordism
