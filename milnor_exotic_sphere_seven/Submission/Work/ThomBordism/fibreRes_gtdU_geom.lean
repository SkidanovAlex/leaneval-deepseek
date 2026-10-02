import Mathlib
import Submission.Work.ThomBordism.frameClassDefs
import Submission.Work.ThomBordism.frameClass_eq
import Submission.Work.ThomBordism.span_frameClass
import Submission.Work.ThomBordism.nfGenBasic
import Submission.Work.ThomBordism.nfRead_ne_zero
import Submission.Work.ThomBordism._gtd.P2
import Submission.Work.ThomBordism._gtd.P3
import Submission.Work.ThomBordism.gtdGaussCandidate
import Submission.Work.ThomBordism._gtd.P5
import Submission.Work.Thom.relCohMap_comp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibre restriction of `gtdU` is the frame reading of the tautological Thom class

The datum of the last mile is a Gauss/classifying map `G` of the normal bundle of an embedding
`E : V ↪ ℝ^{8+k}`, pinned by the two clauses

* `proj (G p) = padGaussFun E ND p.1` (`hbp`), and
* `evalVec (G p) = padEuc k 10 _ (NormalTotal.vec (bundleToNormal E ND p))` (`hvec`),

i.e. `G` is *the* map that sends a normal vector to the point of the tautological bundle over the
padded Gauss plane whose vector is the padded normal vector, read in the σ-corrected frame
`Gauss.gframe`.  Consequently, on the fibre of the normal bundle over `x`, the composite of `G` with
the Euclidean normal homeomorphism is exactly the frame evaluation `frameEval σ_x` of the frame
`σ_x := padGFrame E ND (indexAt x) x` (`Work.ThomBordism.datumFrame`), composed with the frame
reading `nfRead E ND x`.

Since `nfRes` is the pullback along the inclusion of that fibre and `gtdU` the pullback of the
tautological Thom class along `G`, functoriality of `relCohMap` gives

  `nfRes E x k (gtdU E ND G hgm) = (relCohMap (nfRead E ND x)).hom (frameClass k σ_x)`,

which is the geometric input of `Work.ThomBordism.fibreRes_gtdU_canonical`.
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

/-- **The frame of a datum at a point**: the padded σ-corrected normal frame of the normal data. -/
def datumFrame (E : PontryaginThom.EmbeddingData V (8 + k))
    (ND : PontryaginThom.NormalData V k E.e) (x : V.pt) : Stiefel k 10 :=
  ⟨Grassmann.padGFrame E ND (ND.D.indexAt x) x,
    Grassmann.padGFrame_orthonormal E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x)⟩

theorem datumFrame_val (E : PontryaginThom.EmbeddingData V (8 + k))
    (ND : PontryaginThom.NormalData V k E.e) (x : V.pt) :
    (datumFrame E ND x).1 = Grassmann.padGFrame E ND (ND.D.indexAt x) x := rfl

/-- The plane of the datum frame is the Gauss plane. -/
theorem ogMk_datumFrame (E : PontryaginThom.EmbeddingData V (8 + k))
    (ND : PontryaginThom.NormalData V k E.e) (x : V.pt) :
    ogMk k 10 (datumFrame E ND x) = Grassmann.padGaussFun E ND x := by
  rw [Grassmann.padGaussFun,
    Grassmann.padGaussStiefel_of_mem E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x)]
  rfl

/-- **The frame reading of the ambient normal vector reproduces the vector.** -/
theorem frameLI_datumFrame_nfRead (E : PontryaginThom.EmbeddingData V (8 + k))
    (ND : PontryaginThom.NormalData V k E.e) (x : V.pt) (q : ↥(nfSet E x)) :
    frameLI k (datumFrame E ND x) (nfRead E ND x q)
      = Work.PTGeometric.padEuc k 10 (by norm_num) (Work.Tubular.NormalTotal.vec q.1) := by
  have hspan : Work.Tubular.NormalTotal.vec q.1 ∈
      Submodule.span ℝ (Set.range (Gauss.gframe E ND (ND.D.indexAt x) x)) := by
    rw [Grassmann.span_gframe E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x)]
    have h := Work.Tubular.NormalTotal.vec_mem q.1
    rwa [show Work.Tubular.NormalTotal.proj q.1 = x from q.2] at h
  have hexp := sum_inner_smul_eq_self_of_orthonormal
    (Gauss.gframe E ND (ND.D.indexAt x) x)
    (Gauss.orthonormal_gframe E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x)) hspan
  have hcoe : ∀ j : Fin k,
      (nfRead E ND x q) j = inner ℝ (Gauss.gframe E ND (ND.D.indexAt x) x j)
        (Work.Tubular.NormalTotal.vec q.1) := by
    intro j
    show ((readFrame (Gauss.gframe E ND (ND.D.indexAt x) x)
      (Work.Tubular.NormalTotal.vec q.1)).ofLp) j = _
    rw [readFrame_apply]
    rfl
  rw [frameLI_apply, frameLM_apply]
  have hsum : ∑ j, (nfRead E ND x q) j •
        (datumFrame E ND x).1 j
      = ∑ j, inner ℝ (Gauss.gframe E ND (ND.D.indexAt x) x j)
          (Work.Tubular.NormalTotal.vec q.1) •
        Grassmann.padIsom k (Gauss.gframe E ND (ND.D.indexAt x) x j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcoe j]
    rfl
  rw [hsum]
  have hlin : ∑ j, inner ℝ (Gauss.gframe E ND (ND.D.indexAt x) x j)
        (Work.Tubular.NormalTotal.vec q.1) •
        Grassmann.padIsom k (Gauss.gframe E ND (ND.D.indexAt x) x j)
      = Grassmann.padIsom k (∑ j, inner ℝ (Gauss.gframe E ND (ND.D.indexAt x) x j)
          (Work.Tubular.NormalTotal.vec q.1) •
        Gauss.gframe E ND (ND.D.indexAt x) x j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
  rw [hlin, hexp, Grassmann.padIsom_apply]

end

end Work.ThomBordism

namespace Work.ThomBordism

open Work.ThomBordism.Grassmann
open Work.ThomBordism.PontryaginThom

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The classifying map of a datum is the frame evaluation on each fibre**, composed with the
frame reading: the two clauses `hbp` (plane) and `hvec` (vector) pin `G` to
`frameEval (datumFrame E ND x)` after the frame reading `nfRead E ND x`. -/
theorem G_eq_frameEval (E : PontryaginThom.EmbeddingData V (8 + k))
    (ND : PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (tautologicalBundle k 10).TotalSpace))
    (hbp : ∀ p, (tautologicalBundle k 10).proj (G p) = Grassmann.padGaussFun E ND p.1)
    (hvec : ∀ p, Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    (x : V.pt) (q : ↥(nfSet E x)) :
    G (Work.Tubular.normalToBundle E ND q.1)
      = frameEval k (datumFrame E ND x) (nfRead E ND x q) := by
  refine eq_of_proj_eq_of_evalVec_eq k 10 ?_ ?_
  · have h1 : VectorBundleCore.proj (tautologicalBundle k 10)
        (G (Work.Tubular.normalToBundle E ND q.1)) = Grassmann.padGaussFun E ND x := by
      rw [hbp (Work.Tubular.normalToBundle E ND q.1)]
      exact congrArg (Grassmann.padGaussFun E ND)
        (show (Work.Tubular.normalToBundle E ND q.1).proj = x from q.2)
    have h2 : VectorBundleCore.proj (tautologicalBundle k 10)
        (frameEval k (datumFrame E ND x) (nfRead E ND x q)) = Grassmann.padGaussFun E ND x := by
      rw [show VectorBundleCore.proj (tautologicalBundle k 10)
          (frameEval k (datumFrame E ND x) (nfRead E ND x q))
          = (frameEval k (datumFrame E ND x) (nfRead E ND x q)).1 from rfl,
        frameEval_base, ogMk_datumFrame]
    exact h1.trans h2.symm
  · rw [hvec (Work.Tubular.normalToBundle E ND q.1), evalVec_frameEval]
    rw [show Work.Tubular.bundleToNormal E ND (Work.Tubular.normalToBundle E ND q.1) = q.1
      from Work.Tubular.bundleToNormal_normalToBundle E ND q.1]
    exact (frameLI_datumFrame_nfRead E ND x q).symm

end

end Work.ThomBordism

namespace Work.ThomBordism

open Work.ThomBordism.Grassmann
open Work.ThomBordism.PontryaginThom

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The fibre restriction of `gtdU` is the frame reading of the tautological Thom class.**  For a
datum pinned by the plane and vector clauses, the pullback of `gtdU` to the fibre pair of the normal
bundle over `x` is the pullback of `Work.ThomBordism.frameClass` along the frame reading
`nfRead E ND x` — i.e. `gtdU` restricts to the frame reading of the tautological Thom class in the
σ-corrected frame. -/
theorem nfRes_gtdU_eq_frameClass (hk : 1 ≤ k)
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
    (x : V.pt) :
    nfRes E x k (gtdU E ND G hgm)
      = (Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x) (framePunct k)
          (fun p hp => (mem_framePunct k _).mpr (nfRead_ne_zero hk E ND x p hp)) ℤ k).hom
        (frameClass k (datumFrame E ND x)) := by
  classical
  have hΨreq : ∀ p ∈ nfPunct E x, nfRead E ND x p ∈ framePunct k :=
    fun p hp => (mem_framePunct k _).mpr (nfRead_ne_zero hk E ND x p hp)
  -- the pair conditions of the composite
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
  -- step 1: `nfRes (gtdU)` is the pullback of `τ` along the composite
  have hstep1 : nfRes E x k (gtdU E ND G hgm)
      = (Work.Thom.relCohMap
          (G.comp (((Work.Tubular.eucNormalHomeomorph E ND).symm : C(Work.Tubular.NormalTotal E,
            (Work.Tubular.normalBundle E ND).TotalSpace)).comp (nfIncl E x)))
          (nfPunct E x) (Work.Thom.zeroComplement (tautologicalBundle k 10)) hcomp2 ℤ k).hom
        (tautologicalThomClass k 10).τ := by
    rw [nfRes, gtdU]
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
        (nfPunct E x) (Work.Thom.zeroComplement (tautologicalBundle k 10)) hcomp2 ℤ k).hom
        (tautologicalThomClass k 10).τ
      = (Work.Thom.relCohMap ((frameEvalMap k (datumFrame E ND x)).comp (nfRead E ND x))
          (nfPunct E x) (Work.Thom.zeroComplement (tautologicalBundle k 10)) hcomp3 ℤ k).hom
        (tautologicalThomClass k 10).τ :=
    congrArg (fun (φ : Work.Thom.RelCoh ℤ k (tautologicalBundle k 10).TotalSpace
        (Work.Thom.zeroComplement (tautologicalBundle k 10)) ⟶
        Work.Thom.RelCoh ℤ k ↥(nfSet E x) (nfPunct E x)) =>
          φ.hom (tautologicalThomClass k 10).τ)
      (Work.Thom.relCohMap_congrA (A := nfPunct E x)
        (B := Work.Thom.zeroComplement (tautologicalBundle k 10)) hmap hcomp2 hcomp3 ℤ k)
  -- step 4: functoriality of the pullback
  have hstep4 : (Work.Thom.relCohMap ((frameEvalMap k (datumFrame E ND x)).comp (nfRead E ND x))
        (nfPunct E x) (Work.Thom.zeroComplement (tautologicalBundle k 10)) hcomp3 ℤ k).hom
        (tautologicalThomClass k 10).τ
      = (Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x) (framePunct k)
          hΨreq ℤ k).hom (frameClass k (datumFrame E ND x)) :=
    (Work.Thom.relCohMap_compA_apply (A := nfPunct E x) (B := framePunct k)
      (C := Work.Thom.zeroComplement (tautologicalBundle k 10)) (f := nfRead E ND x)
      (g := frameEvalMap k (datumFrame E ND x)) hΨreq
      (frameEvalMap_mem k (datumFrame E ND x)) hcomp3 ℤ k
      (tautologicalThomClass k 10).τ).symm
  rw [hstep1, hrepl, hstep4]

end

end Work.ThomBordism
