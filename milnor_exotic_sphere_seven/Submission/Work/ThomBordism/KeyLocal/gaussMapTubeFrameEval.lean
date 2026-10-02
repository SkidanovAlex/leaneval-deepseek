import Mathlib
import Submission.Work.ThomBordism.KeyLocal.tubeNormDefs
import Submission.Work.ThomBordism.fibreRes_gtdU_geom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The tube-level frame evaluation of the classifying map

The tautological bundle `γ = tautologicalBundle k 10` over the oriented Grassmannian is pinned by
its *oriented plane* `proj` and its evaluated vector `evalVec`
(`Work.ThomBordism.eq_of_proj_eq_of_evalVec_eq`).  `Work.ThomBordism.G_eq_frameEval` uses this to
show that a Gauss map `G` of the normal bundle, pinned by the clauses `hbp` (plane) and `hvec`
(vector), is `frameEval k (datumFrame E ND x) (nfRead E ND x ·)` on each fibre of the normal
bundle, where `datumFrame` is the padded σ-corrected frame of the *preferred* chart `indexAt x`.

This file is the tube-level companion of that statement: on the part of the tube lying over an
*arbitrary* chart `i` of the normal datum (`tubeBaseSet E C ND i`), the same pinned map `G` is
`frameEval` of the chart-`i` frame `tubeFrame E C ND i` in the coordinate reading `tubeNormCoord`
of the normal vector.  The two pinning clauses are the same ones; the only new ingredient is the
elementary frame identity `frameLI_padGFrame_readFrame` (the padded frame `padGFrame` applied to
the coordinate reading of the unpadded frame `gframe` reproduces the padded vector), whose
preferred-chart instance is `Work.ThomBordism.frameLI_datumFrame_nfRead`.
-/

namespace Work.ThomBordism.KeyLocal

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.Grassmann

noncomputable section

/-- **The frame reading of a normal vector in the padded σ-corrected frame.**  For a chart `i` of
the normal datum (in whose base set `x` lies) and a normal vector `w` at `x`, the padded frame
`padGFrame E ND i x` applied to the coordinates of `w` in the unpadded frame `gframe E ND i x`
gives the padded vector `padEuc k 10 w`.  This is the chart-`i` version of
`Work.ThomBordism.frameLI_datumFrame_nfRead`. -/
theorem frameLI_padGFrame_readFrame {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (i : CoverIdx V k)
    {x : V.pt} (hx : x ∈ ND.D.baseSet i) (w : Work.Tubular.Euc (8 + k))
    (hw : w ∈ normalSpace E x) :
    Work.ThomBordism.frameLI k
        ⟨padGFrame E ND i x, padGFrame_orthonormal E ND i hx⟩
        (Work.ThomBordism.readFrame (Work.ThomBordism.Gauss.gframe E ND i x) w)
      = Work.PTGeometric.padEuc k 10 (by norm_num) w := by
  have hspan : w ∈ Submodule.span ℝ (Set.range (Work.ThomBordism.Gauss.gframe E ND i x)) := by
    rw [span_gframe E ND i hx]; exact hw
  have hexp := Work.ThomBordism.sum_inner_smul_eq_self_of_orthonormal
    (Work.ThomBordism.Gauss.gframe E ND i x)
    (Work.ThomBordism.Gauss.orthonormal_gframe E ND i hx) hspan
  have hcoe : ∀ j : Fin k,
      (Work.ThomBordism.readFrame (Work.ThomBordism.Gauss.gframe E ND i x) w) j
        = inner ℝ (Work.ThomBordism.Gauss.gframe E ND i x j) w := by
    intro j
    rw [Work.ThomBordism.readFrame_apply]
    rfl
  rw [Work.ThomBordism.frameLI_apply, Work.ThomBordism.frameLM_apply]
  have hsum : ∑ j, (Work.ThomBordism.readFrame (Work.ThomBordism.Gauss.gframe E ND i x) w) j •
        (⟨padGFrame E ND i x, padGFrame_orthonormal E ND i hx⟩ : Stiefel k 10).1 j
      = ∑ j, inner ℝ (Work.ThomBordism.Gauss.gframe E ND i x j) w •
        padIsom k (Work.ThomBordism.Gauss.gframe E ND i x j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcoe j]
    rfl
  rw [hsum]
  have hlin : ∑ j, inner ℝ (Work.ThomBordism.Gauss.gframe E ND i x j) w •
        padIsom k (Work.ThomBordism.Gauss.gframe E ND i x j)
      = padIsom k (∑ j, inner ℝ (Work.ThomBordism.Gauss.gframe E ND i x j) w •
          Work.ThomBordism.Gauss.gframe E ND i x j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
  rw [hlin, hexp, padIsom_apply]

theorem gaussMapTubeFrameEval {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (i : Work.ThomBordism.PontryaginThom.CoverIdx V k)
    (y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i)) :
    G (Work.Tubular.normalToBundle E ND (C.inv y.1.1))
      = Work.ThomBordism.frameEval k (Work.ThomBordism.KeyLocal.tubeFrame E C ND i y)
          (Work.ThomBordism.KeyLocal.tubeNormCoord E C ND i y) := by
  have key : Work.ThomBordism.frameLI k (Work.ThomBordism.KeyLocal.tubeFrame E C ND i y)
      (Work.ThomBordism.KeyLocal.tubeNormCoord E C ND i y)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (C.inv y.1.1)) :=
    frameLI_padGFrame_readFrame (x := Work.Tubular.NormalTotal.proj (C.inv y.1.1)) E ND i y.2
      (Work.Tubular.NormalTotal.vec (C.inv y.1.1))
      (Work.Tubular.NormalTotal.vec_mem (C.inv y.1.1))
  refine Work.ThomBordism.eq_of_proj_eq_of_evalVec_eq k 10 ?_ ?_
  · have h1 : (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj
        (G (Work.Tubular.normalToBundle E ND (C.inv y.1.1)))
        = Work.ThomBordism.Grassmann.padGaussFun E ND (C.inv y.1.1).proj :=
      hbp (Work.Tubular.normalToBundle E ND (C.inv y.1.1))
    have h2 : (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj
        (Work.ThomBordism.frameEval k (Work.ThomBordism.KeyLocal.tubeFrame E C ND i y)
          (Work.ThomBordism.KeyLocal.tubeNormCoord E C ND i y))
        = Work.ThomBordism.Grassmann.padGaussFun E ND (C.inv y.1.1).proj := by
      rw [show (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj
          (Work.ThomBordism.frameEval k (Work.ThomBordism.KeyLocal.tubeFrame E C ND i y)
            (Work.ThomBordism.KeyLocal.tubeNormCoord E C ND i y))
          = (Work.ThomBordism.frameEval k (Work.ThomBordism.KeyLocal.tubeFrame E C ND i y)
            (Work.ThomBordism.KeyLocal.tubeNormCoord E C ND i y)).1 from rfl,
        Work.ThomBordism.frameEval_base, Work.ThomBordism.KeyLocal.ogMk_tubeFrame]
    exact h1.trans h2.symm
  · rw [hvec (Work.Tubular.normalToBundle E ND (C.inv y.1.1)),
      Work.ThomBordism.evalVec_frameEval]
    rw [Work.Tubular.bundleToNormal_normalToBundle E ND (C.inv y.1.1)]
    exact key.symm

end

end Work.ThomBordism.KeyLocal
