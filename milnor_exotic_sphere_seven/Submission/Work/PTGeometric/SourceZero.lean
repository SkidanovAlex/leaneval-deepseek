import Submission.Work.PTGeometric.SourceFamily
import Submission.Work.PTGeometric.exists_tailBound_flatSourceHomotopy_notMem
import Submission.Work.PTGeometric.cubeToEuc_mem_openCube

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the zero set of the flat source homotopy of a family

The zero set of the null-homotopy `H` of a family's genuine collapse class, pulled back to the flat
source `EuclideanHalfSpace ((8+k)+1)`, is the null-bordism: the transverse preimage of the core
(G4/G5 of the blueprint).  This file proves that it is a **compact** closed subset of the source — the
input of the region construction of `SOURCE_PLAN.md` §2 (the defining function `ρ` needs its zero set
`W₀` compact and closed).

The two bounds are the ones of `SOURCE_PLAN.md` §1.3:

* off a tail ball the homotopy is the basepoint (`Work.PTGeometric.exists_tailBound_flatSourceHomotopy_notMem`,
  which uses the uniform continuity of the collapse of the cube boundary);
* for time `x 0 ≥ 1` the homotopy is at the far end, where it is the basepoint.

## Main definitions and results

* `Work.PTGeometric.notMem_core_t0`
* `Work.PTGeometric.sourceZeroSet`, `…_isClosed`, `…_isCompact`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology unitInterval
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

variable {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- **The zero set of the flat source homotopy of a family**: the preimage of the core, i.e. the
null-bordism of the pieces. -/
def sourceZeroSet (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    Set (EuclideanHalfSpace ((8 + k) + 1)) :=
  {x | flatSourceHomotopy8 (k := k) (familySource G m hpow).H (familySource G m hpow).φ x.1 ∈ G.core}

theorem isClosed_sourceZeroSet (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) : IsClosed (sourceZeroSet G m hpow) :=
  G.isClosed_core.preimage
    ((continuous_flatSourceHomotopy8 k (familySource G m hpow).H
      (familySource G m hpow).φ).comp continuous_subtype_val)

theorem isCompact_sourceZeroSet (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) : IsCompact (sourceZeroSet G m hpow) := by
  set S := familySource G m hpow with hS
  obtain ⟨R, hR⟩ := exists_tailBound_flatSourceHomotopy_notMem (k := k)
    (D := D) S.H S.φ
    (fun _ : Fin (k + 8) => 0) ⟨⟨0, by omega⟩, Or.inl rfl⟩
    S.bdry_eq
    (fun τ => S.bdry _ ⟨⟨0, by omega⟩, Or.inl rfl⟩ τ)
    G.core G.isClosed_core G.t0_notMem_core
  set K : Set (EuclideanSpace ℝ (Fin ((8 + k) + 1))) :=
    {y | 0 ≤ y 0 ∧ y 0 ≤ 1 ∧ ‖tail (k + 8) (srcCast k y)‖ ≤ R} with hK
  have hKcl : IsClosed K := by
    rw [hK]
    refine (isClosed_le continuous_const (continuous_coord0 k)).inter ?_
    refine (isClosed_le (continuous_coord0 k) continuous_const).inter ?_
    exact isClosed_le (((tailCLM (k + 8)).continuous.comp (srcCast k).continuous).norm)
      continuous_const
  have hKbdd : Bornology.IsBounded K := by
    refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := 0)
      (r := ‖(srcCastInv k).comp (consCLM (k + 8))‖ * max 1 R)) ?_
    intro y hy
    rw [hK] at hy
    rw [Metric.mem_closedBall, dist_zero_right]
    have hynorm : y = srcCastInv k (consCLM (k + 8) (y 0, tail (k + 8) (srcCast k y))) := by
      have h2 : (srcCast k y) 0 = y 0 := head_srcCast k y
      have h3 : tail (k + 8) (srcCast k y) = tailCLM (k + 8) (srcCast k y) := rfl
      rw [← h2, h3, consCLM_tail (k + 8) (srcCast k y), srcCastInv_srcCast]
    calc ‖y‖
        = ‖srcCastInv k (consCLM (k + 8) (y 0, tail (k + 8) (srcCast k y)))‖ :=
            congrArg (fun z => ‖z‖) hynorm
      _ ≤ ‖(srcCastInv k).comp (consCLM (k + 8))‖
            * ‖(y 0, tail (k + 8) (srcCast k y))‖ :=
            ContinuousLinearMap.le_opNorm ((srcCastInv k).comp (consCLM (k + 8))) _
      _ ≤ ‖(srcCastInv k).comp (consCLM (k + 8))‖ * max 1 R := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [Prod.norm_def]
          refine max_le (le_trans ?_ (le_max_left _ _)) (le_trans hy.2.2 (le_max_right _ _))
          rw [Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [hy.1], hy.2.1⟩
  have hKcomp : IsCompact K :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKcl, hKbdd⟩
  have hKcomp' : IsCompact ((Subtype.val :
      {y : EuclideanSpace ℝ (Fin ((8 + k) + 1)) // 0 ≤ y 0} →
        EuclideanSpace ℝ (Fin ((8 + k) + 1))) ⁻¹' K) := by
    have hcl : IsClosed {y : EuclideanSpace ℝ (Fin ((8 + k) + 1)) | 0 ≤ y 0} :=
      isClosed_le continuous_const (continuous_coord0 k)
    have hce : IsClosedEmbedding (Subtype.val :
        {y : EuclideanSpace ℝ (Fin ((8 + k) + 1)) // 0 ≤ y 0} →
          EuclideanSpace ℝ (Fin ((8 + k) + 1))) := hcl.isClosedEmbedding_subtypeVal
    exact hce.isCompact_preimage hKcomp
  refine IsCompact.of_isClosed_subset hKcomp' (isClosed_sourceZeroSet G m hpow) ?_
  intro x hx
  rw [hK]
  refine ⟨x.2, ?_, ?_⟩
  · by_contra hcon
    have h1 : 1 ≤ x.1 0 := le_of_lt (not_le.mp hcon)
    have hfar := flatSourceHomotopy8_eq_basepoint_of_one_le (k := k) S.H S.φ S.far (x := x.1) h1
    exact G.t0_notMem_core (hfar ▸ hx)
  · by_contra hcon
    exact hR (srcCast k x.1) (le_of_lt (not_le.mp hcon)) hx

end

end Work.PTGeometric
