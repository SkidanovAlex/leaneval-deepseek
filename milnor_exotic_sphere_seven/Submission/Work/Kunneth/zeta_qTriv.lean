import Mathlib
import Submission.Work.Kunneth.zetaBridgeDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Kunneth

/-!
# The bridge `qTriv^*(ζ(ε^m over pt)) = ζ(ε^m over B)`

Let `Z_B = ε^m over B` be the trivial complex rank-`m` bundle over `B` and `Z_pt = ε^m over PUnit`
the same bundle over the one-point space; `Work.Kunneth.qTriv m B : P(Z_B) → P(Z_pt)` is the
continuous map sending the class of a punctured vector to the class of its *fibre coordinate*.

The tautological line bundle of `P(Z_B)` is the pullback of the tautological line bundle of
`P(Z_pt)` along `qTriv`, and consequently `ζ = c₁(ℓ)` pulls back:

`qTriv^*(ζ(ε^m over pt)) = ζ(ε^m over B)`.

The proof produces the equality of gluing data

`bundleComap (tautLine Z_pt) (qTriv m B) = tautLine Z_B`

through `Work.Thom.bundleCore_ext`, comparing the three structural fields:

* the charts: both are "the `k`-th fibre coordinate is non-zero";
* the index maps: two `Classical.choose`s over predicates that are equal by the chart comparison;
* the transition functions: both are the ratios of the fibre coordinates, which agree because
  `qTriv` sends a vector to itself viewed as a fibre coordinate.

-/

theorem zeta_qTriv (m : ℕ) (B : Type) [TopologicalSpace B] :
    (Work.Thom.CohMap (Work.Kunneth.qTriv m B) ℤ 2).hom
        (Work.LerayHirsch.zeta (Work.LerayHirsch.trivCore m))
      = Work.LerayHirsch.zeta
          (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit) := by
  -- The chart coordinate of the trivial bundle over `B` is the fibre coordinate.
  have hchart : ∀ (i : PUnit)
      (p : ↥(Work.Thom.zeroComplement (Work.Thom.realification
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit)))),
      Work.LerayHirsch.chartCoord
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit) i p
      = (show EuclideanSpace ℂ (Fin m) from p.1.2) := by
    intro i p
    rw [Work.LerayHirsch.chartCoord_def]
    rfl
  -- **(1)** `qTriv` pulls the charts of `ℓ(ε^m over pt)` back to the charts of `ℓ(ε^m over B)`.
  have hbase : ∀ (ik : PUnit × Fin m)
      (x : Work.LerayHirsch.ProjSpace
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit)),
      Work.Kunneth.qTriv m B x ∈
          Work.LerayHirsch.tautBaseSetProj (Work.LerayHirsch.trivCore m) ik ↔
        x ∈ Work.LerayHirsch.tautBaseSetProj
          (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit) ik := by
    intro ik x
    obtain ⟨p, rfl⟩ := Work.LerayHirsch.surjective_mkProj _ x
    rw [Work.Kunneth.qTriv_mkProj]
    rw [Work.LerayHirsch.mem_tautBaseSetProj_mk, Work.LerayHirsch.mem_tautBaseSetProj_mk]
    rw [Work.LerayHirsch.mem_tautBaseSet, Work.LerayHirsch.mem_tautBaseSet]
    simp only [Work.LerayHirsch.chartCoord_trivial]
    rw [hchart]
    constructor <;> rintro ⟨-, h⟩ <;> exact ⟨Set.mem_univ _, h⟩
  -- **(2)** The transition functions agree: both are ratios of the (equal) fibre coordinates.
  have hcoord : ∀ (ik jl : PUnit × Fin m)
      (x : Work.LerayHirsch.ProjSpace
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit)),
      Work.LerayHirsch.tautCoeffLift (Work.LerayHirsch.trivCore m) ik jl
          (Work.Kunneth.qTriv m B x)
        = Work.LerayHirsch.tautCoeffLift
            (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit) ik jl x := by
    intro ik jl x
    obtain ⟨p, rfl⟩ := Work.LerayHirsch.surjective_mkProj _ x
    rw [Work.Kunneth.qTriv_mkProj]
    rw [Work.LerayHirsch.tautCoeffLift_mk, Work.LerayHirsch.tautCoeffLift_mk]
    rw [Work.LerayHirsch.tautCoeff, Work.LerayHirsch.tautCoeff]
    simp only [Work.LerayHirsch.chartCoord_trivial, hchart]
  -- **(3)** The index maps agree: two `Classical.choose`s over predicates equal by `(1)`.
  have hindex : ∀ (x : Work.LerayHirsch.ProjSpace
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit)),
      (Work.LerayHirsch.tautLine (Work.LerayHirsch.trivCore m)).indexAt
          (Work.Kunneth.qTriv m B x)
        = (Work.LerayHirsch.tautLine
            (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit)).indexAt x := by
    intro x
    change Classical.choose (Work.LerayHirsch.exists_mem_tautBaseSetProj
        (Work.LerayHirsch.trivCore m) (Work.Kunneth.qTriv m B x))
      = Classical.choose (Work.LerayHirsch.exists_mem_tautBaseSetProj
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit) x)
    have hpred : (fun ik => Work.Kunneth.qTriv m B x ∈
          Work.LerayHirsch.tautBaseSetProj (Work.LerayHirsch.trivCore m) ik)
        = (fun ik => x ∈ Work.LerayHirsch.tautBaseSetProj
          (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit) ik) :=
      funext fun ik => propext (hbase ik x)
    have hL := Work.LerayHirsch.exists_mem_tautBaseSetProj
      (Work.LerayHirsch.trivCore m) (Work.Kunneth.qTriv m B x)
    have hR := Work.LerayHirsch.exists_mem_tautBaseSetProj
      (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit) x
    calc Classical.choose hL = Classical.choose (hpred ▸ hL) :=
          Classical.choose.congr_simp hpred hL
      _ = Classical.choose hR := congrArg Classical.choose (Subsingleton.elim _ _)
  -- The tautological line bundle is the pullback of the point-bundle's one.
  have hcore : Work.Thom.bundleComap (Work.LerayHirsch.tautLine (Work.LerayHirsch.trivCore m))
        (Work.Kunneth.qTriv m B)
      = Work.LerayHirsch.tautLine
          (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit) := by
    refine Work.Thom.bundleCore_ext ?_ ?_ ?_
    · funext ik
      rw [Work.Thom.bundleComap_baseSet, Work.LerayHirsch.tautLine_baseSet,
        Work.LerayHirsch.tautLine_baseSet]
      ext x
      exact hbase ik x
    · funext x
      rw [Work.Thom.bundleComap_indexAt]
      exact hindex x
    · intro ik jl x
      rw [Work.Thom.bundleComap_coordChange, Work.LerayHirsch.tautLine_coordChange,
        Work.LerayHirsch.tautLine_coordChange]
      apply ContinuousLinearMap.ext
      intro v
      rw [Work.LerayHirsch.tautCoeffCLM_apply, Work.LerayHirsch.tautCoeffCLM_apply,
        hcoord ik jl x]
  rw [Work.LerayHirsch.zeta_comap, hcore]
  rw [Work.LerayHirsch.zeta]

end Work.Kunneth
