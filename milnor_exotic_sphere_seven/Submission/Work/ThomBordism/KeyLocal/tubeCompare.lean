import Mathlib
import Submission.Work.ThomBordism.KeyLocal.chartCompare
import Submission.Work.ThomBordism.KeyLocal.tubeCompareDefs
import Submission.Work.ThomBordism.KeyLocal.tubePointRelative
import Submission.Work.ThomBordism.KeyLocal.perDatum

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
# The last mile, assembled

Two wrappers putting the pieces together:

* `chartCompareAll` is `ChartCompareAll k hk`, produced by the assembly `chartCompare` of the four
  geometric pieces (`tubeTanReadingO`, `tubeNormReading`, `chartProductFormula`, `gmTubeProduct`);
* `TubeCompareAll k hk` is the clean per-datum tube comparison (`keyLocalProof.lean`'s
  `TubeCompare`), obtained from `ChartCompareAll` by the pair-mismatch step `tubePointRelative` and
  then, datum by datum and class by class, by `perDatum` (which uses the uniqueness of the
  admissible class).
-/
namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.FrameSigns

/-- **The chart-level comparison**, as a `Prop` (the conclusion of `chartCompare`). -/
theorem chartCompareAll (k : ℕ) (hk : 1 ≤ k) : ChartCompareAll k hk := by
  intro V _inst E ND G hgm hbp hvec ε C i x hx o ho
  exact chartCompare (V := V) hk E ND G hgm hbp hvec C i x hx o ho

/-- **The per-datum tube comparison**: the hypothesis of `keyLocalProof.lean`'s
`keyLocal_of_tubeComparison`, with a single `s = tauSign` over all data. -/
def TubeCompareAll (k : ℕ) (hk : 1 ≤ k) : Prop :=
  ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
      (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
        = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
      (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
      (w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E))),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
          ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1 →
      (Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C)
          (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
          (fun y hy => hy) ℤ (8 + k)).hom
        (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) 8 k w
          (Work.ThomBordism.gtdUWith E ND G hgm
            (Work.Thom.realThomClassOf hk
              (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.tautologicalBundle_horiO k))))
        = s • Work.ThomBordism.ambientStandardClass E C x

/-- **`TubeCompareAll` holds.** -/
theorem tubeCompareAll (k : ℕ) (hk : 1 ≤ k) : TubeCompareAll k hk := by
  refine ⟨tauSign, tauSign_eq_one_or_neg_one, ?_⟩
  intro V _inst E ND G hgm hbp hvec ε C x w hw
  exact perDatum (V := V) hk (tubePointRelative k hk (chartCompareAll k hk))
    E ND G hgm hbp hvec C x w hw

end

end Work.ThomBordism.KeyLocal
