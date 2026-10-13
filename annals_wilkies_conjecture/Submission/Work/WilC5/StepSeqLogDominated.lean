import Mathlib
import Submission.Work.WilC5.LogDominatedOfInfinite
import Submission.Work.WilC5.StepSeq
import Submission.Work.WilC5.StepSeqUnbounded
import Submission.Work.WilC5.stdPart
import Submission.Work.WilC5.S4ExpG.Glue
import Submission.Work.WilC5.Reduct
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.LRcReduct

set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- **The `LogDominated` invariant of the sequence of vdDMM Lemma 4.4.**  The elements of a
`StepSeq` which is `Unbounded` (each `xₙ` dominates every real constant, i.e. is infinite) satisfy
the pointwise invariant `v(xₙ) < v(log xₙ)` used by the whole §4 iteration
(`Work.WilC5.StepSeq.LogDominated` is exactly the conjunction `VLe (xs n) (logFun (xs n))` and
`¬ VLe (logFun (xs n)) (xs n)` for every `n`).

The proof is two steps: `Unbounded S` at `n` and `N := N` gives `realConst K N ≤ xₙ` and
`¬ xₙ ≤ realConst K N`, hence `¬ IsFiniteVal (xₙ)` (using `realConst_natCast`, i.e.
`realConst K (N:ℝ) = (N:K)`); then `Work.WilC5.LogDominatedOfInfinite` applies at `xₙ`, whose
positivity is `S.hpos n` (`Work.WilC5.S4ExpF.leE_zero_iff`).  No sequence-specific mathematics is
involved: the `(log x)^k < x` input is `Work.WilC5.LogFunPowLtSelf`. -/
theorem StepSeqLogDominated
    {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    {B : WilkiesDesign.CG.LRc.Substructure K} (S : Work.WilC5.StepSeq B)
    (hunb : Work.WilC5.StepSeq.Unbounded S) :
    Work.WilC5.StepSeq.LogDominated S := by
  have hTE : K ⊨ WilkiesDesign.CG.TE := inferInstance
  intro n
  have hxpos : 0 < S.xs n :=
    (Work.WilC5.S4ExpF.leE_zero_iff hTE hadd hleneg (S.xs n)).mp (S.hpos n)
  have hxinf : ¬ Work.WilC5.IsFiniteVal (S.xs n) := by
    -- ## The instance bookkeeping: pin the `LRc`-structure so that it is the one at which
    -- `realConst_natCast` is stated, and transport across `reductStruct_eq_withConstants`.
    let myCR : FirstOrder.Ring.CompatibleRing K :=
      { toStructure := @Work.WilC5.lrcRingReduct K (Work.WilC5.instStructureLRcOfLEc K)
        funMap_add := fun ys => by
          rw [Work.WilC5.lrcRingReduct_funMap]
          have hys : ys = ![ys 0, ys 1] := by funext i; fin_cases i <;> rfl
          rw [hys]; exact hadd _ _
        funMap_mul := fun ys => by
          rw [Work.WilC5.lrcRingReduct_funMap]
          have hys : ys = ![ys 0, ys 1] := by funext i; fin_cases i <;> rfl
          rw [hys]; exact hmul _ _
        funMap_neg := fun ys => by
          rw [Work.WilC5.lrcRingReduct_funMap]
          have hys : ys = ![ys 0] := by funext i; fin_cases i <;> rfl
          rw [hys]; exact Work.WilC5.S4ExpF.negE_eq_neg hTE hadd _
        funMap_zero := fun ys => by
          rw [Work.WilC5.lrcRingReduct_funMap]
          rw [show ys = default from Subsingleton.elim _ _]
          exact Work.WilC5.S4ExpF.zeroE_eq_zero hTE hadd
        funMap_one := fun ys => by
          rw [Work.WilC5.lrcRingReduct_funMap]
          rw [show ys = default from Subsingleton.elim _ _]
          exact hone }
    letI : FirstOrder.Ring.CompatibleRing K := myCR
    letI hRX : WilkiesDesign.CG.rexpL.Structure K :=
      @Work.WilC5.lrcRexpReduct K (Work.WilC5.reductStruct K)
    letI hCT : (FirstOrder.Language.constantsOn ℝ).Structure K :=
      @Work.WilC5.lrcConstReduct K (Work.WilC5.reductStruct K)
    have hstruct : (Work.WilC5.reductStruct K : LRc.Structure K) = LR.withConstantsStructure ℝ :=
      Work.WilC5.reductStruct_eq_withConstants (M := K)
    have hTR : @FirstOrder.Language.Theory.Model LRc K (LR.withConstantsStructure ℝ)
        WilkiesDesign.CG.TR :=
      hstruct ▸ (Work.WilC5.reduct_model_TR K hTE)
    have hnatC : ∀ N : ℕ,
        @Work.WilC5.realConst K (LR.withConstantsStructure ℝ) (N : ℝ) = (N : K) :=
      fun N => @Work.WilC5.realConst_natCast K _ _ _ _ _ _ hTR N
    have hnatR : ∀ N : ℕ,
        @Work.WilC5.realConst K (Work.WilC5.reductStruct K) (N : ℝ) = (N : K) :=
      fun N => (Work.WilC5.realConst_reduct_synth (M := K) N).trans (hnatC N)
    -- ## The mathematics
    rintro ⟨M, hM⟩
    rw [abs_of_pos hxpos] at hM
    have hM' : S.xs n ≤ ((M + 1 : ℕ) : K) := by
      rw [show ((M : ℕ) : K) + 1 = ((M + 1 : ℕ) : K) from by push_cast; ring] at hM
      exact hM
    obtain ⟨-, h2⟩ := hunb n (M + 1)
    have h3 : ¬ (S.xs n ≤ (Work.WilC5.realConst K ((M + 1 : ℕ) : ℝ))) :=
      fun h => h2 ((hleneg _ _).mpr h)
    rw [hnatR (M + 1)] at h3
    exact h3 hM'
  exact Work.WilC5.LogDominatedOfInfinite hrexp hadd hmul hone hleneg hxpos hxinf

end Work.WilC5
