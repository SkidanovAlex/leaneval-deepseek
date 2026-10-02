import Mathlib
import Submission.Work.ThomBordism.stdHalfBallBoundarySign
import Submission.Work.ThomBordism.stdHalfBallOrientExists
import Submission.Work.ThomBordism.locClass_hPairDelta_eq_of_localClass_eq

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

open CategoryTheory
open scoped Manifold
open Work.PTGeometric.HOF

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The model equation (with a universal constant `c`, uniformly in all the data).**

Route: `stdHalfBallOrientExists` produces a class `w₀` whose local classes are the prescribed
`stdIntOrient` at *every* interior point; `stdHalfBallBoundarySign` gives the equation for `w₀` with
a single `c ∈ {±1}`, uniformly in the boundary point `z`; and
`locClass_hPairDelta_eq_of_localClass_eq` (applied to the given geometric hypotheses) shows that any
`w` whose localisation at `x₀` agrees with `w₀`'s has the same boundary local class. -/
theorem bsu_modelEquation (n : ℕ) (hn : 1 ≤ n) :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
      ∀ (cs : ChartedSpace (EuclideanHalfSpace (n + 1)) ↥(stdHalfBall (n + 1)))
        (im : @IsManifold ℝ _ (Euc (n + 1)) _ _ (EuclideanHalfSpace (n + 1)) _ (𝓡∂ (n + 1)) 1
          ↥(stdHalfBall (n + 1)) _ cs)
        [CompactSpace ↥(stdHalfBall (n + 1))] [T2Space ↥(stdHalfBall (n + 1))]
        (hb : @ModelWithCorners.boundary ℝ _ (Euc (n + 1)) _ _ (EuclideanHalfSpace (n + 1)) _
          (𝓡∂ (n + 1)) ↥(stdHalfBall (n + 1)) _ cs = stdHalfBallBdry (n + 1))
        (z : ↥(stdHalfBall (n + 1))) (hz : z ∈ stdHalfBallBdry (n + 1))
        (hzsrc : (⟨z, hz⟩ : ↥(stdHalfBallBdry (n + 1))) ∈ (stdFlatChart n).source)
        (x₀ : ↥(stdHalfBall (n + 1))) (hx₀src : x₀ ∈ (stdIntChart (n + 1)).source)
        (hx₀int : x₀ ∉ stdHalfBallBdry (n + 1))
        {r : ℝ} (hr : 0 < r)
        (hgood : @Work.Orient.halfBallGood (n + 1) _ (TopCat.of ↥(stdHalfBall (n + 1))) cs z r)
        (hx₀ : x₀ ∈ @Work.Orient.halfBallPiece (n + 1) _ (TopCat.of ↥(stdHalfBall (n + 1))) cs z r)
        (w : (Work.Cohomology.relChains (TopCat.of ↥(stdHalfBall (n + 1)))
          (stdHalfBallBdry (n + 1))).homology (n + 1))
        (hw : (HomologicalComplex.homologyMap
              (Work.Orient.relPunct (TopCat.of ↥(stdHalfBall (n + 1))) (stdHalfBallBdry (n + 1))
                x₀ hx₀int) (n + 1)).hom w
            = chartTr (e := stdIntChart (n + 1)) x₀ hx₀src
                (eucFam (n + 1) (by omega) ((stdIntChart (n + 1)) x₀))),
      Work.Orient.locClass (TopCat.of ↥(stdHalfBallBdry (n + 1))) n
          ((Work.Cohomology.hPairδ (TopCat.of ↥(stdHalfBall (n + 1)))
            (stdHalfBallBdry (n + 1)) n).hom w) ⟨z, hz⟩
        = c • chartTr (W := TopCat.of ↥(stdHalfBallBdry (n + 1))) (stdFlatChart n)
            ⟨z, hz⟩ hzsrc (eucFam n hn ((stdFlatChart n) ⟨z, hz⟩)) := by
  classical
  obtain ⟨c, hc, hsign⟩ := stdHalfBallBoundarySign n hn
  refine ⟨c, hc, ?_⟩
  intro cs im hcpt ht2 hb z hz hzsrc x₀ hx₀src hx₀int _ hr hgood hx₀ w hw
  letI : ChartedSpace (EuclideanHalfSpace (n + 1)) ↥(stdHalfBall (n + 1)) := cs
  haveI : IsManifold (𝓡∂ (n + 1)) 1 ↥(stdHalfBall (n + 1)) := im
  haveI : CompactSpace ↥(stdHalfBall (n + 1)) := hcpt
  haveI : T2Space ↥(stdHalfBall (n + 1)) := ht2
  obtain ⟨w₀, hw₀P, _hw₀F⟩ := stdHalfBallOrientExists n hn
  have hloc : (HomologicalComplex.homologyMap
        (Work.Orient.relPunct (TopCat.of ↥(stdHalfBall (n + 1))) (stdHalfBallBdry (n + 1))
          x₀ hx₀int) (n + 1)).hom w
      = (HomologicalComplex.homologyMap
        (Work.Orient.relPunct (TopCat.of ↥(stdHalfBall (n + 1))) (stdHalfBallBdry (n + 1))
          x₀ hx₀int) (n + 1)).hom w₀ :=
    hw.trans (hw₀P x₀ hx₀src).symm
  have h1 := locClass_hPairDelta_eq_of_localClass_eq (W := TopCat.of ↥(stdHalfBall (n + 1)))
    (B := stdHalfBallBdry (n + 1)) (hB := hb) (y := z) (hy := hz) (hr := hr)
    (hgood := hgood) (x₀ := x₀) (hx₀ := hx₀) (hx₀int := hx₀int) (w := w) (w' := w₀) (h := hloc)
  rw [h1]
  exact hsign w₀ hw₀P ⟨z, hz⟩ hzsrc

end Work.ThomBordism
