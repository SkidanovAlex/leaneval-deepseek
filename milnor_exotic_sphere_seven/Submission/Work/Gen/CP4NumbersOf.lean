import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Gen.CP4Smooth8
import Submission.Work.Gen.CP4Numbers
import Submission.Work.SignatureBordism.Rationalisation
import Submission.Work.SignatureBordism.Numbers

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# AREA GEN — the numbers `(σ, p₁², p₂) = (1, 25, 10)` of `ℂP⁴` from its Chern classes

`Work.Gen.cp4Smooth8` fixes the fundamental class `c = Work.Projective.cp4C`.  For the final
assembly of `Work.Drive.Generators8` it is convenient to have the same manifold with an *arbitrary*
generating fundamental class `c`, so `Work.Gen.cp4Smooth8Of` mirrors `Work.Gen.cp2cp2Smooth8Of`.

`Work.Gen.cp4NumbersOf` is the **single point of contact** of AREA GEN with the characteristic-class
computation: given

* the two Chern-class identities for the **defined** tangent bundle,
  `Work.Thom.p1Tangent' ℂP⁴ = 5 • u²` and `Work.Thom.p2Tangent' ℂP⁴ = 10 • u⁴`
  (`u = Work.Gen.uCoh 4 = c₁(O(1))`), whose proofs are the Euler-sequence plus Whitney-sum
  computation (`Work.Gen.EulerChern` for the `stdTangentC` presentation, transported to
  `p1Tangent'`/`p2Tangent'` by `Work.Gen.TangentPresentation` and `Work.Gen.cp4ChernPresentation`),
* the normalisation `⟨u⁴, c⟩ = 1` for a generating fundamental class `c`
  (`Work.Gen.kronH_uFourth_pm_one` shows `⟨u⁴, c⟩ = ±1` for `c = cp4C`, so such a `c` is
  `±cp4C`),

it produces the numbers `σ = 1`, `p₁² = 25`, `p₂ = 10` and the dimension-`8` Hirzebruch identity
`45σ = 7p₂ - p₁²`, using only the ring facts `Submodule.span ℤ {u²} = ⊤`
(`Work.Gen.uSq_span`) and `⟨u², u²⟩ = ⟨u⁴, c⟩`.
-/

open scoped Manifold ContDiff

namespace Work.Gen

open Work.Projective

noncomputable section

/-- **`ℂP⁴` as a `Work.Drive.Smooth8` with a chosen generating fundamental class** (the analogue of
`Work.Gen.cp2cp2Smooth8Of`; `Work.Gen.cp4Smooth8` is the case `c = cp4C`). -/
noncomputable def cp4Smooth8Of
    (c : (Work.Cohomology.chainC ℤ cp4SSet).homology 8)
    (hc : Submodule.span ℤ {c} = ⊤) : Work.Drive.Smooth8 where
  pt := CP 4
  chartedSpace := cp4ChartedSpace
  isManifold := cp4IsManifold
  compactSpace := compactSpace_CP 4
  t2Space := t2Space_CP 4
  connectedSpace := connectedSpace_CP 4
  c := c
  c_generates := hc

/-- The underlying type of `Work.Gen.cp4Smooth8Of` is `ℂP⁴`. -/
theorem cp4Smooth8Of_pt (c : (Work.Cohomology.chainC ℤ cp4SSet).homology 8)
    (hc : Submodule.span ℤ {c} = ⊤) : (cp4Smooth8Of c hc).pt = (CP 4) := rfl

/-- **The numbers of `ℂP⁴` and the dimension-`8` Hirzebruch identity**, from the two Chern-class
identities of the defined tangent bundle together with the normalisation
`⟨u⁴, c⟩ = m = ±1` of the generating fundamental class.  All three numbers are homogeneous in `m`,
and the Hirzebruch identity `45σ = 7p₂ - p₁²` is insensitive to it (`45m = 70m - 25m`). -/
theorem cp4NumbersOf
    (h2 : Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 4)
      = (5 : ℤ) • uSq 4)
    (h4 : Work.Thom.p2Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 4)
      = (10 : ℤ) • uFourth 4)
    (c : (Work.Cohomology.chainC ℤ cp4SSet).homology 8)
    (hc : Submodule.span ℤ {c} = ⊤)
    {m : ℤ} (hm1 : m = 1 ∨ m = -1)
    (hcu : Work.Cohomology.kronH ℤ cp4SSet 8 (uFourth 4) c = m) :
    (cp4Smooth8Of c hc).sigma = m ∧ (cp4Smooth8Of c hc).p1Sq = 25 * m ∧
      (cp4Smooth8Of c hc).p2Num = 10 * m ∧ (cp4Smooth8Of c hc).Hirzebruch := by
  have hm : Work.SignatureBordism.interForm ℤ cp4SSet 4 4 c (uSq 4) (uSq 4) = m := by
    rw [Work.SignatureBordism.interForm_apply]
    exact hcu
  have hsig : (cp4Smooth8Of c hc).sigma = m :=
    Work.SignatureBordism.sigma_eq_of_span_singleton_of_unimodular 4 cp4SSet c (uSq 4)
      uSq_span hm hm1
  have hp1 : (cp4Smooth8Of c hc).p1Sq = 25 * m := by
    show Work.SignatureBordism.p₁SqNumber cp4SSet c
      (Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 4)) = 25 * m
    rw [h2, Work.SignatureBordism.p₁SqNumber_eq_sq cp4SSet c (uSq 4) ((5 : ℤ) • uSq 4)
      (q := 5) (m := m) rfl hm]
    ring
  have hp2 : (cp4Smooth8Of c hc).p2Num = 10 * m := by
    show Work.SignatureBordism.p₂Number cp4SSet c
      (Work.Thom.p2Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 4)) = 10 * m
    rw [h4, Work.SignatureBordism.p₂Number, map_zsmul, LinearMap.smul_apply, smul_eq_mul, hcu]
  exact ⟨hsig, hp1, hp2, by
    show 45 * (cp4Smooth8Of c hc).sigma
      = 7 * (cp4Smooth8Of c hc).p2Num - (cp4Smooth8Of c hc).p1Sq
    rw [hsig, hp1, hp2]; ring⟩

end

end Work.Gen
