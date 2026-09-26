import Mathlib
import Submission.Work.Drive.Generic.nclmBasic
import Submission.Work.Drive.AB.pinSetup
import Submission.Work.Drive.AB.needleShiftedNotOnLine
import Submission.Work.Drive.AB.needleFam_inner_eq_devAvg

/-!
# The chart vector of the shifted needle, paired with an arbitrary direction

`Work.Drive.chartUp r D lam δ₁ δ₂ ε v` is the offset of the shifted needle's base point from the
*line* of its chord: `N' 0 - chordEndA - ⟪N' 0 - chordEndA, v⟫ • v`, i.e. the component of
`N' 0 - chordEndA` orthogonal to the unit chord direction `v`.  This module computes its inner
product with an arbitrary `y`.

The computation is a one-step consequence of the deviation identity
`Work.Drive.needleFam_inner_eq_devAvg` at the parameter `t = period / 4` (the base point of the
shifted needle) and of the fact that the averaged arc fraction there is `1 / 2`
(`Work.Drive.Generic.integral_sweepBump_arcFrac`):

    ⟪chartUp, y⟫
      = ⟪N' 0 - chordEndA, y - ⟪v, y⟫ • v⟫                          (orthogonalisation)
      = ∫∫ bump bump * ⟪loopDev, y - ⟪v,y⟫ • v⟫ + (1/2) ⟪B - A, y - ⟪v,y⟫ • v⟫
      = ∫∫ bump bump * (⟪loopDev, y⟫ - ⟪v,y⟫ * ⟪loopDev, v⟫) + (1/2) * ‖B - A‖ * 0 ,

the last term vanishing because `B - A = ‖B - A‖ • v` is parallel to `v`.  The two-dimensional
average is `Work.Drive.Generic.bumpAvg₂`, so the statement is exactly the announced identity.
-/

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

theorem nclm_chartUp_inner {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : Continuous r) {d : LeanEval.KnotTheory.Quadrisecant.BandArcData}
    (D : Work.Drive.SweepData d) {lam δ₁ δ₂ ε : ℝ}
    (hlam1 : lam < 1 / 2) (hδ₁0 : 0 < δ₁)
    (hδ₁4 : δ₁ ≤ LeanEval.KnotTheory.Quadrisecant.period / 4)
    {v : LeanEval.KnotTheory.Quadrisecant.Space} (hv : ‖v‖ = 1)
    (hb : Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
            = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v) :
    ∀ y : LeanEval.KnotTheory.Quadrisecant.Space,
      inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) y
        = Work.Drive.Generic.bumpAvg₂ (fun v' u =>
            inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
                (Work.Drive.arcFrac lam δ₁ (LeanEval.KnotTheory.Quadrisecant.period / 4) u)) y
              - inner ℝ v y * inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
                  (Work.Drive.arcFrac lam δ₁ (LeanEval.KnotTheory.Quadrisecant.period / 4) u)) v) := by
  intro y
  set g : ℝ → ℝ → ℝ := fun v' u =>
      inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
          (Work.Drive.arcFrac lam δ₁ (LeanEval.KnotTheory.Quadrisecant.period / 4) u)) y
        - inner ℝ v y * inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
            (Work.Drive.arcFrac lam δ₁ (LeanEval.KnotTheory.Quadrisecant.period / 4) u)) v with hg
  have hzone : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
      Work.Drive.sweepParam (LeanEval.KnotTheory.Quadrisecant.period / 4 - δ₁ * u) ≤ 1 / 2 :=
    fun u hu => Work.Drive.sweepParam_quarter_sub_le hδ₁0.le hδ₁4 hu
  have hA0 : (∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u *
      Work.Drive.arcFrac lam δ₁ (LeanEval.KnotTheory.Quadrisecant.period / 4) u) = 1 / 2 :=
    integral_sweepBump_arcFrac hδ₁0 hδ₁4
  have hv1 : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hBAsub : inner ℝ (Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε)
      (y - (inner ℝ v y) • v) = 0 := by
    rw [hb, real_inner_smul_left, inner_sub_right, real_inner_smul_right, hv1, mul_one]
    ring
  have hchart : inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) y
      = inner ℝ (Work.Drive.needleFam r D lam δ₁ δ₂ ε (LeanEval.KnotTheory.Quadrisecant.period / 4) -
          Work.Drive.chordEndA r D δ₂ ε) (y - (inner ℝ v y) • v) := by
    simp only [Work.Drive.chartUp, Work.Drive.nCoord, Work.Drive.shiftedNeedle, zero_add]
    rw [inner_sub_left, real_inner_smul_left, inner_sub_right, real_inner_smul_right]
    ring
  rw [hchart]
  have hdev := Work.Drive.needleFam_inner_eq_devAvg (r := r) (D := D) (lam := lam) (δ₁ := δ₁)
    (δ₂ := δ₂) (ε := ε) (t := LeanEval.KnotTheory.Quadrisecant.period / 4)
    (e := y - (inner ℝ v y) • v) hr hlam1 hzone
  have hpoint : ∀ v' u : ℝ,
      inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
        (Work.Drive.arcFrac lam δ₁ (LeanEval.KnotTheory.Quadrisecant.period / 4) u))
        (y - (inner ℝ v y) • v) = g v' u := by
    intro v' u
    rw [inner_sub_right, real_inner_smul_right, hg]
  have hcongr : (∫ v' in (-1 : ℝ)..1, Work.Drive.sweepBump v' *
        (∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u *
          inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
            (Work.Drive.arcFrac lam δ₁ (LeanEval.KnotTheory.Quadrisecant.period / 4) u))
            (y - (inner ℝ v y) • v)))
      = ∫ v' in (-1 : ℝ)..1, Work.Drive.sweepBump v' *
        (∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u * g v' u) := by
    refine intervalIntegral.integral_congr (fun v' _ => ?_)
    rw [show (∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u *
          inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
            (Work.Drive.arcFrac lam δ₁ (LeanEval.KnotTheory.Quadrisecant.period / 4) u))
            (y - (inner ℝ v y) • v))
        = ∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u * g v' u from
      intervalIntegral.integral_congr (fun u _ => by rw [hpoint v' u])]
  rw [hdev, hA0, hBAsub, mul_zero, add_zero, hcongr]
  rfl

end Work.Drive.Generic
