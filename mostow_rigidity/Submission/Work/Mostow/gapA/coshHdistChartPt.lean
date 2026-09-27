import Mathlib
import Submission.Work.Mostow.gapA.slabDefs
import Submission.Work.Mostow.gapA.chartPtFacts

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {a b : E 3}

/-!
# The cosine-hyperbolic distance of two points of the `(a,b)` Fermi chart

`chartPt a b B v w` is the point of `ℍ³` whose Fermi coordinates around the geodesic
`geodSet a b` are `(v,w)`, and `axisPt_slabDefs a b B v w` is its hyperboloid lift
(`chartPt_hlift`).  The Minkowski pairing computation below gives, for two such points,

`⟨axisPt_slabDefs (v,w), axisPt_slabDefs (v',w')⟩ = -(cosh‖w‖ cosh‖w'‖ cosh(arsinh (v 0) - arsinh (v' 0))
                                   - sinhc‖w‖ sinhc‖w'‖ ⟪w,w'⟫)`,

which is exactly the standard Fermi-coordinate formula for `cosh (hdist · ·)` since
`cosh (hdist v v') = cosh (arsinh (v 0) - arsinh (v' 0))` in `ℍ¹`.
-/

/-- `cosh (hdist v v') = cosh (arsinh (v 0) - arsinh (v' 0))` for points of the `ℍ¹` chart. -/
private lemma cosh_hdist_e1_coord (v v' : E 1) :
    Real.cosh (hdist v v') = Real.cosh (Real.arsinh (v 0) - Real.arsinh (v' 0)) := by
  have hnorm : ‖v‖ ^ 2 = (v 0) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs]
  have hnorm' : ‖v'‖ ^ 2 = (v' 0) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs]
  have ht : tpart v = Real.cosh (Real.arsinh (v 0)) := by
    rw [tpart, hnorm, ← Real.cosh_arsinh]
  have ht' : tpart v' = Real.cosh (Real.arsinh (v' 0)) := by
    rw [tpart, hnorm', ← Real.cosh_arsinh]
  have hi : inner ℝ v v' = v 0 * v' 0 := by
    rw [PiLp.inner_apply, Fin.sum_univ_one, Real.inner_apply]
  have hsin : v 0 * v' 0
      = Real.sinh (Real.arsinh (v 0)) * Real.sinh (Real.arsinh (v' 0)) := by
    rw [Real.sinh_arsinh, Real.sinh_arsinh]
  rw [cosh_hdist', ht, ht', hi, hsin, ← Real.cosh_sub]

/-- The Minkowski pairing of the two normal vectors `w 0 • E1 + w 1 • E2` and
`w' 0 • E1 + w' 1 • E2` is `⟪w,w'⟫`. -/
private lemma mink_normal_pair (B : AxisBasis a b) (w w' : E 2) :
    mink (w 0 • B.E1 + w 1 • B.E2) (w' 0 • B.E1 + w' 1 • B.E2) = inner ℝ w w' := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [Real.inner_apply]
  rw [minkSeg_add_left, minkSeg_add_right, minkSeg_add_right,
    minkSeg_smul, minkSeg_smul, minkSeg_smul, minkSeg_smul,
    mink_E2_E1, B.n11, B.n22, B.n12]
  ring

/-- The normal vector `w 0 • E1 + w 1 • E2` is Minkowski orthogonal to the axis. -/
private lemma mink_normal_gcAxis (B : AxisBasis a b) (s : ℝ) (w : E 2) :
    mink (w 0 • B.E1 + w 1 • B.E2) (gcAxis a b s) = 0 := by
  rw [minkSeg_comm]
  exact chartPt_mink_gcAxis_E1E2 B s w

/-- The Minkowski pairing of two Fermi points. -/
private lemma mink_axisPt_pair (B : AxisBasis a b) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) (v v' : E 1) (w w' : E 2) :
    mink (axisPt_slabDefs a b B v w) (axisPt_slabDefs a b B v' w')
      = -(Real.cosh ‖w‖ * Real.cosh ‖w'‖
              * Real.cosh (Real.arsinh (v 0) - Real.arsinh (v' 0))
          - Submission.Mostow.sinhc ‖w‖ * Submission.Mostow.sinhc ‖w'‖ * inner ℝ w w') := by
  have h1 : mink (gcAxis a b (Real.arsinh (v 0))) (gcAxis a b (Real.arsinh (v' 0)))
      = -Real.cosh (Real.arsinh (v 0) - Real.arsinh (v' 0)) :=
    mink_gcAxis a b ha hb hab _ _
  have h2 := chartPt_mink_gcAxis_E1E2 B (Real.arsinh (v 0)) w'
  have h3 := mink_normal_gcAxis B (Real.arsinh (v' 0)) w
  have h4 := mink_normal_pair B w w'
  rw [axisPt_slabDefs, axisPt_slabDefs, minkSeg_add_left, minkSeg_add_right, minkSeg_add_right,
    minkSeg_smul, minkSeg_smul, minkSeg_smul, minkSeg_smul, h1, h2, h3, h4]
  ring

/-- **The Fermi-coordinate distance formula.**  For two points of the Fermi chart about the
geodesic `geodSet a b`,

`cosh (hdist p p') = cosh‖w‖ cosh‖w'‖ cosh (hdist v v') - sinhc‖w‖ sinhc‖w'‖ ⟪w,w'⟫`. -/
theorem coshHdistChartPt (a b : Submission.Mostow.E 3) (B : Work.Mostow.gapA.AxisBasis a b)
    (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b)
    (v v' : Submission.Mostow.E 1) (w w' : Submission.Mostow.E 2) :
    Real.cosh (Submission.Mostow.hdist (Work.Mostow.gapA.chartPt a b B v w)
        (Work.Mostow.gapA.chartPt a b B v' w'))
      = Real.cosh ‖w‖ * Real.cosh ‖w'‖ * Real.cosh (Submission.Mostow.hdist v v')
          - Submission.Mostow.sinhc ‖w‖ * Submission.Mostow.sinhc ‖w'‖ * inner ℝ w w' := by
  have hlift1 : hlift (chartPt a b B v w) = axisPt_slabDefs a b B v w := chartPt_hlift B ha hb hab v w
  have hlift2 : hlift (chartPt a b B v' w') = axisPt_slabDefs a b B v' w' :=
    chartPt_hlift B ha hb hab v' w'
  have htime1 : tpart (chartPt a b B v w) = axisPt_slabDefs a b B v w (Sum.inr 0) := by
    rw [← hlift1]; exact (hlift_inr _).symm
  have htime2 : tpart (chartPt a b B v' w') = axisPt_slabDefs a b B v' w' (Sum.inr 0) := by
    rw [← hlift2]; exact (hlift_inr _).symm
  have hinner : inner ℝ (chartPt a b B v w) (chartPt a b B v' w')
      = ∑ i : Fin 3, axisPt_slabDefs a b B v w (Sum.inl i) * axisPt_slabDefs a b B v' w' (Sum.inl i) := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.inner_apply]; rfl
  have hmink := mink_axisPt_pair B ha hb hab v v' w w'
  have key : tpart (chartPt a b B v w) * tpart (chartPt a b B v' w')
        - inner ℝ (chartPt a b B v w) (chartPt a b B v' w')
      = - mink (axisPt_slabDefs a b B v w) (axisPt_slabDefs a b B v' w') := by
    rw [htime1, htime2, hinner, mink]
    ring
  rw [cosh_hdist', key, hmink, ← cosh_hdist_e1_coord v v']
  ring

end

end Work.Mostow.gapA
