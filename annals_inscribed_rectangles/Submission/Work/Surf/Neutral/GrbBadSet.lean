import Mathlib
import Submission.Work.Surf.Neutral.GrbLevel
import Submission.Work.Surf.volume_badSet_eq_zero

/-!
# (Neutral copy) `GrbBadSet`

Verbatim copy of the module `Work.Surf.ChordN.grbBadSet` in the namespace `Work.Surf.ChordN`, with:

* every import of a module whose closure contains the declaration `Work.Drive.toC` of
  `Submission/Work/Drive/winding_eq_crossing_sum.lean` redirected to the neutral copy of that module
  (the only such channel is the import of `Submission/Work/Drive/line_crossings_even.lean`, replaced
  by `Submission/Work/Drive/Neutral/HalfDir.lean`);
* every qualified reference to the declarations of the neutral half-direction file
  (`halfDir`, `continuous_halfDir`, `halfDir_apply`, `halfDir_add_self`, `rescaleAngle`,
  `twoPiNeZero`, `toC`) redirected to `Work.Drive.NH`.

Reason: `Work.Drive.toC` is declared both in `Submission/Work/Drive/winding_eq_crossing_sum.lean` (in
the chord-parity world) and in `Submission/Work/Drive/UmlaufSetup.lean` (in the capping world), so the
two worlds cannot be imported together.  With these copies,
`Work.Surf.ChordN.chord_crossing_parity` — the strict base case of the mod-2 intersection form of
`ℝP²` — is importable next to `Work.Drive.CappingSpace`; see
`Submission/Work/Drive/cutTransportStrict.lean`.
-/
/-!
# The bad directions for the boundary curve of the difference map

We fix a `C¹` plane curve `g : ℝ → ℝ × ℝ` and consider the directions that a ray from the origin has
to avoid so that it meets the curve `t ↦ g t` finitely often, never at the corner times
`0, 1/4, 1/2, 3/4`, and always transversally.

* `gCritical g`: the parameters at which the curve is tangent to its own radial direction
  (`cross2 (g u) (deriv g u) = 0`).
* `gTanCone g`: the union of the lines `ℝ ∙ g u` over the critical parameters — the image of the
  map `φ (u, c) = c • g u` on `gCritical g × Set.univ`, a null set by the equal-dimension case of
  Sard's theorem.
* `gCornerSet g`: the four lines through the values `g (j / 4)`, `j = 0, 1, 2, 3`.
* `gBadSet g = gTanCone g ∪ gCornerSet g`.

The advantage over `Work.Surf.badSet` (which uses the piecewise linear loop `sqBoxLoop`) is that a
`C¹` curve is differentiable everywhere, so no corner parameters have to be excluded from the
critical set, and no reparametrisation is needed.
-/

namespace Work.Surf.ChordN

open Work.Drive.NH

open Set MeasureTheory
open Work.Drive Work.Surf.GRB

noncomputable section

open scoped Topology

/-- The parameters at which `g` is tangent to its own radial direction. -/
def gCritical (g : ℝ → ℝ × ℝ) : Set ℝ := {u : ℝ | cross2 (g u) (deriv g u) = 0}

/-- The tangent cone of the curve `g`: the union of the lines `ℝ ∙ g u` over the critical
parameters. -/
def gTanCone (g : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  (fun p : ℝ × ℝ => p.2 • g p.1) '' (gCritical g ×ˢ Set.univ)

/-- The four lines through the values of `g` at the corner times `j / 4`, `j = 0, 1, 2, 3`. -/
def gCornerSet (g : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  ⋃ j : Fin 4, Set.range (fun r : ℝ => r • g ((j : ℝ) / 4))

/-- The set of directions that a good ray has to avoid. -/
def gBadSet (g : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) := gTanCone g ∪ gCornerSet g

/-! ## The tangent cone is null -/

/-- The derivative of `φ (u, c) = c • g u`. -/
lemma hasFDerivAt_gTanParam (g : ℝ → ℝ × ℝ) (hg : ContDiff ℝ 1 g) (u c : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => p.2 • g p.1)
      (c • ((fderiv ℝ g u).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (g u)) (u, c) := by
  have hgu : DifferentiableAt ℝ g u := (hg.differentiable (by norm_num)).differentiableAt
  have hc : HasFDerivAt (fun p : ℝ × ℝ => p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (u, c) :=
    ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hf : HasFDerivAt (fun p : ℝ × ℝ => g p.1)
      ((fderiv ℝ g u).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) (u, c) :=
    HasFDerivAt.comp (x := (u, c)) (g := g) (f := fun p : ℝ × ℝ => p.1)
      (f' := ContinuousLinearMap.fst ℝ ℝ ℝ) (g' := fderiv ℝ g u)
      hgu.hasFDerivAt (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.fst ℝ ℝ ℝ))
  exact hc.smul hf

/-- The derivative of `φ (u, c) = c • g u` is singular at every critical parameter. -/
lemma det_fderiv_gTanParam_eq_zero (g : ℝ → ℝ × ℝ) (hg : ContDiff ℝ 1 g) {u c : ℝ}
    (hu : u ∈ gCritical g) :
    (fderiv ℝ (fun p : ℝ × ℝ => p.2 • g p.1) (u, c)).det = 0 := by
  have hφ := hasFDerivAt_gTanParam g hg u c
  rw [hφ.fderiv]
  set A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    c • ((fderiv ℝ g u).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (g u) with hA
  have key : ∀ dt dc : ℝ, A (dt, dc)
      = c • ((fderiv ℝ g u) dt) + dc • g u := by
    intro dt dc
    simp [hA, ContinuousLinearMap.smulRight_apply]
  have hker : A.ker ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    by_cases hg0 : g u = 0
    · have hA0 : A (0, 1) = 0 := by
        rw [key 0 1]
        simp [hg0]
      exact ⟨(0, 1), LinearMap.mem_ker.mpr hA0, by simp⟩
    · obtain ⟨μ, hμ⟩ := exists_smul_of_cross2_eq_zero hg0 hu
      have hA1 : A (1, -(c * μ)) = 0 := by
        rw [key 1 (-(c * μ)), fderiv_apply_one_eq_deriv, hμ]
        simp [smul_smul]
      exact ⟨(1, -(c * μ)), LinearMap.mem_ker.mpr hA1, by simp⟩
  have hd : LinearMap.det A.toLinearMap = 0 :=
    (LinearMap.det_eq_zero_iff_ker_ne_bot (f := A.toLinearMap)).mpr hker
  simpa [ContinuousLinearMap.det] using hd

/-- **The tangent cone of a `C¹` curve is Lebesgue null.** -/
theorem volume_gTanCone_eq_zero (g : ℝ → ℝ × ℝ) (hg : ContDiff ℝ 1 g) :
    MeasureTheory.volume (gTanCone g) = 0 := by
  show MeasureTheory.volume
    ((fun p : ℝ × ℝ => p.2 • g p.1) '' (gCritical g ×ˢ Set.univ)) = 0
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
    (s := gCritical g ×ˢ Set.univ)
    (f := fun p : ℝ × ℝ => p.2 • g p.1)
    (f' := fun p => fderiv ℝ (fun p : ℝ × ℝ => p.2 • g p.1) p) ?_ ?_
  · rintro ⟨u, c⟩ _
    rw [(hasFDerivAt_gTanParam g hg u c).fderiv]
    exact (hasFDerivAt_gTanParam g hg u c).hasFDerivWithinAt
  · rintro ⟨u, c⟩ hp
    exact det_fderiv_gTanParam_eq_zero g hg hp.1

/-- **The four corner lines are Lebesgue null.** -/
theorem volume_gCornerSet_eq_zero (g : ℝ → ℝ × ℝ) :
    MeasureTheory.volume (gCornerSet g) = 0 := by
  show MeasureTheory.volume
    (⋃ j : Fin 4, Set.range (fun r : ℝ => r • g ((j : ℝ) / 4))) = 0
  exact measure_iUnion_null (fun j => volume_range_smul_eq_zero _)

/-- **The bad set of a `C¹` curve is Lebesgue null.** -/
theorem volume_gBadSet_eq_zero (g : ℝ → ℝ × ℝ) (hg : ContDiff ℝ 1 g) :
    MeasureTheory.volume (gBadSet g) = 0 := by
  show MeasureTheory.volume (gTanCone g ∪ gCornerSet g) = 0
  exact measure_union_null (volume_gTanCone_eq_zero g hg) (volume_gCornerSet_eq_zero g)

/-- `0` lies on each of the four corner lines. -/
lemma zero_mem_gCornerSet (g : ℝ → ℝ × ℝ) : (0 : ℝ × ℝ) ∈ gCornerSet g :=
  Set.mem_iUnion.mpr ⟨0, ⟨0, by simp⟩⟩

/-- `0` is bad: it lies on each of the four corner lines. -/
lemma zero_mem_gBadSet (g : ℝ → ℝ × ℝ) : (0 : ℝ × ℝ) ∈ gBadSet g :=
  Or.inr (zero_mem_gCornerSet g)

/-- **A good direction exists** for a `C¹` curve: one outside the bad set, which is necessarily
non-zero. -/
theorem exists_notMem_gBadSet (g : ℝ → ℝ × ℝ) (hg : ContDiff ℝ 1 g) :
    ∃ v : ℝ × ℝ, v ∉ gBadSet g ∧ v ≠ 0 := by
  by_contra h
  have hsub : (Set.univ : Set (ℝ × ℝ)) ⊆ gBadSet g := by
    intro v _
    by_cases hv : v ∈ gBadSet g
    · exact hv
    · exact absurd ⟨v, hv, fun h0 => by rw [h0] at hv; exact hv (zero_mem_gBadSet g)⟩ h
  have hzero : MeasureTheory.volume (Set.univ : Set (ℝ × ℝ)) = 0 :=
    measure_mono_null hsub (volume_gBadSet_eq_zero g hg)
  have hball : MeasureTheory.volume (Metric.ball (0 : ℝ × ℝ) 1) = 0 :=
    measure_mono_null (Set.subset_univ _) hzero
  have hpos : (0 : ENNReal) < MeasureTheory.volume (Metric.ball (0 : ℝ × ℝ) 1) :=
    Metric.isOpen_ball.measure_pos MeasureTheory.volume
      ⟨0, Metric.mem_ball_self (by norm_num)⟩
  rw [hball] at hpos
  exact lt_irrefl 0 hpos

/-! ## The face curves of the difference map -/

section Faces

variable {a b : ℝ → EuclideanSpace ℝ (Fin 2)}

/-- The bottom face `x 1 = 0` of the difference map. -/
def fBot (a b : ℝ → EuclideanSpace ℝ (Fin 2)) : ℝ → ℝ × ℝ := fun s => grbDiff a b (s, 0)

/-- The top face `x 1 = 1` of the difference map. -/
def fTop (a b : ℝ → EuclideanSpace ℝ (Fin 2)) : ℝ → ℝ × ℝ := fun s => grbDiff a b (s, 1)

/-- The left face `x 0 = 0` of the difference map. -/
def fLft (a b : ℝ → EuclideanSpace ℝ (Fin 2)) : ℝ → ℝ × ℝ := fun t => grbDiff a b (0, t)

/-- The right face `x 0 = 1` of the difference map. -/
def fRgt (a b : ℝ → EuclideanSpace ℝ (Fin 2)) : ℝ → ℝ × ℝ := fun t => grbDiff a b (1, t)

/-- **The bad directions of the difference map of two `C¹` curves**: the tangent cones of the
boundary curve and of the four face curves, together with the four corner lines. -/
def grbBad (a b : ℝ → EuclideanSpace ℝ (Fin 2)) : Set (ℝ × ℝ) :=
  gTanCone (grbCurveR a b) ∪ gTanCone (fBot a b) ∪ gTanCone (fTop a b) ∪
    gTanCone (fLft a b) ∪ gTanCone (fRgt a b) ∪ gCornerSet (grbCurveR a b)

lemma contDiff_fBot (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) : ContDiff ℝ 1 (fBot a b) :=
  (grbDiff_contDiff ha hb).comp (by fun_prop : ContDiff ℝ 1 (fun s : ℝ => (s, (0:ℝ))))

lemma contDiff_fTop (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) : ContDiff ℝ 1 (fTop a b) :=
  (grbDiff_contDiff ha hb).comp (by fun_prop : ContDiff ℝ 1 (fun s : ℝ => (s, (1:ℝ))))

lemma contDiff_fLft (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) : ContDiff ℝ 1 (fLft a b) :=
  (grbDiff_contDiff ha hb).comp (by fun_prop : ContDiff ℝ 1 (fun t : ℝ => ((0:ℝ), t)))

lemma contDiff_fRgt (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) : ContDiff ℝ 1 (fRgt a b) :=
  (grbDiff_contDiff ha hb).comp (by fun_prop : ContDiff ℝ 1 (fun t : ℝ => ((1:ℝ), t)))

/-- **The bad directions of the difference map of two `C¹` curves are Lebesgue null.** -/
theorem volume_grbBad_eq_zero (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) :
    MeasureTheory.volume (grbBad a b) = 0 := by
  have h1 := volume_gTanCone_eq_zero (grbCurveR a b) (contDiff_grbCurveR ha hb)
  have h2 := volume_gTanCone_eq_zero (fBot a b) (contDiff_fBot ha hb)
  have h3 := volume_gTanCone_eq_zero (fTop a b) (contDiff_fTop ha hb)
  have h4 := volume_gTanCone_eq_zero (fLft a b) (contDiff_fLft ha hb)
  have h5 := volume_gTanCone_eq_zero (fRgt a b) (contDiff_fRgt ha hb)
  have h6 := volume_gCornerSet_eq_zero (grbCurveR a b)
  show MeasureTheory.volume (gTanCone (grbCurveR a b) ∪ gTanCone (fBot a b)
    ∪ gTanCone (fTop a b) ∪ gTanCone (fLft a b) ∪ gTanCone (fRgt a b)
    ∪ gCornerSet (grbCurveR a b)) = 0
  exact measure_union_null (measure_union_null (measure_union_null (measure_union_null
    (measure_union_null h1 h2) h3) h4) h5) h6

/-- The zero direction is bad. -/
lemma zero_mem_grbBad (a b : ℝ → EuclideanSpace ℝ (Fin 2)) : (0 : ℝ × ℝ) ∈ grbBad a b := by
  rw [grbBad]
  exact Or.inr (zero_mem_gCornerSet (grbCurveR a b))

/-- A good direction exists for the difference map of two `C¹` curves. -/
theorem exists_notMem_grbBad (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) :
    ∃ v : ℝ × ℝ, v ∉ grbBad a b ∧ v ≠ 0 := by
  by_contra h
  have hsub : (Set.univ : Set (ℝ × ℝ)) ⊆ grbBad a b := by
    intro v _
    by_cases hv : v ∈ grbBad a b
    · exact hv
    · refine absurd ⟨v, hv, fun h0 => ?_⟩ h
      exact hv (h0 ▸ zero_mem_grbBad a b)
  have hzero : MeasureTheory.volume (Set.univ : Set (ℝ × ℝ)) = 0 :=
    measure_mono_null hsub (volume_grbBad_eq_zero ha hb)
  have hball : MeasureTheory.volume (Metric.ball (0 : ℝ × ℝ) 1) = 0 :=
    measure_mono_null (Set.subset_univ _) hzero
  have hpos : (0 : ENNReal) < MeasureTheory.volume (Metric.ball (0 : ℝ × ℝ) 1) :=
    Metric.isOpen_ball.measure_pos MeasureTheory.volume
      ⟨0, Metric.mem_ball_self (by norm_num)⟩
  rw [hball] at hpos
  exact lt_irrefl 0 hpos

end Faces

end

end Work.Surf.ChordN
