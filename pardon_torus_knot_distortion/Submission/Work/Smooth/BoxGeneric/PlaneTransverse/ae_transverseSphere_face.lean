import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.FaceRegular.ae_comp_affine
import Submission.Work.Smooth.BoxGeneric.PlaneTransverse.ae_transverseSphere_coord

namespace Work.Smooth.BoxGeneric.PlaneTransverse

/-- The level set of the signed face `faceLin c σ i ε` at the value `s` is the coordinate
hyperplane `{y | y (σ i) = ε * s * boxSide i + c (σ i)}`: `faceLin c σ i ε` is the affine
function `y ↦ ε * (y (σ i) - c (σ i)) / boxSide i`, and for `ε = ±1` the factor `ε` can be moved
across the equation. -/
theorem faceLin_levelSet_eq (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (ε s : ℝ) (hε : ε = 1 ∨ ε = -1) :
    {y : LeanEval.KnotTheory.PardonDistortion.R3 | Work.Smooth.BoxGeneric.faceLin c σ i ε y = s} =
      {y : LeanEval.KnotTheory.PardonDistortion.R3 |
        y (σ i) = (ε * Submission.boxSide i) * s + c (σ i)} := by
  have hb : Submission.boxSide i ≠ 0 := ne_of_gt (Submission.boxSide_pos i)
  have hε2 : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  ext y
  simp only [Set.mem_ofPred_eq, Work.Smooth.BoxGeneric.faceLin_apply,
    Work.Smooth.BoxGeneric.signedFace_apply]
  constructor
  · intro h
    have h2 : (y (σ i) - c (σ i)) / Submission.boxSide i = ε * s := by
      have h3 := congrArg (fun t => ε * t) h
      rw [← mul_assoc, hε2, one_mul] at h3
      exact h3
    rw [div_eq_iff hb] at h2
    rw [show (ε * Submission.boxSide i) * s = ε * s * Submission.boxSide i from by ring]
    linarith
  · intro h
    rw [h, mul_div_assoc', div_eq_iff hb]
    rw [show ε * (((ε * Submission.boxSide i) * s + c (σ i)) - c (σ i))
        = (ε * ε) * (s * Submission.boxSide i) from by ring]
    rw [hε2, one_mul]

/-- **Almost every face cut of the box is transverse to the surface.**

Each of the six signed face level sets `{y | faceLin c σ i ε y = s}` (`ε = ±1`) is the coordinate
hyperplane `{y | y (σ i) = ε * s * boxSide i + c (σ i)}` (`faceLin_levelSet_eq`).  For each
coordinate `σ i`, almost every coordinate level is transverse to the surface
(`ae_transverseSphere_coord`); since `s ↦ ε * s * boxSide i + c (σ i)` is a nonzero affine
reparametrisation of `ℝ`, almost every `s` gives a transverse coordinate level
(`Work.Smooth.BoxGeneric.FaceRegular.ae_comp_affine`).  Intersecting the finitely many (three
coordinates, two signs) almost-everywhere statements concludes. -/
theorem ae_transverseSphere_face {ψ : Submission.Diffeo} (hS : Work.Smooth.BoxGeneric.SardCoord ψ) (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ∀ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) → Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ) {y : LeanEval.KnotTheory.PardonDistortion.R3 | Work.Smooth.BoxGeneric.faceLin c σ i ε y = s} := by
  have key : ∀ i : Fin 3, ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ)
          {y : LeanEval.KnotTheory.PardonDistortion.R3 | Work.Smooth.BoxGeneric.faceLin c σ i 1 y = s} ∧
      Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ)
          {y : LeanEval.KnotTheory.PardonDistortion.R3 | Work.Smooth.BoxGeneric.faceLin c σ i (-1) y = s} := by
    intro i
    have hcoord := ae_transverseSphere_coord hS hclass (σ i)
    have h1 : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ)
          {y : LeanEval.KnotTheory.PardonDistortion.R3 | Work.Smooth.BoxGeneric.faceLin c σ i 1 y = s} := by
      have hcomp := Work.Smooth.BoxGeneric.FaceRegular.ae_comp_affine (a := c (σ i))
        (b := 1 * Submission.boxSide i)
        (by rw [one_mul]; exact ne_of_gt (Submission.boxSide_pos i))
        (P := fun u => Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ)
          {y : LeanEval.KnotTheory.PardonDistortion.R3 | y (σ i) = u}) hcoord
      filter_upwards [hcomp] with s hs
      rw [faceLin_levelSet_eq c σ i 1 s (Or.inl rfl)]
      exact hs
    have h2 : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ)
          {y : LeanEval.KnotTheory.PardonDistortion.R3 | Work.Smooth.BoxGeneric.faceLin c σ i (-1) y = s} := by
      have hb : (-1 : ℝ) * Submission.boxSide i ≠ 0 := by
        have := Submission.boxSide_pos i; nlinarith
      have hcomp := Work.Smooth.BoxGeneric.FaceRegular.ae_comp_affine (a := c (σ i))
        (b := (-1) * Submission.boxSide i) hb
        (P := fun u => Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ)
          {y : LeanEval.KnotTheory.PardonDistortion.R3 | y (σ i) = u}) hcoord
      filter_upwards [hcomp] with s hs
      rw [faceLin_levelSet_eq c σ i (-1) s (Or.inr rfl)]
      exact hs
    exact h1.and h2
  refine MeasureTheory.ae_all_iff.mpr (fun i => ?_)
  filter_upwards [key i] with s hs ε hε
  rcases hε with hε | hε
  · rw [hε]; exact hs.1
  · rw [hε]; exact hs.2

end Work.Smooth.BoxGeneric.PlaneTransverse
