/-
# Continuity of the cleared kernel `AfunFun` in the two complex variables

The cleared kernel `AfunFun ℓ d τ z` is a function on the product `ℍ × ℍ` of the upper
half-plane with itself, and `Submission.Work.Asymptotics.continuous_AfunFun` shows that it
is jointly continuous there.

For the Fourier-interpolation argument one needs to view `AfunFun` as a function of two
*complex* variables `p.1, p.2`, obtained by pushing them into `ℍ` with the section
`UpperHalfPlane.ofComplex`; this section is only continuous on the open upper half-plane
`{z : ℂ | 0 < z.im}` (off it, `ofComplex` is the constant section `Classical.choice`).
Hence the natural statement is continuity *on* the set `{p | 0 < p.1.im ∧ 0 < p.2.im}`,
which is exactly the content of `continuousOn_afunFun_ofComplex` below: compose the joint
continuity of `AfunFun` on `ℍ × ℍ` with the continuity of `p ↦ (ofComplex p.1, ofComplex p.2)`
on the open set where both imaginary parts are positive.

The only ingredient that needs Mathlib's API is the fact that
`UpperHalfPlane.ofComplex : OpenPartialHomeomorph ℂ ℍ` is continuous on its source, which is
`UpperHalfPlane.upperHalfPlaneSet = {z : ℂ | 0 < z.im}`.  This follows from
`OpenPartialHomeomorph.continuousOn`, since `ofComplex` is the inverse of the open embedding
`UpperHalfPlane.coe`.
-/
import Mathlib
import Submission.Work.Asymptotics.continuous_AfunFun

namespace Work.Asymptotics

/-- The section `UpperHalfPlane.ofComplex : ℂ → ℍ` is continuous on the open upper
half-plane. -/
private lemma continuousOn_ofComplex_upperHalfPlaneSet :
    ContinuousOn (fun z : ℂ => UpperHalfPlane.ofComplex z) {z : ℂ | 0 < z.im} := by
  have h := OpenPartialHomeomorph.continuousOn UpperHalfPlane.ofComplex
  have hsrc : UpperHalfPlane.ofComplex.source = {z : ℂ | 0 < z.im} := by
    rw [UpperHalfPlane.ofComplex, OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, UpperHalfPlane.range_coe]
  rwa [hsrc] at h

/-- The map `p ↦ (ofComplex p.1, ofComplex p.2)` is continuous on the set where both
imaginary parts are positive. -/
private lemma continuousOn_prod_ofComplex :
    ContinuousOn (fun p : ℂ × ℂ =>
        (UpperHalfPlane.ofComplex p.1, UpperHalfPlane.ofComplex p.2))
      {p : ℂ × ℂ | 0 < p.1.im ∧ 0 < p.2.im} := by
  have hof := continuousOn_ofComplex_upperHalfPlaneSet
  refine (hof.comp continuous_fst.continuousOn ?_).prodMk
    (hof.comp continuous_snd.continuousOn ?_)
  · exact fun p hp => hp.1
  · exact fun p hp => hp.2

theorem continuousOn_afunFun_ofComplex (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) :
    ContinuousOn (fun p : ℂ × ℂ =>
      Work.Asymptotics.AfunFun ℓ d (UpperHalfPlane.ofComplex p.1) (UpperHalfPlane.ofComplex p.2))
      {p : ℂ × ℂ | 0 < p.1.im ∧ 0 < p.2.im} := by
  have hmain : ContinuousOn (fun q : UpperHalfPlane × UpperHalfPlane =>
      Work.Asymptotics.AfunFun ℓ d q.1 q.2) Set.univ :=
    (continuous_AfunFun ℓ d).continuousOn
  have hres := hmain.comp continuousOn_prod_ofComplex (fun p _ => trivial)
  exact hres

end Work.Asymptotics
