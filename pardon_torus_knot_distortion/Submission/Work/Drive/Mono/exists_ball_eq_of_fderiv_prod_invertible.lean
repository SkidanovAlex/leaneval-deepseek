import Mathlib
import Submission.Work.Drive.Mono.SphereFaceDefs

namespace Work.Drive.Mono

/-- **Local uniqueness of a common level from an invertible derivative.**

If `F, G : ℝ × ℝ → ℝ` are `C¹`, `fderiv F p ≠ 0` and `fderiv G p` is not a real multiple of
`fderiv F p`, then near `p` the pair `(F, G)` is injective: there is `δ > 0` such that any two
points of the ball of radius `δ` around `p` on which both `F` and `G` agree must be equal.  (The
derivative of `q ↦ (G q, F q)` at `p` is `(fderiv G p).prod (fderiv F p)`, which is invertible
when `fderiv F p ≠ 0` and `fderiv G p` is not a multiple of it, by
`Work.Drive.Mono.isInvertible_prod_of_forall_ne_smul`; the inverse function theorem
`HasStrictFDerivAt.toOpenPartialHomeomorph` then gives a local homeomorphism, hence local
injectivity.) -/
theorem exists_ball_eq_of_fderiv_prod_invertible {F G : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (hFne : fderiv ℝ F p ≠ 0) (hind : ∀ t : ℝ, fderiv ℝ G p ≠ t • fderiv ℝ F p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℝ × ℝ, dist q p < δ → F q = F p → G q = G p → q = p := by
  -- the pair of derivatives of `(G, F)` is invertible
  have hFG : ((fderiv ℝ G p).prod (fderiv ℝ F p)).IsInvertible :=
    isInvertible_prod_of_forall_ne_smul hFne hind
  obtain ⟨A, hA⟩ := hFG
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  -- `(G, F)` has the product derivative at `p`, by strict differentiability of both coordinates
  have hpair : HasStrictFDerivAt (fun q : ℝ × ℝ => (G q, F q))
      ((fderiv ℝ G p).prod (fderiv ℝ F p)) p :=
    (hG.contDiffAt.hasStrictFDerivAt hn).prodMk (hF.contDiffAt.hasStrictFDerivAt hn)
  have hstrict : HasStrictFDerivAt (fun q : ℝ × ℝ => (G q, F q))
      (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
    rwa [← hA] at hpair
  -- the inverse function theorem: `(G, F)` is a local homeomorphism at `p`
  let Φ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    hstrict.toOpenPartialHomeomorph (fun q : ℝ × ℝ => (G q, F q))
  have hΦcoe : (Φ : ℝ × ℝ → ℝ × ℝ) = fun q => (G q, F q) := hstrict.toOpenPartialHomeomorph_coe
  have hpΦ : p ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  -- a ball inside the source of `Φ`
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds hpΦ)
  refine ⟨δ, hδpos, ?_⟩
  intro q hq hFq hGq
  have hqΦ : q ∈ Φ.source := hδsub hq
  -- equal `F`- and `G`-values give equal `Φ`-values, so injectivity of `Φ` on its source applies
  have heq : Φ q = Φ p := by rw [hΦcoe]; simp [hFq, hGq]
  exact Φ.injOn hqΦ hpΦ heq

end Work.Drive.Mono
