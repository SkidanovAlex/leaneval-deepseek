import Mathlib
import Submission.Work.Drive.genericFullDefs
import Submission.CollinearityMap
import Submission.Transversality
import Submission.TrisecantCurve
import Submission.LocalCurve
import Submission.Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent
import Submission.Commons.Analysis.Normed.isInvertible_of_det_columns
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ## Helpers for the local uniqueness of the vertical trace

The two-variable slice `(y, m') ↦ Φ(a, a+y, m')` of the collinearity map at a fixed first
parameter, together with its *Gram-reduced* form

  `G(y,m') = (⟨Φ(a,a+y,m'), ∂_b⟩, ⟨Φ(a,a+y,m'), ∂_m⟩)`,

whose derivative at `(b-a, m)` is the Gram matrix of the two partials `∂_b, ∂_m`.  When the
partials are linearly independent this matrix is invertible, so (by the inverse function theorem,
in the form of `HasStrictFDerivAt.eventually_left_inverse`) `G` is locally injective; and since
`Φ = 0` implies `G = 0`, the zero set of `Φ` near `(b-a, m)` is the single point `(b-a, m)`.

Nothing below unfolds `collPartialB`/`collPartialM` (which would expose the `PiLp`/`WithLp`
representation of `Space` and trip an instance diamond): the derivative facts are taken in the
`collPartial…` form from `hasDerivAt_collinearity_b_axis`/`hasDerivAt_collinearity_m_axis`, and the
Gram matrix is matched to `gram_det_ne_zero_of_linearIndependent` through `Matrix.det_fin_two_of`. -/

noncomputable section

/-- The two-variable slice of the collinearity map at a fixed first parameter `a`:
`(y, m') ↦ Φ(a, a+y, m')`. -/
private def collSlice (r : ℝ → Space) (a : ℝ) (p : ℝ × ℝ) : Space :=
  collinearityValue r a (a + p.1) p.2

/-- The Gram-reduced slice: pair the slice with the two partials `∂_b`, `∂_m` frozen at the
base triple. -/
private def collGramMap (r : ℝ → Space) (a b m : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (inner ℝ (collSlice r a p) (collPartialB r a b m),
    inner ℝ (collSlice r a p) (collPartialM r a b m))

/-- The slice is smooth (it is the collinearity map composed with the smooth affine embedding
`p ↦ (a, a + p.1, p.2)`). -/
private lemma contDiff_collSlice {r : ℝ → Space} (hr : IsSmoothKnot r) (a : ℝ) :
    ContDiff ℝ ⊤ (collSlice r a) := by
  have hΦ : ContDiff ℝ ⊤ (fun q : RealParamTriple => collinearityMap r q) :=
    contDiff_collinearityMap hr
  have he : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (a, (a + p.1, p.2)) : ℝ × ℝ → RealParamTriple) := by
    refine ContDiff.prodMk contDiff_const ?_
    refine ContDiff.prodMk ?_ contDiff_snd
    exact ContDiff.add contDiff_const contDiff_fst
  have h := hΦ.comp he
  rw [show collSlice r a = (fun p : ℝ × ℝ => collinearityMap r (a, (a + p.1, p.2))) from rfl]
  exact h

/-- The Gram-reduced slice is smooth. -/
private lemma contDiff_collGramMap {r : ℝ → Space} (hr : IsSmoothKnot r) (a b m : ℝ) :
    ContDiff ℝ ⊤ (collGramMap r a b m) := by
  unfold collGramMap
  refine ContDiff.prodMk ?_ ?_
  · exact (contDiff_inner_fixed (collPartialB r a b m)).comp (contDiff_collSlice hr a)
  · exact (contDiff_inner_fixed (collPartialM r a b m)).comp (contDiff_collSlice hr a)

/-- **Local injectivity from a strictly differentiable invertible derivative**: if `f` has an
invertible strict derivative at `p₀`, then `f` is injective on a neighbourhood of `p₀`.  (Proof:
the local inverse `hf.localInverse` is a left inverse of `f` near `p₀`.) -/
private lemma local_inj_of_hasStrictFDerivAt_equiv {f : (ℝ × ℝ) → (ℝ × ℝ)}
    {D : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)} {p₀ : ℝ × ℝ}
    (hf : HasStrictFDerivAt f (D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℝ × ℝ, dist z p₀ < ε → f z = f p₀ → z = p₀ := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp hf.eventually_left_inverse
  refine ⟨ε, hε, fun z hz hfz => ?_⟩
  have h1 := h hz
  have h0 := hf.eventually_left_inverse.self_of_nhds
  rw [hfz] at h1
  exact h1.symm.trans h0

end

open LeanEval.KnotTheory.Quadrisecant in
/-- **Local uniqueness of collinear triples at a fixed first parameter.** If `(a,b,m)` is a collinear triple of a smooth knot whose `(b,m)`-partials of the collinearity map are linearly independent, then near `(b,m)` the only collinear triple with the same first parameter `a` is `(a,b,m)` itself: the vertical trace of the trisecant locus at the column `a` is locally a single point.  Proof route: the inverse-function principle at `(y,m') ↦ (inner (Φ(a, a+y, m')) ∂_b, inner (Φ(a, a+y, m')) ∂_m)`, whose derivative at the base point is the Gram matrix of the two independent partials.  Worked-out hint: a direct formalisation is nearly complete (see `Submission/Work/Drive/finiteMeridianFibre_of_tangentChordGP.lean`); the only failure is a `PiLp`/`WithLp` instance diamond when rewriting `collPartialB r a b m` to `cross3 (r a - r m) (velocity r b)`.  Keeping the two forms separate -- use the `cross3 ...` forms returned by `hasDerivAt_collinearity_middle` and `hasDerivAt_collinearity_third` for the derivative facts, and `convert`/`Set.EqOn` rather than `simpa` when passing between them -- resolves it.  Useful ingredients: `Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent`, `Commons.Analysis.Normed.isInvertible_of_det_columns`, `Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv`, `ContDiffAt.hasStrictFDerivAt'`. -/
theorem local_uniqueness_of_partialsBM_independent {r : ℝ → Space} (hr : IsSmoothKnot r)
    {a b m : ℝ} (hcol : collinearityValue r a b m = 0)
    (hLI : LinearIndependent ℝ ![collPartialB r a b m, collPartialM r a b m]) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y m' : ℝ, |y - (b - a)| < ε → |m' - m| < ε →
      collinearityValue r a (a + y) m' = 0 → y = b - a ∧ m' = m := by
  have hGcd : ContDiff ℝ ⊤ (collGramMap r a b m) := contDiff_collGramMap hr a b m
  have hGdiff : DifferentiableAt ℝ (collGramMap r a b m) (b - a, m) :=
    (ContDiff.of_le hGcd le_top).differentiable_one (b - a, m)
  -- the first column of the derivative of the reduced slice: the `b`-axis Gram column
  have hcol1 : (fderiv ℝ (collGramMap r a b m) (b - a, m)) ((1, 0) : ℝ × ℝ) =
      (inner ℝ (collPartialB r a b m) (collPartialB r a b m),
       inner ℝ (collPartialB r a b m) (collPartialM r a b m)) := by
    have hg := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
      (H := collGramMap r a b m) (p := (b - a, m)) (e := ((1, 0) : ℝ × ℝ)) hGdiff
    have hb := hasDerivAt_collinearity_b_axis hr a b m
    have h1 := hasDerivAt_comp_clm hb ((innerSLFlip ℝ (collPartialB r a b m) : Space →L[ℝ] ℝ))
    have h2 := hasDerivAt_comp_clm hb ((innerSLFlip ℝ (collPartialM r a b m) : Space →L[ℝ] ℝ))
    have hp : HasDerivAt (fun s : ℝ => (inner ℝ (collinearityValue r a (b + s) m) (collPartialB r a b m),
        inner ℝ (collinearityValue r a (b + s) m) (collPartialM r a b m)))
        (inner ℝ (collPartialB r a b m) (collPartialB r a b m),
         inner ℝ (collPartialB r a b m) (collPartialM r a b m)) 0 := h1.prodMk h2
    have hfun : (fun s : ℝ => collGramMap r a b m ((b - a, m) + s • ((1, 0) : ℝ × ℝ))) =
        fun s : ℝ => (inner ℝ (collinearityValue r a (b + s) m) (collPartialB r a b m),
          inner ℝ (collinearityValue r a (b + s) m) (collPartialM r a b m)) := by
      funext s
      have hpts : ((b - a, m) + s • ((1, 0) : ℝ × ℝ)) = (b - a + s, m) := by
        ext <;> simp
      rw [hpts]
      have hs : collSlice r a (b - a + s, m) = collinearityValue r a (b + s) m := by
        unfold collSlice
        rw [show a + (b - a + s) = b + s from by ring]
      unfold collGramMap
      rw [hs]
    have hdir : HasDerivAt (fun s : ℝ => collGramMap r a b m ((b - a, m) + s • ((1, 0) : ℝ × ℝ)))
        (inner ℝ (collPartialB r a b m) (collPartialB r a b m),
         inner ℝ (collPartialB r a b m) (collPartialM r a b m)) 0 := by
      rw [hfun]
      exact hp
    exact hg.unique hdir
  -- the second column: the `m`-axis Gram column
  have hcol2 : (fderiv ℝ (collGramMap r a b m) (b - a, m)) ((0, 1) : ℝ × ℝ) =
      (inner ℝ (collPartialM r a b m) (collPartialB r a b m),
       inner ℝ (collPartialM r a b m) (collPartialM r a b m)) := by
    have hg := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
      (H := collGramMap r a b m) (p := (b - a, m)) (e := ((0, 1) : ℝ × ℝ)) hGdiff
    have hm := hasDerivAt_collinearity_m_axis hr a b m
    have h1 := hasDerivAt_comp_clm hm ((innerSLFlip ℝ (collPartialB r a b m) : Space →L[ℝ] ℝ))
    have h2 := hasDerivAt_comp_clm hm ((innerSLFlip ℝ (collPartialM r a b m) : Space →L[ℝ] ℝ))
    have hp : HasDerivAt (fun s : ℝ => (inner ℝ (collinearityValue r a b (m + s)) (collPartialB r a b m),
        inner ℝ (collinearityValue r a b (m + s)) (collPartialM r a b m)))
        (inner ℝ (collPartialM r a b m) (collPartialB r a b m),
         inner ℝ (collPartialM r a b m) (collPartialM r a b m)) 0 := h1.prodMk h2
    have hfun : (fun s : ℝ => collGramMap r a b m ((b - a, m) + s • ((0, 1) : ℝ × ℝ))) =
        fun s : ℝ => (inner ℝ (collinearityValue r a b (m + s)) (collPartialB r a b m),
          inner ℝ (collinearityValue r a b (m + s)) (collPartialM r a b m)) := by
      funext s
      have hpts : ((b - a, m) + s • ((0, 1) : ℝ × ℝ)) = (b - a, m + s) := by
        ext <;> simp
      rw [hpts]
      have hs : collSlice r a (b - a, m + s) = collinearityValue r a b (m + s) := by
        unfold collSlice
        rw [show a + (b - a) = b from by ring]
      unfold collGramMap
      rw [hs]
    have hdir : HasDerivAt (fun s : ℝ => collGramMap r a b m ((b - a, m) + s • ((0, 1) : ℝ × ℝ)))
        (inner ℝ (collPartialM r a b m) (collPartialB r a b m),
         inner ℝ (collPartialM r a b m) (collPartialM r a b m)) 0 := by
      rw [hfun]
      exact hp
    exact hg.unique hdir
  -- the determinant of the derivative is the determinant of the Gram matrix of the two partials
  have hdet : (inner ℝ (collPartialB r a b m) (collPartialB r a b m)) *
        (inner ℝ (collPartialM r a b m) (collPartialM r a b m)) -
        (inner ℝ (collPartialB r a b m) (collPartialM r a b m)) *
        (inner ℝ (collPartialM r a b m) (collPartialB r a b m)) ≠ 0 := by
    have h := Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent
      (x := collPartialB r a b m) (y := collPartialM r a b m) hLI
    have hEq : Matrix.det !![inner ℝ (collPartialB r a b m) (collPartialB r a b m),
          inner ℝ (collPartialB r a b m) (collPartialM r a b m);
        inner ℝ (collPartialM r a b m) (collPartialB r a b m),
          inner ℝ (collPartialM r a b m) (collPartialM r a b m)]
        = (inner ℝ (collPartialB r a b m) (collPartialB r a b m)) *
            (inner ℝ (collPartialM r a b m) (collPartialM r a b m)) -
          (inner ℝ (collPartialB r a b m) (collPartialM r a b m)) *
            (inner ℝ (collPartialM r a b m) (collPartialB r a b m)) := by
      rw [Matrix.det_fin_two_of]
    rw [← hEq]
    exact h
  -- hence the derivative is invertible and the reduced slice is locally injective
  have hInv : (fderiv ℝ (collGramMap r a b m) (b - a, m)).IsInvertible :=
    Commons.Analysis.Normed.isInvertible_of_det_columns hcol1 hcol2 hdet
  obtain ⟨D, hD⟩ := hInv
  have hstrict : HasStrictFDerivAt (collGramMap r a b m)
      (fderiv ℝ (collGramMap r a b m) (b - a, m)) (b - a, m) :=
    (ContDiff.contDiffAt hGcd).hasStrictFDerivAt (by simp)
  have hstrictA : HasStrictFDerivAt (collGramMap r a b m) (D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
      (b - a, m) := hD ▸ hstrict
  obtain ⟨ε, hε, hε'⟩ := local_inj_of_hasStrictFDerivAt_equiv hstrictA
  refine ⟨ε, hε, fun y m' hy hm' hcol' => ?_⟩
  have hdist : dist ((y, m') : ℝ × ℝ) (b - a, m) < ε := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_lt hy hm'
  -- `Φ = 0` at `(y,m')` makes the reduced slice agree with its value at the base point
  have hfz : collGramMap r a b m (y, m') = collGramMap r a b m (b - a, m) := by
    have h1 : collSlice r a (y, m') = 0 := hcol'
    have h0 : collSlice r a (b - a, m) = 0 := by
      show collinearityValue r a (a + (b - a)) m = 0
      rw [show a + (b - a) = b from by ring]
      exact hcol
    unfold collGramMap
    rw [h1, h0]
  have hz := hε' (y, m') hdist hfz
  exact ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩

end Work.Drive
