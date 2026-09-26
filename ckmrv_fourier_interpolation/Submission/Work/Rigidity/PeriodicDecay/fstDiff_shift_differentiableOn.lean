import Mathlib
import Submission.Work.Rigidity.Basic
import Submission.Work.Rigidity.Diff

namespace Work.Rigidity.PeriodicDecay

/-- The function `z ↦ fstDiff f (z + I)` on `ℂ` is holomorphic on the half plane
`{z | -1 < z.im}` whenever `f ∘ ofComplex` is holomorphic on `ℍ` (i.e. on `{z | 0 < z.im}`).

Indeed, for `z` in that half plane the point `z + I` lies in `ℍ`, and

  `fstDiff f (ofComplex (z + I)) = (f ∘ ofComplex)(z + 1 + I) - (f ∘ ofComplex)(z + I)`,

because `ofComplex (z + I)` has imaginary part `z.im + 1 > 0`, so translating it by `1`
amounts to the complex translation `z ↦ z + 1`.  Both maps `z ↦ z + I` and `z ↦ z + 1 + I`
are affine (hence holomorphic), and they send `{z | -1 < z.im}` into `{z | 0 < z.im}`, so
the composition with the holomorphic `f ∘ ofComplex` is holomorphic, and so is its
difference. -/
theorem fstDiff_shift_differentiableOn {f : UpperHalfPlane → ℂ}
    (hf : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im}) :
    DifferentiableOn ℂ
      (fun z : ℂ => Work.Rigidity.fstDiff f (UpperHalfPlane.ofComplex (z + Complex.I)))
      {z : ℂ | -1 < z.im} := by
  have hI : DifferentiableOn ℂ (fun z : ℂ => z + Complex.I) {z : ℂ | -1 < z.im} :=
    (differentiable_id.add_const Complex.I).differentiableOn
  have hJ : DifferentiableOn ℂ (fun z : ℂ => z + 1 + Complex.I) {z : ℂ | -1 < z.im} :=
    ((differentiable_id.add_const (1 : ℂ)).add_const Complex.I).differentiableOn
  have hmapsI : Set.MapsTo (fun z : ℂ => z + Complex.I) {z : ℂ | -1 < z.im}
      {z : ℂ | 0 < z.im} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    simp only [Complex.add_im, Complex.I_im]
    linarith
  have hmapsJ : Set.MapsTo (fun z : ℂ => z + 1 + Complex.I) {z : ℂ | -1 < z.im}
      {z : ℂ | 0 < z.im} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    simp only [Complex.add_im, Complex.one_im, Complex.I_im]
    linarith
  have hdiff : DifferentiableOn ℂ (fun z : ℂ =>
      (f ∘ UpperHalfPlane.ofComplex) (z + 1 + Complex.I)
        - (f ∘ UpperHalfPlane.ofComplex) (z + Complex.I)) {z : ℂ | -1 < z.im} :=
    (hf.comp hJ hmapsJ).sub (hf.comp hI hmapsI)
  refine hdiff.congr ?_
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  have hw : 0 < (z + Complex.I).im := by
    simp only [Complex.add_im, Complex.I_im]; linarith
  have hw' : 0 < (z + 1 + Complex.I).im := by
    simp only [Complex.add_im, Complex.one_im, Complex.I_im]; linarith
  rw [Work.Rigidity.fstDiff_apply, Function.comp_apply, Function.comp_apply]
  have hstep : ((1 : ℝ) +ᵥ UpperHalfPlane.ofComplex (z + Complex.I))
      = UpperHalfPlane.ofComplex (z + 1 + Complex.I) := by
    ext
    rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    push_cast
    ring
  rw [hstep]

end Work.Rigidity.PeriodicDecay
