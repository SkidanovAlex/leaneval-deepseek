import Mathlib
import Submission.Work.Drive.squareDisk
import Submission.Work.Drive.injective_fderiv_sqDisk_foldBox

namespace Work.Drive

open scoped Topology ContDiff

/-!
# The derivative of `sqDisk ∘ foldBox` in a coordinate direction never vanishes on the open square

`Work.Drive.sqDisk` is the classical square-to-disk map `sqDisk y = (a·√(1 − b²/2), b·√(1 − a²/2))`
with `a = 2 y 0 − 1`, `b = 2 y 1 − 1` (cut off by a smooth bump), and `Work.Drive.foldBox` folds the
plane coordinates into `[0,1]` by `foldFun x = (1 − cos (π x))/2`.

Here we prove: for `y ∈ [0,1]²` and a coordinate direction `i` with `y i ∈ (0,1)`, the derivative of
`g := sqDisk ∘ foldBox` at `y` *in the direction* `eᵢ` is non-zero.  Unlike
`Work.Drive.injective_fderiv_sqDisk_foldBox` (which needs **both** coordinates in `(0,1)`, because the
fold degenerates at `0` and `1`), only the single coordinate `i` has to be interior, and the direction
`eᵢ` is the one that stays non-degenerate.

The computation: along the line `t ↦ y + t • e₀` the *real part* of `g` is
`(2 foldFun (y 0 + t) − 1) · sqWeight (2 foldFun (y 1) − 1)`, whose derivative at `0` is
`π sin (π y 0) · sqWeight (2 foldFun (y 1) − 1) ≠ 0`; along `t ↦ y + t • e₁` the *imaginary part* of
`g` is `(2 foldFun (y 1 + t) − 1) · sqWeight (2 foldFun (y 0) − 1)` with derivative
`π sin (π y 1) · sqWeight (2 foldFun (y 0) − 1) ≠ 0`.  The weights never vanish on the (folded)
square, since `foldFun '' ℝ = [0,1]` makes their argument lie in `[-1,1]`, where
`sqWeight x² = 1 − x²/2 ≥ 1/2`.
-/

theorem sqDisk_foldBox_fderiv_single_ne_zero (y : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ Submission.Drive.unitBox 1) {i : Fin 2} (h : y i ∈ Set.Ioo (0 : ℝ) 1) :
    fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) => Work.Drive.sqDisk (Work.Drive.foldBox z)) y
      (EuclideanSpace.single i 1) ≠ 0 := by
  set G : EuclideanSpace ℝ (Fin 2) → ℂ := fun z => sqDisk (foldBox z) with hG
  have hcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G :=
    sqDisk_contDiff.comp (contDiff_iff_contDiffAt.mpr fun z =>
      contMDiffAt_iff_contDiffAt.mp (foldBox_contMDiff z))
  have hdiff : DifferentiableAt ℝ G y := (hcont.contDiffAt).differentiableAt (by simp)
  -- the weights at the folded coordinates are non-zero
  have hweight : ∀ j : Fin 2, sqWeight (2 * foldFun (y j) - 1) ≠ 0 := by
    intro j
    have hb : |2 * foldFun (y j) - 1| ≤ 1 := by
      have hj := foldFun_mem_Icc (y j)
      rw [abs_le]
      exact ⟨by linarith [hj.1], by linarith [hj.2]⟩
    have hsq := sqWeight_sq hb
    have hle := abs_le.mp hb
    have hpos : 0 < sqWeight (2 * foldFun (y j) - 1) ^ 2 := by
      rw [hsq]; nlinarith [hle.1, hle.2]
    intro hzero
    rw [hzero] at hpos
    norm_num at hpos
  have hsin : ∀ j : Fin 2, y j ∈ Set.Ioo (0 : ℝ) 1 →
      0 < Real.pi * Real.sin (Real.pi * (y j)) := by
    intro j hj
    have hπ0 : 0 < Real.pi * y j := mul_pos Real.pi_pos hj.1
    have hπ1 : Real.pi * y j < Real.pi := by nlinarith [hj.2, Real.pi_pos]
    have := Real.sin_pos_of_pos_of_lt_pi hπ0 hπ1
    positivity
  have himm : ∀ (i : Fin 2), y i ∈ Set.Ioo (0 : ℝ) 1 →
      fderiv ℝ G y (EuclideanSpace.single i 1) ≠ 0 := by
    intro i hi
    have hline := hdiff.hasFDerivAt.hasLineDerivAt (EuclideanSpace.single i (1 : ℝ))
    fin_cases i
    · -- `i = 0`: the real part of the line derivative is `π sin (π y 0) · sqWeight (2 foldFun (y 1) − 1)`
      have hpt : ∀ t : ℝ,
          (sqDisk (foldBox (y + t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))).re
            = (2 * foldFun (y 0 + t) - 1) * sqWeight (2 * foldFun (y 1) - 1) := fun t => by
        simp [sqDisk_apply_re, foldBox]
      have h1 : HasDerivAt
          (fun t : ℝ => Complex.reCLM (G (y + t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))))
          (Complex.reCLM ((fderiv ℝ G y) (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))) 0 :=
        hasDerivAt_clm_comp' Complex.reCLM hline
      have hlin0 : HasDerivAt (fun t : ℝ => y 0 + t) (1 : ℝ) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add (y 0)
      have hfold0 : HasDerivAt (fun t : ℝ => foldFun (y 0 + t))
          (Real.pi * Real.sin (Real.pi * (y 0)) / 2) 0 := by
        have hp : (fun t : ℝ => y 0 + t) 0 = y 0 := by simp
        have hrec : HasDerivAt foldFun (Real.pi * Real.sin (Real.pi * (y 0)) / 2)
            ((fun t : ℝ => y 0 + t) 0) := by
          rw [hp]; exact foldFun_hasDerivAt' (y 0)
        have := hrec.comp 0 hlin0
        simpa [Function.comp_def] using this
      have hA0 : HasDerivAt (fun t : ℝ => 2 * foldFun (y 0 + t) - 1)
          (Real.pi * Real.sin (Real.pi * (y 0))) 0 := by
        have h2 := (hfold0.const_mul 2).sub_const 1
        refine h2.congr_deriv ?_
        ring
      have hF0 : HasDerivAt
          (fun t : ℝ => (2 * foldFun (y 0 + t) - 1) * sqWeight (2 * foldFun (y 1) - 1))
          (Real.pi * Real.sin (Real.pi * (y 0)) * sqWeight (2 * foldFun (y 1) - 1)) 0 :=
        hA0.mul_const _
      have hR : HasDerivAt
          (fun t : ℝ => Complex.reCLM (G (y + t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))))
          (Real.pi * Real.sin (Real.pi * (y 0)) * sqWeight (2 * foldFun (y 1) - 1)) 0 := by
        refine hF0.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
        funext t
        simp only [hG, Complex.reCLM_apply]
        exact hpt t
      have heq := hR.unique h1
      have hne : Real.pi * Real.sin (Real.pi * (y 0)) * sqWeight (2 * foldFun (y 1) - 1) ≠ 0 :=
        mul_ne_zero (ne_of_gt (hsin 0 hi)) (hweight 1)
      have key : Complex.reCLM ((fderiv ℝ G y) (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) ≠ 0 :=
        fun hz => hne (heq.trans hz)
      intro hzero
      exact key (by have hhc := congrArg Complex.reCLM hzero; simpa using hhc)
    · -- `i = 1`: the imaginary part of the line derivative is `π sin (π y 1) · sqWeight (2 foldFun (y 0) − 1)`
      have hpt : ∀ t : ℝ,
          (sqDisk (foldBox (y + t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))).im
            = (2 * foldFun (y 1 + t) - 1) * sqWeight (2 * foldFun (y 0) - 1) := fun t => by
        simp [sqDisk_apply_im, foldBox]
      have h1 : HasDerivAt
          (fun t : ℝ => Complex.imCLM (G (y + t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))))
          (Complex.imCLM ((fderiv ℝ G y) (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))) 0 :=
        hasDerivAt_clm_comp' Complex.imCLM hline
      have hlin1 : HasDerivAt (fun t : ℝ => y 1 + t) (1 : ℝ) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add (y 1)
      have hfold1 : HasDerivAt (fun t : ℝ => foldFun (y 1 + t))
          (Real.pi * Real.sin (Real.pi * (y 1)) / 2) 0 := by
        have hp : (fun t : ℝ => y 1 + t) 0 = y 1 := by simp
        have hrec : HasDerivAt foldFun (Real.pi * Real.sin (Real.pi * (y 1)) / 2)
            ((fun t : ℝ => y 1 + t) 0) := by
          rw [hp]; exact foldFun_hasDerivAt' (y 1)
        have := hrec.comp 0 hlin1
        simpa [Function.comp_def] using this
      have hA1 : HasDerivAt (fun t : ℝ => 2 * foldFun (y 1 + t) - 1)
          (Real.pi * Real.sin (Real.pi * (y 1))) 0 := by
        have h2 := (hfold1.const_mul 2).sub_const 1
        refine h2.congr_deriv ?_
        ring
      have hF1 : HasDerivAt
          (fun t : ℝ => (2 * foldFun (y 1 + t) - 1) * sqWeight (2 * foldFun (y 0) - 1))
          (Real.pi * Real.sin (Real.pi * (y 1)) * sqWeight (2 * foldFun (y 0) - 1)) 0 :=
        hA1.mul_const _
      have hS : HasDerivAt
          (fun t : ℝ => Complex.imCLM (G (y + t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))))
          (Real.pi * Real.sin (Real.pi * (y 1)) * sqWeight (2 * foldFun (y 0) - 1)) 0 := by
        refine hF1.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
        funext t
        simp only [hG, Complex.imCLM_apply]
        exact hpt t
      have heq := hS.unique h1
      have hne : Real.pi * Real.sin (Real.pi * (y 1)) * sqWeight (2 * foldFun (y 0) - 1) ≠ 0 :=
        mul_ne_zero (ne_of_gt (hsin 1 hi)) (hweight 0)
      have key : Complex.imCLM ((fderiv ℝ G y) (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) ≠ 0 :=
        fun hz => hne (heq.trans hz)
      intro hzero
      exact key (by have hhc := congrArg Complex.imCLM hzero; simpa using hhc)
  exact himm i h

end Work.Drive
