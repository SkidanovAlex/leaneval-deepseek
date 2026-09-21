import Mathlib
import Submission.Work.OddVolterra.SweptDefs

/-!
# Calculus of the iterated first-variable partial derivatives of `A`

For a two-variable function `A` that is smooth on an open set `O`, the `m`-th iterated
derivative of `x ↦ A x σ` is again smooth on `O`, and its two partial derivatives are
`pder A (m+1)` and `qder A m` respectively.
-/

noncomputable section

namespace Work.OddVolterra.Swept

open Work.OddVolterra

variable {A : ℝ → ℝ → ℝ} {O : Set (ℝ × ℝ)}

/-- The uncurried version of `A` is smooth on `O`, hence so is every iterated first-variable
partial derivative. -/
theorem contDiffOn_uncurried_pder (hO : IsOpen O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) O) (m : ℕ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => pder A m q.1 q.2) O := by
  induction m with
  | zero => simpa [pder] using hA
  | succ m ih =>
    have hfderiv : ContDiffOn ℝ (↑(⊤ : ℕ∞))
        (fun q : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) q) ((1:ℝ),(0:ℝ))) O :=
      (ih.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
    refine hfderiv.congr ?_
    intro q hq
    have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) q :=
      (ih.differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds hq)
    have hcurve : HasDerivAt (fun x : ℝ => (x, q.2)) ((1:ℝ),(0:ℝ)) q.1 :=
      (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
    have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt q.1 hcurve
    have h1 : deriv (fun x : ℝ => pder A m x q.2) q.1
        = (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) q) ((1:ℝ),(0:ℝ)) := hcomp.deriv
    rw [← h1]
    simp only [pder, iteratedDeriv_succ]

/-- Derivative of `x ↦ pder A m x σ` is `pder A (m+1) · σ`. -/
theorem hasDerivAt_pder_fst (hO : IsOpen O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) O) {m : ℕ} {u σ : ℝ}
    (huσ : (u, σ) ∈ O) :
    HasDerivAt (fun x : ℝ => pder A m x σ) (pder A (m + 1) u σ) u := by
  have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ) :=
    ((contDiffOn_uncurried_pder hO hA m).differentiableOn (by norm_num)).differentiableAt
      (hO.mem_nhds huσ)
  have hcurve : HasDerivAt (fun x : ℝ => (x, σ)) ((1:ℝ),(0:ℝ)) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u σ)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt u hcurve
  have hcomp' : HasDerivAt (fun x : ℝ => pder A m x σ)
      ((fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((1:ℝ),(0:ℝ))) u := by
    simpa [Function.comp_def] using hcomp
  have hval : (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((1:ℝ),(0:ℝ))
      = pder A (m + 1) u σ := by
    rw [← hcomp'.deriv]; simp only [pder, iteratedDeriv_succ]
  exact hcomp'.congr_deriv hval

/-- Derivative of `y ↦ pder A m u y` is `qder A m ·`. -/
theorem hasDerivAt_pder_snd (hO : IsOpen O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) O) {m : ℕ} {u σ : ℝ}
    (huσ : (u, σ) ∈ O) :
    HasDerivAt (fun y : ℝ => pder A m u y) (qder A m u σ) σ := by
  have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ) :=
    ((contDiffOn_uncurried_pder hO hA m).differentiableOn (by norm_num)).differentiableAt
      (hO.mem_nhds huσ)
  have hcurve : HasDerivAt (fun y : ℝ => (u, y)) ((0:ℝ),(1:ℝ)) σ :=
    (hasDerivAt_const σ u).prodMk (hasDerivAt_id σ)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt σ hcurve
  have hcomp' : HasDerivAt (fun y : ℝ => pder A m u y)
      ((fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((0:ℝ),(1:ℝ))) σ := by
    simpa [Function.comp_def] using hcomp
  have hval : (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((0:ℝ),(1:ℝ))
      = qder A m u σ := by
    rw [← hcomp'.deriv]; rfl
  exact hcomp'.congr_deriv hval

/-- The Fréchet derivative of the uncurried `m`-th first-variable partial of `A`. -/
theorem hasFDerivAt_uncurried_pder (hO : IsOpen O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) O) {m : ℕ} {u σ : ℝ}
    (huσ : (u, σ) ∈ O) :
    HasFDerivAt (fun q : ℝ × ℝ => pder A m q.1 q.2)
      ((pder A (m + 1) u σ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (qder A m u σ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, σ) := by
  have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ) :=
    ((contDiffOn_uncurried_pder hO hA m).differentiableOn (by norm_num)).differentiableAt
      (hO.mem_nhds huσ)
  have hfd := hdiff.hasFDerivAt
  have hcurve1 : HasDerivAt (fun x : ℝ => (x, σ)) ((1:ℝ),(0:ℝ)) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u σ)
  have hcurve2 : HasDerivAt (fun y : ℝ => (u, y)) ((0:ℝ),(1:ℝ)) σ :=
    (hasDerivAt_const σ u).prodMk (hasDerivAt_id σ)
  have hcomp1 : HasDerivAt (fun x : ℝ => pder A m x σ)
      ((fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((1:ℝ),(0:ℝ))) u := by
    simpa [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt u hcurve1
  have hcomp2 : HasDerivAt (fun y : ℝ => pder A m u y)
      ((fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((0:ℝ),(1:ℝ))) σ := by
    simpa [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt σ hcurve2
  have h1 : (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((1:ℝ),(0:ℝ))
      = pder A (m+1) u σ := by
    rw [← hcomp1.deriv]; simp only [pder, iteratedDeriv_succ]
  have h2 : (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((0:ℝ),(1:ℝ))
      = qder A m u σ := by
    rw [← hcomp2.deriv]; rfl
  have hL : (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ))
      = ((pder A (m + 1) u σ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (qder A m u σ) • ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = v.1 • ((1:ℝ),(0:ℝ)) + v.2 • ((0:ℝ),(1:ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul, h1, h2]
    simp [smul_eq_mul, mul_comm]
  rw [← hL]
  exact hfd

/-- The uncurried version of `qder A m` is smooth wherever `A` is. -/
theorem contDiffOn_uncurried_qder (hO : IsOpen O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) O) (m : ℕ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => qder A m q.1 q.2) O := by
  have hfd : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fun q : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) q) ((0:ℝ),(1:ℝ))) O :=
    ((contDiffOn_uncurried_pder hO hA m).fderiv_of_isOpen hO (by simp)).clm_apply
      contDiffOn_const
  refine hfd.congr ?_
  intro q hq
  have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) q :=
    ((contDiffOn_uncurried_pder hO hA m).differentiableOn (by norm_num)).differentiableAt
      (hO.mem_nhds hq)
  have hcurve : HasDerivAt (fun y : ℝ => (q.1, y)) ((0:ℝ),(1:ℝ)) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt q.2 hcurve
  have hcomp' : HasDerivAt (fun y : ℝ => pder A m q.1 y)
      ((fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) q) ((0:ℝ),(1:ℝ))) q.2 := by
    simpa [Function.comp_def] using hcomp
  exact hcomp'.deriv

end Work.OddVolterra.Swept
