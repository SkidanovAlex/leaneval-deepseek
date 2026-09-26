import Mathlib
import Submission.Work.RadialSpace.contDiff_parametric_integral

namespace Work.RadialSpace

open Filter Topology MeasureTheory Set
open scoped Topology ContDiff Interval

/-!
# Iterated derivatives of the parametric interval integral `u ↦ ∫ t in (0:ℝ)..1, φ (u * t)`

The `j`-th derivative of `u ↦ ∫ t in 0..1, φ (u * t)` is obtained by differentiating `j` times
under the integral sign: it equals `∫ t in 0..1, t ^ j * φ^{(j)} (u * t)`.

The proof is an induction on `j`.  The inductive step differentiates under the integral sign using
`hasDerivAt_intervalIntegral_param` from `Submission.Work.RadialSpace.contDiff_parametric_integral`;
the pointwise derivative of the integrand `t ↦ t ^ j * φ^{(j)} (u * t)` is computed with the
one-dimensional chain rule (`HasDerivAt.scomp`).
-/

/-- The `j`-th iterated derivative of a smooth function is smooth. -/
private lemma contDiff_iteratedDeriv (φ : ℝ → ℂ) (hφ : ContDiff ℝ Smooth φ) (j : ℕ) :
    ContDiff ℝ Smooth (iteratedDeriv j φ) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv j hφ

/-- The uncurried integrand `(u, t) ↦ t ^ j * φ^{(j)} (u * t)` is `C^1` (indeed smooth). -/
private lemma contDiffOn_uncurry_weighted (φ : ℝ → ℂ) (hφ : ContDiff ℝ Smooth φ) (j : ℕ) :
    ContDiffOn ℝ (((0 : ℕ) : ℕ∞ω) + 1)
      (Function.uncurry (fun u t : ℝ => t ^ j * iteratedDeriv j φ (u * t)))
      (Set.univ ×ˢ Set.univ) := by
  have hgs : ContDiff ℝ Smooth (iteratedDeriv j φ) := contDiff_iteratedDeriv φ hφ j
  have hcomp : ContDiff ℝ Smooth (fun p : ℝ × ℝ => iteratedDeriv j φ (p.1 * p.2)) :=
    hgs.comp (contDiff_fst.mul contDiff_snd)
  have hro : ContDiff ℝ Smooth (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff).comp contDiff_snd
  have hprod : ContDiff ℝ (((0 : ℕ) : ℕ∞ω) + 1)
      (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) ^ j * iteratedDeriv j φ (p.1 * p.2)) :=
    ((hro.pow j).mul hcomp).of_le (by decide)
  rw [Set.univ_prod_univ, contDiffOn_univ]
  exact hprod

/-- The pointwise derivative of the integrand `v ↦ t ^ j * φ^{(j)} (v * t)`. -/
private lemma deriv_weighted_iteratedDeriv (φ : ℝ → ℂ) (hφ : ContDiff ℝ Smooth φ)
    (j : ℕ) (t u : ℝ) :
    deriv (fun v : ℝ => t ^ j * iteratedDeriv j φ (v * t)) u
      = t ^ (j + 1) * iteratedDeriv (j + 1) φ (u * t) := by
  have hgs : ContDiff ℝ Smooth (iteratedDeriv j φ) := contDiff_iteratedDeriv φ hφ j
  have hdiff : Differentiable ℝ (iteratedDeriv j φ) := hgs.differentiable (by decide)
  have hinner : HasDerivAt (fun v : ℝ => v * t) t u := by
    simpa using (hasDerivAt_id u).mul_const t
  have houter : HasDerivAt (iteratedDeriv j φ) (deriv (iteratedDeriv j φ) (u * t)) (u * t) :=
    (hdiff.differentiableAt (x := u * t)).hasDerivAt
  have h := (houter.scomp u hinner).const_mul (t ^ j : ℂ)
  simp only [Function.comp_apply] at h
  rw [h.deriv, ← iteratedDeriv_succ, Complex.real_smul, pow_succ']
  ring

theorem iteratedDeriv_intervalIntegral_param (φ : ℝ → ℂ) (hφ : ContDiff ℝ Work.RadialSpace.Smooth φ)
    (j : ℕ) (u : ℝ) :
    iteratedDeriv j (fun u : ℝ => ∫ t in (0 : ℝ)..1, φ (u * t)) u
      = ∫ t in (0 : ℝ)..1, t ^ j * iteratedDeriv j φ (u * t) := by
  have key : ∀ j : ℕ, iteratedDeriv j (fun u : ℝ => ∫ t in (0 : ℝ)..1, φ (u * t))
      = fun u : ℝ => ∫ t in (0 : ℝ)..1, t ^ j * iteratedDeriv j φ (u * t) := by
    intro j
    induction j with
    | zero =>
      funext u
      simp [iteratedDeriv_zero]
    | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext u
      have hstep : deriv (fun u => ∫ t in (0 : ℝ)..1, t ^ j * iteratedDeriv j φ (u * t)) u
          = ∫ t in (0 : ℝ)..1, deriv (fun v : ℝ => t ^ j * iteratedDeriv j φ (v * t)) u := by
        simpa using (hasDerivAt_intervalIntegral_param (s := Set.univ) (m := 0)
          (k := fun u t : ℝ => t ^ j * iteratedDeriv j φ (u * t)) isOpen_univ
          (contDiffOn_uncurry_weighted φ hφ j) (Set.mem_univ u)).deriv
      rw [hstep]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      exact deriv_weighted_iteratedDeriv φ hφ j t u
  exact congrFun (key j) u

end Work.RadialSpace
