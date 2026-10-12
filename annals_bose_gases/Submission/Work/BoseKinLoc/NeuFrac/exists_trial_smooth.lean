import Mathlib.Analysis.Fourier.Notation
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Submission.Work.BSKinetic.integrable_kinFT_sq
import Submission.Work.BoseKinLoc.Defs
import Submission.Work.BoseKinLoc.NeuFrac.deriv_sum_pconv
import Submission.Work.BoseKinLoc.NeuFrac.exists_schwartz_resolvent_smooth
import Submission.Work.BoseKinLoc.NeuFrac.parseval_pconv_re
import Submission.Work.BoseKinLoc.NeuFrac.plancherel_pconv_schwartz
import Submission.Work.BoseKinLoc.NeuFrac.trial_algebra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.NeuFrac.exists_trial_smooth`

**The intended (non-vacuous) form of `exists_trial`.**

The requested statement `Work.BoseKinLoc.NeuFrac.exists_trial` quantifies over
`hψ : ContDiff ℝ ⊤ ψ`, and `⊤ : ℕ∞ω` is the *analytic* order `ω`, not `C^∞` (which is the
scoped notation `∞`).  With `HasCompactSupport` an analytic `ψ` is identically zero, so the
requested statement is vacuous; see the discussion in `NeuFrac/exists_trial.lean` and the
sibling refutation in `NeuFrac/exists_flat_g.lean`.

This file proves the statement the consumer `neumann_bound` actually needs (FS `final_v2.tex`,
BS `eq:Neumannineq`): for `ψ ∈ C^∞` **smooth** with compact support and `c > 0` there is a
smooth `θ` such that

`2∫ψθ − Σ_k∫(∂_kθ)² − c∫θ² ≥ (2π)⁻³∫_p ‖ψ̂(p)‖²/(‖p‖²+c)`.

The trial function is the resolvent `θ = Re 𝓕⁻¹((‖p‖²+c)⁻¹ 𝓕ψ)`, a Schwartz function: its
Fourier multiplier construction, and the reality/symmetry argument, are
`exists_schwartz_resolvent_smooth`.  The three quadratic ingredients are then the
p-convention Plancherel identities `plancherel_pconv_schwartz` (the mass), `deriv_sum_pconv`
(the kinetic energy) and `parseval_pconv_re` (the cross term `/∫ψθ`), and the final pointwise
algebra `2/(x+c) − x/(x+c)² − c/(x+c)² = 1/(x+c)` is `trial_algebra`.

This yields `Q(θ) = 2∫ψθ − Σ_k∫(∂_kθ)² − c∫θ²ᵢ=ᵢ(2π)⁻³∫_p ‖ψ̂(p)‖²/(‖p‖²+c)` **with equality**,
i.e. the attained supremum of `Q` over the trial class, matching the definition of
`raFrac`'s plancherel form in `raFrac_eq`.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff Real BigOperators

set_option autoImplicit false

namespace Work.BoseKinLoc.NeuFrac

theorem exists_trial_smooth (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcs : HasCompactSupport ψ) {c : ℝ} (hc : 0 < c) :
    ∃ θ : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiff ℝ ∞ θ ∧
      MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => (θ x) ^ 2) ∧
      (∀ k : Fin 3, MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        (fderiv ℝ θ x (Submission.BoseGases.kcStdBasis k)) ^ 2)) ∧
      MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ψ x * θ x) ∧
      (2 * (∫ x : EuclideanSpace ℝ (Fin 3), ψ x * θ x)
        - (∑ k : Fin 3, ∫ x : EuclideanSpace ℝ (Fin 3),
            (fderiv ℝ θ x (Submission.BoseGases.kcStdBasis k)) ^ 2)
        - c * (∫ x : EuclideanSpace ℝ (Fin 3), (θ x) ^ 2)
        ≥ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 / (‖p‖ ^ 2 + c)) := by
  obtain ⟨W, hWre, hWft⟩ := exists_schwartz_resolvent_smooth ψ hψ hcs hc
  set θ : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => (W x).re with hθdef
  have hWeq : (W : EuclideanSpace ℝ (Fin 3) → ℂ) = fun y => ((θ y : ℝ) : ℂ) := by
    funext y
    rw [hθdef]
    exact Complex.ext rfl (by simp [hWre y])
  have hθcont : ContDiff ℝ ∞ θ := by
    show ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) => (W x).re)
    have h := (Complex.reCLM.contDiff (n := ∞)).comp (W.smooth (⊤ : ℕ∞))
    simpa only [Function.comp_def, Complex.reCLM_apply] using h
  have hθdiff : ∀ x : EuclideanSpace ℝ (Fin 3), DifferentiableAt ℝ θ x := by
    intro x
    have h2 : DifferentiableAt ℝ ((Complex.reCLM : ℂ →L[ℝ] ℝ) ∘ (W : EuclideanSpace ℝ (Fin 3) → ℂ)) x :=
      Complex.reCLM.differentiableAt.comp x W.differentiableAt
    simpa only [hθdef, Function.comp_def, Complex.reCLM_apply] using h2
  have hchain : ∀ (x m : EuclideanSpace ℝ (Fin 3)),
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => ((θ y : ℝ) : ℂ)) x m
      = ((fderiv ℝ θ x m : ℝ) : ℂ) := by
    intro x m
    have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => ((θ y : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (fderiv ℝ θ x)) x :=
      (Complex.ofRealCLM.hasFDerivAt (x := θ x)).comp x (hθdiff x).hasFDerivAt
    rw [h1.fderiv]
    rfl
  have hWfd : ∀ (x m : EuclideanSpace ℝ (Fin 3)),
      fderiv ℝ (W : EuclideanSpace ℝ (Fin 3) → ℂ) x m = ((fderiv ℝ θ x m : ℝ) : ℂ) := by
    intro x m
    rw [hWeq]
    exact hchain x m
  have hmul : ∀ p : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.kinFT (W : EuclideanSpace ℝ (Fin 3) → ℂ) p
      = ((↑‖p‖ : ℂ) ^ 2 + ↑c)⁻¹ * Work.BoseKinLoc.fhat ψ p := by
    intro p
    rw [hWft p]
    rfl
  have haeq : ∀ p : EuclideanSpace ℝ (Fin 3),
      ((↑‖p‖ : ℂ) ^ 2 + ↑c)⁻¹ = (((‖p‖ ^ 2 + c)⁻¹ : ℝ) : ℂ) := by
    intro p
    rw [← Complex.ofReal_pow, ← Complex.ofReal_add, ← Complex.ofReal_inv]
  have hnorm : ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖((((‖p‖ ^ 2 + c)⁻¹ : ℝ)) : ℂ)‖ = (‖p‖ ^ 2 + c)⁻¹ := by
    intro p
    have h2 : ‖((((‖p‖ ^ 2 + c)⁻¹ : ℝ)) : ℂ)‖ ^ 2 = ((‖p‖ ^ 2 + c)⁻¹) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
    nlinarith [norm_nonneg ((((‖p‖ ^ 2 + c)⁻¹ : ℝ)) : ℂ),
      show (0 : ℝ) ≤ (‖p‖ ^ 2 + c)⁻¹ by positivity]
  have hkin : ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖Submission.BoseGases.kinFT (W : EuclideanSpace ℝ (Fin 3) → ℂ) p‖ ^ 2
      = ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 / (‖p‖ ^ 2 + c) ^ 2 := by
    intro p
    rw [hmul p, haeq p, norm_mul, hnorm p, mul_pow, div_eq_mul_inv, ← inv_pow]
    ring
  have hψc_smooth : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) => (ψ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hψ
  have hψc_cs : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin 3) => (ψ x : ℂ)) :=
    hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)
  set F : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ := hψc_cs.toSchwartzMap hψc_smooth with hF
  have hF_coe : (F : EuclideanSpace ℝ (Fin 3) → ℂ) = fun x => (ψ x : ℂ) := rfl
  have hFreal : ∀ x : EuclideanSpace ℝ (Fin 3), (F x).im = 0 := by
    intro x; rw [hF_coe]; simp
  have hA : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) := by
    simpa only [Work.BoseKinLoc.fhat] using Work.BSKinetic.integrable_kinFT_sq ψ hψ hcs
  set J0 : ℝ := ∫ p : EuclideanSpace ℝ (Fin 3), ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 / (‖p‖ ^ 2 + c)
    with hJ0
  set J1 : ℝ := ∫ p : EuclideanSpace ℝ (Fin 3),
      ‖p‖ ^ 2 * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 / (‖p‖ ^ 2 + c) ^ 2 with hJ1
  set J2 : ℝ := ∫ p : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 / (‖p‖ ^ 2 + c) ^ 2 with hJ2
  refine ⟨θ, hθcont, ?_, ?_, ?_, ?_⟩
  · have hmem : MemLp (W : EuclideanSpace ℝ (Fin 3) → ℂ) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
      SchwartzMap.memLp W 2 volume
    have h1 : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ‖W x‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
    refine h1.congr ?_
    filter_upwards with x
    show ‖W x‖ ^ 2 = (θ x) ^ 2
    rw [hθdef, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hWre x]
    ring
  · intro k
    have hLD : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        ‖(LineDeriv.lineDerivOp (Submission.BoseGases.kcStdBasis k) W :
            EuclideanSpace ℝ (Fin 3) → ℂ) x‖ ^ 2) := by
      have hmem : MemLp (LineDeriv.lineDerivOp (Submission.BoseGases.kcStdBasis k) W :
          EuclideanSpace ℝ (Fin 3) → ℂ) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
        SchwartzMap.memLp _ 2 volume
      exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
    refine hLD.congr ?_
    filter_upwards with x
    show ‖(LineDeriv.lineDerivOp (Submission.BoseGases.kcStdBasis k) W :
        EuclideanSpace ℝ (Fin 3) → ℂ) x‖ ^ 2
      = (fderiv ℝ θ x (Submission.BoseGases.kcStdBasis k)) ^ 2
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hWfd x (Submission.BoseGases.kcStdBasis k),
      ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  · have hWint : MeasureTheory.Integrable (W : EuclideanSpace ℝ (Fin 3) → ℂ) :=
      SchwartzMap.integrable W
    have hθint : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => θ x) := by
      refine hWint.re.congr ?_
      filter_upwards with x
      show RCLike.re (W x) = θ x
      rw [hθdef]
      rfl
    have hbdd : ∀ x : EuclideanSpace ℝ (Fin 3), ‖ψ x‖ ≤ SchwartzMap.seminorm ℂ 0 0 F := by
      intro x
      have h := SchwartzMap.norm_le_seminorm ℂ F x
      rwa [show ‖F x‖ = ‖ψ x‖ from by simp [hF_coe]] at h
    refine (hθint.mul_bdd hψ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hbdd)).congr ?_
    filter_upwards with x
    ring
  · have hI2 : (∫ x : EuclideanSpace ℝ (Fin 3), (θ x) ^ 2)
        = ((2 * Real.pi) ^ 3)⁻¹ * J2 := by
      rw [hJ2]
      rw [show (∫ x : EuclideanSpace ℝ (Fin 3), (θ x) ^ 2)
            = ∫ x : EuclideanSpace ℝ (Fin 3), ‖W x‖ ^ 2 from by
        refine integral_congr_ae ?_
        filter_upwards with x
        show (θ x) ^ 2 = ‖W x‖ ^ 2
        rw [hθdef, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hWre x]
        ring]
      rw [← plancherel_pconv_schwartz W]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards with x
      exact hkin x
    have hI1 : (∑ k : Fin 3, ∫ x : EuclideanSpace ℝ (Fin 3),
            (fderiv ℝ θ x (Submission.BoseGases.kcStdBasis k)) ^ 2)
        = ((2 * Real.pi) ^ 3)⁻¹ * J1 := by
      rw [hJ1]
      rw [show (∑ k : Fin 3, ∫ x : EuclideanSpace ℝ (Fin 3),
              (fderiv ℝ θ x (Submission.BoseGases.kcStdBasis k)) ^ 2)
          = ∑ k : Fin 3, ∫ x : EuclideanSpace ℝ (Fin 3),
              ‖fderiv ℝ (W : EuclideanSpace ℝ (Fin 3) → ℂ) x
                (Submission.BoseGases.kcStdBasis k)‖ ^ 2 from by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine integral_congr_ae ?_
        filter_upwards with x
        show (fderiv ℝ θ x (Submission.BoseGases.kcStdBasis k)) ^ 2
          = ‖fderiv ℝ (W : EuclideanSpace ℝ (Fin 3) → ℂ) x
              (Submission.BoseGases.kcStdBasis k)‖ ^ 2
        rw [hWfd x (Submission.BoseGases.kcStdBasis k), ← Complex.normSq_eq_norm_sq,
          Complex.normSq_ofReal]
        ring]
      rw [deriv_sum_pconv W]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [hkin x]
      ring
    have hA0 : (∫ x : EuclideanSpace ℝ (Fin 3), ψ x * θ x)
        = ((2 * Real.pi) ^ 3)⁻¹ * J0 := by
      rw [hJ0]
      rw [show (∫ x : EuclideanSpace ℝ (Fin 3), ψ x * θ x)
            = ∫ x : EuclideanSpace ℝ (Fin 3), (F x).re * (W x).re from by
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [hθdef, hF_coe]
        simp]
      rw [parseval_pconv_re F W hFreal hWre]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards with x
      have hkeq : Submission.BoseGases.kinFT (F : EuclideanSpace ℝ (Fin 3) → ℂ) x
          = Work.BoseKinLoc.fhat ψ x := by
        simp only [Work.BoseKinLoc.fhat, hF_coe]
      rw [hkeq, hmul x, haeq x, map_mul, Complex.conj_ofReal]
      rw [show Work.BoseKinLoc.fhat ψ x * (((((‖x‖ ^ 2 + c)⁻¹ : ℝ)) : ℂ)
            * (starRingEnd ℂ) (Work.BoseKinLoc.fhat ψ x))
          = (((((‖x‖ ^ 2 + c)⁻¹ : ℝ)) : ℂ))
            * (Work.BoseKinLoc.fhat ψ x * (starRingEnd ℂ) (Work.BoseKinLoc.fhat ψ x)) from by ring,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.ofReal_re, div_eq_mul_inv, mul_comm]
    rw [hA0, hI1, hI2]
    have h3 : 2 * (((2 * Real.pi) ^ 3)⁻¹ * J0) - ((2 * Real.pi) ^ 3)⁻¹ * J1
        - c * (((2 * Real.pi) ^ 3)⁻¹ * J2)
        = ((2 * Real.pi) ^ 3)⁻¹ * (2 * J0 - J1 - c * J2) := by ring
    have ht : 2 * J0 - J1 - c * J2 = J0 := by
      rw [hJ0, hJ1, hJ2]
      simpa only [] using trial_algebra
        (A := fun p : EuclideanSpace ℝ (Fin 3) => ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) hc hA
    rw [h3, ht]

end Work.BoseKinLoc.NeuFrac
