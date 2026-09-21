import Mathlib
import Submission.Commons.Analysis.Calculus.iteratedFDeriv_intervalIntegral_comp_smul

/-!
# Smoothness of parametric interval integrals

If `F : ℝ × P → E` is `C^n` (globally) then so is `p ↦ ∫ θ in a..b, F (θ, p)`.

The proof is an induction on `n`.  The derivative of the parametric integral is again a
parametric integral, namely of `θ ↦ (fderiv ℝ F (θ, p)).comp (inr ℝ ℝ P)`, so the induction
hypothesis applies; the differentiation-under-the-integral-sign step is
`Commons.Analysis.Calculus.hasFDerivAt_intervalIntegral_of_continuous`.

Note that the codomain `E` must be quantified *inside* the induction, because the induction step
replaces `E` by `P →L[ℝ] E`; this is why the statement below is a `∀ (n : ℕ) (E : Type u) ...`
rather than fixing `E` in the binder list.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

universe u

namespace Work.Analysis.Calculus

theorem contDiff_intervalIntegral_param (P : Type u) [NormedAddCommGroup P] [NormedSpace ℝ P]
    [ProperSpace P] :
    ∀ (n : ℕ) (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (F : ℝ × P → E) (a b : ℝ), ContDiff ℝ (n : ℕ∞) F →
      ContDiff ℝ (n : ℕ∞) (fun p : P => ∫ θ in a..b, F (θ, p)) := by
  intro n
  induction n with
  | zero =>
      intro E _ _ _ F a b hF
      refine contDiff_zero.mpr ?_
      have huncurry : Continuous (Function.uncurry (fun (p : P) (θ : ℝ) => F (θ, p))) := by
        have hfun : Function.uncurry (fun (p : P) (θ : ℝ) => F (θ, p)) =
            fun q : P × ℝ => F (q.2, q.1) := rfl
        rw [hfun]
        have hswap : Continuous (fun q : P × ℝ => (q.2, q.1)) := by fun_prop
        exact hF.continuous.comp hswap
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : P) (θ : ℝ) => F (θ, p)) (a₀ := a) huncurry (s := fun _ : P => b)
        continuous_const
  | succ n ih =>
      intro E _ _ _ F a b hF
      have hfderiv : ContDiff ℝ (n : ℕ∞) (fderiv ℝ F) := by
        refine hF.fderiv_right ?_
        simp
      have hlin_top : ContDiff ℝ (⊤ : ℕ∞)
          (fun T : (ℝ × P) →L[ℝ] E => T.comp (ContinuousLinearMap.inr ℝ ℝ P)) := by
        fun_prop
      have hlin : ContDiff ℝ (n : ℕ∞)
          (fun T : (ℝ × P) →L[ℝ] E => T.comp (ContinuousLinearMap.inr ℝ ℝ P)) :=
        hlin_top.of_le (by exact_mod_cast le_top)
      have hG : ContDiff ℝ (n : ℕ∞)
          (fun q : ℝ × P => (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ ℝ P)) :=
        hlin.comp hfderiv
      have hInt : ContDiff ℝ (n : ℕ∞)
          (fun p : P =>
            ∫ θ in a..b, (fderiv ℝ F (θ, p)).comp (ContinuousLinearMap.inr ℝ ℝ P)) :=
        ih (P →L[ℝ] E)
          (fun q : ℝ × P => (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ ℝ P)) a b hG
      rw [show ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 from by simp]
      refine (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ)
        (f := fun p : P => ∫ θ in a..b, F (θ, p)) (n := n)).2
        ⟨fun p : P =>
          ∫ θ in a..b, (fderiv ℝ F (θ, p)).comp (ContinuousLinearMap.inr ℝ ℝ P), ?_, ?_⟩
      · exact hInt
      · intro p
        have huncurry : Continuous
            (Function.uncurry (fun (p : P) (θ : ℝ) => F (θ, p))) := by
          have hfun : Function.uncurry (fun (p : P) (θ : ℝ) => F (θ, p)) =
              fun q : P × ℝ => F (q.2, q.1) := rfl
          rw [hfun]
          exact hF.continuous.comp (by fun_prop : Continuous (fun q : P × ℝ => (q.2, q.1)))
        have huncurry' : Continuous (Function.uncurry
            (fun (p : P) (θ : ℝ) =>
              (fderiv ℝ F (θ, p)).comp (ContinuousLinearMap.inr ℝ ℝ P))) := by
          have hfun : Function.uncurry (fun (p : P) (θ : ℝ) =>
              (fderiv ℝ F (θ, p)).comp (ContinuousLinearMap.inr ℝ ℝ P)) =
              fun q : P × ℝ => (fderiv ℝ F (q.2, q.1)).comp
                (ContinuousLinearMap.inr ℝ ℝ P) := rfl
          rw [hfun]
          have h1 : Continuous (fun q : P × ℝ => fderiv ℝ F (q.2, q.1)) :=
            (hF.continuous_fderiv (by simp)).comp (by fun_prop : Continuous fun q : P × ℝ => (q.2, q.1))
          exact (by fun_prop : Continuous fun T : (ℝ × P) →L[ℝ] E =>
            T.comp (ContinuousLinearMap.inr ℝ ℝ P)).comp h1
        have hdiff : ∀ y : P, ∀ θ : ℝ,
            HasFDerivAt (fun y : P => F (θ, y))
              ((fderiv ℝ F (θ, y)).comp (ContinuousLinearMap.inr ℝ ℝ P)) y := by
          intro y θ
          have h1 : HasFDerivAt F (fderiv ℝ F (θ, y)) (θ, y) :=
            ((hF.differentiable (by simp)).differentiableAt).hasFDerivAt
          have h2 : HasFDerivAt (fun y : P => (θ, y)) (ContinuousLinearMap.inr ℝ ℝ P) y :=
            hasFDerivAt_prodMk_right θ y
          exact h1.comp y h2
        exact Commons.Analysis.Calculus.hasFDerivAt_intervalIntegral_of_continuous
          huncurry huncurry' hdiff

end Work.Analysis.Calculus
