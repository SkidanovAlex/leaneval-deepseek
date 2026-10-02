import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Strat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A scalar "partial derivative" with non-vanishing derivative

If the `(k+1)`-st iterated derivative of `f : ℝⁿ → ℝᵐ` at `x` does not vanish, then some *scalar*
function obtained from the `k`-th iterated derivative of `f` has non-vanishing derivative at `x`,
and vanishes at every point where the derivatives of `f` of order `≤ k` vanish.

This is the input of the "vanishing stratum" piece of Sard's theorem: the stratum
`Zk f k \ Zk f (k+1)` lies in the zero set of such a `σ`, along which `σ` has non-vanishing
derivative, so that the stratum lies in a smooth hypersurface.
-/

open scoped ContDiff MeasureTheory
open MeasureTheory Set

namespace Work.ThomBordism.Transversality.Sard

open Work.ThomBordism.Transversality (CInf CInfOn VanishToOrder Zk IsCriticalPoint)

/-- **The scalar partial of order `k` with non-vanishing derivative.** -/
theorem scalarPartial {n m k : ℕ} (hk : 1 ≤ k)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} (hf : CInf f)
    (h : iteratedFDeriv ℝ (k+1) f x ≠ 0) :
    ∃ σ : EuclideanSpace ℝ (Fin n) → ℝ, CInf σ ∧
      (∀ y, VanishToOrder f k y → σ y = 0) ∧ fderiv ℝ σ x ≠ 0 := by
  classical
  -- a non-vanishing value of the `(k+1)`-st derivative, and one of its coordinates
  obtain ⟨mm, hm⟩ : ∃ mm : Fin (k+1) → EuclideanSpace ℝ (Fin n),
      (iteratedFDeriv ℝ (k+1) f x) mm ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (ContinuousMultilinearMap.ext hc)
  obtain ⟨j, hj⟩ : ∃ j : Fin m, ((iteratedFDeriv ℝ (k+1) f x) mm).ofLp j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hm (PiLp.ext fun i => by simpa using hc i)
  -- the two continuous linear maps appearing in the scalar partial
  set A : ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin m)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin m)) (Fin.tail mm) with hA
  set v : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin m => ℝ) j with hv
  refine ⟨fun y => v (A (iteratedFDeriv ℝ k f y)), ?_, ?_, ?_⟩
  · -- smoothness
    have hΦ : CInf fun y : EuclideanSpace ℝ (Fin n) => iteratedFDeriv ℝ k f y :=
      hf.iteratedFDeriv_right (i := k) (by exact le_of_eq rfl)
    exact v.contDiff.comp (A.contDiff.comp hΦ)
  · -- vanishing on the stratum
    intro y hy
    have h0 : iteratedFDeriv ℝ k f y = 0 := hy k hk le_rfl
    simp [h0]
  · -- the derivative at `x`
    have hΦ : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => iteratedFDeriv ℝ k f y)
        (fderiv ℝ (iteratedFDeriv ℝ k f) x) x :=
      (hf.contDiffAt.iteratedFDeriv_right (m := smoothHeight) (i := k) (by exact le_of_eq rfl)).hasStrictFDerivAt
        (n := smoothHeight) (by simp) |>.hasFDerivAt
    have h1 : HasFDerivAt (A ∘ fun y : EuclideanSpace ℝ (Fin n) => iteratedFDeriv ℝ k f y)
        (A ∘SL fderiv ℝ (iteratedFDeriv ℝ k f) x) x :=
      (ContinuousLinearMap.hasFDerivAt A).comp x hΦ
    have h2 : HasFDerivAt (fun y => v (A (iteratedFDeriv ℝ k f y)))
        (v ∘SL (A ∘SL fderiv ℝ (iteratedFDeriv ℝ k f) x)) x :=
      HasFDerivAt.comp x (ContinuousLinearMap.hasFDerivAt v) h1
    rw [h2.fderiv]
    have hval : (v ∘SL (A ∘SL fderiv ℝ (iteratedFDeriv ℝ k f) x)) (mm 0)
        = ((iteratedFDeriv ℝ (k+1) f x) mm).ofLp j := by
      simp only [ContinuousLinearMap.comp_apply, hA, hv, PiLp.proj_apply,
        ContinuousMultilinearMap.apply_apply, iteratedFDeriv_succ_apply_left]
    intro hzero
    have h1 := congrArg (fun (g : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) => g (mm 0)) hzero
    simp only [ContinuousLinearMap.zero_apply] at h1
    rw [hval] at h1
    exact hj h1

end Work.ThomBordism.Transversality.Sard
