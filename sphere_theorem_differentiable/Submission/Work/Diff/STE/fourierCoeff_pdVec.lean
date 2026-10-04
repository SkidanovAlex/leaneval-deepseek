import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.fourierCoeff_pd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Fourier coefficients of iterated partial derivatives

Layer A of the STE Fourier toolkit, iterated form of `fourierCoeff_pd`: if `f` is `Cᵏ` and
`1`-periodic then the Fourier multiplier of `∂_{l 0} ⋯ ∂_{l (k-1)}` is the product
`∏ i, 2πi m (l i)`,

  `fourierCoeff (pdVec k l f) m = (∏ i, 2πi m (l i)) * fourierCoeff f m`.

Two auxiliary facts about `pd` are used, and proved here:

* `pd j f` is again `1`-periodic in every coordinate when `f` is (the derivative of a periodic
  function is periodic, since translating the argument does not change the derivative);
* `pd j f` is `Cᵐ` when `f` is `Cᵐ⁺¹` (the derivative `fderiv ℝ f` is `Cᵐ` and `pd j f` is its
  composition with the constant map `x ↦ (x, eⱼ)`).

The induction on `k` splits off the *last* index, because `pdVec k l f = pdList (List.ofFn l) f`
and `List.foldr` peels the head; with `List.ofFn_succ'` the list `List.ofFn l` is the append
`(List.ofFn (l ∘ Fin.castSucc)).concat (l (Fin.last _))`, so the last derivative is the
outermost one and the induction hypothesis applies to `pd (l (Fin.last k)) f`.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The derivative of a `1`-periodic function (in every coordinate) is again periodic: the
derivative of `y ↦ f (y + c)` at `x` is `fderiv f (x + c)` because translating by a constant
has derivative the identity, and `f (· + c) = f`. -/
lemma periodicIn_pd_of_differentiable (i j : ι) {f : (ι → ℝ) → ℂ} (hf : Differentiable ℝ f)
    (hper : PeriodicIn i f) : PeriodicIn i (pd j f) := by
  intro x
  have hφ : fderiv ℝ (fun y : ι → ℝ => y + Pi.single i 1) x
      = ContinuousLinearMap.id ℝ (ι → ℝ) := by
    simp
  have hcomp : fderiv ℝ (fun y : ι → ℝ => f (y + Pi.single i 1)) x = fderiv ℝ f x := by
    rw [show (fun y : ι → ℝ => f (y + Pi.single i 1)) = f from funext hper]
  have h2 : fderiv ℝ (fun y : ι → ℝ => f (y + Pi.single i 1)) x
      = (fderiv ℝ f (x + Pi.single i 1)).comp
          (fderiv ℝ (fun y : ι → ℝ => y + Pi.single i 1) x) :=
    fderiv_comp x (hf.differentiableAt) (by fun_prop)
  rw [hcomp, hφ, ContinuousLinearMap.comp_id] at h2
  simp only [pd]
  rw [← h2]

/-- A partial derivative lowers the order of differentiability by one: `f` of class `Cⁿ` has
`pd j f` of class `Cᵐ` for `m + 1 ≤ n`. -/
lemma contDiff_pd_of_contDiff (j : ι) {f : (ι → ℝ) → ℂ} {n m : ℕ}
    (hf : ContDiff ℝ (n : WithTop ℕ∞) f) (hmn : m + 1 ≤ n) :
    ContDiff ℝ (m : WithTop ℕ∞) (pd j f) := by
  have hle : (m : WithTop ℕ∞) + 1 ≤ ((n : ℕ) : WithTop ℕ∞) := by exact_mod_cast hmn
  have h := hf.contDiff_fderiv_apply (m := (m : WithTop ℕ∞)) hle
  have h2 : ContDiff ℝ (m : WithTop ℕ∞) (fun x : ι → ℝ => (x, (Pi.single j 1 : ι → ℝ))) := by
    fun_prop
  exact h.comp h2

/-- The iterated form, stated with all variables bound so that the induction on `k` is clean. -/
lemma fourierCoeff_pdVec_aux : ∀ (k : ℕ) (l : Fin k → ι) (f : (ι → ℝ) → ℂ),
    ContDiff ℝ (k : WithTop ℕ∞) f → Periodic1 f → ∀ m : ι → ℤ,
    Work.Diff.STE.fourierCoeff (Work.Diff.STE.pdVec k l f) m
      = (∏ i, (2 * Real.pi * Complex.I * (m (l i) : ℂ))) * Work.Diff.STE.fourierCoeff f m := by
  intro k
  induction k with
  | zero =>
    intro l f hf hper m
    simp [pdVec, pdList]
  | succ k ih =>
    intro l f hf hper m
    -- peel off the last derivative
    have hpd : pdVec (k + 1) l f
        = pdVec k (fun i : Fin k => l (Fin.castSucc i)) (pd (l (Fin.last k)) f) := by
      simp only [pdVec, pdList, List.ofFn_succ', List.concat_eq_append, List.foldr_append,
        List.foldr_cons, List.foldr_nil]
    have hcd : ContDiff ℝ (k : WithTop ℕ∞) (pd (l (Fin.last k)) f) :=
      contDiff_pd_of_contDiff _ (n := k + 1) (m := k) hf (le_refl (k + 1))
    have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
    have hperpd : Periodic1 (pd (l (Fin.last k)) f) :=
      fun i => periodicIn_pd_of_differentiable i (l (Fin.last k)) hdiff (hper i)
    rw [hpd, ih (fun i : Fin k => l (Fin.castSucc i)) (pd (l (Fin.last k)) f) hcd hperpd m]
    rw [fourierCoeff_pd (l (Fin.last k)) f m (hf.of_le (by norm_num)) (hper _)]
    rw [Fin.prod_univ_castSucc]
    ring

theorem fourierCoeff_pdVec {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (l : Fin k → ι)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ k f) (hper : Work.Diff.STE.Periodic1 f) (m : ι → ℤ) :
    Work.Diff.STE.fourierCoeff (Work.Diff.STE.pdVec k l f) m
      = (∏ i, (2 * Real.pi * Complex.I * (m (l i) : ℂ))) * Work.Diff.STE.fourierCoeff f m :=
  fourierCoeff_pdVec_aux k l f hf hper m

end Work.Diff.STE
