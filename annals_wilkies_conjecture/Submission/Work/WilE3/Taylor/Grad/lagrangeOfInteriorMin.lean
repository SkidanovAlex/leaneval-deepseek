import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Taylor.Polar.Basic
import Submission.Work.WilE3.Taylor.Polar.Lagrange

/-!
  annals_wilkies_conjecture, AREA E3: the Lagrange condition at an interior minimum of the squared
  gradient norm on a level set.

  The Łojasiewicz/polar argument (`Submission/Work/WilE3/Taylor/Polar/`) routes the minimisers of
  `Φ` on the shells `{dist (·, Z) = ρ}` into the polar set by a Lagrange multiplier argument.  This
  file supplies the companion statement used when the minimum is taken *inside* the zero set, i.e.
  on the level set `{z | Φ z = Φ u}`: if `u` minimises `G := ∑ l (∂ₗ Φ)²` on the level set of `Φ`
  and `∇Φ u ≠ 0`, then `∇G u ∥ ∇Φ u`.

  The proof is a direct application of the Lagrange multiplier theorem, in the form already
  available in this workspace as `Work.WilE3.Taylor.grad_parallel_of_isLocalExtrOn`: both `G` and
  `Φ` are analytic (hence strictly differentiable), `u` is a local minimum of `G` on the level set
  `{z | Φ z = Φ u}` by hypothesis, and the constraint gradient `∇Φ u` is non-zero.

  The analyticity of `G` is the only ingredient that needs care: `∇Φ` is analytic because `Φ` is
  (`AnalyticAt.fderiv`), and analyticity is preserved by evaluation of a continuous linear map at a
  fixed vector and by the finite sum of squares.
-/

namespace Work.WilE3.Taylor.Grad

open Classical Topology Filter

/-- Each component `z ↦ ∂ₗ Φ z` of the gradient of an everywhere-analytic `Φ` is analytic: it is
`(L ↦ L (eₗ)) ∘ (fderiv ℝ Φ)`, a composition of analytic maps. -/
theorem analyticAt_grad_comp {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} (hΦ : ∀ z, AnalyticAt ℝ Φ z)
    (l : Fin k) : ∀ z, AnalyticAt ℝ (fun w => Work.WilE3.Taylor.grad Φ w l) z := by
  intro z
  have h1 : AnalyticAt ℝ (fun w => fderiv ℝ Φ w) z := AnalyticAt.fderiv (hΦ z)
  have h2 : AnalyticAt ℝ (fun (L : (Fin k → ℝ) →L[ℝ] ℝ) => L (Pi.single l 1))
      (fderiv ℝ Φ z) :=
    ((ContinuousLinearMap.apply ℝ ℝ (Pi.single l 1)).analyticAt _).congr
      (Eventually.of_forall fun L => rfl)
  have h3 := h2.comp h1
  simpa [Function.comp_def, Work.WilE3.Taylor.grad] using h3

/-- The squared gradient norm `z ↦ ∑ l, (∂ₗ Φ z)²` of an everywhere-analytic `Φ` is analytic
everywhere. -/
theorem analyticAt_grad_sqSum {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} (hΦ : ∀ z, AnalyticAt ℝ Φ z) :
    ∀ z, AnalyticAt ℝ (fun w => ∑ l, (Work.WilE3.Taylor.grad Φ w l) ^ 2) z := by
  intro z
  refine Finset.analyticAt_fun_sum Finset.univ fun l _ => ?_
  exact (analyticAt_grad_comp hΦ l z).pow 2

/-- **The Lagrange condition at a constrained minimum of the squared gradient norm.**  Let `Φ` be
everywhere real-analytic and let `u` minimise `G := ∑ l, (∂ₗ Φ)²` on the level set
`{z | Φ z = Φ u}` of `Φ`, with `∇Φ u ≠ 0`.  Then `∇G u` is a multiple of `∇Φ u`.

(Since `G` is analytic it is strictly differentiable at `u`, and `u` is a local minimum of `G` on
the level set `{z | Φ z = Φ u}`, so the Lagrange multiplier theorem
`grad_parallel_of_isLocalExtrOn` gives the parallelism.  Note `fderiv ℝ Φ u ≠ 0` because
`∇Φ u ≠ 0`.) -/
theorem exists_smul_grad_sqSum_of_minOn_level {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {u : Fin k → ℝ}
    (hΦ : ∀ z, AnalyticAt ℝ Φ z) (hgu : Work.WilE3.Taylor.grad Φ u ≠ 0)
    (hcrit : ∀ z : Fin k → ℝ, Φ z = Φ u →
      (∑ l, (Work.WilE3.Taylor.grad Φ u l) ^ 2) ≤ (∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2)) :
    ∃ c : ℝ, Work.WilE3.Taylor.grad (fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) u
      = c • Work.WilE3.Taylor.grad Φ u := by
  have hG1 : HasStrictFDerivAt (fun z => ∑ l, (grad Φ z l) ^ 2)
      (fderiv ℝ (fun z => ∑ l, (grad Φ z l) ^ 2) u) u :=
    (analyticAt_grad_sqSum hΦ u).contDiffAt.hasStrictFDerivAt (n := 1) (by norm_num)
  have hΦ1 : HasStrictFDerivAt Φ (fderiv ℝ Φ u) u :=
    (hΦ u).contDiffAt.hasStrictFDerivAt (n := 1) (by norm_num)
  have hextr : IsLocalExtrOn (fun z => ∑ l, (grad Φ z l) ^ 2) {z | Φ z = Φ u} u := by
    refine Or.inl ?_
    show ∀ᶠ z in 𝓝[{z : Fin k → ℝ | Φ z = Φ u}] u,
      (∑ l, (grad Φ u l) ^ 2) ≤ (∑ l, (grad Φ z l) ^ 2)
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hcrit z hz
  exact grad_parallel_of_isLocalExtrOn hextr hG1 hΦ1 hgu

/-- **The Lagrange condition at an interior minimum, in polar (minors) form.**  Let `Φ` be
everywhere real-analytic, `∇Φ u ≠ 0`, and suppose that `u` minimises the squared gradient norm
`∑ l, (∂ₗ Φ)²` on the level set `{z | Φ z = Φ u}` of `Φ`.  Then the gradient of `Φ` at `u` and the
gradient at `u` of the squared gradient norm are parallel, i.e. all the `2 × 2` minors
`(∇Φ u) i · ∇G u j - (∇Φ u) j · ∇G u i` vanish. -/
theorem lagrangeOfInteriorMin {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {u : Fin k → ℝ}
    (hΦ : ∀ z, AnalyticAt ℝ Φ z) (hgu : Work.WilE3.Taylor.grad Φ u ≠ 0)
    (hcrit : ∀ z : Fin k → ℝ, Φ z = Φ u →
      (∑ l, (Work.WilE3.Taylor.grad Φ u l) ^ 2) ≤ (∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2)) :
    ∀ i j : Fin k,
      Work.WilE3.Taylor.grad Φ u i *
          Work.WilE3.Taylor.grad (fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) u j
        - Work.WilE3.Taylor.grad Φ u j *
          Work.WilE3.Taylor.grad (fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) u i
        = 0 := by
  obtain ⟨c, hc⟩ := exists_smul_grad_sqSum_of_minOn_level hΦ hgu hcrit
  intro i j
  rw [hc]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end Work.WilE3.Taylor.Grad
