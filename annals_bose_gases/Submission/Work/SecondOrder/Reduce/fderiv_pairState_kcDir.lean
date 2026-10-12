import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Submission.Work.SecondOrder.Reduce.Decompose
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SecondOrder.Reduce.fderiv_pairState_kcDir`

The pair-excited (quasi-free) trial state is a finite linear combination of its
matching components (`Work.SecondOrder.pairState_eq_sum_components`),

    pairState N ψ wt G = Σ_{p ∈ pmatch N} wt (nPair p) · pairComp N ψ G p .

Since `fderiv` is additive over finite sums and commutes with scalar
multiplication, the directional derivative of the state along the corpus
coordinate direction `kcDir N i k` is the corresponding weighted sum of the
directional derivatives of the components — the identity that lets the energy
of the state be assembled from the bilinear form on the components
(`Reduce/pairStateE_eq_quadratic`).
-/

namespace Work.SecondOrder.Reduce

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Each pairing entry `x ↦ G (x a) (x b)` is `C¹` in the configuration `x`,
because it is the `C¹` function `(u, v) ↦ G u v` composed with the (continuous,
linear) pairing of coordinates. -/
private lemma contDiff_pairEntry {N : ℕ} {G : ℝ³ → ℝ³ → ℝ}
    (hG : ContDiff ℝ 1 (fun p : ℝ³ × ℝ³ => G p.1 p.2)) (a b : Fin N) :
    ContDiff ℝ 1 (fun x : Submission.BoseGases.X N => G (x a) (x b)) := by
  have hH : ContDiff ℝ 1 (fun x : Submission.BoseGases.X N => (x a, x b)) := by
    rw [contDiff_prod_iff]
    exact ⟨by simpa [Function.comp_def] using contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) a,
           by simpa [Function.comp_def] using contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) b⟩
  have := hG.comp hH
  simpa [Function.comp_def] using this

/-- A matching component `pairComp N ψ G p` is `C¹`: it is the product of the
condensate orbital product `∏ᵢ ψ(xᵢ)` and of the finitely many pairing entries
`G (x i) (x (p i))`, `i ∈ pairRep p`. -/
private lemma contDiff_pairComp {N : ℕ} {psi : ℝ³ → ℝ} {G : ℝ³ → ℝ³ → ℝ}
    (hpsi : ContDiff ℝ 1 psi)
    (hG : ContDiff ℝ 1 (fun p : ℝ³ × ℝ³ => G p.1 p.2)) (p : Fin N → Fin N) :
    ContDiff ℝ 1 (Work.SecondOrder.pairComp N psi G p) := by
  unfold Work.SecondOrder.pairComp
  refine ContDiff.mul ?_ ?_
  · refine contDiff_prod (f := fun i => fun x : Submission.BoseGases.X N => psi (x i)) ?_
    intro i _
    exact hpsi.comp (contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) i)
  · refine contDiff_prod (f := fun i => fun x : Submission.BoseGases.X N => G (x i) (x (p i))) ?_
    intro i _
    exact contDiff_pairEntry hG i (p i)

/-- **Directional derivative of the pair-excited state along a corpus coordinate
direction.**  Since the state is the weighted sum of its matching components,
its `kcDir N i k`-derivative is the corresponding weighted sum of the
components' derivatives. -/
theorem fderiv_pairState_kcDir {N : ℕ} {psi : EuclideanSpace ℝ (Fin 3) → ℝ} {wt : ℕ → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hpsi : ContDiff ℝ 1 psi)
    (hG : ContDiff ℝ 1 (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => G p.1 p.2))
    (x : Submission.BoseGases.X N) (i : Fin N) (k : Fin 3) :
    fderiv ℝ (Work.SecondOrder.pairState N psi wt G) x (Submission.BoseGases.kcDir N i k)
      = ∑ p ∈ Work.SecondOrder.pmatch N,
          wt (Work.SecondOrder.nPair p)
            * fderiv ℝ (Work.SecondOrder.pairComp N psi G p) x
                (Submission.BoseGases.kcDir N i k) := by
  -- The state is the weighted sum of its matching components.
  have hident : Work.SecondOrder.pairState N psi wt G
      = fun y : Submission.BoseGases.X N =>
          ∑ p ∈ Work.SecondOrder.pmatch N,
            wt (Work.SecondOrder.nPair p) * Work.SecondOrder.pairComp N psi G p y := by
    funext y
    exact Work.SecondOrder.pairState_eq_sum_components y
  -- Each component is differentiable at `x`.
  have hdiff : ∀ p, DifferentiableAt ℝ (Work.SecondOrder.pairComp N psi G p) x :=
    fun p => (contDiff_pairComp hpsi hG p).differentiable_one.differentiableAt
  -- `HasFDerivAt` for the finite sum of functions (identified with the lambda).
  have hfuneq : (∑ p ∈ Work.SecondOrder.pmatch N,
        fun y : Submission.BoseGases.X N =>
          wt (Work.SecondOrder.nPair p) * Work.SecondOrder.pairComp N psi G p y)
      = (fun y : Submission.BoseGases.X N =>
          ∑ p ∈ Work.SecondOrder.pmatch N,
            wt (Work.SecondOrder.nPair p) * Work.SecondOrder.pairComp N psi G p y) := by
    funext y
    rw [Finset.sum_apply]
  have hSraw : HasFDerivAt
      (∑ p ∈ Work.SecondOrder.pmatch N,
        fun y : Submission.BoseGases.X N =>
          wt (Work.SecondOrder.nPair p) * Work.SecondOrder.pairComp N psi G p y)
      (∑ p ∈ Work.SecondOrder.pmatch N,
        (wt (Work.SecondOrder.nPair p)) •
          fderiv ℝ (Work.SecondOrder.pairComp N psi G p) x) x :=
    HasFDerivAt.sum (fun p _ =>
      (hdiff p).hasFDerivAt.const_mul (wt (Work.SecondOrder.nPair p)))
  rw [hident]
  rw [← hfuneq]
  rw [hSraw.fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]

end Work.SecondOrder.Reduce
