import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SecondOrder.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/SecondOrder` — the component decomposition and the Wick double sum

The pair-excited state is a finite linear combination of its matching components
`pairComp N ψ G p` (one summand per partial matching `p`, with weight
`wt (nPair p)`):

    pairState N ψ wt G = Σ_{p ∈ pmatch N} wt (nPair p) · pairComp N ψ G p .

Consequently the box norm of the state is a **double sum over pairs of partial
matchings** — the first step of Wick's theorem for the quasi-free state: the
`(p,q)` term is the configuration integral of `pairComp p · pairComp q`, whose
"union graph" (each label has degree ≤ 2) is what the cluster expansion of the
ESY/Yau–Yin energy computation organises itself around.  The remaining,
genuinely analytic step — evaluating/factorising that double sum for the
concrete Bogoliubov kernel — is the named residual of this chapter
(`NOTES.md` §4).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.SecondOrder

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Component decomposition.**  The pair state is the weighted sum of its
matching components. -/
theorem pairState_eq_sum_components {N : ℕ} {psi : ℝ³ → ℝ} {wt : ℕ → ℝ}
    {G : ℝ³ → ℝ³ → ℝ} (x : X N) :
    pairState N psi wt G x
      = ∑ p ∈ pmatch N, wt (nPair p) * pairComp N psi G p x := by
  unfold pairState pairComp pairAmp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  ring

/-- Integral of a finite double sum over the box (finite Fubini). -/
private lemma integral_sum_sum {N : ℕ} {ℓ : ℝ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (F : ι → ι → X N → ℝ)
    (h : ∀ p ∈ s, ∀ q ∈ s, Integrable (F p q)
      (volume.restrict (abox N ℓ))) :
    (∫ x in abox N ℓ, ∑ p ∈ s, ∑ q ∈ s, F p q x)
      = ∑ p ∈ s, ∑ q ∈ s, ∫ x in abox N ℓ, F p q x := by
  have h1 : (∫ x in abox N ℓ, ∑ p ∈ s, ∑ q ∈ s, F p q x)
      = ∑ p ∈ s, ∫ x in abox N ℓ, ∑ q ∈ s, F p q x :=
    integral_finsetSum (s := s) (f := fun p => fun x => ∑ q ∈ s, F p q x)
      (fun p hp => integrable_finsetSum (s := s) (f := fun q => F p q)
        (fun q hq => h p hp q hq))
  rw [h1]
  exact Finset.sum_congr rfl (fun p hp =>
    integral_finsetSum (s := s) (f := fun q => F p q) (fun q hq => h p hp q hq))

/-- **The Wick double-sum expansion of the norm.**  The norm square of the pair
state is the double sum of the configuration integrals of its matching
components, weighted by `wt (nPair p) · wt (nPair q)`.

(`hint` is the finiteness of the finitely many configuration integrals involved;
it holds for continuous data on the compact box.) -/
theorem pairStateZ_eq_doubleSum {N : ℕ} {ℓ : ℝ} {psi : ℝ³ → ℝ} {wt : ℕ → ℝ}
    {G : ℝ³ → ℝ³ → ℝ}
    (hint : ∀ p ∈ pmatch N, ∀ q ∈ pmatch N,
      MeasureTheory.Integrable (fun x : X N => pairComp N psi G p x * pairComp N psi G q x)
        (volume.restrict (abox N ℓ))) :
    pairStateZ N ℓ psi wt G
      = ∑ p ∈ pmatch N, ∑ q ∈ pmatch N,
          wt (nPair p) * wt (nPair q) * pairOverlap N ℓ psi G p q := by
  have hsq : ∀ x : X N,
      (∑ p ∈ pmatch N, wt (nPair p) * pairComp N psi G p x) ^ 2
        = ∑ p ∈ pmatch N, ∑ q ∈ pmatch N,
            (wt (nPair p) * pairComp N psi G p x) * (wt (nPair q) * pairComp N psi G q x) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
  have hint2 : ∀ p ∈ pmatch N, ∀ q ∈ pmatch N,
      Integrable (fun x : X N =>
        (wt (nPair p) * pairComp N psi G p x) * (wt (nPair q) * pairComp N psi G q x))
        (volume.restrict (abox N ℓ)) := by
    intro p hp q hq
    refine ((hint p hp q hq).const_mul (wt (nPair p) * wt (nPair q))).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    ring
  unfold pairStateZ
  rw [funext (pairState_eq_sum_components (N := N) (psi := psi) (wt := wt) (G := G))]
  rw [funext hsq]
  rw [integral_sum_sum (pmatch N)
    (fun p q => fun x : X N =>
      (wt (nPair p) * pairComp N psi G p x) * (wt (nPair q) * pairComp N psi G q x))
    hint2]
  refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
  rw [show (fun x : X N =>
        (wt (nPair p) * pairComp N psi G p x) * (wt (nPair q) * pairComp N psi G q x))
      = fun x : X N =>
          (wt (nPair p) * wt (nPair q)) * (pairComp N psi G p x * pairComp N psi G q x) by
        funext x; ring]
  rw [integral_const_mul]
  rfl

end Work.SecondOrder
