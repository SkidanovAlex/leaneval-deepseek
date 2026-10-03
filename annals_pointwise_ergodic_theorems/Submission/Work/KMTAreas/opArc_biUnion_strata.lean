import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.opArc_eq_sum_singletons
import Submission.Work.BourgainPlan.IonescuWainger.StrataCompDefs

/-!
# Additivity of `opArc` over a disjoint family of strata

`opArc ψ hψ E f hf` is the Fourier multiplier on `ℓ²(ℤ)` with symbol `Σ_{β ∈ E} ψ(· - β)`
(Tao's `Op_{φ;E}`), so it is additive in the *arc set* `E`: for a pairwise disjoint family
`(sigmaStrataFinset A)_{A ∈ s}` the arc set `⋃_{A ∈ s} sigmaStrataFinset A` gives the sum of the
operators.

The proof is the two structural facts already available:

* `opArc_eq_sum_singletons` writes `opArc ψ hψ E f hf = Σ_{β ∈ E} opArc ψ hψ {β} f hf`
  (the symbol identity `arcSymbol φ E = Σ_{β ∈ E} φ(· - β)`);
* `Finset.sum_biUnion` regroups a sum over a union of pairwise disjoint finsets.

Both `opArc ψ hψ {β}` (a single arc) and the intermediate symbol identity are linear in the
symbol, so nothing analytic is needed here.
-/

namespace Work.KMTAreas

open Work.BourgainPlan.IonescuWainger

theorem opArc_biUnion_strata (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hψ : MeasureTheory.MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (s : Finset (Finset ℕ))
    (hdisj : ∀ A ∈ s, ∀ B ∈ s, A ≠ B →
      Disjoint (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A)
        (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset B))
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    Work.BourgainPlan.IonescuWainger.opArc ψ hψ
        (s.biUnion Work.BourgainPlan.IonescuWainger.sigmaStrataFinset) f hf
      = ∑ A ∈ s, Work.BourgainPlan.IonescuWainger.opArc ψ hψ
          (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A) f hf := by
  have hsymm : Set.PairwiseDisjoint (↑s)
      (fun A => Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A) := hdisj
  rw [Work.BourgainPlan.IonescuWainger.opArc_eq_sum_singletons ψ hψ
        (s.biUnion Work.BourgainPlan.IonescuWainger.sigmaStrataFinset) f hf,
      Finset.sum_biUnion hsymm]
  exact Finset.sum_congr rfl fun A _ =>
    (Work.BourgainPlan.IonescuWainger.opArc_eq_sum_singletons ψ hψ
      (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A) f hf).symm

end Work.KMTAreas
