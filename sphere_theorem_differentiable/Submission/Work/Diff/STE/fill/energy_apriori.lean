import Submission.Work.Diff.STE.flat.pairing_sharp
import Submission.Work.Diff.STE.fill.pairingBoundSharp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The flat a priori energy estimate, from the sharp static pairing bound

`Work.Diff.STE.flat.energy_apriori` (the final Grönwall assembly of the flat Galerkin scheme) is the
only `sorry` left in the flat Cauchy chain of `Submission/Work/Diff/STE/flat/`.  The proved
reduction `Work.Diff.STE.flat.energy_apriori_of_pairing_sharp` (`flat/pairing_sharp.lean`) shows
that its whole analytic content is the sharp static pairing bound
`Work.Diff.STE.flat.PairingBoundSharp`, which is proved in this directory as
`Work.Diff.STE.fill.pairingBoundSharp`.

This file therefore records the *sorry-free* version of the flat a priori estimate under the same
name, so that `TorusCauchy.lean` can use it (the twin in `flat/energy_apriori.lean` keeps its
`sorry`; it cannot import this file, since this file imports it).
-/

namespace Work.Diff.STE.fill

theorem energy_apriori {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Tc : ℝ) (hc : 0 < Tc) (N : ℕ) (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
          HasDerivAt (fun s => c s k' i j)
            (Work.Diff.STE.fourierCoeff (fun x =>
              Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) k') t) →
        (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c t k' = 0) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c t) x) i j * v i * v j) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc,
          Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM (c t)) ≤ B ^ 2) →
        ∀ t ∈ Set.Ico (0 : ℝ) Tc,
          Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM (c t))
            ≤ (Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM (c 0)) + 1)
                * Real.exp (C * t) - 1 :=
  Work.Diff.STE.flat.energy_apriori_of_pairing_sharp hn Φ hshape k lam hlam B
    (Work.Diff.STE.fill.pairingBoundSharp hn Φ hshape k hk lam hlam B hB)

end Work.Diff.STE.fill
