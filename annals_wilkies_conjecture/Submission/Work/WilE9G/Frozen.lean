/-
  Subproject WilE9G — **the target theorem**, stated exactly as in the design file
  (`sources/wilkiesE3E9/wilkies_E3E9_gaps.lean`, `WilkiesDesign.E.Gaps.EffStratAE_of_frozen`).

  THIS FILE CONTAINS THE UNPROVED FRONTIER.  Everything else in the directory is proved
  (`Defs`, `Basic`, `Collapse`, `Amb`, and the delegated `Sard/*`, `Amb/stratum_zero_to_amb`).
  The proof of `EffStratAE_of_frozen` below is the remaining work; `STATUS.md` in this directory
  records exactly which pieces are in place and which are not.

  The two hypotheses are the frozen holes `E2_components` and `E5_strat` of
  `Submission/Work/Wilkies/E/Spec.lean`, copied verbatim.
-/
import Submission.Work.WilE9G.Collapse
import Submission.Work.WilE9G.Amb

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G
open WilkiesDesign WilkiesDesign.E Work.WilE9.Sharp

/-- **The frozen `E2_components`** (copied verbatim from `WilkiesDesign.E.E2_components`):
Khovanskii's bound on the number of connected components of a semi-Pfaffian set. -/
def FrozenE2 : Prop :=
  ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
    ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
      ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y

/-- **The frozen `E5_strat`** (copied verbatim from `WilkiesDesign.E.E5_strat`): the
Gabrielov–Vorobjov fibrewise weak stratification. -/
def FrozenE5 : Prop :=
  ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)),
    X.fmt ≤ F →
    ∃ L : List (Stratum p q), L.length ≤ b.eval X.deg ∧
      (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
      X.set = (⋃ S ∈ L, S.X.set) ∧ L.Pairwise (fun S T => Disjoint S.X.set T.X.set)

/- **THE DELIVERABLE.**  `Work.WilE9G.EffStratAE_of_frozen`, with the two frozen hypotheses
written out verbatim above (`FrozenE2`, `FrozenE5`), is the assembly of the pieces proved in this
directory: G1 (`WilE9G/G1.lean`), G3 (`WilE9G/Mult/exists_multiplier_of_ambStratum_fibre.lean`),
the Lagrange-stratum construction
(`WilE9G/Lagrange/exists_lagrange_stratum.lean`), FIX-5's a.e. nondegeneracy
(`WilE9G/Lagrange/exists_null_of_degenerate.lean`), the Fubini core
(`WilE9G/Fubini/ae_null_slice_of_null.lean`) and the covering crux (`WilE9G/Cover.lean`).
Its final assembly is the remaining work; the exact statement is

```
theorem EffStratAE_of_frozen
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ L : List (Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧ L.Pairwise (fun S T => Disjoint S.X.set T.X.set)) :
    EffStratAE
```

and it is delegated at `Submission/Work/WilE9G/EffStratAE_of_frozen.lean`; the declaration is *not*
repeated here, so that importing both files cannot clash.  See `STATUS.md` §3–§5 and §8 for the
route, the state of each piece, and the two corrections to the design's route. -/

end Work.WilE9G
