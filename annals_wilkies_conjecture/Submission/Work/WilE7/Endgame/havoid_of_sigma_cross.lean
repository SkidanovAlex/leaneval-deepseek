import Mathlib
import Submission.Work.WilE7.Endgame.E2Aux
import Submission.Work.WilE7.Endgame.witness_mem_pairFrontierBaseFst

namespace Work.WilE7.Endgame

open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv pairPtUp)

/-- **Avoidance of the `Σ`-family on a crossing pair.**

Suppose `T`, `T'` are two strata of the `(n, m+1)` frame whose absolute points `u`, `v` have the
same base projection `x₀ ∈ C`, and `C` is disjoint from the `π_n`-images of every member of the
family `Sig`.  Let `Wl` be a family of strata of the pair frame `(n + (m+1), n + (m+1))` such that
the `π_n`-image of the pair-sub-base of every `W` with `pPair - W.j < (n+m+1) - T.j` is covered by
`Sig` (hypothesis `hW`), and likewise for the pair-frontier base when equality holds (hypothesis
`hWf`).

Then the pair point `pairPtUp u v` cannot lie strictly inside a stratum `W` whose codimension gap
exceeds `(n+m+1) - T.j` (first conjunct), and it cannot lie on the frontier of a stratum `W` whose
codimension gap is exactly `(n+m+1) - T.j` (second conjunct).  In both cases the base projection of
`pairPtUp u v` would be covered by `Sig` while lying in `C`, contradicting `hdisj`. -/
theorem havoid_of_sigma_cross {n m s : ℕ}
    (T T' : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (Sig : List (WilkiesDesign.E.SemiPf (n + s)))
    (Wl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)))
    (hW : ∀ W ∈ Wl, Work.WilE7.CoreStep.pPair n m - W.j < n + (m + 1) - T.j →
      Work.CoreStep.pairSubBaseFst n m W ⊆ ⋃ S ∈ Sig, WilkiesDesign.E.projFirst n s '' S.set)
    (hWf : ∀ W ∈ Wl, Work.WilE7.CoreStep.pPair n m - W.j = n + (m + 1) - T.j →
      Work.CoreStep.pairFrontierBaseFst n m W ⊆
        ⋃ S ∈ Sig, WilkiesDesign.E.projFirst n s '' S.set)
    (C : Set (Fin n → ℝ))
    (hdisj : ∀ S ∈ Sig, Disjoint C (WilkiesDesign.E.projFirst n s '' S.set)) :
    ∀ (u v : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ) (x₀ : Fin n → ℝ),
      u ∈ T.X.set → v ∈ T'.X.set →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) = x₀ →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv v) = x₀ →
      x₀ ∈ C →
      ((∀ W ∈ Wl, Work.WilE7.CoreStep.pairPtUp u v ∈ W.X.set →
          n + (m + 1) - T.j ≤ Work.WilE7.CoreStep.pPair n m - W.j) ∧
        (∀ W ∈ Wl, Work.WilE7.CoreStep.pairPtUp u v ∈ closure W.X.set \ W.X.set →
          Work.WilE7.CoreStep.pPair n m - W.j ≠ n + (m + 1) - T.j)) := by
  intro u v x₀ hu hv hbaseu hbasev hx₀C
  constructor
  · -- First conjunct: `pairPtUp u v` strictly inside `W` forces the codimension gap to be small.
    intro W hWl hWmem
    by_contra hcon
    rw [not_le] at hcon
    -- `hcon : pPair n m - W.j < n + (m+1) - T.j`, so `hW` covers the base projection of `W`.
    have hsub := hW W hWl hcon
    -- The base projection of the pair point lies in `pairSubBaseFst n m W`, and equals `x₀`.
    have hbase : Work.CoreStep.pairBaseFst n m
        (Work.WilE7.MainDesign.absPt (Work.WilE7.CoreStep.pairPtUp u v)) ∈
        Work.CoreStep.pairSubBaseFst n m W := ⟨_, ⟨_, hWmem, rfl⟩, rfl⟩
    rw [Work.CoreStep.pairBaseFst_absPt_pairPtUp u v, hbaseu] at hbase
    obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp (hsub hbase)
    exact (Set.disjoint_left.mp (hdisj S hS)) hx₀C hxS
  · -- Second conjunct: `pairPtUp u v` on the frontier of `W` forbids exact equality.
    intro W hWl hWfr hcon
    have hsub := hWf W hWl hcon
    have hbase := witness_mem_pairFrontierBaseFst W hWfr.1 hWfr.2
    rw [Work.CoreStep.pairBaseFst_absPt_pairPtUp u v, hbaseu] at hbase
    obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp (hsub hbase)
    exact (Set.disjoint_left.mp (hdisj S hS)) hx₀C hxS

end Work.WilE7.Endgame
