import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB2.Sector.jointProj_resolution
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Sector.secProj_resolution` — the resolution of the identity by the
`n₊ = k` sectors

`secProj ℓ k Φ = Σ_{|S| = k} E_S Φ` collects the joint sector projections over all
subsets `S ⊆ {0,…,n−1}` of cardinality `k` (`Submission.Work.BoseFixB2.Defs`).  Since
every subset of `{0,…,n−1}` has at most `n` elements, summing `secProj ℓ k Φ` over
`k ∈ range (n+1)` collects each joint sector exactly once, so by
`jointProj_resolution`:

    Σ_{k ≤ n} 1_{n₊ = k} Φ = Φ.

The only content is the combinatorial reindexing

    Σ_{k ∈ range (n+1)} Σ_{S ∈ powersetCard k (range n)} f S
      = Σ_{S ∈ powerset (range n)} f S,

which is `Finset.sum_fiberwise_of_maps_to` applied to the cardinality map
`powerset (range n) → range (n+1)` (well defined because `S ⊆ range n` gives
`S.card ≤ n`), with `Finset.powersetCard_eq_filter` identifying the fibres
`{S ∈ powerset (range n) | S.card = k}` with `powersetCard k (range n)`.

No continuity or positivity hypothesis is used by the reindexing itself; `hℓ` and `hΦ`
enter only through `jointProj_resolution`.
-/

namespace Work.BoseFixB2.Sector

open Work.BoseFixB2
open Submission.BoseGases

set_option linter.unusedVariables false

/-- **The reindexing lemma.**  Summing a function of a finite set of slots over the
`k`-element subsets of `{0,…,n−1}`, for all `k ≤ n`, is the same as summing it over all
subsets of `{0,…,n−1}`: the fibres of the cardinality map on `(range n).powerset` are the
`powersetCard`s. -/
lemma sum_powersetCard_eq_sum_powerset {n : ℕ} (f : Finset ℕ → X n → ℝ) :
    (∑ k ∈ Finset.range (n + 1), ∑ S ∈ (Finset.range n).powersetCard k, f S)
      = ∑ S ∈ (Finset.range n).powerset, f S := by
  have hmem : ∀ S ∈ (Finset.range n).powerset, S.card ∈ Finset.range (n + 1) := by
    intro S hS
    rw [Finset.mem_range]
    have h1 : S ⊆ Finset.range n := Finset.mem_powerset.mp hS
    have h2 : S.card ≤ n := by
      simpa using Finset.card_le_card h1
    omega
  have key := Finset.sum_fiberwise_of_maps_to (s := (Finset.range n).powerset)
    (t := Finset.range (n + 1)) (g := Finset.card) hmem f
  simp only [Finset.powersetCard_eq_filter]
  exact key

theorem secProj_resolution {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : Continuous Φ) :
    (∑ k ∈ Finset.range (n + 1), Work.BoseFixB2.secProj ℓ k Φ) = Φ := by
  simp only [secProj]
  rw [sum_powersetCard_eq_sum_powerset (fun S => jointProj ℓ S Φ)]
  exact jointProj_resolution hℓ Φ hΦ

end Work.BoseFixB2.Sector
