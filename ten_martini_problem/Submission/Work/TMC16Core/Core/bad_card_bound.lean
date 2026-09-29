import Mathlib
import Submission.Work.TMC16Core.Core.card_nn_lt_le
import Submission.Work.TMC16Core.Basic.nnDist

/-!
# The cardinality bound for the "bad" grid points

`Work.TMC16Core.Core.bad_card_bound` is the elementary counting estimate used in the
Avila–Jitomirskaya analysis of the rational-frequency almost-Mathieu operator.

Setting: `L ≥ 1`, `p : ℤ` coprime to `L`, `x : ℝ`, `η > 0`.  The `L` numbers
`2x + k·(p/L)`, `k = 1, …, L`, are — because `k ↦ k·p mod L` permutes the residues
modulo `L` — the `L` equally spaced points of the `1/L`-grid `2x + j/L`, `j = 0, …, L-1`.
Hence any two of them are `1/L`-separated, and those lying at distance `< π η` from an
integer form an arc of length `2 π η` on the circle, which contains at most
`2 π η L + 1` of them (this is `Work.TMC16Core.Core.card_nn_lt_le`).

The hypothesis `hj₁`/`hmin` says that `j₁` is a minimiser of `nn (2x + k·(p/L))` over
`k ∈ {1,…,L}`, and `hj₁bad` that the minimiser is *not* in `bad`.  This gives the last
unit:

* if the minimiser itself lies in the filtered set `S` of "bad" grid points, then
  `bad ⊆ S.erase j₁`, so `card bad + 1 ≤ card S ≤ 2 π η L + 1`;
* if not, then `nn (2x + j₁·(p/L)) ≥ π η` and minimality propagates this to every
  `k ∈ {1,…,L}`, so `S = ∅` and `bad = ∅`.

In both cases `card bad ≤ 2 π η L`.
-/

namespace Work.TMC16Core.Core

/-- **Cardinality of the bad set.**  If `bad` consists of grid indices `k ∈ {1,…,L}` with
`nn (2x + k·(p/L)) < π η` (`hsub`) and avoids one minimiser `j₁` of `nn` over the grid
(`hj₁`, `hmin`, `hj₁bad`), then `card bad ≤ 2 π η L`. -/
theorem bad_card_bound {L : ℕ} (hL : 0 < L) {p : ℤ} (hcop : Nat.Coprime p.natAbs L) (x η : ℝ)
    (hη : 0 < η) {j₁ : ℕ} (hj₁ : j₁ ∈ Finset.Icc 1 L)
    (hmin : ∀ j ∈ Finset.Icc 1 L,
      Work.TMC16Core.Basic.nn (2 * x + (j₁ : ℝ) * ((p : ℝ) / (L : ℝ)))
        ≤ Work.TMC16Core.Basic.nn (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ))))
    {bad : Finset ℕ}
    (hsub : bad ⊆ (Finset.Icc 1 L).filter (fun k : ℕ =>
      Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (L : ℝ))) < Real.pi * η))
    (hj₁bad : j₁ ∉ bad) :
    (bad.card : ℝ) ≤ 2 * Real.pi * η * (L : ℝ) := by
  classical
  set S : Finset ℕ := (Finset.Icc 1 L).filter (fun k : ℕ =>
      Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (L : ℝ))) < Real.pi * η) with hSdef
  have hbadS : bad ⊆ S := hsub
  -- the grid count: at most `2 π η L + 1` indices satisfy the smallness condition
  have hSbound : (S.card : ℝ) ≤ 2 * Real.pi * η * (L : ℝ) + 1 := by
    rw [hSdef]
    have h := card_nn_lt_le hL hcop x (Real.pi * η) (by positivity)
    linarith [h]
  by_cases hmem : j₁ ∈ S
  · -- the minimiser is itself a bad grid point: `bad` misses at least one point of `S`
    have hsub' : bad ⊆ S.erase j₁ := by
      intro k hk
      exact Finset.mem_erase.mpr ⟨fun h => hj₁bad (h ▸ hk), hbadS hk⟩
    have hcard : bad.card ≤ (S.erase j₁).card := Finset.card_le_card hsub'
    have herase : (S.erase j₁).card = S.card - 1 := Finset.card_erase_of_mem hmem
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨j₁, hmem⟩
    have hcast : ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by
      rw [Nat.cast_sub hpos, Nat.cast_one]
    have hle : (bad.card : ℝ) ≤ (S.card : ℝ) - 1 := by
      calc (bad.card : ℝ) ≤ ((S.erase j₁).card : ℝ) := by exact_mod_cast hcard
        _ = ((S.card - 1 : ℕ) : ℝ) := by rw [herase]
        _ = (S.card : ℝ) - 1 := hcast
    linarith
  · -- otherwise minimality forces every grid point to be far from the integers, and `S = ∅`
    have hge : Real.pi * η ≤
        Work.TMC16Core.Basic.nn (2 * x + (j₁ : ℝ) * ((p : ℝ) / (L : ℝ))) := by
      refine not_lt.mp (fun hlt => hmem ?_)
      exact Finset.mem_filter.mpr ⟨hj₁, hlt⟩
    have hSempty : S = ∅ := by
      rw [hSdef]
      apply Finset.subset_empty.mp
      intro k hk
      obtain ⟨hkI, hklt⟩ := Finset.mem_filter.mp hk
      have := hmin k hkI
      linarith
    have hbad_empty : bad = ∅ := by
      apply Finset.subset_empty.mp
      intro k hk
      have hkS : k ∈ S := hbadS hk
      rw [hSempty] at hkS
      exact hkS
    rw [hbad_empty, Finset.card_empty, Nat.cast_zero]
    positivity

end Work.TMC16Core.Core
