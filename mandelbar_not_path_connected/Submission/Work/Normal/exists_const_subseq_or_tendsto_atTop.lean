import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter

namespace Work.Normal

/-- A sequence of natural numbers either takes some value infinitely often (i.e. has a
constant subsequence indexed by an unbounded set), or it tends to infinity. -/
theorem exists_const_subseq_or_tendsto_atTop (k : ℕ → ℕ) :
    (∃ m : ℕ, ∀ N : ℕ, ∃ n > N, k n = m) ∨ Filter.Tendsto k Filter.atTop Filter.atTop := by
  by_cases h : ∃ m : ℕ, ∀ N : ℕ, ∃ n > N, k n = m
  · exact Or.inl h
  · right
    rw [tendsto_atTop_atTop]
    -- For each value `m`, `k` avoids `m` beyond some index.
    have h' : ∀ m : ℕ, ∃ N : ℕ, ∀ n : ℕ, n > N → k n ≠ m := by
      intro m
      by_contra hm
      apply h
      refine ⟨m, fun N => ?_⟩
      by_contra hN
      exact hm ⟨N, fun n hn heq => hN ⟨n, hn, heq⟩⟩
    intro b
    -- Beyond the maximum of the avoidance bounds for `0, …, b-1`, `k` is at least `b`.
    refine ⟨(Finset.range b).sup (fun m => Classical.choose (h' m)) + 1, fun a ha => ?_⟩
    by_contra hb
    have hlt : k a < b := not_le.mp hb
    have hmem : k a ∈ Finset.range b := Finset.mem_range.mpr hlt
    have hle : Classical.choose (h' (k a)) ≤ (Finset.range b).sup (fun m => Classical.choose (h' m)) :=
      Finset.le_sup (f := fun m => Classical.choose (h' m)) hmem
    have hspec : ∀ n, n > Classical.choose (h' (k a)) → k n ≠ k a := Classical.choose_spec (h' (k a))
    have : a > Classical.choose (h' (k a)) := by omega
    exact hspec a this rfl

end Work.Normal
