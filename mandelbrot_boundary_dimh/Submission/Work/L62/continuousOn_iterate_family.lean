import Mathlib

/-!
# Joint continuity of iterates of a jointly continuous family of self-maps

Let `Ω ⊆ ℂ` be a set, `Λ ⊆ ℂ` a parameter set, and `H : ℂ → ℂ → ℂ` a family such that

* for every `β ∈ Λ` the map `H β` sends `Ω` into itself (`hmap`), and
* the evaluation map `(β, z) ↦ H β z` is continuous on the product `Λ × Ω` (`hcont`).

Then for every `k` the map `(β, z) ↦ (H β)^[k] z` is continuous on `Λ × Ω`.

The proof models the iterate by the self-map `Φ p = (p.1, H p.1 p.2)` of `Λ × Ω`:
`Φ^[k] p = (p.1, (H p.1)^[k] p.2)`, so the required function is the second component
of `Φ^[k]`.  The map `Φ` is continuous on `Λ × Ω` by `hcont`, maps `Λ × Ω` into itself
by `hmap`, and `ContinuousOn.iterate` then gives continuity of every iterate.
-/

namespace Work.L62

open Set Function

/-- The `k`-fold iterate of the "graph map" `p ↦ (p.1, H p.1 p.2)` is the graph of the
`k`-th iterate of the inner family: `Φ^[k] p = (p.1, (H p.1)^[k] p.2)`. -/
private theorem iterate_graph (H : ℂ → ℂ → ℂ) (k : ℕ) (p : ℂ × ℂ) :
    ((fun q : ℂ × ℂ => (q.1, H q.1 q.2))^[k] p) = (p.1, (H p.1)^[k] p.2) := by
  induction k generalizing p with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih p]
    simp [Function.iterate_succ_apply']

theorem continuousOn_iterate_family {Ω Λ : Set ℂ} {H : ℂ → ℂ → ℂ} (k : ℕ)
    (hmap : ∀ β ∈ Λ, Set.MapsTo (H β) Ω Ω)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (Λ ×ˢ Ω)) :
    ContinuousOn (fun p : ℂ × ℂ => (H p.1)^[k] p.2) (Λ ×ˢ Ω) := by
  -- The graph map `Φ` and its iterates are continuous on `Λ × Ω`.
  have key : ContinuousOn
      (fun p : ℂ × ℂ => ((fun q : ℂ × ℂ => (q.1, H q.1 q.2))^[k] p).2) (Λ ×ˢ Ω) := by
    have hFc : ContinuousOn (fun q : ℂ × ℂ => (q.1, H q.1 q.2)) (Λ ×ˢ Ω) :=
      ContinuousOn.prodMk continuous_fst.continuousOn hcont
    have hFm : Set.MapsTo (fun q : ℂ × ℂ => (q.1, H q.1 q.2)) (Λ ×ˢ Ω) (Λ ×ˢ Ω) := by
      intro p hp
      exact ⟨hp.1, hmap p.1 hp.1 hp.2⟩
    exact (hFc.iterate hFm k).snd
  refine ContinuousOn.congr key ?_
  intro p hp
  simp only [iterate_graph H k p]

end Work.L62
