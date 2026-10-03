import Mathlib
import Submission.Work.Horn.flower_defs

/-!
# Local constancy of the petal index on the parabolic basin

For a parabolic germ `f z = z + a z^(q+1) + o(z^(q+1))` the `q` attracting petals
`Flower.petal q a M j` form a Markov partition of the parabolic basin: an orbit that has entered
the petal of index `j` can never leave it (except by hitting `0`), so the set of indices `i` with
`f^[n] z ∈ petal i` for some `n` is either empty or a singleton `{j}`; and if
`f^[n] z ∈ petal j`, then for all `w` close enough to `z` also `f^[n] w ∈ petal j`.  Hence the
"which petal does the orbit enter" index is locally constant on the basin.

The neighbourhood is obtained by continuity of the iterate `f^[n]` at `z` — this is why the
hypotheses contain the differentiability of `f` on the open set `D` and the fact (built into
`ParabolicBasin`) that a full neighbourhood of `z` has all its iterates inside `D`.

Everything else is purely combinatorial: `MapsTo f (petal j) (petal j ∪ {0})` says the sets
`petal j ∪ {0}` are forward invariant (as `f 0 = 0`), the petals are disjoint and do not contain
`0`, so two different petals can never both be visited.
-/

set_option linter.unusedVariables false

namespace Work.Horn

open MandelDim Filter Topology

theorem petal_index_locally_const {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hb : Work.Horn.Flower.Bounds f D q a ρ) (hM : 0 < M)
    (hgeo : Work.Horn.Flower.PetalFacts q a M)
    (hmaps : ∀ j : Fin q, Set.MapsTo f (Work.Horn.Flower.petal q a M j)
      (Work.Horn.Flower.petal q a M j ∪ {0}))
    (hcap : ∀ z ∈ MandelDim.ParabolicBasin f D,
      ∃ n : ℕ, f^[n] z ∈ ⋃ j, Work.Horn.Flower.petal q a M j) :
    ∀ z ∈ MandelDim.ParabolicBasin f D, ∃ U ∈ nhds z, ∀ w ∈ U, ∀ i : Fin q,
      ((∃ n : ℕ, f^[n] z ∈ Work.Horn.Flower.petal q a M i) ↔
        (∃ n : ℕ, f^[n] w ∈ Work.Horn.Flower.petal q a M i)) := by
  -- `petal j ∪ {0}` is forward invariant
  have hinv : ∀ j : Fin q, ∀ u : ℂ, (u ∈ Work.Horn.Flower.petal q a M j ∨ u = 0) →
      (f u ∈ Work.Horn.Flower.petal q a M j ∨ f u = 0) := by
    intro j u hu
    rcases hu with hu | hu
    · exact Set.mem_or_mem_of_mem_union (hmaps j hu)
    · rw [hu, hb.hfix]
      exact Or.inr rfl
  have hiter : ∀ j : Fin q, ∀ u : ℂ, (u ∈ Work.Horn.Flower.petal q a M j ∨ u = 0) →
      ∀ k : ℕ, (f^[k] u ∈ Work.Horn.Flower.petal q a M j ∨ f^[k] u = 0) := by
    intro j u hu k
    induction k with
    | zero => simpa using hu
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact hinv j _ ih
  -- an orbit that visits `petal i` visits no other petal
  have key : ∀ {y : ℂ} {i : Fin q} {N : ℕ}, f^[N] y ∈ Work.Horn.Flower.petal q a M i →
      ∀ j : Fin q, (∃ n : ℕ, f^[n] y ∈ Work.Horn.Flower.petal q a M j) → j = i := by
    intro y i N hN j hm
    obtain ⟨m, hm⟩ := hm
    by_contra hne
    have hne' : i ≠ j := fun h => hne h.symm
    rcases le_total N m with hNm | hmN
    · -- iterate the visit at time `N` forward to time `m ≥ N`
      have h : f^[m] y ∈ Work.Horn.Flower.petal q a M i ∨ f^[m] y = 0 := by
        have hh := hiter i (f^[N] y) (Or.inl hN) (m - N)
        rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hNm] at hh
      have hni : f^[m] y ∈ Work.Horn.Flower.petal q a M i := by
        rcases h with h | h
        · exact h
        · exact absurd (h ▸ hm) (hgeo.not_mem_petal_zero j)
      exact (Set.disjoint_left.mp (hgeo.disjoint_petal i j hne')) hni hm
    · have h : f^[N] y ∈ Work.Horn.Flower.petal q a M j ∨ f^[N] y = 0 := by
        have hh := hiter j (f^[m] y) (Or.inl hm) (N - m)
        rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hmN] at hh
      have hnj : f^[N] y ∈ Work.Horn.Flower.petal q a M j := by
        rcases h with h | h
        · exact h
        · exact absurd (h ▸ hN) (hgeo.not_mem_petal_zero i)
      exact (Set.disjoint_left.mp (hgeo.disjoint_petal i j hne')) hN hnj
  intro z hz
  -- the petal entered by the orbit of `z`, and the time it is entered
  obtain ⟨n, hn⟩ := hcap z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hn
  -- a neighbourhood on which all iterates stay in `D` (hence `f^[k]` is continuous there)
  obtain ⟨U₀, hU₀, hmap, -⟩ := hz
  have hzU₀ : z ∈ U₀ := mem_of_mem_nhds hU₀
  have hzD : ∀ k : ℕ, f^[k] z ∈ D := fun k => hmap k hzU₀
  have hcont : ∀ k : ℕ, ContinuousAt (f^[k]) z := by
    intro k
    induction k with
    | zero => simpa using continuousAt_id
    | succ m ih =>
        have hm : ContinuousAt f (f^[m] z) :=
          (hf.differentiableAt (hD.mem_nhds (hzD m))).continuousAt
        rw [Function.iterate_succ']
        exact hm.comp ih
  -- the preimage of the entered petal under `f^[n]` is the required neighbourhood
  refine ⟨(f^[n]) ⁻¹' Work.Horn.Flower.petal q a M i,
    (hcont n).preimage_mem_nhds ((hgeo.isOpen_petal i).mem_nhds hi), ?_⟩
  intro w hw j
  have keyz : (∃ m : ℕ, f^[m] z ∈ Work.Horn.Flower.petal q a M j) ↔ j = i := by
    refine ⟨fun h => key hi j h, ?_⟩
    intro hji
    rw [hji]
    exact ⟨n, hi⟩
  have keyw : (∃ m : ℕ, f^[m] w ∈ Work.Horn.Flower.petal q a M j) ↔ j = i := by
    refine ⟨fun h => key hw j h, ?_⟩
    intro hji
    rw [hji]
    exact ⟨n, hw⟩
  exact keyz.trans keyw.symm

end Work.Horn
