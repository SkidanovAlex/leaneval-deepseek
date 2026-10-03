import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.spread_chain_nesting
import Submission.Work.Horn.petal_image_ne_zero

namespace Work.Horn

set_option linter.unusedVariables false

open Set Filter Topology

noncomputable section

/-!
# Saturated nesting of the spread chain

This file proves `Work.Horn.spread_chain_nesting_saturated`.  The chain is the one of
`Work.Horn.spreadChain`; the new content with respect to `Work.Horn.spread_chain_nesting` is that
the level `W (n+1) i` is *saturated*: every preconnected `C ⊆ D` lying in `G ⁻¹' (W n i)` that
meets `W (n+1) i` is already contained in `W (n+1) i`.  The reason is that `W (n+1) i` is exactly
one connected component of the open set `D ∩ G ⁻¹' (W n i)` (all the components meeting the
connected `W n i` coincide), and a preconnected subset of an open set that meets a connected
component is contained in that component.

The main technical input is therefore the following saturation property of a single spread step,
which is proved *before* anything about the chain.
-/

/-- **One spread step is component-saturated.**  Under the same hypotheses as
`Work.Horn.spreadStep_spec`, `spreadStep G D A i` is a single connected component of the open set
`D ∩ G ⁻¹' (A i)`; consequently any preconnected `C ⊆ D` with `G '' C ⊆ A i` that meets
`spreadStep G D A i` is contained in it. -/
lemma spreadStep_saturated {q : ℕ} {G : ℂ → ℂ} {D : Set ℂ} {A : Fin q → Set ℂ}
    (hD : IsOpen D) (hG : DifferentiableOn ℂ G D)
    (hopen : ∀ i, IsOpen (A i)) (hconn : ∀ i, IsConnected (A i))
    (hsub : ∀ i, A i ⊆ D) (hmap : ∀ i, G '' A i ⊆ A i)
    (hdisj : ∀ i j : Fin q, i ≠ j → Disjoint (A i) (A j)) :
    ∀ i, ∀ C : Set ℂ, IsPreconnected C → C ⊆ D → C ⊆ G ⁻¹' (A i) →
      (C ∩ spreadStep G D A i).Nonempty → C ⊆ spreadStep G D A i := by
  intro i C hCpre hCD hCG hmeet
  obtain ⟨x₀, hx₀⟩ := (hconn i).nonempty
  -- `A i` is contained in the open set whose components we take
  have hAsubU : A i ⊆ D ∩ G ⁻¹' (A i) := fun y hy => ⟨hsub i hy, hmap i ⟨y, hy, rfl⟩⟩
  -- all the components of `D ∩ G ⁻¹' (A i)` that meet `A i` coincide
  have heq : spreadStep G D A i = connectedComponentIn (D ∩ G ⁻¹' (A i)) x₀ := by
    rw [spreadStep]
    apply subset_antisymm
    · intro z hz
      obtain ⟨x, hx, hzCC⟩ := Set.mem_iUnion₂.mp hz
      have hxcc : x ∈ connectedComponentIn (D ∩ G ⁻¹' (A i)) x₀ :=
        IsPreconnected.subset_connectedComponentIn (hconn i).isPreconnected hx₀ hAsubU hx
      rw [connectedComponentIn_eq hxcc]
      exact hzCC
    · intro z hz
      exact Set.mem_iUnion₂.mpr ⟨x₀, hx₀, hz⟩
  have hCU : C ⊆ D ∩ G ⁻¹' (A i) := fun z hz => ⟨hCD hz, hCG hz⟩
  obtain ⟨y, hyC, hyStep⟩ := hmeet
  have hycc : y ∈ connectedComponentIn (D ∩ G ⁻¹' (A i)) x₀ := heq ▸ hyStep
  rw [heq, connectedComponentIn_eq hycc]
  exact IsPreconnected.subset_connectedComponentIn hCpre hyC hCU

/-- **Nesting of the spread chain, component-saturated form** (`NOTES_GERM_F0.md` §§41–43;
replaces the one-sided `Work.Horn.spread_chain_nesting` as the object the rest of the chain
leans on).

Same hypotheses as `Work.Horn.spread_chain_nesting` (petals `V` of a parabolic germ `G` on the
open `D`, `G 0 = 0`, petals disjoint, `G`-forward-invariant modulo `0`, accumulating at `0`,
capturing every basin orbit, locally constant entered index, `0 ∉ V i`, `0` outside the basin).
Conclusion: a chain `W : ℕ → Fin q → Set ℂ` with `W 0 i = V i`; all `W n i` open, connected and
`⊆ D`; increasing; the *saturation* clause (every preconnected `C ⊆ D` inside `G ⁻¹' (W n i)` that
meets `W (n+1) i` lies in `W (n+1) i` — the clause
`Work.Horn.spread_chain_covering_off_critval` consumes, verbatim); the level clause (such `C`
meeting `W n i` lies in `W (n+1) i`); `G` maps `W (n+1) i` into `W n i ∪ {0}`; and level-wise
disjointness across indices.

Proof: reuse the recursion of `Work.Horn.spread_chain_nesting`
(`W (n+1) i = spreadStep G D (W n) i = connectedComponentIn (D ∩ G ⁻¹' (W n i)) x₀`, a single
component by that file's connectedness argument).  Given preconnected `C ⊆ D ∩ G ⁻¹' (W n i)`
meeting `W (n+1) i`, `IsPreconnected.subset_connectedComponentIn` plus `connectedComponentIn_eq`
gives `C ⊆ W (n+1) i`.  The level clause follows from saturation plus monotonicity.  No
properness, no simple connectivity and no critical-point input is claimed. -/
theorem spread_chain_nesting_saturated {G : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    (hD : IsOpen D) (hG : DifferentiableOn ℂ G D) (h0 : (0 : ℂ) ∈ D) (hfix : G 0 = 0)
    (hVopen : ∀ i, IsOpen (V i)) (hVconn : ∀ i, IsConnected (V i)) (hVsub : ∀ i, V i ⊆ D)
    (hVmap : ∀ i, ∀ z ∈ V i, G z ∈ V i ∪ {0})
    (hVne : ∀ i, (0 : ℂ) ∉ V i)
    (hVdisj : ∀ i j : Fin q, i ≠ j → Disjoint (V i) (V j))
    (hVcl : ∀ i, (0 : ℂ) ∈ closure (V i))
    (h0out : (0 : ℂ) ∉ MandelDim.ParabolicBasin G D)
    (hVcapture : ∀ z ∈ MandelDim.ParabolicBasin G D, ∃ n : ℕ, G^[n] z ∈ ⋃ i, V i)
    (hVreach : ∀ z ∈ D, (∃ n : ℕ, (∀ k < n, G^[k] z ∈ D) ∧ G^[n] z ∈ ⋃ i, V i) →
      z ∈ MandelDim.ParabolicBasin G D)
    (hVindex : ∀ z ∈ MandelDim.ParabolicBasin G D, ∃ U ∈ nhds z, ∀ w ∈ U, ∀ i : Fin q,
      ((∃ n : ℕ, G^[n] z ∈ V i) ↔ (∃ n : ℕ, G^[n] w ∈ V i))) :
    ∃ W : ℕ → Fin q → Set ℂ,
      (∀ n i, IsOpen (W n i)) ∧ (∀ n i, IsConnected (W n i)) ∧ (∀ n i, W n i ⊆ D) ∧
      (∀ i, W 0 i = V i) ∧
      (∀ n i, W n i ⊆ W (n + 1) i) ∧
      (∀ n i, ∀ C : Set ℂ, IsPreconnected C → C ⊆ D → C ⊆ G ⁻¹' (W n i) →
        (C ∩ W (n + 1) i).Nonempty → C ⊆ W (n + 1) i) ∧
      (∀ n i, ∀ C : Set ℂ, IsPreconnected C → C ⊆ D → C ⊆ G ⁻¹' (W n i) →
        (W n i ∩ C).Nonempty → C ⊆ W (n + 1) i) ∧
      (∀ n i, Set.MapsTo G (W (n + 1) i) (W n i ∪ {0})) ∧
      (∀ n i j : Fin q, i ≠ j → Disjoint (W n i) (W n j)) := by
  classical
  -- a point of a petal never maps to `0`
  have hnozero : ∀ i, ∀ z ∈ V i, G z ≠ 0 :=
    petal_image_ne_zero hD hG hVconn hVsub hVcl hVreach h0out
  -- hence `G` maps each petal into itself
  have hGV : ∀ i, G '' V i ⊆ V i := by
    intro i
    rintro _ ⟨y, hy, rfl⟩
    rcases hVmap i y hy with h | h
    · exact h
    · exact absurd h (hnozero i y hy)
  -- the induction invariant for the spread chain
  have key : ∀ n, (∀ i, IsOpen (spreadChain G D V n i)) ∧
      (∀ i, IsConnected (spreadChain G D V n i)) ∧
      (∀ i, spreadChain G D V n i ⊆ D) ∧
      (∀ i, G '' spreadChain G D V n i ⊆ spreadChain G D V n i) ∧
      (∀ i j : Fin q, i ≠ j → Disjoint (spreadChain G D V n i) (spreadChain G D V n j)) := by
    intro n
    induction n with
    | zero => exact ⟨hVopen, hVconn, hVsub, hGV, hVdisj⟩
    | succ n ih =>
      obtain ⟨ho, hc, hs, hm, hd⟩ := ih
      obtain ⟨so, sc, ss, hAst, sm, _hmax, sd⟩ := spreadStep_spec hD hG ho hc hs hm hd
      refine ⟨so, sc, ss, ?_, sd⟩
      intro i
      exact subset_trans (sm i) (hAst i)
  refine ⟨spreadChain G D V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n i; exact (key n).1 i
  · intro n i; exact (key n).2.1 i
  · intro n i; exact (key n).2.2.1 i
  · intro i; rfl
  · -- monotonicity
    intro n i
    obtain ⟨ho, hc, hs, hm, hd⟩ := key n
    obtain ⟨_so, _sc, _ss, hAst, _sm, _hmax, _sd⟩ := spreadStep_spec hD hG ho hc hs hm hd
    exact hAst i
  · -- the saturation clause
    intro n i C hCpre hCD hCG hmeet
    obtain ⟨ho, hc, hs, hm, hd⟩ := key n
    exact spreadStep_saturated hD hG ho hc hs hm hd i C hCpre hCD hCG hmeet
  · -- the level clause
    intro n i C hCpre hCD hCG hmeet
    obtain ⟨ho, hc, hs, hm, hd⟩ := key n
    obtain ⟨_so, _sc, _ss, _hAst, _sm, hmax, _sd⟩ := spreadStep_spec hD hG ho hc hs hm hd
    exact hmax i C hCpre hCD hCG hmeet
  · -- `G` maps the next level into the previous one (modulo `0`)
    intro n i
    obtain ⟨ho, hc, hs, hm, hd⟩ := key n
    obtain ⟨_so, _sc, _ss, _hAst, sm, _hmax, _sd⟩ := spreadStep_spec hD hG ho hc hs hm hd
    intro z hz
    exact Or.inl (sm i ⟨z, hz, rfl⟩)
  · -- level-wise disjointness
    intro n i j hij
    exact (key n).2.2.2.2 i j hij

end

end Work.Horn
