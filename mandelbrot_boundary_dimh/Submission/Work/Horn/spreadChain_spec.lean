import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.spread_chain_nesting
import Submission.Work.Horn.spread_chain_nesting_saturated
import Submission.Work.Horn.spread_union_basic
import Submission.Work.Horn.spread_chain_covering_off_critval
import Submission.Work.Horn.petal_components_upper_local
import Submission.Work.Horn.basin_basic_Dg
import Submission.Work.Horn.hopen_Dg
import Submission.Work.Horn.petal_image_ne_zero
import Submission.Work.Horn.flower_petals_Dg

namespace Work.Horn
open Set Filter Topology
open scoped Topology

/-- **The chain of `Work.Horn.spreadChain`, with all the properties needed downstream, for the
*canonical* chain.**  This is `Work.Horn.spread_chain_nesting_saturated` with the existential
quantifier over the chain replaced by the concrete chain `spreadChain G D V`: the induction of
that file in fact computes the chain, so the saturated chain *is* `spreadChain G D V`.

The hypotheses are those of `spread_chain_nesting_saturated`, minus `hVindex` (never used: the
construction of the chain has nothing to do with the Markov index) and minus `hVcapture` (also
unused: the capture property is a property of the basin, not of the chain).  `hD`/`hG`/`h0out`
are the structural facts about the ambient map that the spread step needs, and
`hVreach`/`h0out` are used only to know that the petals are mapped into themselves
(`petal_image_ne_zero`: a petal point never maps to `0`).

Conclusion: every `spreadChain G D V n i` is open, connected and inside `D`; level `0` is `V`;
the chain is increasing; `G` maps level `n+1` into level `n` modulo `0`; level `n+1` is
*component-saturated* (`C` preconnected, `⊆ D`, `⊆ G ⁻¹' (W n i)`, meeting `W (n+1) i` implies
`C ⊆ W (n+1) i`) and one-sidedly maximal; and distinct indices stay disjoint, level-wise. -/
theorem spreadChain_props {G : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    (hD : IsOpen D) (hG : DifferentiableOn ℂ G D)
    (hVopen : ∀ i, IsOpen (V i)) (hVconn : ∀ i, IsConnected (V i)) (hVsub : ∀ i, V i ⊆ D)
    (hVmap : ∀ i, ∀ z ∈ V i, G z ∈ V i ∪ {0})
    (hVne : ∀ i, (0 : ℂ) ∉ V i)
    (hVdisj : ∀ i j : Fin q, i ≠ j → Disjoint (V i) (V j))
    (hVcl : ∀ i, (0 : ℂ) ∈ closure (V i))
    (h0out : (0 : ℂ) ∉ MandelDim.ParabolicBasin G D)
    (hVreach : ∀ z ∈ D, (∃ n : ℕ, (∀ k < n, G^[k] z ∈ D) ∧ G^[n] z ∈ ⋃ i, V i) →
      z ∈ MandelDim.ParabolicBasin G D) :
    (∀ n i, IsOpen (spreadChain G D V n i)) ∧
    (∀ n i, IsConnected (spreadChain G D V n i)) ∧
    (∀ n i, spreadChain G D V n i ⊆ D) ∧
    (∀ i, spreadChain G D V 0 i = V i) ∧
    (∀ n i, spreadChain G D V n i ⊆ spreadChain G D V (n + 1) i) ∧
    (∀ n i, Set.MapsTo G (spreadChain G D V (n + 1) i) (spreadChain G D V n i ∪ {0})) ∧
    (∀ n i, ∀ C : Set ℂ, IsPreconnected C → C ⊆ D → C ⊆ G ⁻¹' (spreadChain G D V n i) →
      (C ∩ spreadChain G D V (n + 1) i).Nonempty → C ⊆ spreadChain G D V (n + 1) i) ∧
    (∀ n i, ∀ C : Set ℂ, IsPreconnected C → C ⊆ D → C ⊆ G ⁻¹' (spreadChain G D V n i) →
      (spreadChain G D V n i ∩ C).Nonempty → C ⊆ spreadChain G D V (n + 1) i) ∧
    (∀ (n : ℕ) (i j : Fin q), i ≠ j → Disjoint (spreadChain G D V n i) (spreadChain G D V n j)) := by
  -- a point of a petal never maps to `0`, so `G` maps each petal into itself
  have hnozero : ∀ i, ∀ z ∈ V i, G z ≠ 0 :=
    petal_image_ne_zero hD hG hVconn hVsub hVcl hVreach h0out
  have hGV : ∀ i, G '' V i ⊆ V i := by
    intro i
    rintro _ ⟨y, hy, rfl⟩
    rcases hVmap i y hy with h | h
    · exact h
    · exact absurd h (hnozero i y hy)
  -- the induction invariant of the spread chain
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n i; exact (key n).1 i
  · intro n i; exact (key n).2.1 i
  · intro n i; exact (key n).2.2.1 i
  · intro i; rfl
  · -- monotonicity
    intro n i
    obtain ⟨ho, hc, hs, hm, hd⟩ := key n
    obtain ⟨_so, _sc, _ss, hAst, _sm, _hmax, _sd⟩ := spreadStep_spec hD hG ho hc hs hm hd
    exact hAst i
  · -- `G` maps the next level into the previous one (modulo `0`)
    intro n i
    obtain ⟨ho, hc, hs, hm, hd⟩ := key n
    obtain ⟨_so, _sc, _ss, _hAst, sm, _hmax, _sd⟩ := spreadStep_spec hD hG ho hc hs hm hd
    intro z hz
    exact Or.inl (sm i ⟨z, hz, rfl⟩)
  · -- the component-saturation clause
    intro n i C hCpre hCD hCG hmeet
    obtain ⟨ho, hc, hs, hm, hd⟩ := key n
    exact spreadStep_saturated hD hG ho hc hs hm hd i C hCpre hCD hCG hmeet
  · -- the one-sided maximality clause
    intro n i C hCpre hCD hCG hmeet
    obtain ⟨ho, hc, hs, hm, hd⟩ := key n
    obtain ⟨_so, _sc, _ss, _hAst, _sm, hmax, _sd⟩ := spreadStep_spec hD hG ho hc hs hm hd
    exact hmax i C hCpre hCD hCG hmeet
  · -- level-wise disjointness
    intro n i j hij
    exact (key n).2.2.2.2 i j hij

theorem spreadChain_spec {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    {q : ℕ} {V : Fin q → Set ℂ}
    (hVopen : ∀ (i : Fin q), IsOpen (V i)) (hVconn : ∀ (i : Fin q), IsConnected (V i))
    (hVsub : ∀ (i : Fin q), V i ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))
    (hVmap : ∀ (i : Fin q), ∀ z ∈ V i, MandelDim.pushdown d.E z ∈ V i ∪ {0})
    (hVne : ∀ (i : Fin q), (0 : ℂ) ∉ V i)
    (hVdisj : ∀ (i j : Fin q), i ≠ j → Disjoint (V i) (V j))
    (hVcl : ∀ (i : Fin q), (0 : ℂ) ∈ closure (V i))
    (hVcapture : ∀ z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))),
      ∃ n : ℕ, (MandelDim.pushdown d.E)^[n] z ∈ ⋃ i, V i)
    (hVreach : ∀ z ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
      (∃ n : ℕ, (∀ k < n, (MandelDim.pushdown d.E)^[k] z ∈
          insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ∧
        (MandelDim.pushdown d.E)^[n] z ∈ ⋃ i, V i) →
      z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) :
    let W : ℕ → Fin q → Set ℂ := Work.Horn.spreadChain (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) V
    (∀ (n : ℕ) (i : Fin q), IsOpen (W n i)) ∧
    (∀ (n : ℕ) (i : Fin q), IsConnected (W n i)) ∧
    (∀ (n : ℕ) (i : Fin q), W n i ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ∧
    (∀ (i : Fin q), W 0 i = V i) ∧
    (∀ (n : ℕ) (i : Fin q), W n i ⊆ W (n + 1) i) ∧
    (∀ (n : ℕ) (i : Fin q), Set.MapsTo (MandelDim.pushdown d.E) (W (n + 1) i) (W n i ∪ {0})) ∧
    (∀ (n : ℕ) (i : Fin q) (C : Set ℂ), IsPreconnected C →
      C ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) → C ⊆ (MandelDim.pushdown d.E) ⁻¹' (W n i) →
      (C ∩ W (n + 1) i).Nonempty → C ⊆ W (n + 1) i) ∧
    (∀ (n : ℕ) (i : Fin q) (C : Set ℂ), IsPreconnected C →
      C ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) → C ⊆ (MandelDim.pushdown d.E) ⁻¹' (W n i) →
      (W n i ∩ C).Nonempty → C ⊆ W (n + 1) i) ∧
    (∀ (n : ℕ) (i j : Fin q), i ≠ j → Disjoint (W n i) (W n j)) := by
  classical
  -- the structural facts about `g = pushdown d.E` on `D_g = {0} ∪ π(Bu ∪ Bl)`:
  -- openness of the domain, holomorphy of `g`, and `0` outside the parabolic basin
  obtain ⟨hBuO, hBlO, -, -, -, -, -⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hD : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    isOpen_insert_piExp hBuO hBlO hup hlo
  have hG : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  have h0out : (0 : ℂ) ∉ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    zero_not_mem_basin_pushdown hF0 d hB hBne hBu hBl hsub hup hlo
  exact spreadChain_props hD hG hVopen hVconn hVsub hVmap hVne hVdisj hVcl h0out hVreach

end Work.Horn
