import Mathlib
import Submission.Work.BMF.adi_all_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The bicycle sets of the `q`-subgraph and of the full graph

`bikeSet D q ℓ` (the bicycles of the `q`-subgraph) is the sub-collection of `bikeSetAll D ℓ`
(the bicycles of the full quadruple graph) consisting of those bicycles whose attached prime
set contains `q`, i.e. whose `q` lies in `bikePrimesQ D ℓ t`.

This is `Work.BMF.bikeSetAll_bridge`, the bridge used to average `card_bikeSet` over the
primes `q ∈ [P₂/2, P₂]`.
-/

namespace Work.BMF

/-- `Finset.mem_product` is stated for the `Multiset` notation `×ˢ` and therefore does not
match the `.product` shape by `rw`; this is the same statement in the shape we need. -/
lemma bike_mem_product {α β : Type*} {s : Finset α} {t : Finset β} {p : α × β} :
    p ∈ s.product t ↔ p.1 ∈ s ∧ p.2 ∈ t := Finset.mem_product

/-- `IsPrimeIn a b p` is exactly membership in the finset `primesIn a b`. -/
lemma bike_mem_primesIn {a b : ℝ} {p : ℕ} (h : IsPrimeIn a b p) : p ∈ primesIn a b := by
  obtain ⟨hp, ha, hb⟩ := h
  refine Finset.mem_filter.mpr ⟨?_, hp⟩
  rw [natIcc, Finset.mem_Icc]
  exact ⟨Nat.ceil_le.mpr ha, Nat.le_floor hb⟩

/-- The `q`-closed walks through `x` are exactly the closed walks of the full graph through `x`
all of whose steps lie in the `q`-subgraph. -/
lemma closedWalkAll_filter_eq {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : QuadData k f c C X L P₁ P₂) (q ℓ : ℕ) (x : ℝ) :
    closedWalkVal D q ℓ x = (closedWalkAll D ℓ x).filter
      (fun W => ∀ j : Fin ℓ, GAdjQ D q (W j.castSucc) (W j.succ)) := by
  ext W
  simp only [closedWalkVal, closedWalkAll, walkSet, walkSetAll, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hq, hcl, hbase⟩
    exact ⟨⟨fun j => GAdjQ_le_GAdjAll D (hq j), hcl.symm, hbase⟩, hq⟩
  · rintro ⟨⟨hAll, hcl, hbase⟩, hq⟩
    exact ⟨hq, hcl.symm, hbase⟩

theorem bikeSetAll_bridge {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : Work.BMF.QuadData k f c C X L P₁ P₂) (q ℓ : ℕ) :
    Work.BMF.bikeSet D q ℓ = (Work.BMF.bikeSetAll D ℓ).filter
      (fun t => q ∈ Work.BMF.bikePrimesQ D ℓ t) := by
  classical
  -- The left-hand side, with the `q`-closed walks replaced by their description in the full graph.
  have hL : bikeSet D q ℓ = (D.edges.filter (fun e => q ∈ edgeS D e)).sigma
      (fun e => ((closedWalkAll D ℓ e.x₁).filter
            (fun W => ∀ j : Fin ℓ, GAdjQ D q (W j.castSucc) (W j.succ))).product
          ((closedWalkAll D ℓ e.x₂).filter
            (fun W => ∀ j : Fin ℓ, GAdjQ D q (W j.castSucc) (W j.succ)))) := by
    simp only [bikeSet]
    congr 1
    funext e
    rw [closedWalkAll_filter_eq, closedWalkAll_filter_eq]
  rw [hL]
  simp only [bikeSetAll, bikePrimesQ]
  ext t
  simp only [Finset.mem_sigma, Finset.mem_filter, bike_mem_product]
  constructor
  · rintro ⟨⟨he, heq⟩, ⟨h1, g1⟩, h2, g2⟩
    exact ⟨⟨he, h1, h2⟩, bike_mem_primesIn (edgeS_subset D he heq), heq, g1, g2⟩
  · rintro ⟨⟨he, h1, h2⟩, hp, heq, g1, g2⟩
    exact ⟨⟨he, heq⟩, ⟨h1, g1⟩, h2, g2⟩

end Work.BMF
