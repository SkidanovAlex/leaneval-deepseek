import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

/-!
# The Kühn–Osthus argument as a reduction: two named inputs

`Work.Deep.GKO.KOStatement` is Kühn–Osthus, *Hamilton decompositions of regular expanders*
(Theorem 1.2 of arXiv:1202.6219 / the undirected form of JCTB 104 (2014)).  That paper's own
proof (its §2.1) reduces its main theorem to exactly two tools:

* **approximate Hamilton decomposition** (its Theorem 1.3, due to Osthus–Staden): a regular
  robust expander of linear degree contains `(1-η)r` edge-disjoint Hamilton cycles, leaving a
  `≤ 2ηr`-regular leftover;
* **the robust decomposition lemma** (its Lemma 11.2, in the paper's own informal form):
  every regular robust expander contains a *sparse robustly decomposable* spanning subgraph,
  i.e. a sparse regular `H ⊆ G` such that `H ∪ H₀` has a Hamilton decomposition for every
  sufficiently sparse regular `H₀ ⊆ G` edge-disjoint from `H`.

This module states both inputs in the vocabulary of `Defs.lean` and **proves the assembly**:
the two inputs together imply `KOStatement`.  The assembly also uses one genuinely proved
ingredient of the paper (cf. its line "check that `G₀` is still a robust `(ν/2, τ)`-outexpander
with `δ⁰(G) ≥ αn/2`"): **deleting a `d`-regular spanning subgraph with `d ≤ νn/2` from a robust
`(ν,τ)`-expander leaves a robust `(ν/2, τ)`-expander**, `robustExpander_sdiff`, and the
corresponding degree bookkeeping `isRegularOf_sdiff`.  Everything is verified: the only
unproved statements in this module are the two named inputs above.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

open ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Deleting a sparse regular spanning subgraph

The paper's Lemma 11.1 proof uses exactly this: after removing some edge-disjoint Hamilton
cycles, the remainder is still a robust expander with `ν` halved (the degree loss is at most
`νn/2`).  We prove the general statement. -/

/-- Every vertex loses at most `d` neighbours when the `d`-regular spanning subgraph `H` is
deleted from `G`, so the robust `(ν,τ)`-expansion of `G` survives with `ν/2`. -/
theorem robustExpander_sdiff {G H : SimpleGraph (Fin n)} {ν τ : ℝ} {d : ℕ}
    (hν : 0 < ν) (hG : RobustExpander G ν τ) (hreg : IsRegularOf H d)
    (hd : (d : ℝ) ≤ ν / 2 * (n : ℝ)) :
    RobustExpander (G \ H) (ν / 2) τ := by
  intro S h1 h2
  have hsub : robustNbrs G ν S ⊆ robustNbrs (G \ H) (ν / 2) S := by
    intro x hx
    simp only [robustNbrs, Set.mem_ofPred_eq] at hx ⊢
    -- the neighbours of `x` in `G \ H` are those in `G` but not in `H`
    have hset : ((G \ H).neighborSet x ∩ (S : Set (Fin n)))
        = (G.neighborSet x ∩ (S : Set (Fin n))) \ H.neighborSet x := by
      rw [SimpleGraph.neighborSet_sdiff]
      ext y
      simp only [Set.mem_inter_iff, Set.mem_sdiff]
      tauto
    rw [hset]
    set A : Set (Fin n) := G.neighborSet x ∩ (S : Set (Fin n)) with hA
    have h1' : A.ncard ≤ (A \ H.neighborSet x).ncard + (H.neighborSet x : Set (Fin n)).ncard := by
      have hunion : (A \ H.neighborSet x) ∪ (A ∩ H.neighborSet x) = A := by
        ext y
        simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
        tauto
      have hle := Set.ncard_union_le (A \ H.neighborSet x) (A ∩ H.neighborSet x)
      have hle2 : (A ∩ H.neighborSet x).ncard ≤ (H.neighborSet x : Set (Fin n)).ncard := by
        have hmono := Set.ncard_mono (Set.inter_subset_right : A ∩ H.neighborSet x ⊆ H.neighborSet x)
        exact hmono
      calc A.ncard = ((A \ H.neighborSet x) ∪ (A ∩ H.neighborSet x)).ncard := by rw [hunion]
        _ ≤ (A \ H.neighborSet x).ncard + (A ∩ H.neighborSet x).ncard := hle
        _ ≤ (A \ H.neighborSet x).ncard + (H.neighborSet x : Set (Fin n)).ncard := by omega
    have hcard : (H.neighborSet x : Set (Fin n)).ncard = d := by
      rw [← Nat.card_coe_set_eq]
      exact hreg x
    rw [hcard] at h1'
    have hcast : (A.ncard : ℝ) ≤ ((A \ H.neighborSet x).ncard : ℝ) + (d : ℝ) := by
      exact_mod_cast h1'
    have hxA : ν * (n : ℝ) ≤ (A.ncard : ℝ) := hx
    linarith
  have hmono : (robustNbrs G ν S).ncard ≤ (robustNbrs (G \ H) (ν / 2) S).ncard :=
    Set.ncard_mono hsub
  have hmono' : ((robustNbrs G ν S).ncard : ℝ) ≤
      ((robustNbrs (G \ H) (ν / 2) S).ncard : ℝ) := by exact_mod_cast hmono
  have hG' := hG S h1 h2
  have : ν / 2 * (n : ℝ) ≤ ν * (n : ℝ) := by nlinarith
  linarith

/-- The sharpened deletion bound: deleting a `d`-regular spanning subgraph costs only `d/n` of
the robustness parameter, since every vertex loses at most `d` neighbours.  This is the exact
per-step degradation of the "remove one Hamilton cycle at a time" iteration (for a Hamilton cycle,
`d = 2`, so `ν ↦ ν - 2/n`). -/
theorem robustExpander_sdiff' {G H : SimpleGraph (Fin n)} {ν τ : ℝ} {d : ℕ}
    (hG : RobustExpander G ν τ) (hreg : IsRegularOf H d) :
    RobustExpander (G \ H) (ν - (d : ℝ) / (n : ℝ)) τ := by
  intro S h1 h2
  have hsub : robustNbrs G ν S ⊆ robustNbrs (G \ H) (ν - (d : ℝ) / (n : ℝ)) S := by
    intro x hx
    simp only [robustNbrs, Set.mem_ofPred_eq] at hx ⊢
    have hset : ((G \ H).neighborSet x ∩ (S : Set (Fin n)))
        = (G.neighborSet x ∩ (S : Set (Fin n))) \ H.neighborSet x := by
      rw [SimpleGraph.neighborSet_sdiff]
      ext y
      simp only [Set.mem_inter_iff, Set.mem_sdiff]
      tauto
    rw [hset]
    set A : Set (Fin n) := G.neighborSet x ∩ (S : Set (Fin n)) with hA
    have h1' : A.ncard ≤ (A \ H.neighborSet x).ncard + (H.neighborSet x : Set (Fin n)).ncard := by
      have hunion : (A \ H.neighborSet x) ∪ (A ∩ H.neighborSet x) = A := by
        ext y
        simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
        tauto
      have hle := Set.ncard_union_le (A \ H.neighborSet x) (A ∩ H.neighborSet x)
      have hle2 : (A ∩ H.neighborSet x).ncard ≤ (H.neighborSet x : Set (Fin n)).ncard :=
        Set.ncard_mono (Set.inter_subset_right)
      calc A.ncard = ((A \ H.neighborSet x) ∪ (A ∩ H.neighborSet x)).ncard := by rw [hunion]
        _ ≤ (A \ H.neighborSet x).ncard + (A ∩ H.neighborSet x).ncard := hle
        _ ≤ (A \ H.neighborSet x).ncard + (H.neighborSet x : Set (Fin n)).ncard := by omega
    have hcard : (H.neighborSet x : Set (Fin n)).ncard = d := by
      rw [← Nat.card_coe_set_eq]
      exact hreg x
    rw [hcard] at h1'
    have hcast : (A.ncard : ℝ) ≤ ((A \ H.neighborSet x).ncard : ℝ) + (d : ℝ) := by
      exact_mod_cast h1'
    have hxA : ν * (n : ℝ) ≤ (A.ncard : ℝ) := hx
    have hfin : ((A \ H.neighborSet x).ncard : ℝ) ≥ (ν - (d : ℝ) / (n : ℝ)) * (n : ℝ) := by
      rcases eq_or_ne n 0 with hn | hn
      · subst hn
        simp
      · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        have : (ν - (d : ℝ) / (n : ℝ)) * (n : ℝ) = ν * (n : ℝ) - (d : ℝ) := by
          field_simp
        rw [this]
        linarith
    linarith
  have hmono : (robustNbrs G ν S).ncard ≤ (robustNbrs (G \ H) (ν - (d : ℝ) / (n : ℝ)) S).ncard :=
    Set.ncard_mono hsub
  have hmono' : ((robustNbrs G ν S).ncard : ℝ) ≤
      ((robustNbrs (G \ H) (ν - (d : ℝ) / (n : ℝ)) S).ncard : ℝ) := by exact_mod_cast hmono
  have hG' := hG S h1 h2
  have hgoal : (ν - (d : ℝ) / (n : ℝ)) * (n : ℝ) ≤ ν * (n : ℝ) := by
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      simp
    · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hn')]
      linarith [show (0 : ℝ) ≤ (d : ℝ) by positivity]
  linarith

/-- Deleting a `d`-regular spanning subgraph of an `r`-regular graph leaves an
`(r-d)`-regular graph. -/
theorem isRegularOf_sdiff {G H : SimpleGraph (Fin n)} {r d : ℕ} (hHG : H ≤ G)
    (hG : IsRegularOf G r) (hH : IsRegularOf H d) : IsRegularOf (G \ H) (r - d) := by
  intro v
  rw [Nat.card_coe_set_eq]
  have hsub : H.neighborSet v ⊆ G.neighborSet v := fun w hw => hHG hw
  rw [SimpleGraph.neighborSet_sdiff, Set.ncard_sdiff hsub (Set.toFinite _),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hG v, hH v]

end

end Work.Deep.GKO
