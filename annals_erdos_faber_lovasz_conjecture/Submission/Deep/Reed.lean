/-
# The locally sparse colouring bound of Molloy–Reed

!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
!!  READ THIS FIRST -- CORRECTION OF THE ORIGINAL REQUEST (2026-09-22)       !!
!!                                                                            !!
!!  This file used to define `ReedStatement`, the statement                  !!
!!  `chi(G) <= ceil((omega(G) + Delta(G) + 1)/2)`, and prove                     !!
!!  `molloyReedStatement_of_reed : ReedStatement -> MolloyReedStatement`.    !!
!!  THAT WAS A MISTAKE: Reed's `omega,Delta,chi` bound is an OPEN CONJECTURE       !!
!!  (Reed 1998; see e.g. Bonamy-Perrett-Postle, "Colouring graphs with      !!
!!  sparse neighbourhoods", arXiv:1810.06704, where a partial result is      !!
!!  proved and it is explicitly called a conjecture).  It must NOT be        !!
!!  targeted.                                                                !!
!!                                                                            !!
!!  The correct target is `SparseGraphStatement` below: the bound for        !!
!!  "`delta`-sparse" graphs, i.e. graphs in which every neighbourhood spans  !!
!!  at most `(1-delta) * Delta^2 / 2` edges.  Molloy and Reed proved it with      !!
!!  a SINGLE application of the *naive colouring procedure* (random colour   !!
!!  from `[k]`, then uncolour both ends of every monochromatic edge, then    !!
!!  finish by greedy list colouring); see                                  !!
!!    * Molloy-Reed, "Graph Colouring and the Probabilistic Method", ch. 10, !!
!!      Theorem 10.5 (the source cited by the EFL paper),                    !!
!!    * Bruhn-Joos, "A stronger bound for the strong chromatic index",       !!
!!    * Bonamy-Perrett-Postle, arXiv:1810.06704, section 3 (a self-contained!!
!!      modern treatment -- the LaTeX source is in `Papers/bpp/` of this     !!
!!      workspace); the three key ingredients are the extension           !!
!!      proposition (colouring `(N(u)) - (Dist(u)) >= d(u)+1-k` extends),    !!
!!      the expectation computation for pairs/triples of coloured            !!
!!      neighbours, and a concentration inequality plus the Lovasz Local     !!
!!      Lemma.                                                              !!
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

`MolloyReedStatement` (`Submission/EFL/LocallySparse.lean`) is one of the four
deep inputs of the final assembly: a graph all of whose neighbourhoods are
locally sparse (`e(G[N(v)]) <= (1-zeta) Delta^2/2`) has chromatic number at most
`(1-zeta/e^6) Delta`, for `Delta >= Delta_0(zeta)` with `Delta_0` polynomially
bounded in `1/zeta`.

`SparseGraphStatement` below is the theorem of Molloy-Reed/Bruhn-Joos for
`delta`-sparse graphs, with the *same* hypothesis shape, an explicit constant
`c >= 1/100` in place of the tiny `1/e^6`, and `(Delta+1)` in place of `Delta`.
`molloyReedStatement_of_sparse` derives `MolloyReedStatement` from it by
elementary arithmetic (`1/100 > 1/e^6` and `Delta >= C/zeta`).

The subproject `Submission/Work/Deep/{Reed,Sparse}/` is asked to prove
`SparseGraphStatement`.

**The deterministic half of that proof is already done** in
`Submission/Deep/NCP.lean` (my file, coordinator): it proves the greedy
list-colouring lemma, the extension proposition `colorable_of_partial`
(Bonamy–Perrett–Postle, Prop. 3.2), defines the interface

  `NCPCoreStatement`  — what the naive colouring procedure has to produce,

and proves `sparseGraphStatement_of_ncp : NCPCoreStatement → SparseGraphStatement`.
So the remaining obligation for the probabilistic half is exactly
`NCPCoreStatement` (a partial proper colouring with `Dist(u) + d(u) < Col(u) + k`
at every vertex), and it can be plugged in by
`sparseGraphStatement_of_ncp`.  The subproject may of course use its own
equivalent formulation.
-/
import Submission.EFL.LocallySparse
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
open scoped BigOperators
open Function

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {V : Type*}

lemma nbrEdges_eq_card_sym2 [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : nbrEdges G v = (G.edgeFinset ∩ (G.neighborFinset v).sym2).card := by
  rw [nbrEdges, ← Finset.card_map (f := (Embedding.subtype (· ∈ G.neighborSet v)).sym2Map)
      (s := (G.induce (G.neighborSet v)).edgeFinset),
    SimpleGraph.map_edgeFinset_induce, SimpleGraph.neighborFinset_def]

lemma choose_le_nbrEdges [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {t : Finset V} (ht : G.IsClique (t : Set V)) (htN : ∀ u ∈ t, G.Adj v u) :
    t.card.choose 2 ≤ nbrEdges G v := by
  classical
  have hclique_card : (⊤ : SimpleGraph ↥t).edgeFinset.card = t.card.choose 2 := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_coe]
  have hsub : ((⊤ : SimpleGraph ↥t).edgeFinset.map (Embedding.subtype (· ∈ t)).sym2Map)
      ⊆ G.edgeFinset ∩ (G.neighborFinset v).sym2 := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_map.mp he
    refine Sym2.ind (f := fun e₀ => e₀ ∈ (⊤ : SimpleGraph ↥t).edgeFinset →
      (Embedding.subtype (· ∈ t)).sym2Map e₀ ∈
      G.edgeFinset ∩ (G.neighborFinset v).sym2) ?_ e₀ he₀
    intro x y hxy
    have hne : x ≠ y := by
      have h1 := hxy
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h1
      simpa using h1
    rw [Embedding.sym2Map_apply, Sym2.map_mk]
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact ht x.2 y.2 (by intro h; exact hne (Subtype.ext h))
    · rw [Finset.mk_mem_sym2_iff]
      constructor
      · rw [SimpleGraph.mem_neighborFinset]; simpa using htN x x.2
      · rw [SimpleGraph.mem_neighborFinset]; simpa using htN y y.2
  rw [nbrEdges_eq_card_sym2, ← hclique_card, ← Finset.card_map]
  exact Finset.card_le_card hsub


/-- **Clique number bound from local sparsity.** -/
lemma cliqueNum_le_of_local [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ζ Δ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ ≤ 1) (hΔ1 : 1 ≤ Δ)
    (hsp : ∀ v : V, (nbrEdges G v : ℝ) ≤ (1 - ζ) * Δ ^ 2 / 2) :
    (G.cliqueNum : ℝ) ≤ 2 + Real.sqrt (1 - ζ) * Δ := by
  rcases lt_or_ge G.cliqueNum 3 with hlt | hge
  · have h2 : (G.cliqueNum : ℝ) ≤ 2 := by
      have h : G.cliqueNum ≤ 2 := by omega
      exact_mod_cast h
    have hs : 0 ≤ Real.sqrt (1 - ζ) := Real.sqrt_nonneg _
    have hΔ0 : 0 ≤ Δ := by linarith
    nlinarith [mul_nonneg hs hΔ0]
  · obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
    have hscard : s.card = G.cliqueNum := hs.card_eq
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [hscard]; omega : 0 < s.card)
    set t : Finset V := s.erase v with htdef
    have htclique : G.IsClique (t : Set V) :=
      Set.Pairwise.mono (by
        intro u hu
        rw [htdef] at hu
        exact (Finset.mem_erase.mp hu).2) hs.isClique
    have htN : ∀ u ∈ t, G.Adj v u := by
      intro u hu
      rw [htdef] at hu
      obtain ⟨huv, hus⟩ := Finset.mem_erase.mp hu
      exact hs.isClique hv hus (Ne.symm huv)
    have hcount := choose_le_nbrEdges G v htclique htN
    have hle : ((G.cliqueNum : ℝ) - 1) * ((G.cliqueNum : ℝ) - 2) ≤ (1 - ζ) * Δ ^ 2 := by
      have htcard : t.card = G.cliqueNum - 1 := by
        rw [htdef, Finset.card_erase_of_mem hv, hscard]
      have h1 : ((t.card.choose 2 : ℕ) : ℝ) ≤ (1 - ζ) * Δ ^ 2 / 2 :=
        le_trans (by exact_mod_cast hcount) (hsp v)
      rw [htcard, Nat.cast_choose_two] at h1
      have hc : (((G.cliqueNum - 1 : ℕ)) : ℝ) = (G.cliqueNum : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ G.cliqueNum)]
        norm_num
      rw [hc] at h1
      linarith
    have hbase : ((G.cliqueNum : ℝ) - 2) ^ 2 ≤ (1 - ζ) * Δ ^ 2 := by
      have hω3 : (3 : ℝ) ≤ (G.cliqueNum : ℝ) := by exact_mod_cast hge
      nlinarith [hle]
    have hsqrt := Real.le_sqrt_of_sq_le hbase
    have hsq : Real.sqrt ((1 - ζ) * Δ ^ 2) = Real.sqrt (1 - ζ) * Δ := by
      rw [Real.sqrt_mul (by linarith) (Δ ^ 2), Real.sqrt_sq (by linarith)]
    rw [hsq] at hsqrt
    linarith

/-- **The Molloy–Reed bound for locally sparse (`δ`-sparse) graphs.**

There is a constant `c ≥ 1/100` and a threshold `Δ₀ δ`, polynomially bounded in
`1/δ`, such that every finite graph `G` with `Δ(G) ≤ Δ ≥ Δ₀ δ` in which every
neighbourhood spans at most `(1-δ)Δ²/2` edges admits a `(1 - c·δ)(Δ+1)`-colouring.

This is the statement proved by the naive colouring procedure of Molloy and Reed
("Graph Colouring and the Probabilistic Method", Chapter 10) and Bruhn–Joos;
the constant they obtain is `c ≈ 0.0238`, comfortably above `1/100`, and their
hypothesis is the (slightly stronger) `e(G[N(v)]) ≤ (1-δ)·C(Δ,2)`.  See
`Papers/bpp/ColouringSparseGraphsRevision-clean.tex`, Section 3, for a
self-contained modern treatment. -/
def SparseGraphStatement : Prop :=
  ∃ c : ℝ, 1 / 100 ≤ c ∧ ∃ Δ₀ : ℝ → ℝ,
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 → 0 < Δ₀ δ) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ m : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → Δ₀ δ ≤ C / δ ^ m) ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ),
      Δ₀ δ ≤ Δ → (G.maxDegree : ℝ) ≤ Δ →
      (∀ v : V, (nbrEdges G v : ℝ) ≤ (1 - δ) * Δ ^ 2 / 2) →
      ∃ k : ℕ, (k : ℝ) ≤ (1 - c * δ) * (Δ + 1) ∧ G.Colorable k

/-- `100 < e⁶`. -/
lemma hundred_lt_exp_six : (100 : ℝ) < Real.exp 6 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp 6 = Real.exp 1 ^ 6 := (Real.exp_one_pow 6).symm
  have h3 : (2.7 : ℝ) ≤ (2.7182818283 : ℝ) := by norm_num
  rw [h2]
  calc (100 : ℝ) < (2.7 : ℝ) ^ 6 := by norm_num
    _ ≤ (2.7182818283 : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) h3 6
    _ ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) (le_of_lt h1) 6

/-- **The reduction.**  The Molloy–Reed bound for `δ`-sparse graphs implies the
form of the locally sparse colouring theorem consumed by the EFL development. -/
theorem molloyReedStatement_of_sparse (h : SparseGraphStatement) : MolloyReedStatement := by
  obtain ⟨c, hc, Δ₀, hΔ₀pos, ⟨C, hC, m, hΔ₀bdd⟩, hmain⟩ := h
  have hc' : 0 < c - 1 / Real.exp 6 := by
    have h100 : 1 / Real.exp 6 < 1 / 100 := by
      rw [div_lt_div_iff₀ (Real.exp_pos 6) (by norm_num : (0:ℝ) < 100)]
      nlinarith [hundred_lt_exp_six]
    linarith
  refine ⟨fun ζ => max (Δ₀ ζ) (1 / ((c - 1 / Real.exp 6) * ζ)), ?_, ?_, ?_⟩
  · intro ζ hζ0 hζ1
    exact lt_of_lt_of_le (hΔ₀pos ζ hζ0 hζ1) (le_max_left _ _)
  · refine ⟨C + 1 / (c - 1 / Real.exp 6), by positivity, m + 1, ?_⟩
    intro ζ hζ0 hζ1
    have h1 : Δ₀ ζ ≤ C / ζ ^ m := hΔ₀bdd ζ hζ0 hζ1
    have h2 : 1 / ((c - 1 / Real.exp 6) * ζ) ≤ (1 / (c - 1 / Real.exp 6)) / ζ ^ (m + 1) := by
      rw [div_le_div_iff₀ (mul_pos hc' hζ0) (pow_pos hζ0 (m + 1))]
      have hzm : ζ ^ m ≤ 1 := pow_le_one₀ (le_of_lt hζ0) hζ1
      have hstep := mul_le_mul_of_nonneg_right hzm (le_of_lt hζ0)
      have hreq : (1 / (c - 1 / Real.exp 6)) * ((c - 1 / Real.exp 6) * ζ) = ζ := by
        rw [one_div, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc'), one_mul]
      rw [hreq]
      simpa [pow_succ] using hstep
    have h3 : C / ζ ^ m ≤ C / ζ ^ (m + 1) := by
      rw [div_le_div_iff₀ (pow_pos hζ0 m) (pow_pos hζ0 (m + 1))]
      have h1 : ζ ^ (m + 1) ≤ ζ ^ m := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg (le_of_lt hζ0) m) hζ1
      exact mul_le_mul_of_nonneg_left h1 (le_of_lt hC)
    calc max (Δ₀ ζ) (1 / ((c - 1 / Real.exp 6) * ζ))
        ≤ max (C / ζ ^ m) ((1 / (c - 1 / Real.exp 6)) / ζ ^ (m + 1)) :=
          max_le_max h1 h2
      _ ≤ (C + 1 / (c - 1 / Real.exp 6)) / ζ ^ (m + 1) := by
          rw [add_div]
          refine max_le ?_ ?_
          · calc C / ζ ^ m ≤ C / ζ ^ (m + 1) := h3
              _ ≤ C / ζ ^ (m + 1) + (1 / (c - 1 / Real.exp 6)) / ζ ^ (m + 1) :=
                le_add_of_nonneg_right (by positivity)
          · exact le_add_of_nonneg_left (by positivity)
  · intro ζ hζ0 hζ1 W _instW _instW' G _instG Δ hthr hmax hsp
    have hthr1 : Δ₀ ζ ≤ Δ := le_trans (le_max_left _ _) hthr
    have hthr2 : 1 / ((c - 1 / Real.exp 6) * ζ) ≤ Δ := le_trans (le_max_right _ _) hthr
    obtain ⟨k, hk, hcol⟩ := hmain ζ hζ0 hζ1 W G Δ hthr1 hmax hsp
    refine ⟨k, ?_, hcol⟩
    have hkey : 1 ≤ Δ * ((c - 1 / Real.exp 6) * ζ) := by
      rw [div_le_iff₀ (mul_pos hc' hζ0)] at hthr2
      exact hthr2
    have hstep : (1 - c * ζ) * (Δ + 1) ≤ (1 - ζ / Real.exp 6) * Δ := by
      have hcz : 0 ≤ c * ζ := mul_nonneg (by linarith) (le_of_lt hζ0)
      have h2 : (1 : ℝ) ≤ ζ * Δ * (c - 1 / Real.exp 6) := by nlinarith [hkey]
      have h3 : 1 - c * ζ ≤ ζ * Δ * (c - 1 / Real.exp 6) := by linarith
      have expand : (1 - ζ / Real.exp 6) * Δ - (1 - c * ζ) * (Δ + 1)
          = ζ * Δ * (c - 1 / Real.exp 6) - (1 - c * ζ) := by ring
      linarith [h3, expand]
    linarith [hk, hstep]

end

end ErdosFaberLovaszConjecture
