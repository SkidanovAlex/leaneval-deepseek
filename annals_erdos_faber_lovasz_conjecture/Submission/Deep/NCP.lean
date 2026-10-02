/-
# The naive colouring procedure: the deterministic half

This module provides the deterministic skeleton of the proof of
`ErdosFaberLovaszConjecture.SparseGraphStatement` (`Submission/Deep/Reed.lean`),
i.e. of the Molloy–Reed bound for locally sparse graphs.  The probabilistic
half (the naive colouring procedure and its concentration analysis) is the
target of the subproject `Submission/Work/Deep/Sparse/`.

Contents:

* `listColoring_of_degree_lt_card` — the greedy list-colouring lemma for graphs:
  if every vertex `w` has a list of more than `deg w` colours, then the graph
  has a proper colouring from the lists.
* `colorable_of_partial` — **Proposition 3.2** of Bonamy–Perrett–Postle
  (arXiv:1810.06704) / the extension step of the naive colouring procedure: a
  partial proper `k`-colouring in which every vertex `u` satisfies
  `Col(u) - Dist(u) ≥ d(u) + 1 - k` extends to a `k`-colouring of the graph.
-/
import Submission.Deep.Reed
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

/-! ## Greedy list colouring -/

/-- A partial colouring of `W` in the graph `H`: a map `ψ : W → Option α` which is
proper on its support (adjacent vertices cannot receive the same non-`none`
value). -/
def IsPartialColoringOption {W α : Type*} (H : SimpleGraph W) (ψ : W → Option α) : Prop :=
  ∀ u v, H.Adj u v → ψ u = ψ v → ψ u = none

/-- **Greedy list colouring.**  If every vertex of a finite graph has a list of
more than `deg w` colours, then the graph is list-colourable. -/
theorem listColoring_of_degree_lt_card {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {α : Type*} [Fintype α] [DecidableEq α]
    (L : W → Finset α) (h : ∀ w, H.degree w < (L w).card) :
    ∃ ψ : W → α, (∀ w, ψ w ∈ L w) ∧ ∀ u v, H.Adj u v → ψ u ≠ ψ v := by
  classical
  have key : ∀ S : Finset W, ∃ ψ : W → Option α,
      IsPartialColoringOption H ψ ∧
      (∀ w c, ψ w = some c → c ∈ L w) ∧
      (∀ w, w ∈ S ↔ ψ w ≠ none) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        exact ⟨fun _ => none, fun u v _ h => h, fun w c hc => absurd hc (by simp),
          fun w => by simp⟩
    | insert a S ha ih =>
        obtain ⟨ψ, hproper, hmem, hsupp⟩ := ih
        -- the colours already used on the neighbours of `a`
        set F : Finset α := (Finset.univ : Finset α).filter
          (fun c => ∃ v, v ∈ H.neighborFinset a ∧ ψ v = some c) with hF
        have hadj_mem : ∀ {x y : W}, H.Adj x y → y ∈ H.neighborFinset x := by
          intro x y hxy
          exact (H.mem_neighborFinset (v := x) (w := y)).mpr hxy
        have hFmem : ∀ {v : W} {d : α}, v ∈ H.neighborFinset a → ψ v = some d → d ∈ F := by
          intro v d hv hd
          rw [hF, Finset.mem_filter]
          exact ⟨Finset.mem_univ d, ⟨v, hv, hd⟩⟩
        have hFle : F.card ≤ H.degree a := by
          have hinj : ∀ c ∈ F, ∃ v, v ∈ H.neighborFinset a ∧ ψ v = some c := by
            intro c hc; rw [hF, Finset.mem_filter] at hc; exact hc.2
          let g : α → W := fun c => if hc : c ∈ F then Classical.choose (hinj c hc) else a
          have hg : ∀ c ∈ F, g c ∈ H.neighborFinset a ∧ ψ (g c) = some c := by
            intro c hc; dsimp only [g]; rw [dif_pos hc]; exact Classical.choose_spec (hinj c hc)
          refine Finset.card_le_card_of_injOn g (fun c hc => (hg c hc).1) ?_
          intro c₁ hc₁ c₂ hc₂ hEq
          have h1 := (hg c₁ hc₁).2
          have h2 := (hg c₂ hc₂).2
          have : (some c₁ : Option α) = some c₂ := by rw [← h1, hEq, h2]
          exact Option.some.inj this
        obtain ⟨c, hcL, hcF⟩ : ∃ c ∈ L a, c ∉ F := by
          have hlt : F.card < (L a).card := lt_of_le_of_lt hFle (h a)
          have hnotsub : ¬ L a ⊆ F := fun hsub =>
            absurd (Finset.card_le_card hsub) (not_le.mpr hlt)
          obtain ⟨c, hcL, hcF⟩ := Finset.not_subset.mp hnotsub
          exact ⟨c, hcL, hcF⟩
        refine ⟨Function.update ψ a (some c), ?_, ?_, ?_⟩
        · -- properness
          intro u v huv huv_eq
          have hupd : ∀ w, Function.update ψ a (some c) w = if w = a then some c else ψ w :=
            fun w => Function.update_apply ψ a (some c) w
          by_cases hua : u = a
          · have hu : Function.update ψ a (some c) u = some c := by rw [hupd, if_pos hua]
            have hadj : H.Adj a v := hua ▸ huv
            by_cases hva : v = a
            · rw [hva] at hadj
              exact absurd hadj (H.loopless.irrefl a)
            · have hv : Function.update ψ a (some c) v = ψ v := by rw [hupd, if_neg hva]
              rw [hu, hv] at huv_eq
              exact absurd (hFmem (hadj_mem hadj) huv_eq.symm) hcF
          · have hu : Function.update ψ a (some c) u = ψ u := by rw [hupd, if_neg hua]
            rw [hu] at huv_eq ⊢
            by_cases hva : v = a
            · have hv : Function.update ψ a (some c) v = some c := by rw [hupd, if_pos hva]
              rw [hv] at huv_eq
              exact absurd (hFmem (hadj_mem (hva ▸ huv.symm)) huv_eq) hcF
            · have hv : Function.update ψ a (some c) v = ψ v := by rw [hupd, if_neg hva]
              rw [hv] at huv_eq
              exact hproper u v huv huv_eq
        · -- membership in the lists
          intro w c' hw
          rw [Function.update_apply ψ a (some c) w] at hw
          by_cases hwa : w = a
          · rw [if_pos hwa] at hw
            have hcc : c' = c := (Option.some.inj hw).symm
            rw [hcc, hwa]; exact hcL
          · rw [if_neg hwa] at hw
            exact hmem w c' hw
        · -- support
          intro w
          rw [Function.update_apply ψ a (some c) w]
          by_cases hwa : w = a
          · rw [if_pos hwa, hwa]
            simp
          · rw [if_neg hwa, Finset.mem_insert, hsupp w]
            constructor
            · rintro (h | h)
              · exact absurd h hwa
              · exact h
            · exact Or.inr
  obtain ⟨ψ, hproper, hmem, hsupp⟩ := key (Finset.univ : Finset W)
  have hne : ∀ w, (ψ w).isSome := by
    intro w
    cases hw : ψ w with
    | none => exact absurd hw ((hsupp w).mp (Finset.mem_univ w))
    | some c => simp
  refine ⟨fun w => Option.get _ (hne w),
    fun w => hmem w _ (Option.coe_get (hne w)).symm, ?_⟩
  intro u v huv hEq
  have hEq' : ψ u = ψ v := by
    calc ψ u = some (Option.get _ (hne u)) := (Option.coe_get (hne u)).symm
      _ = some (Option.get _ (hne v)) := congrArg some hEq
      _ = ψ v := Option.coe_get (hne v)
  have hcontra : ¬ (ψ u).isSome := by
    rw [hproper u v huv hEq']
    simp
  exact hcontra (hne u)

/-! ## The extension step of the naive colouring procedure -/

section Extension

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An `Option` which is not `none` is a `some`. -/
lemma some_of_ne_none {α : Type*} {o : Option α} (h : o ≠ none) : ∃ a, o = some a := by
  cases o with
  | none => exact absurd rfl h
  | some a => exact ⟨a, rfl⟩

/-- The chosen value of an `Option` which is known not to be `none`. -/
noncomputable def optionOut {α : Type*} {o : Option α} (h : o ≠ none) : α :=
  Classical.choose (some_of_ne_none h)

lemma optionOut_spec {α : Type*} {o : Option α} (h : o ≠ none) : o = some (optionOut h) :=
  Classical.choose_spec (some_of_ne_none h)

/-- Reassemble a total colouring from a partial colouring `ψ` and a colouring
`ψ'` of the uncoloured part. -/
noncomputable def totalColouring {k : ℕ} (ψ : V → Option (Fin k))
    (ψ' : {u : V // ψ u = none} → Fin k) (u : V) : Fin k :=
  if h : ψ u = none then ψ' ⟨u, h⟩ else optionOut h

lemma totalColouring_of_none {k : ℕ} {ψ : V → Option (Fin k)}
    {ψ' : {u : V // ψ u = none} → Fin k} {u : V} (h : ψ u = none) :
    totalColouring ψ ψ' u = ψ' ⟨u, h⟩ := dif_pos h

lemma totalColouring_of_some {k : ℕ} {ψ : V → Option (Fin k)}
    {ψ' : {u : V // ψ u = none} → Fin k} {u : V} {c : Fin k} (h : ψ u = some c) :
    totalColouring ψ ψ' u = c := by
  have hne : ψ u ≠ none := by rw [h]; exact Option.some_ne_none c
  rw [totalColouring, dif_neg hne]
  have hspec := optionOut_spec hne
  have h2 : (some c : Option (Fin k)) = some (optionOut hne) := h ▸ hspec
  exact (Option.some.inj h2).symm

/-- The number of coloured neighbours of `u`. -/
noncomputable def colCount {α : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (ψ : V → Option α) (u : V) : ℕ :=
  ((G.neighborFinset u).filter (fun v => ψ v ≠ none)).card

/-- The number of distinct colours appearing on the neighbours of `u`. -/
noncomputable def distCount {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (ψ : V → Option (Fin k)) (u : V) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter
    (fun c => ∃ v ∈ G.neighborFinset u, ψ v = some c)).card

/-- **Extension of a partial colouring** (Bonamy-Perrett-Postle, Prop. 3.2).
If a partial proper `k`-colouring has, at every vertex `u`,
`Col(u) - Dist(u) ≥ d(u) + 1 - k` (written without subtraction as
`Dist(u) + d(u) < Col(u) + k`), then it extends to a `k`-colouring. -/
theorem colorable_of_partial {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (ψ : V → Option (Fin k)) (hψ : IsPartialColoringOption G ψ)
    (hgood : ∀ u, distCount G ψ u + G.degree u < colCount G ψ u + k) :
    G.Colorable k := by
  classical
  set U : Set V := {u | ψ u = none} with hU
  have hUts : U.toFinset = Finset.univ.filter (fun v => ψ v = none) := by
    ext v; simp [hU]
  let L : U → Finset (Fin k) := fun w =>
    (Finset.univ : Finset (Fin k)).filter
      (fun c => ¬ ∃ v ∈ G.neighborFinset (w : V), ψ v = some c)
  have hLdef : ∀ w : U, L w = (Finset.univ : Finset (Fin k)).filter
      (fun c => ¬ ∃ v ∈ G.neighborFinset (w : V), ψ v = some c) := fun w => rfl
  have hdeg : ∀ w : U, (G.induce U).degree w
      = ((G.neighborFinset (w : V)).filter (fun v => ψ v = none)).card := by
    intro w
    rw [SimpleGraph.degree,
      ← Finset.card_map (f := Function.Embedding.subtype (· ∈ U))
        (s := (G.induce U).neighborFinset w),
      SimpleGraph.map_neighborFinset_induce (G := G) (s := U) w, hUts]
    congr 1
    ext v
    simp
  have hgood' : ∀ w : U, (G.induce U).degree w < (L w).card := by
    intro w
    -- the two filters of the neighbourhood of `w`
    have hsum : ((G.neighborFinset (w : V)).filter (fun v => ψ v = none)).card
        + ((G.neighborFinset (w : V)).filter (fun v => ψ v ≠ none)).card
        = G.degree (w : V) := by
      show ((G.neighborFinset (w : V)).filter (fun v => ψ v = none)).card
          + ((G.neighborFinset (w : V)).filter (fun v => ψ v ≠ none)).card
          = (G.neighborFinset (w : V)).card
      exact Finset.card_filter_add_card_filter_not (s := G.neighborFinset (w : V))
        (p := fun v => ψ v = none)
    have hcol : ((G.neighborFinset (w : V)).filter (fun v => ψ v ≠ none)).card
        = colCount G ψ (w : V) := rfl
    have hb : ((G.neighborFinset (w : V)).filter (fun v => ψ v = none)).card
        = G.degree (w : V) - colCount G ψ (w : V) := by
      omega
    -- the number of distinct colours
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin k)))
      (p := fun c => ∃ v ∈ G.neighborFinset (w : V), ψ v = some c)
    have hdist : ((Finset.univ : Finset (Fin k)).filter
        (fun c => ∃ v ∈ G.neighborFinset (w : V), ψ v = some c)).card
        = distCount G ψ (w : V) := rfl
    have htot : (Finset.univ : Finset (Fin k)).card = k := Finset.card_fin k
    have hLcard : (L w).card = k - distCount G ψ (w : V) := by
      rw [hLdef w]
      omega
    have h1 : colCount G ψ (w : V) ≤ G.degree (w : V) := by
      rw [colCount, hcol] at *
      exact Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : distCount G ψ (w : V) ≤ k := by
      rw [distCount] at *
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (le_of_eq htot)
    rw [hdeg w, hLcard, hb]
    have h4 := hgood (w : V)
    omega
  obtain ⟨ψ', hψ'mem, hψ'prop⟩ := listColoring_of_degree_lt_card (G.induce U) L hgood'
  refine ⟨⟨totalColouring ψ ψ', ?_⟩⟩
  intro u v huv huv_eq
  by_cases hu : ψ u = none
  · by_cases hv : ψ v = none
    · have hUu : u ∈ U := by simpa [hU] using hu
      have hUv : v ∈ U := by simpa [hU] using hv
      have hadj : (G.induce U).Adj ⟨u, hUu⟩ ⟨v, hUv⟩ := huv
      have hne := hψ'prop _ _ hadj
      rw [totalColouring_of_none hu, totalColouring_of_none hv] at huv_eq
      exact absurd huv_eq hne
    · obtain ⟨c, hc⟩ := some_of_ne_none hv
      have hcv : ψ v = some c := hc
      have hUu : u ∈ U := by simpa [hU] using hu
      have hmem := hψ'mem ⟨u, hUu⟩
      rw [totalColouring_of_none hu] at huv_eq
      rw [totalColouring_of_some hcv] at huv_eq
      have hforb : ¬ ∃ w ∈ G.neighborFinset u, ψ w = some (ψ' ⟨u, hUu⟩) := by
        have hmem' := hmem
        rw [hLdef ⟨u, hUu⟩] at hmem'
        exact (Finset.mem_filter.mp hmem').2
      exact hforb ⟨v, (G.mem_neighborFinset (v := u) (w := v)).mpr huv,
        by rw [huv_eq]; exact hcv⟩
  · obtain ⟨c, hcu⟩ := some_of_ne_none hu
    by_cases hv : ψ v = none
    · have hUv : v ∈ U := by simpa [hU] using hv
      have hmem := hψ'mem ⟨v, hUv⟩
      rw [totalColouring_of_some hcu] at huv_eq
      rw [totalColouring_of_none hv] at huv_eq
      have hforb : ¬ ∃ w ∈ G.neighborFinset v, ψ w = some (ψ' ⟨v, hUv⟩) := by
        have hmem' := hmem
        rw [hLdef ⟨v, hUv⟩] at hmem'
        exact (Finset.mem_filter.mp hmem').2
      exact hforb ⟨u, (G.mem_neighborFinset (v := v) (w := u)).mpr huv.symm,
        by rw [← huv_eq]; exact hcu⟩
    · obtain ⟨c', hcv⟩ := some_of_ne_none hv
      rw [totalColouring_of_some hcu, totalColouring_of_some hcv] at huv_eq
      have hEq : ψ u = ψ v := by rw [hcu, hcv, huv_eq]
      have hnone := hψ u v huv hEq
      rw [hcu] at hnone
      exact Option.some_ne_none c hnone

end Extension


/-! ## The interface to the probabilistic core -/

/-- **The output of the naive colouring procedure**, as a hypothesis: a partial
proper `k`-colouring in which every vertex satisfies the extension condition
`Dist(u) + d(u) < Col(u) + k`.  This is exactly the statement the probabilistic
half of the proof of `SparseGraphStatement` has to produce (random colouring +
uncolouring + concentration + Lovász Local Lemma); `sparseGraphStatement_of_ncp`
turns it into `SparseGraphStatement` using the deterministic extension step. -/
def NCPCoreStatement : Prop :=
  ∃ c : ℝ, 1 / 100 ≤ c ∧ ∃ Δ₀ : ℝ → ℝ,
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 → 0 < Δ₀ δ) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ m : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → Δ₀ δ ≤ C / δ ^ m) ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ),
      Δ₀ δ ≤ Δ → (G.maxDegree : ℝ) ≤ Δ →
      (∀ v : V, (nbrEdges G v : ℝ) ≤ (1 - δ) * Δ ^ 2 / 2) →
      ∃ k : ℕ, (k : ℝ) ≤ (1 - c * δ) * (Δ + 1) ∧
        ∃ ψ : V → Option (Fin k), IsPartialColoringOption G ψ ∧
          ∀ u : V, distCount G ψ u + G.degree u < colCount G ψ u + k

/-- **Deterministic assembly.**  The output of the naive colouring procedure
implies the locally sparse colouring bound: the partial colouring is extended by
`colorable_of_partial`. -/
theorem sparseGraphStatement_of_ncp (h : NCPCoreStatement) : SparseGraphStatement := by
  obtain ⟨c, hc, Δ₀, hpos, hbdd, hmain⟩ := h
  exact ⟨c, hc, Δ₀, hpos, hbdd, fun δ hδ0 hδ1 V _ _ G _ Δ hthr hmax hsp => by
    obtain ⟨k, hk, ψ, hψ, hgood⟩ := hmain δ hδ0 hδ1 V G Δ hthr hmax hsp
    exact ⟨k, hk, colorable_of_partial G ψ hψ hgood⟩⟩

end

end ErdosFaberLovaszConjecture
