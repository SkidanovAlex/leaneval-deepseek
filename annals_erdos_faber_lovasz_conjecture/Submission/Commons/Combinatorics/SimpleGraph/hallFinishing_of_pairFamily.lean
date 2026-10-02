import Mathlib.Data.Set.Card
import Submission.Commons.Combinatorics.SimpleGraph.hall_based_finishing

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.Combinatorics.SimpleGraph

theorem hallFinishing_of_pairFamily {n : ℕ} (R : Set (Set (Fin n)))
    (hR2 : ∀ f ∈ R, f.ncard = 2)
    (C : Finset (Fin n)) (Cw : Fin n → Finset (Fin n)) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hC : 7 * δ * (n : ℝ) ≤ (C.card : ℝ))
    (hU : ∃ U : Finset (Fin n), (U.card : ℝ) ≤ δ * (n : ℝ) ∧
      ∀ e ∈ R, ∃ u ∈ e, u ∈ U)
    (hdeg : ∀ w : Fin n,
      {x : Fin n | x ≠ w ∧ ({w, x} : Set (Fin n)) ∈ R}.ncard ≤ C.card - (Cw w).card)
    (hCw : ∀ w : Fin n, ((Cw w).card : ℝ) ≤ δ * (n : ℝ))
    (hCcol : ∀ c ∈ C,
      (((Finset.univ : Finset (Fin n)).filter (fun w => c ∈ Cw w)).card : ℝ) ≤ δ * (n : ℝ)) :
    ∃ ψ : R → Fin n, (∀ e : R, ψ e ∈ C) ∧
      (∀ e₁ e₂ : R, e₁ ≠ e₂ → ((e₁.1 : Set (Fin n)) ∩ e₂.1).Nonempty → ψ e₁ ≠ ψ e₂) ∧
      (∀ e : R, ∀ v ∈ (e.1 : Set (Fin n)), ψ e ∉ Cw v) := by
  classical
  -- The graph underlying the pair family.
  let G : SimpleGraph (Fin n) :=
    { Adj := fun a b => a ≠ b ∧ ({a, b} : Set (Fin n)) ∈ R
      symm := Std.Symm.mk (fun a b h => ⟨h.1.symm, by rw [Set.pair_comm]; exact h.2⟩)
      loopless := Std.Irrefl.mk (fun a h => h.1 rfl) }
  haveI : DecidableRel G.Adj := Classical.decRel G.Adj
  -- Neighbours of `v` are exactly the partners `w` of `v` in `R`.
  have hneigh : ∀ v : Fin n,
      G.neighborSet v = {w : Fin n | w ≠ v ∧ ({v, w} : Set (Fin n)) ∈ R} := by
    intro v
    ext w
    rw [SimpleGraph.mem_neighborSet]
    change (v ≠ w ∧ ({v, w} : Set (Fin n)) ∈ R) ↔
      (w ≠ v ∧ ({v, w} : Set (Fin n)) ∈ R)
    exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩
  have hdeg_eq : ∀ v : Fin n,
      G.degree v = {w : Fin n | w ≠ v ∧ ({v, w} : Set (Fin n)) ∈ R}.ncard := by
    intro v
    rw [← SimpleGraph.card_neighborSet_eq_degree (G := G) v, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, hneigh v]
  -- Transfer the hypotheses to the graph.
  have hC' : 7 * δ * (Fintype.card (Fin n) : ℝ) ≤ (C.card : ℝ) := by simpa using hC
  have hU' : ∃ U : Finset (Fin n), (U.card : ℝ) ≤ δ * (Fintype.card (Fin n) : ℝ) ∧
      ∀ e ∈ G.edgeSet, ∃ u ∈ (e : Sym2 (Fin n)), u ∈ U := by
    obtain ⟨U, hUcard, hUcover⟩ := hU
    refine ⟨U, by simpa using hUcard, ?_⟩
    have key : ∀ e : Sym2 (Fin n), e ∈ G.edgeSet → ∃ u ∈ (e : Sym2 (Fin n)), u ∈ U := by
      intro e
      refine Sym2.inductionOn e ?_
      intro a b he
      rw [SimpleGraph.mem_edgeSet] at he
      change a ≠ b ∧ ({a, b} : Set (Fin n)) ∈ R at he
      obtain ⟨u, hue, huU⟩ := hUcover ({a, b} : Set (Fin n)) he.2
      exact ⟨u, by simpa [Sym2.mem_iff] using hue, huU⟩
    exact fun e he => key e he
  have hdeg' : ∀ w : Fin n, (G.degree w : ℝ) ≤ (C.card : ℝ) - ((Cw w).card : ℝ) := by
    intro w
    have h := hdeg w
    have hCwle : (Cw w).card ≤ C.card := by
      have h1 : ((Cw w).card : ℝ) ≤ δ * (n : ℝ) := hCw w
      have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have h2 : δ * (n : ℝ) ≤ 7 * δ * (n : ℝ) := by nlinarith [hδ0, hn]
      have : ((Cw w).card : ℝ) ≤ (C.card : ℝ) := by linarith
      exact_mod_cast this
    calc (G.degree w : ℝ) =
          ({x : Fin n | x ≠ w ∧ ({w, x} : Set (Fin n)) ∈ R}.ncard : ℝ) := by rw [hdeg_eq w]
      _ ≤ ((C.card - (Cw w).card : ℕ) : ℝ) := by exact_mod_cast h
      _ ≤ (C.card : ℝ) - ((Cw w).card : ℝ) := by rw [Nat.cast_sub hCwle]
  have hCw' : ∀ w : Fin n, ((Cw w).card : ℝ) ≤ δ * (Fintype.card (Fin n) : ℝ) := by
    intro w; simpa using hCw w
  have hCcol' : ∀ c ∈ C,
      (((Finset.univ : Finset (Fin n)).filter (fun w => c ∈ Cw w)).card : ℝ) ≤
        δ * (Fintype.card (Fin n) : ℝ) := by
    intro c hc; simpa using hCcol c hc
  obtain ⟨φ, hφ1, hφ2, hφ3⟩ :=
    hall_based_finishing G C Cw δ hδ0 hδ1 hC' hU' hdeg' hCw' hCcol'
  -- Every pair of `R` corresponds to an edge of `G`.
  have htoEdge : ∀ f : R, ∃ e : G.edgeSet, ((e : Sym2 (Fin n)) : Set (Fin n)) = f.1 := by
    intro f
    obtain ⟨a, b, hab, hf⟩ := Set.ncard_eq_two.mp (hR2 f f.2)
    refine ⟨⟨s(a, b), ?_⟩, ?_⟩
    · rw [SimpleGraph.mem_edgeSet]
      change a ≠ b ∧ ({a, b} : Set (Fin n)) ∈ R
      exact ⟨hab, hf ▸ f.2⟩
    · rw [Sym2.coe_mk, hf]
  let ef : R → G.edgeSet := fun f => Classical.choose (htoEdge f)
  have hef : ∀ f : R, ((ef f : Sym2 (Fin n)) : Set (Fin n)) = f.1 :=
    fun f => Classical.choose_spec (htoEdge f)
  refine ⟨fun f => φ (ef f), ?_, ?_, ?_⟩
  · intro f
    exact hφ1 (ef f)
  · intro f₁ f₂ hf12 hinn
    refine hφ2 (ef f₁) (ef f₂) ?_ ?_
    · intro h
      exact hf12 (Subtype.ext (by rw [← hef f₁, ← hef f₂, h]))
    · obtain ⟨v, hv⟩ := hinn
      rw [Set.mem_inter_iff] at hv
      refine ⟨v, ?_, ?_⟩
      · change v ∈ ((ef f₁ : Sym2 (Fin n)) : Set (Fin n)); rw [hef f₁]; exact hv.1
      · change v ∈ ((ef f₂ : Sym2 (Fin n)) : Set (Fin n)); rw [hef f₂]; exact hv.2
  · intro f v hv
    refine hφ3 (ef f) v ?_
    change v ∈ ((ef f : Sym2 (Fin n)) : Set (Fin n)); rw [hef f]; exact hv

end Commons.Combinatorics.SimpleGraph