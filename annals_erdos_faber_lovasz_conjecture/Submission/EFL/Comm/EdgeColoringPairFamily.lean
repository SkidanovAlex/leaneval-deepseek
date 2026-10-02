import Submission.Commons.Combinatorics.SimpleGraph.vizing_two_max

set_option autoImplicit false

namespace Commons.Combinatorics.SimpleGraph

/-- A family `R` of two-element subsets of `Fin n` in which every vertex is in at most `D`
of the pairs, and in which at most two vertices lie in exactly `D` of the pairs, admits a
proper `D`-edge-colouring (pairs sharing a vertex get different colours). -/
theorem edgeColoring_of_pairFamily_two_max {n : ℕ} (R : Set (Set (Fin n)))
    (hR2 : ∀ f ∈ R, f.ncard = 2)
    (D : ℕ)
    (hD : ∀ v : Fin n, {w : Fin n | w ≠ v ∧ ({v, w} : Set (Fin n)) ∈ R}.ncard ≤ D)
    (hfew : {v : Fin n | {w : Fin n | w ≠ v ∧ ({v, w} : Set (Fin n)) ∈ R}.ncard = D}.ncard ≤ 2) :
    ∃ col : R → Fin D, ∀ f₁ f₂ : R, f₁ ≠ f₂ →
      ((f₁.1 : Set (Fin n)) ∩ f₂.1).Nonempty → col f₁ ≠ col f₂ := by
  classical
  -- The graph underlying the pair family.
  let G : SimpleGraph (Fin n) :=
    { Adj := fun a b => a ≠ b ∧ ({a, b} : Set (Fin n)) ∈ R
      symm := Std.Symm.mk (fun a b h => ⟨h.1.symm, by rw [Set.pair_comm]; exact h.2⟩)
      loopless := Std.Irrefl.mk (fun a h => h.1 rfl) }
  -- The neighbours of `v` are exactly the vertices `w` with `{v,w} ∈ R`.
  have hneigh : ∀ v : Fin n,
      G.neighborSet v = {w : Fin n | w ≠ v ∧ ({v, w} : Set (Fin n)) ∈ R} := by
    intro v
    ext w
    rw [SimpleGraph.mem_neighborSet]
    change (v ≠ w ∧ ({v, w} : Set (Fin n)) ∈ R) ↔
      (w ≠ v ∧ ({v, w} : Set (Fin n)) ∈ R)
    constructor
    · rintro ⟨hvw, hmem⟩
      exact ⟨hvw.symm, hmem⟩
    · rintro ⟨hwv, hmem⟩
      exact ⟨hwv.symm, hmem⟩
  -- Degrees of `G` are the cardinalities appearing in the hypotheses.
  have hdeg : ∀ v : Fin n,
      G.degree v = {w : Fin n | w ≠ v ∧ ({v, w} : Set (Fin n)) ∈ R}.ncard := by
    intro v
    rw [← natcard_neighborSet_eq_degree (G := G) v, Nat.card_coe_set_eq, hneigh v]
  have hD' : ∀ v : Fin n, G.degree v ≤ D := fun v => by rw [hdeg v]; exact hD v
  have hfew' : {v : Fin n | G.degree v = D}.ncard ≤ 2 := by
    have hset : {v : Fin n | G.degree v = D} =
        {v : Fin n | {w : Fin n | w ≠ v ∧ ({v, w} : Set (Fin n)) ∈ R}.ncard = D} := by
      ext v
      simp only [Set.mem_ofPred_eq]
      rw [hdeg v]
    rw [hset]
    exact hfew
  -- Vizing for graphs with at most two vertices of maximum degree.
  obtain ⟨C⟩ := vizing_two_max G D hD' hfew'
  -- Every pair of `R` corresponds to an edge of `G`.
  have htoEdge : ∀ f : R, ∃ e : G.edgeSet, (e : Set (Fin n)) = f.1 := by
    intro f
    obtain ⟨a, b, hab, hf⟩ := Set.ncard_eq_two.mp (hR2 f f.2)
    refine ⟨⟨s(a, b), ?_⟩, ?_⟩
    · rw [SimpleGraph.mem_edgeSet]
      change a ≠ b ∧ ({a, b} : Set (Fin n)) ∈ R
      exact ⟨hab, hf ▸ f.2⟩
    · rw [Sym2.coe_mk, hf]
  let e : R → G.edgeSet := fun f => Classical.choose (htoEdge f)
  have he : ∀ f : R, (e f : Set (Fin n)) = f.1 := fun f => Classical.choose_spec (htoEdge f)
  refine ⟨fun f => C (e f), ?_⟩
  intro f₁ f₂ hf12 hinn
  refine C.valid ?_
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, ?_⟩
  · intro h
    exact hf12 (Subtype.ext (by rw [← he f₁, ← he f₂, h]))
  · obtain ⟨v, hv⟩ := hinn
    have hv₁ : v ∈ (e f₁ : Set (Fin n)) := by rw [he f₁]; exact hv.1
    have hv₂ : v ∈ (e f₂ : Set (Fin n)) := by rw [he f₂]; exact hv.2
    exact ⟨v, hv₁, hv₂⟩


/-- **Vizing's theorem in the pair-family form**: a family `R` of two-element
subsets of `Fin n` in which every vertex lies in at most `D` of the pairs admits
a proper `(D+1)`-edge-colouring (pairs sharing a vertex get different colours). -/
theorem edgeColoring_of_pairFamily {n : ℕ} (R : Set (Set (Fin n)))
    (hR2 : ∀ f ∈ R, f.ncard = 2)
    (D : ℕ)
    (hD : ∀ v : Fin n, {w : Fin n | w ≠ v ∧ ({v, w} : Set (Fin n)) ∈ R}.ncard ≤ D) :
    ∃ col : R → Fin (D + 1), ∀ f₁ f₂ : R, f₁ ≠ f₂ →
      ((f₁.1 : Set (Fin n)) ∩ f₂.1).Nonempty → col f₁ ≠ col f₂ := by
  classical
  -- The graph underlying the pair family.
  let G : SimpleGraph (Fin n) :=
    { Adj := fun a b => a ≠ b ∧ ({a, b} : Set (Fin n)) ∈ R
      symm := Std.Symm.mk (fun a b h => ⟨h.1.symm, by rw [Set.pair_comm]; exact h.2⟩)
      loopless := Std.Irrefl.mk (fun a h => h.1 rfl) }
  -- The neighbours of `v` are exactly the vertices `w` with `{v,w} ∈ R`.
  have hneigh : ∀ v : Fin n,
      G.neighborSet v = {w : Fin n | w ≠ v ∧ ({v, w} : Set (Fin n)) ∈ R} := by
    intro v
    ext w
    rw [SimpleGraph.mem_neighborSet]
    change (v ≠ w ∧ ({v, w} : Set (Fin n)) ∈ R) ↔
      (w ≠ v ∧ ({v, w} : Set (Fin n)) ∈ R)
    constructor
    · rintro ⟨hvw, hmem⟩
      exact ⟨hvw.symm, hmem⟩
    · rintro ⟨hwv, hmem⟩
      exact ⟨hwv.symm, hmem⟩
  -- Degrees of `G` are the cardinalities appearing in the hypotheses.
  have hdeg : ∀ v : Fin n,
      G.degree v = {w : Fin n | w ≠ v ∧ ({v, w} : Set (Fin n)) ∈ R}.ncard := by
    intro v
    rw [← natcard_neighborSet_eq_degree (G := G) v, Nat.card_coe_set_eq, hneigh v]
  have hD' : ∀ v : Fin n, G.degree v ≤ D := fun v => by rw [hdeg v]; exact hD v
  have hmax : G.maxDegree ≤ D := G.maxDegree_le_of_forall_degree_le D hD'
  -- Vizing's theorem gives a proper edge colouring with `maxDegree + 1 ≤ D + 1` colours.
  obtain ⟨C⟩ := (vizing G).mono (by omega : G.maxDegree + 1 ≤ D + 1)
  -- Every pair of `R` corresponds to an edge of `G`.
  have htoEdge : ∀ f : R, ∃ e : G.edgeSet, (e : Set (Fin n)) = f.1 := by
    intro f
    obtain ⟨a, b, hab, hf⟩ := Set.ncard_eq_two.mp (hR2 f f.2)
    refine ⟨⟨s(a, b), ?_⟩, ?_⟩
    · rw [SimpleGraph.mem_edgeSet]
      change a ≠ b ∧ ({a, b} : Set (Fin n)) ∈ R
      exact ⟨hab, hf ▸ f.2⟩
    · rw [Sym2.coe_mk, hf]
  let e : R → G.edgeSet := fun f => Classical.choose (htoEdge f)
  have he : ∀ f : R, (e f : Set (Fin n)) = f.1 := fun f => Classical.choose_spec (htoEdge f)
  refine ⟨fun f => C (e f), ?_⟩
  intro f₁ f₂ hf12 hinn
  refine C.valid ?_
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, ?_⟩
  · intro h
    exact hf12 (Subtype.ext (by rw [← he f₁, ← he f₂, h]))
  · obtain ⟨v, hv⟩ := hinn
    have hv₁ : v ∈ (e f₁ : Set (Fin n)) := by rw [he f₁]; exact hv.1
    have hv₂ : v ∈ (e f₂ : Set (Fin n)) := by rw [he f₂]; exact hv.2
    exact ⟨v, hv₁, hv₂⟩

end Commons.Combinatorics.SimpleGraph
