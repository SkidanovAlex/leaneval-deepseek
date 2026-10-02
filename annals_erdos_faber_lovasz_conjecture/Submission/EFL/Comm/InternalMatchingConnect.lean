import Submission.EFL.Comm.UpperRegularPerfectMatching
import Submission.EFL.InternalAbsorption
import Submission.EFL.ColourClassSplitting

/-!
# Discharging the perfect-matching input of §7.2

The §7.2 internal absorption `internal_absorption` is proved modulo the
hypothesis `InternalMatchingInput n B` (the paper's Proposition
`internal-matching-prop`).  This module discharges that hypothesis: it
transports the common

* a 2-edge family `R ⊆ P(W)` on a vertex set `W` is turned into a
  `SimpleGraph ↥W` (`graphOf`), with `degree` matching `degIn` and the upper
  regularity matching `edgeCount`;
* the perfect matching produced by the graph version
  (`upper_regular_exists_perfectMatching_general`, the ported commons lemma)
  is turned back into a matching family `Set R` covering `W`, using
  `Subgraph.isPerfectMatching_iff` (`∀ v, ∃! w, M.Adj v w`) to obtain an
  involution `f` of `W` whose orbits `{v, f v}` are the matched edges.

The main result is `internalMatchingInput : InternalMatchingInput n B` for
every `B`, whence `internal_absorption` no longer needs a hypothesis.
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-! ## The 2-graph of a 2-edge family on a vertex set -/

/-- The simple graph on the vertex set `W` whose edges are the members of the
2-edge family `R` lying in `W` (the hypothesis `edgeSize e = 2` makes the
adjacency irreflexive). -/
def graphOf (R : Hypergraph (Fin n)) (W : Set (Fin n)) (hR2 : ∀ e ∈ R, edgeSize e = 2) :
    SimpleGraph ↥W where
  Adj x y := ({x.1, y.1} : Set (Fin n)) ∈ R
  symm := ⟨fun x y h => by rw [Set.pair_comm]; exact h⟩
  loopless := ⟨fun x h => by
    have h2 : edgeSize ({x.1, x.1} : Set (Fin n)) = 2 := hR2 _ h
    have h3 : ({x.1, x.1} : Set (Fin n)) = {x.1} := by
      ext y
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [h3, edgeSize_eq_ncard] at h2
    simp at h2⟩

theorem graphOf_adj {R : Hypergraph (Fin n)} {W : Set (Fin n)}
    {hR2 : ∀ e ∈ R, edgeSize e = 2} {x y : ↥W} :
    (graphOf R W hR2).Adj x y ↔ ({x.1, y.1} : Set (Fin n)) ∈ R := Iff.rfl

/-- The degree in `graphOf` is the degree `degIn` inside `W`. -/
theorem graphOf_degree {R : Hypergraph (Fin n)} {W : Set (Fin n)}
    {hR2 : ∀ e ∈ R, edgeSize e = 2} (x : ↥W)
    [Fintype ((graphOf R W hR2).neighborSet x)] :
    (graphOf R W hR2).degree x = degIn R W x.1 := by
  rw [SimpleGraph.degree, degIn_eq_ncard, ← card_sfin]
  refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
  · intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    rw [mem_sfin]
    exact ⟨y.2, hy⟩
  · intro y₁ _ y₂ _ h
    exact Subtype.ext h
  · intro b hb
    rw [mem_sfin] at hb
    exact ⟨⟨b, hb.1⟩, by rw [SimpleGraph.mem_neighborFinset]; exact hb.2, rfl⟩

/-- `Fintype.card ↥W = W.ncard`. -/
theorem fintype_card_coe (W : Set (Fin n)) [Fintype ↥W] : Fintype.card ↥W = W.ncard := by
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

/-- The number of edges of `graphOf R W` between two finsets of `↥W` is the
`edgeCount` between their images. -/
theorem card_filter_adj_eq_edgeCount {R : Hypergraph (Fin n)} {W : Set (Fin n)}
    (hR2 : ∀ e ∈ R, edgeSize e = 2) (S T : Finset ↥W) :
    (((S.product T).filter (fun p => (graphOf R W hR2).Adj p.1 p.2)).card)
      = edgeCount R (S.image Subtype.val) (T.image Subtype.val) := by
  classical
  unfold edgeCount
  refine Finset.card_bij (fun p _ => (p.1.1, p.2.1)) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, mem_product_aux] at hp
    rw [Finset.mem_filter, mem_product_aux]
    exact ⟨⟨Finset.mem_image.mpr ⟨p.1, hp.1.1, rfl⟩,
      Finset.mem_image.mpr ⟨p.2, hp.1.2, rfl⟩⟩, hp.2⟩
  · intro p _ q _ h
    have h1 : p.1.1 = q.1.1 := congrArg Prod.fst h
    have h2 : p.2.1 = q.2.1 := congrArg Prod.snd h
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · intro q hq
    rw [Finset.mem_filter, mem_product_aux] at hq
    obtain ⟨a, ha, ha'⟩ := Finset.mem_image.mp hq.1.1
    obtain ⟨b, hb, hb'⟩ := Finset.mem_image.mp hq.1.2
    refine ⟨(a, b), ?_, ?_⟩
    · rw [Finset.mem_filter, mem_product_aux]
      refine ⟨⟨ha, hb⟩, ?_⟩
      change ({↑a, ↑b} : Set (Fin n)) ∈ R
      rw [ha', hb']
      exact hq.2
    · exact Prod.ext ha' hb'

/-- The upper-regularity of `R` transfers to `graphOf R W`. -/
theorem upperRegular_graphOf {R : Hypergraph (Fin n)} {W : Set (Fin n)} [Fintype ↥W]
    (hR2 : ∀ e ∈ R, edgeSize e = 2) {ρ ξ : ℝ}
    (hreg : ∀ S T : Finset (Fin n), S ⊆ sfin W → T ⊆ sfin W → Disjoint S T →
      ξ * (W.ncard : ℝ) ≤ (S.card : ℝ) → ξ * (W.ncard : ℝ) ≤ (T.card : ℝ) →
      (edgeCount R S T : ℝ) ≤ (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ)) :
    ∀ S T : Finset ↥W, Disjoint S T → ξ * (Fintype.card ↥W : ℝ) ≤ (S.card : ℝ) →
      ξ * (Fintype.card ↥W : ℝ) ≤ (T.card : ℝ) →
      (((S.product T).filter (fun p => (graphOf R W hR2).Adj p.1 p.2)).card : ℝ) ≤
        (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ) := by
  classical
  intro S T hdisj hS hT
  have himg : ∀ x : {S : Finset ↥W // True}, True := fun _ => trivial
  have hScard : (S.image Subtype.val).card = S.card :=
    Finset.card_image_of_injective _ (fun x y h => Subtype.ext h)
  have hTcard : (T.image Subtype.val).card = T.card :=
    Finset.card_image_of_injective _ (fun x y h => Subtype.ext h)
  have hSW : S.image Subtype.val ⊆ sfin W := by
    intro w hw
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hw
    rw [mem_sfin]; exact x.2
  have hTW : T.image Subtype.val ⊆ sfin W := by
    intro w hw
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hw
    rw [mem_sfin]; exact x.2
  have hdisj' : Disjoint (S.image Subtype.val) (T.image Subtype.val) := by
    rw [Finset.disjoint_left] at hdisj ⊢
    intro w hw hw'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨y, hy, hy'⟩ := Finset.mem_image.mp hw'
    have hyx : y = x := Subtype.ext hy'
    exact hdisj hx (hyx ▸ hy)
  have hS' : ξ * (W.ncard : ℝ) ≤ ((S.image Subtype.val).card : ℝ) := by
    rw [fintype_card_coe] at hS; rw [hScard]; exact hS
  have hT' : ξ * (W.ncard : ℝ) ≤ ((T.image Subtype.val).card : ℝ) := by
    rw [fintype_card_coe] at hT; rw [hTcard]; exact hT
  have hmain := hreg _ _ hSW hTW hdisj' hS' hT'
  rw [hScard, hTcard] at hmain
  rw [card_filter_adj_eq_edgeCount hR2 S T]
  exact hmain

/-- **The perfect matching of the graph version gives a matching covering
`W`** (the conclusion of the paper's Proposition `internal-matching-prop`). -/
theorem exists_matchingFamily_of_perfectMatching {R : Hypergraph (Fin n)} {W : Set (Fin n)}
    {hR2 : ∀ e ∈ R, edgeSize e = 2} {M : (graphOf R W hR2).Subgraph}
    (hM : M.IsPerfectMatching) :
    ∃ M' : Set R, IsMatchingFam M' ∧ CoversFam M' W := by
  classical
  have huniq : ∀ v : ↥W, ∃! w, M.Adj v w := (SimpleGraph.Subgraph.isPerfectMatching_iff).mp hM
  set f : ↥W → ↥W := fun v => Classical.choose (huniq v) with hfdef
  have hf1 : ∀ v, M.Adj v (f v) := fun v => (Classical.choose_spec (huniq v)).1
  have hf2 : ∀ v w, M.Adj v w → w = f v := fun v w h => (Classical.choose_spec (huniq v)).2 w h
  have hinv : ∀ v, f (f v) = v := fun v => (hf2 (f v) v (hf1 v).symm).symm
  have hedge : ∀ v : ↥W, ({v.1, (f v).1} : Set (Fin n)) ∈ R :=
    fun v => (hf1 v).adj_sub
  -- two orbits of the involution `f` that meet are equal
  have horbit : ∀ (e₁ e₂ : Set (Fin n)) (v₁ v₂ : ↥W),
      e₁ = ({v₁.1, (f v₁).1} : Set (Fin n)) → e₂ = ({v₂.1, (f v₂).1} : Set (Fin n)) →
      (e₁ ∩ e₂).Nonempty → e₁ = e₂ := by
    rintro e₁ e₂ v₁ v₂ rfl rfl ⟨x, hx1, hx2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx1 hx2
    have key : v₁ = v₂ ∨ v₁ = f v₂ := by
      rcases hx1 with h1 | h1 <;> rcases hx2 with h2 | h2
      · exact Or.inl (Subtype.ext (h1.symm.trans h2))
      · exact Or.inr (Subtype.ext (h1.symm.trans h2))
      · refine Or.inr ?_
        have h3 : f v₁ = v₂ := Subtype.ext (h1.symm.trans h2)
        rw [← hinv v₁, h3]
      · refine Or.inl ?_
        have h3 : f v₁ = f v₂ := Subtype.ext (h1.symm.trans h2)
        rw [← hinv v₁, ← hinv v₂, h3]
    rcases key with h | h
    · rw [h]
    · rw [h, hinv v₂, Set.pair_comm]
  set M' : Set R := {e | ∃ v : ↥W, (e : Set (Fin n)) = ({v.1, (f v).1} : Set (Fin n))}
    with hM'def
  refine ⟨M', ?_, ?_⟩
  · intro e₁ he₁ e₂ he₂ hne
    obtain ⟨v₁, hv₁⟩ := he₁
    obtain ⟨v₂, hv₂⟩ := he₂
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hne (Subtype.ext (horbit _ _ v₁ v₂ hv₁ hv₂ ⟨x, hx, hx'⟩))
  · intro w hw
    refine ⟨⟨({w, (f ⟨w, hw⟩).1} : Set (Fin n)), hedge ⟨w, hw⟩⟩, ⟨⟨w, hw⟩, rfl⟩, ?_⟩
    exact Set.mem_insert _ _

/-- **Proposition `internal-matching-prop`** (the §7.2 perfect-matching
input), discharged from the ported commons lemma. -/
theorem internalMatchingInput (n : ℕ) (B : ℕ) : InternalMatchingInput n B := by
  intro W R ρ ξ heven hρ hξ hξρ hρ1 hB hRW hR2 hdeg hreg
  haveI hW : Fintype ↥W := Fintype.ofFinite _
  haveI hAdj : DecidableRel (graphOf R W hR2).Adj := fun a b => Classical.propDecidable _
  haveI : DecidableRel (graphOf R W hR2).Adj := Classical.decRel _
  have hB' : (B : ℝ) ≤ ρ ^ 2 * (Fintype.card ↥W : ℝ) := by
    rw [fintype_card_coe]; exact hB
  have heven' : Even (Fintype.card ↥W) := by
    rw [fintype_card_coe]; exact heven
  have hdeg' : ∀ v : ↥W,
      3 * ρ * (Fintype.card ↥W : ℝ) / 4 ≤ ((graphOf R W hR2).degree v : ℝ) := by
    intro v
    rw [graphOf_degree (R := R) (W := W) (hR2 := hR2) v, fintype_card_coe]
    exact hdeg v.1 v.2
  have hreg' := upperRegular_graphOf hR2 hreg
  obtain ⟨M, hM⟩ :=
    Commons.Combinatorics.SimpleGraph.upper_regular_exists_perfectMatching_general
      (V := ↥W) (graphOf R W hR2) (B := B) (ρ := ρ) (ξ := ξ)
      hρ hξ hξρ hρ1 hB' heven' hdeg'
      (by
        intro S T hdisj hS hT
        have hh := hreg' S T hdisj hS hT
        convert hh using 2
        refine Finset.card_bij (fun a _ => a) ?_ ?_ ?_
        · intro a ha
          simpa only [Finset.mem_filter] using ha
        · exact fun _ _ _ _ h => h
        · intro b hb
          exact ⟨b, by simpa only [Finset.mem_filter] using hb, rfl⟩)
  exact exists_matchingFamily_of_perfectMatching hM

end

end ErdosFaberLovaszConjecture
