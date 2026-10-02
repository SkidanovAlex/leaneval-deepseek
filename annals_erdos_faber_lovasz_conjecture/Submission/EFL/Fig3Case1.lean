import Submission.EFL.Fig3Blocks
import Submission.Commons.Analysis.Real.reordering_threshold
import Submission.EFL.LargeEdgeCase1

/-!
# Theorem 6.1, Case 1: the good ordering produced by Figure 3

`exists_goodOrdering_of_app1_app2` takes the App-1 split of `𝓗' = 𝓗 ∖ 𝓗_huge`
(produced by one application of the Reordering Lemma, `reordering_split`) and
a *good* ordering of the remaining left part `𝓗₁^left` (the App-2 firing in
case (6.2:a) of the paper), and produces an ordering of `𝓗` in which every
edge has preceding degree at most `(1−2σ)n`.

The blocks are `𝓗_huge → 𝓗₁^left → 𝓗₁^good` and the degree bookkeeping is
the paper's (b)–(d):

* `𝓗_huge` is bounded by `|𝓗_huge| ≤ 32/β²` (`natCard_hugeEdges_le`);
* `𝓗₁^left` adds the huge edges meeting the edge (`≤ 32/β²`) on top of the
  App-2 bound `(1−3σ)n`;
* `𝓗₁^good` adds the huge edges and the edges of `𝓗₁^left` meeting it, both
  bounded by `γ₂n/3` (the App-1 bound and the initial-segment property),
  on top of its own `γ₂n/3`-bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- **Case 1 of Theorem 6.1, ordering form.**  Given the App-1 split of
`𝓗' = 𝓗 ∖ 𝓗_huge` into `Good ∪ Left` (with `Left` an initial segment of
`ord₁`, the bound `γ₂n/3` on `Good`, and the `(O2)` size information) and a
*good* ordering `ord₂` of `Left` with bound `(1−3σ)n`, the three blocks
`𝓗_huge → Left → Good` concatenate to an ordering of `𝓗` in which every edge
has preceding degree at most `(1−2σ)n`. -/
theorem exists_goodOrdering_of_app1_app2 {n r₁ : ℕ} {β γ₂ σ : ℝ} {𝓗 : Hypergraph (Fin n)}
    (hβ : 0 < β) (hγ₂0 : 0 < γ₂) (hσ0 : 0 < σ) (hσ3 : 3 * σ ≤ 1)
    (hr₁ : 2 ≤ r₁) (h2n : 2 ≤ n) (hβn : 8 ≤ β * (n : ℝ))
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ)) (hlin : 𝓗.IsLinear)
    (hA₁ : 32 / β ^ 2 ≤ σ * (n : ℝ))
    (hA₂ : 32 / β ^ 2 + 2 * γ₂ * (n : ℝ) / 3 ≤ (1 - 2 * σ) * (n : ℝ))
    {k₁ : ℕ} (ord₁ : (nonHuge 𝓗 β) ≃ Fin k₁)
    (Good Left : Hypergraph (Fin n))
    (hGsub : Good ⊆ nonHuge 𝓗 β) (hLsub : Left ⊆ nonHuge 𝓗 β)
    (hpart : Good ∪ Left = nonHuge 𝓗 β) (hdisj : Disjoint Good Left)
    (hdeg : ∀ e : nonHuge 𝓗 β, (e : Set (Fin n)) ∈ Good →
      (precedingDegree (nonHuge 𝓗 β) ord₁ e : ℝ) ≤ (γ₂ / 3) * (n : ℝ))
    (hseg : ∀ f u : nonHuge 𝓗 β, (f : Set (Fin n)) ∈ Left → (u : Set (Fin n)) ∈ Good →
      (ord₁ f : ℕ) ≤ (ord₁ u : ℕ))
    {k₂ : ℕ} (ord₂ : Left ≃ Fin k₂)
    (hdeg₂ : ∀ e : Left, (precedingDegree Left ord₂ e : ℝ) ≤ (1 - 3 * σ) * (n : ℝ)) :
    ∃ K : ℕ, ∃ ord : 𝓗 ≃ Fin K,
      ∀ e : 𝓗, (precedingDegree 𝓗 ord e : ℝ) ≤ (1 - 2 * σ) * (n : ℝ) := by
  classical
  set A : Hypergraph (Fin n) := 𝓗.hugeEdges β with hAdef
  have hn1 : 1 ≤ n := by omega
  -- the cover `𝓗 = A ∪ Left ∪ Good`
  have hcoverA : A ∪ nonHuge 𝓗 β = 𝓗 := by
    ext e; constructor
    · rintro (he | he)
      · exact ((mem_hugeEdges 𝓗 β e).mp he).1
      · exact (nonHuge_subset 𝓗 β) he
    · intro he
      by_cases h : β * (n : ℝ) / 4 ≤ (edgeSize e : ℝ)
      · exact Or.inl ((mem_hugeEdges 𝓗 β e).mpr ⟨he, h⟩)
      · exact Or.inr ⟨he, h⟩
  have hcover3 : A ∪ Left ∪ Good = 𝓗 := by
    have hLG : Left ∪ Good = nonHuge 𝓗 β := by rw [Set.union_comm]; exact hpart
    rw [Set.union_assoc, hLG, hcoverA]
  -- disjointness
  have hdisjAL : Disjoint A Left := by
    rw [Set.disjoint_left]
    intro e heA heL
    exact (hLsub heL).2 ((mem_hugeEdges 𝓗 β e).mp heA).2
  have hdisjAG : Disjoint A Good := by
    rw [Set.disjoint_left]
    intro e heA heG
    exact (hGsub heG).2 ((mem_hugeEdges 𝓗 β e).mp heA).2
  -- orderings
  haveI : Fintype ↥A := Fintype.ofFinite _
  obtain ⟨m, ordC, hordCrank, hordCdeg⟩ := exists_restricted_ordering (𝓖 := nonHuge 𝓗 β) ord₁ hGsub
  -- bounds
  have hAbr : ∀ e : A, (precedingDegree A (Fintype.equivFin ↥A) e : ℝ) ≤ (1 - 2 * σ) * (n : ℝ) := by
    intro e
    have h1 : precedingDegree A (Fintype.equivFin ↥A) e ≤ Nat.card A := by
      rw [precedingDegree]
      have hle : (precedingNeighbours A (Fintype.equivFin ↥A) e).card ≤
          (Finset.univ : Finset A).card := Finset.card_le_card (Finset.subset_univ _)
      rw [Finset.card_univ] at hle
      rw [Nat.card_eq_fintype_card]
      exact hle
    have h2 : (Nat.card A : ℝ) ≤ 32 / β ^ 2 := by
      rw [hAdef]
      exact natCard_hugeEdges_le hlin hβ hβn hn1
    have h3 : 32 / β ^ 2 ≤ (1 - 2 * σ) * (n : ℝ) := by nlinarith [hA₁, hσ3, hσ0]
    have h4 : ((precedingDegree A (Fintype.equivFin ↥A) e : ℕ) : ℝ) ≤ (Nat.card A : ℝ) := by
      exact_mod_cast h1
    linarith
  have hBbr : ∀ e : Left, ((Nat.card {f : A //
        ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} : ℝ)
      + (precedingDegree Left ord₂ e : ℝ)) ≤ (1 - 2 * σ) * (n : ℝ) := by
    intro e
    have h1 : Nat.card {f : A // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} ≤ Nat.card A :=
      Nat.card_le_card_of_injective (fun x => x.1) (fun a b hab => Subtype.ext hab)
    have h2 : (Nat.card A : ℝ) ≤ 32 / β ^ 2 := by
      rw [hAdef]
      exact natCard_hugeEdges_le hlin hβ hβn hn1
    have h3 := hdeg₂ e
    have h1' : ((Nat.card {f : A // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} : ℕ) : ℝ)
        ≤ (Nat.card A : ℝ) := by exact_mod_cast h1
    nlinarith [h1', h2, h3, hA₁, hσ0]
  have hCbr : ∀ e : Good, ((Nat.card {f : (A ∪ Left : Hypergraph (Fin n)) //
        ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} : ℝ)
      + (precedingDegree Good ordC e : ℝ)) ≤ (1 - 2 * σ) * (n : ℝ) := by
    intro e
    have hsplit := natCard_interFiber_le_add (𝓖₁ := A) (𝓖₂ := Left) (𝓖 := A ∪ Left)
      rfl hdisjAL (e : Set (Fin n))
    have hfibA : Nat.card {f : A // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty}
        ≤ Nat.card A :=
      Nat.card_le_card_of_injective (fun x => x.1) (fun a b hab => Subtype.ext hab)
    have hA2' : (Nat.card A : ℝ) ≤ 32 / β ^ 2 := by
      rw [hAdef]; exact natCard_hugeEdges_le hlin hβ hβn hn1
    -- the `Left`-fibre injects into the preceding neighbours of `e` in `𝓗'`
    have hfibL : Nat.card {f : Left // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty}
        ≤ precedingDegree (nonHuge 𝓗 β) ord₁ ⟨(e : Set (Fin n)), hGsub e.2⟩ := by
      rw [precedingDegree_eq_natCard]
      refine Nat.card_le_card_of_injective
        (fun f : {f : Left // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} =>
          (⟨⟨(f.1 : Set (Fin n)), hLsub f.1.2⟩, ?_, ?_, ?_⟩ :
            {f : nonHuge 𝓗 β // f ≠ ⟨(e : Set (Fin n)), hGsub e.2⟩ ∧
              ord₁ f ≤ ord₁ ⟨(e : Set (Fin n)), hGsub e.2⟩ ∧
              ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty})) ?_
      · -- distinctness
        intro hc
        have hEq : (f.1 : Set (Fin n)) = (e : Set (Fin n)) := Subtype.ext_iff.mp hc
        have hmem : (f.1 : Set (Fin n)) ∈ Good := by rw [hEq]; exact e.2
        exact (Set.disjoint_left.mp hdisj) hmem f.1.2
      · exact hseg _ _ f.1.2 e.2
      · exact f.2
      · intro a b hab
        have h2 : (a.1 : Set (Fin n)) = (b.1 : Set (Fin n)) :=
          congrArg (fun x : {f : nonHuge 𝓗 β // f ≠ ⟨(e : Set (Fin n)), hGsub e.2⟩ ∧
              ord₁ f ≤ ord₁ ⟨(e : Set (Fin n)), hGsub e.2⟩ ∧
              ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} => (x.1 : Set (Fin n))) hab
        exact Subtype.ext (Subtype.ext h2)
    have hdegE := hdeg ⟨(e : Set (Fin n)), hGsub e.2⟩ e.2
    have hordCe := hordCdeg ⟨(e : Set (Fin n)), e.2⟩
    -- numeric combination
    have hs := hsplit
    have h1' : ((Nat.card {f : A // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} : ℕ) : ℝ)
        ≤ (Nat.card A : ℝ) := by exact_mod_cast hfibA
    have h2' : ((Nat.card {f : Left // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} : ℕ) : ℝ)
        ≤ (γ₂ / 3) * (n : ℝ) := by
      have : ((Nat.card {f : Left // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} : ℕ) : ℝ)
          ≤ (precedingDegree (nonHuge 𝓗 β) ord₁ ⟨(e : Set (Fin n)), hGsub e.2⟩ : ℝ) := by
        exact_mod_cast hfibL
      linarith
    have h3' : ((precedingDegree Good ordC e : ℕ) : ℝ) ≤ (γ₂ / 3) * (n : ℝ) := by
      have hcast : ((precedingDegree Good ordC e : ℕ) : ℝ) ≤
          (precedingDegree (nonHuge 𝓗 β) ord₁ ⟨(e : Set (Fin n)), hGsub e.2⟩ : ℝ) := by
        exact_mod_cast hordCe
      linarith
    have hsum' : ((Nat.card {f : (A ∪ Left : Hypergraph (Fin n)) //
          ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} : ℕ) : ℝ) ≤
        (Nat.card A : ℝ) + (γ₂ / 3) * (n : ℝ) := by
      have : ((Nat.card {f : (A ∪ Left : Hypergraph (Fin n)) //
            ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} : ℕ) : ℝ) ≤
          ((Nat.card {f : A // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} : ℕ) : ℝ) +
          ((Nat.card {f : Left // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} : ℕ) : ℝ) := by
        exact_mod_cast hsplit
      linarith
    nlinarith [hsum', h3', hA2', hA₂, hγ₂0]
  obtain ⟨K, ord, hbound⟩ := exists_ordering_of_three_blocks hcover3 hdisjAL hdisjAG hdisj.symm
    (Fintype.equivFin ↥A) ord₂ ordC hAbr hBbr hCbr
  exact ⟨K, ord, hbound⟩

/-- **Case 1 of Theorem 6.1, in the `LargeEdgeNonExtremal` form.**  Combining
the Figure-3 ordering (`exists_goodOrdering_of_app1_app2`) with Case 1 of the
proof (`largeEdge_case1`, i.e. Propositions 6.9 + 6.10) yields the
non-extremal alternative. -/
theorem largeEdge_nonExtremal_of_app1_app2 {n r₁ r₀ : ℕ} {β γ₂ σ γ₁ : ℝ}
    {𝓗 : Hypergraph (Fin n)}
    (hβ : 0 < β) (hγ₂0 : 0 < γ₂) (hσ0 : 0 < σ) (hσ3 : 3 * σ ≤ 1) (hσ23 : σ ≤ 2 / 3)
    (hr₁ : 2 ≤ r₁) (h2n : 2 ≤ n) (hr₀ : 1 ≤ r₀) (hβn8 : 8 ≤ β * (n : ℝ))
    (hsize : ∀ e : 𝓗, r₁ < edgeSize (e : Set (Fin n)))
    (hsizeR : ∀ e : 𝓗, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ))
    (hlin : 𝓗.IsLinear) (hγ₁σ : γ₁ ≤ σ / 2)
    (hβn : (r₀ : ℝ) < β * (n : ℝ) / 4)
    (hA₁ : 32 / β ^ 2 ≤ σ * (n : ℝ))
    (hA₂ : 32 / β ^ 2 + 2 * γ₂ * (n : ℝ) / 3 ≤ (1 - 2 * σ) * (n : ℝ))
    {k₁ : ℕ} (ord₁ : (nonHuge 𝓗 β) ≃ Fin k₁)
    (Good Left : Hypergraph (Fin n))
    (hGsub : Good ⊆ nonHuge 𝓗 β) (hLsub : Left ⊆ nonHuge 𝓗 β)
    (hpart : Good ∪ Left = nonHuge 𝓗 β) (hdisj : Disjoint Good Left)
    (hdeg : ∀ e : nonHuge 𝓗 β, (e : Set (Fin n)) ∈ Good →
      (precedingDegree (nonHuge 𝓗 β) ord₁ e : ℝ) ≤ (γ₂ / 3) * (n : ℝ))
    (hseg : ∀ f u : nonHuge 𝓗 β, (f : Set (Fin n)) ∈ Left → (u : Set (Fin n)) ∈ Good →
      (ord₁ f : ℕ) ≤ (ord₁ u : ℕ))
    {k₂ : ℕ} (ord₂ : Left ≃ Fin k₂)
    (hdeg₂ : ∀ e : Left, (precedingDegree Left ord₂ e : ℝ) ≤ (1 - 3 * σ) * (n : ℝ))
    (hmargin : (2 : ℝ) * (n : ℝ) / ((β / 5) * (r₀ : ℝ)) < ((σ / 2) * (n : ℝ)) / 4)
    (hbig : ((bigFinset (β / 5) (𝓗.largeEdges r₀)).card : ℝ) < ((σ / 2) * (n : ℝ)) / 2)
    {φmed : (𝓗.medEdges r₁ r₀).Coloring (Fin n)} {Cmed : Finset (Fin n)}
    (hφmed : φmed.UsesColourSet Cmed) (hCmed : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ))
    (hmedb : ∀ c : Fin n, (φmed.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ))
    (hbudget : (Cmed.card : ℝ) + 1 ≤ (σ / 2) * (n : ℝ)) :
    LargeEdgeNonExtremal n σ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 := by
  classical
  obtain ⟨K, ord, hbound⟩ :=
    exists_goodOrdering_of_app1_app2 hβ hγ₂0 hσ0 hσ3 hr₁ h2n hβn8 hsizeR hlin hA₁ hA₂
      ord₁ Good Left hGsub hLsub hpart hdisj hdeg hseg ord₂ hdeg₂
  obtain ⟨m, ordL, -, hdegL⟩ :=
    exists_restricted_ordering (𝓖 := 𝓗) ord (𝓖' := 𝓗.largeEdges r₀) (largeEdges_subset 𝓗 r₀)
  refine largeEdge_case1 (n := n) (r₁ := r₁) (r₀ := r₀) (σ := σ) (γ₁ := γ₁) (β := β)
    hlin h2n hr₀ hσ0 hσ23 hsize hβ hγ₁σ hβn hmargin hbig (k := m) ordL ?_ hφmed hCmed hmedb
    hbudget
  intro e
  have h1 := hdegL e
  have h2 : (precedingDegree 𝓗 ord ⟨(e : Set (Fin n)), largeEdges_subset 𝓗 r₀ e.2⟩ : ℝ) ≤
      (1 - 2 * σ) * (n : ℝ) := hbound _
  have h3 : ((precedingDegree (𝓗.largeEdges r₀) ordL e : ℕ) : ℝ) ≤
      (precedingDegree 𝓗 ord ⟨(e : Set (Fin n)), largeEdges_subset 𝓗 r₀ e.2⟩ : ℝ) := by
    exact_mod_cast h1
  linarith

/-- **App 1 (Figure 3), with the numeric bounds specialised.**  The
Reordering Lemma applied to `𝓗' = 𝓗 ∖ 𝓗_huge` at `(τ₁, K₁) = (1−γ₂/3, K₁)`,
with the App-1 numeric bounds substituted: the good part has preceding
degree `≤ γ₂n/3`, the volume set `W` has volume `≥ γ₂^{20}`, and its edges
have size at most `γ₂^{-10}·r₂` (paper (W₁1)/(W₁2)). -/
theorem app1_split {n r₁ : ℕ} {β γ₂ : ℝ} {𝓗 : Hypergraph (Fin n)}
    (hβ : 0 < β) (hγ₂0 : 0 < γ₂) (hγ₂1 : γ₂ ≤ 1 / 2000) (hr₁ : 2 ≤ r₁) (h2n : 2 ≤ n)
    (hR₁ : 4 * (1 / (2 * γ₂)) ^ 20 ≤ (r₁ : ℝ)) (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ)) :
    ∃ (k : ℕ) (ord : (nonHuge 𝓗 β) ≃ Fin k) (Good Left : Hypergraph (Fin n)) (r₂ : ℕ)
      (W : Finset (nonHuge 𝓗 β)),
      Good ⊆ nonHuge 𝓗 β ∧ Left ⊆ nonHuge 𝓗 β ∧ Good ∪ Left = nonHuge 𝓗 β ∧
      Disjoint Good Left ∧
      (∀ e : nonHuge 𝓗 β, (e : Set (Fin n)) ∈ Good →
        (precedingDegree (nonHuge 𝓗 β) ord e : ℝ) ≤ (γ₂ / 3) * (n : ℝ)) ∧
      (∀ e : nonHuge 𝓗 β, (e : Set (Fin n)) ∈ Left → r₂ ≤ edgeSize (e : Set (Fin n))) ∧
      (∀ e : nonHuge 𝓗 β, e ∈ W → (e : Set (Fin n)) ∈ Left) ∧
      (W = ∅ → Left = ∅) ∧
      (W = ∅ ∨ γ₂ ^ 20 ≤ Hypergraph.volume (nonHuge 𝓗 β) W) ∧
      (∀ e : nonHuge 𝓗 β, e ∈ W →
        (edgeSize (e : Set (Fin n)) : ℝ) ≤ (1 / γ₂ ^ 10) * (r₂ : ℝ)) ∧
      (∀ f u : nonHuge 𝓗 β, (f : Set (Fin n)) ∈ Left → (u : Set (Fin n)) ∈ Good →
        (ord f : ℕ) ≤ (ord u : ℕ)) := by
  classical
  obtain ⟨k, ord, Good, Left, r₂, W, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ :=
    reordering_split (τ := app1tau γ₂) (K := app1K γ₂) (nonHuge_subset 𝓗 β) h2n hr₁
      (by simp only [app1tau]; linarith) (by simp only [app1tau]; linarith)
      (by simp only [app1K]; exact Nat.one_le_ceil_iff.mpr (by positivity))
      (app1_margins hγ₂0 hγ₂1 hR₁) hlin hsize
  refine ⟨k, ord, Good, Left, r₂, W, h1, h2, h3, h4, ?_, h6, h7, h8, ?_, ?_, h11⟩
  · intro e he
    have h5e := h5 e he
    have hEq : (1 - app1tau γ₂) * (n : ℝ) = (γ₂ / 3) * (n : ℝ) := by
      simp only [app1tau]; ring
    linarith [h5e]
  · rcases h9 with h | h
    · exact Or.inl h
    · exact Or.inr ((app1_volBound_ge hγ₂0 hγ₂1).trans h)
  · intro e heW
    have h10e := h10 e heW
    have hfac := app1_sizeFactor_le hγ₂0 hγ₂1
    have hr₂ : (0 : ℝ) ≤ (r₂ : ℝ) := Nat.cast_nonneg r₂
    nlinarith [h10e, hfac, hr₂]

/-- **App-2 margins.**  For `σ` small (`3σ ≤ 1/10000`) there is a threshold
`R` such that the Reordering Lemma margins at `(τ, K) = (3σ, 1)` hold for
every `r₁ ≥ R`.  This is the App-2 analogue of `app1_margins`; it is the
`σ ≪ 1` instance of the paper's hierarchy, proved from the elementary
inequalities in `Commons.Analysis.Real.reordering_threshold`. -/
theorem app2_margins {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : 3 * σ ≤ 1 / 10000) :
    ∃ R : ℕ, ∀ r₁ : ℕ, (R : ℝ) ≤ (r₁ : ℝ) → ReorderingMargins r₁ (3 * σ) 1 := by
  obtain ⟨R, hR⟩ := Commons.Analysis.Real.reordering_threshold (τ := 3 * σ)
    (by linarith) hσ1
  refine ⟨R, fun r₁ hr => ?_⟩
  have h := hR (r₁ : ℝ) hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [tauQuarter] using h.1
  · simpa using h.2.1
  · simpa [tauQuarter] using h.2.2.1
  · simpa using h.2.2.2.1
  · simpa using h.2.2.2.2.1
  · simpa [tauQuarter, sizeFactor] using h.2.2.2.2.2.1
  · simpa [tauQuarter, sizeFactor] using h.2.2.2.2.2.2

end

end ErdosFaberLovaszConjecture
