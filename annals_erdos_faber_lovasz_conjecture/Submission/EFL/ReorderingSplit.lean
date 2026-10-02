import Submission.EFL.LargeEdgeCase1
import Submission.EFL.LargeEdgeSetup

/-!
# Splitting a hypergraph along one application of the Reordering Lemma

This module packages one application of the Reordering Lemma (Lemma 6.2) in
the shape needed by Figure 3 of the paper: for a subfamily `𝓖` of a linear
hypergraph `𝓗` whose edges all have size `≥ r₁`, at parameters `(τ, K)`, one
obtains

* an ordering `ord : 𝓖 ≃ Fin k`,
* a split `𝓖 = Good ⊔ Left` (the `𝓗ᵢ^good` / `𝓗ᵢ^left` of Figure 3), where
  * every edge of `Good` has preceding degree `≤ (1−τ)n` in `𝓖`, and
  * every edge of `Left` has size at least `r₂ := |e*|` (the distinguished
    edge `e*` of the volume alternative),
* a finset `W ⊆ Left` of edges whose volume is at least `volBound τ K`
  (vacuous — `W = ∅` — in the *good* case), each of size at most
  `sizeFactor τ K · r₂`.

In the good case (`W = ∅`) we have `Left = ∅` and `Good = 𝓖`; in the volume
case `Left` is the `⪯e*`-prefix of `ord` and `W` is the volume witness `W`
of the Reordering Lemma.

Figure 3 of the paper is three applications of `reordering_split`
(`app1_split` on `𝓗' = 𝓗 ∖ 𝓗_huge`, `app2_split` on the remaining left part,
and `app3_good` on the residual family), combined into one ordering of `𝓗`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- **One application of the Reordering Lemma, split into the Figure-3
shape.**  For a subfamily `𝓖 ⊆ 𝓗` of a linear hypergraph whose edges all
have size `≥ r₁` and the Reordering Lemma margins `ReorderingMargins r₁ τ K`,
there are an ordering `ord` of `𝓖`, a partition `𝓖 = Good ⊔ Left`, a
threshold `r₂` and a finset `W ⊆ Left` such that

* every edge of `Good` has `𝓖`-preceding degree at most `(1−τ)n`;
* every edge of `Left` has size at least `r₂`;
* either `W = ∅` (the good case, in which also `Left = ∅`), or
  `vol(W) ≥ volBound τ K`;
* every edge of `W` has size at most `sizeFactor τ K · r₂`. -/
theorem reordering_split {n r₁ : ℕ} (τ : ℝ) (K : ℕ) {𝓗 𝓖 : Hypergraph (Fin n)}
    (hsub : 𝓖 ⊆ 𝓗) (h2n : 2 ≤ n) (h2r₁ : 2 ≤ r₁) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hK : 1 ≤ K) (hmarg : ReorderingMargins r₁ τ K) (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ)) :
    ∃ (k : ℕ) (ord : 𝓖 ≃ Fin k) (Good Left : Hypergraph (Fin n)) (r₂ : ℕ)
      (W : Finset 𝓖),
      Good ⊆ 𝓖 ∧ Left ⊆ 𝓖 ∧ Good ∪ Left = 𝓖 ∧ Disjoint Good Left ∧
      (∀ e : 𝓖, (e : Set (Fin n)) ∈ Good →
        (precedingDegree 𝓖 ord e : ℝ) ≤ (1 - τ) * (n : ℝ)) ∧
      (∀ e : 𝓖, (e : Set (Fin n)) ∈ Left → r₂ ≤ edgeSize (e : Set (Fin n))) ∧
      (∀ e : 𝓖, e ∈ W → (e : Set (Fin n)) ∈ Left) ∧
      (W = ∅ → Left = ∅) ∧
      (W = ∅ ∨ volBound τ K ≤ Hypergraph.volume 𝓖 W) ∧
      (∀ e : 𝓖, e ∈ W →
        (edgeSize (e : Set (Fin n)) : ℝ) ≤ sizeFactor τ K * (r₂ : ℝ)) ∧
      (∀ f u : 𝓖, (f : Set (Fin n)) ∈ Left → (u : Set (Fin n)) ∈ Good →
        (ord f : ℕ) ≤ (ord u : ℕ)) ∧
      /- `r₂` is the size of a member of `W`, or `W = ∅` and `r₂ = r₁`
      (so that in all cases `r₂ ≥ r₁ ≥ 2`). -/
      ((W = ∅ ∧ r₂ = r₁) ∨ ∃ e : 𝓖, e ∈ W ∧ edgeSize (e : Set (Fin n)) = r₂) := by
  classical
  obtain ⟨k, ord, hgood | hvol⟩ :=
    reorderingLemma_of_subfamily (τ := τ) (K := K) hsub h2n h2r₁ hτ0 hτ1 hK hmarg hlin
      (fun e he => hsize ⟨e, he⟩)
  · -- good case: Good := 𝓖, Left := ∅, W := ∅
    refine ⟨k, ord, 𝓖, ∅, r₁, ∅, subset_rfl, Set.empty_subset _, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inl rfl, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
    · ext e; simp
    · exact disjoint_bot_right
    · intro e _; exact hgood e
    · intro e he; exact absurd he (Set.notMem_empty e)
    · intro e he; exact absurd he (Finset.notMem_empty e)
    · intro _; rfl
    · intro e he; exact absurd he (Finset.notMem_empty e)
    · intro f u hf _; exact absurd hf (Set.notMem_empty _)
  · -- volume case
    obtain ⟨eStar, W, hWle, hWmax, hWvol, hO1, hO2, heStarW⟩ := hvol
    let Good : Hypergraph (Fin n) :=
      {e : Set (Fin n) | ∃ he : e ∈ 𝓖, (ord eStar : ℕ) < (ord ⟨e, he⟩ : ℕ)}
    let Left : Hypergraph (Fin n) :=
      {e : Set (Fin n) | ∃ he : e ∈ 𝓖, (ord ⟨e, he⟩ : ℕ) ≤ (ord eStar : ℕ)}
    have hmemGood : ∀ {e : Set (Fin n)} (he : e ∈ 𝓖),
        e ∈ Good ↔ (ord eStar : ℕ) < (ord ⟨e, he⟩ : ℕ) := by
      intro e he
      constructor
      · rintro ⟨he', hlt⟩
        have hEq : (⟨e, he'⟩ : 𝓖) = ⟨e, he⟩ := Subtype.ext rfl
        rwa [hEq] at hlt
      · intro h; exact ⟨he, h⟩
    have hmemLeft : ∀ {e : Set (Fin n)} (he : e ∈ 𝓖),
        e ∈ Left ↔ (ord ⟨e, he⟩ : ℕ) ≤ (ord eStar : ℕ) := by
      intro e he
      constructor
      · rintro ⟨he', hlt⟩
        have hEq : (⟨e, he'⟩ : 𝓖) = ⟨e, he⟩ := Subtype.ext rfl
        rwa [hEq] at hlt
      · intro h; exact ⟨he, h⟩
    refine ⟨k, ord, Good, Left, edgeSize (eStar : Set (Fin n)), W, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inr hWvol, ?_, ?_, Or.inr ⟨eStar, heStarW, rfl⟩⟩
    · intro e he
      exact he.1
    · intro e he
      exact he.1
    · ext e; constructor
      · rintro (he | he)
        · exact he.1
        · exact he.1
      · intro he
        rcases lt_or_ge ((ord eStar : ℕ)) ((ord ⟨e, he⟩ : ℕ)) with h | h
        · exact Or.inl ((hmemGood he).mpr h)
        · exact Or.inr ((hmemLeft he).mpr h)
    · rw [Set.disjoint_left]
      intro e heG heL
      exact absurd heG.2 (not_lt.mpr heL.2)
    · intro e heGood
      have hlt := (hmemGood e.2).mp heGood
      exact hO1 e (le_of_lt hlt) (fun hc => by
        rw [hc] at hlt
        exact absurd hlt (lt_irrefl _))
    · intro e heLeft
      have h := hO2 (e := eStar) (f := e) ((hmemLeft e.2).mp heLeft) le_rfl
      exact_mod_cast h
    · intro e heW
      exact (hmemLeft e.2).mpr (hWle e heW)
    · intro hemp
      exact absurd (hemp ▸ heStarW) (Finset.notMem_empty eStar)
    · intro e heW
      exact hWmax (e₁ := e) (e₂ := eStar) heW heStarW
    · intro f u hfLeft huGood
      exact le_of_lt (lt_of_le_of_lt ((hmemLeft f.2).mp hfLeft) ((hmemGood u.2).mp huGood))

/-- **App 3 closed, in the disjoint-subfamilies form.**  If a subfamily `𝓖₃`
of a linear hypergraph (all edges of size `≥ r₁ ≥ 10⁸`) meets a second
subfamily `𝓖₂` disjountly, and `𝓖₂` carries a volume set `W₂` of volume
`≥ 1−δ³` while `δ ≤ volBound app3tau app3K`, then `𝓖₃` admits an ordering
with all preceding degrees at most `(1 − app3tau)n = n/2000`.

This is the App-3 closing argument of Figure 3 in the general form needed
when `𝓗₃ = (𝓗₁^left ∖ W₂) ∪ 𝓗_huge` (rather than a rank interval of `⪯₂`):
the volume alternative of the Reordering Lemma on `𝓖₃` would produce `W′`
with `vol(W′) ≥ δ`, which together with `vol(W₂) ≥ 1−δ³` contradicts
`vol(W₂) + vol(W′) ≤ 1` (the ambient images are disjoint). -/
theorem app3_good_of_disjoint {n r₁ : ℕ} {𝓗 𝓖₂ 𝓖₃ : Hypergraph (Fin n)}
    (hsub₂ : 𝓖₂ ⊆ 𝓗) (hsub₃ : 𝓖₃ ⊆ 𝓗) (hdisj : Disjoint 𝓖₂ 𝓖₃)
    (h2n : 2 ≤ n) (h2r₁ : 2 ≤ r₁) (hK : (1 : ℕ) ≤ app3K)
    (hR : (100000000 : ℝ) ≤ (r₁ : ℝ)) (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδV : δ ≤ volBound app3tau app3K)
    (W₂ : Finset 𝓖₂) (hvol₂ : (1 : ℝ) - δ ^ 3 ≤ Hypergraph.volume 𝓖₂ W₂) :
    ∃ k₃ : ℕ, ∃ ord₃ : 𝓖₃ ≃ Fin k₃, GoodOrdering app3tau ord₃ := by
  classical
  obtain ⟨k₃, ord₃, hgood | hvol⟩ :=
    app3_firing (𝓖 := 𝓖₃) hsub₃ h2n h2r₁ hK hR hlin (fun e he => hsize ⟨e, he⟩)
  · exact ⟨k₃, ord₃, hgood⟩
  · exfalso
    obtain ⟨W', hW'⟩ := volume_ge_delta_of_witness δ hδV hvol
    have himg : Disjoint (subfamilyImage hsub₂ W₂) (subfamilyImage hsub₃ W') :=
      subfamilyImage_disjoint_of_disjoint (subset_refl _) (subset_refl _) hdisj hsub₂ hsub₃ W₂ W'
    exact app3_volume_collapse hlin hsub₂ hsub₃ δ hδ0 hδ1 W₂ W' hvol₂ hW' himg



/-! ## Splitting neighbourhood counts across a disjoint cover -/

/-- The number of edges of a cover `𝓖 = 𝓖₁ ⊔ 𝓖₂` meeting a fixed vertex set
`e` is at most the sum of the corresponding counts in the two parts. -/
theorem natCard_interFiber_le_add {n : ℕ} {𝓖₁ 𝓖₂ 𝓖 : Hypergraph (Fin n)}
    (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (hdisj : Disjoint 𝓖₁ 𝓖₂) (e : Set (Fin n)) :
    Nat.card {f : 𝓖 // ((f : Set (Fin n)) ∩ e).Nonempty} ≤
      Nat.card {f : 𝓖₁ // ((f : Set (Fin n)) ∩ e).Nonempty} +
      Nat.card {f : 𝓖₂ // ((f : Set (Fin n)) ∩ e).Nonempty} := by
  classical
  let Φ : {f : 𝓖 // ((f : Set (Fin n)) ∩ e).Nonempty} →
      {f : 𝓖₁ // ((f : Set (Fin n)) ∩ e).Nonempty} ⊕
      {f : 𝓖₂ // ((f : Set (Fin n)) ∩ e).Nonempty} := fun f =>
    if h : (f.1 : Set (Fin n)) ∈ 𝓖₁ then
      Sum.inl ⟨⟨(f.1 : Set (Fin n)), h⟩, f.2⟩
    else
      Sum.inr ⟨⟨(f.1 : Set (Fin n)), by
          exact (Set.mem_union _ _ _).mp (hcover.symm ▸ f.1.2) |>.resolve_left h⟩, f.2⟩
  have hΦ : Function.Injective Φ := by
    intro a b hab
    simp only [Φ] at hab
    by_cases ha₁ : (a.1 : Set (Fin n)) ∈ 𝓖₁ <;> by_cases hb₁ : (b.1 : Set (Fin n)) ∈ 𝓖₁
    · simp only [dif_pos ha₁, dif_pos hb₁] at hab
      have hx := Sum.inl.inj hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : {f : 𝓖₁ // ((f : Set (Fin n)) ∩ e).Nonempty} => (x.1 : Set (Fin n))) hx))
    · simp only [dif_pos ha₁, dif_neg hb₁] at hab
      exact absurd hab (by simp)
    · simp only [dif_neg ha₁, dif_pos hb₁] at hab
      exact absurd hab (by simp)
    · simp only [dif_neg ha₁, dif_neg hb₁] at hab
      have hx := Sum.inr.inj hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : {f : 𝓖₂ // ((f : Set (Fin n)) ∩ e).Nonempty} => (x.1 : Set (Fin n))) hx))
  have h := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_sum] at h
  exact h

end

end ErdosFaberLovaszConjecture
