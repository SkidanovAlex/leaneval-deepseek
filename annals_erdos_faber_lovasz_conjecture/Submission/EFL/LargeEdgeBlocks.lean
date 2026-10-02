import Submission.EFL.Fig3Case1
import Submission.EFL.StabilityLoop

/-!
# The block decomposition of Figure 3 (Theorem 6.1 of the paper)

This module fires the first two applications of the Reordering Lemma in the
proof of Theorem 6.1 (`large-edge-thm`) and packages the resulting blocks.

* **App 1** is applied to `𝓗' = 𝓗 ∖ 𝓗_huge` at `(τ₁, K₁) = (1 − γ₂/3, K₁)`
  (`reordering_split`): it splits `𝓗' = 𝓗₁^good ⊔ 𝓗₁^left` and produces a
  threshold `r₂` with `|e| ≥ r₂` on `𝓗₁^left`.
* **App 2** is applied to `𝓗₁^left` at `(3σ, 1)`: it splits
  `𝓗₁^left = 𝓗₂^good ⊔ 𝓗₂^left` and produces the volume set `W₂ ⊆ 𝓗₂^left`
  (with threshold `r₃`).
* The residual family is `𝓗₃ = 𝓗_huge ∪ (𝓗₂^left ∖ W₂)`, so that
  `𝓗 = 𝓗₃ ⊔ W₂ ⊔ 𝓗₂^good ⊔ 𝓗₁^good` — the partition
  `eq:large-edge-thm-partition` of the paper (in the shape needed for the
  colouring arguments, where `W₂` is an explicit block rather than an
  initial segment of `⪯₂`).

The predicate `BlocksOK` records all the data and the properties that the two
cases of the proof consume; `exists_largeEdgeBlocks` is the firing theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- An edge is not both *huge* and *non-huge*. -/
theorem disjoint_hugeEdges_nonHuge (𝓗 : Hypergraph (Fin n)) (β : ℝ) :
    Disjoint (𝓗.hugeEdges β) (nonHuge 𝓗 β) := by
  rw [Set.disjoint_left]
  intro e h1 h2
  exact h2.2 h1.2

/-- The `finFam` of a non-empty finset is non-empty. -/
theorem finFam_nonempty {𝓗 : Hypergraph (Fin n)} {S : Finset 𝓗} (h : S.Nonempty) :
    (finFam S).Nonempty := by
  obtain ⟨e, he⟩ := h
  exact ⟨(e : Set (Fin n)), mem_finFam.mpr ⟨e.2, he⟩⟩

/-- The `finFam` of the empty finset is empty. -/
theorem finFam_empty {𝓗 : Hypergraph (Fin n)} : finFam (𝓗 := 𝓗) ∅ = ∅ := by
  ext e
  simp [mem_finFam]

/-- **The properties of the App-1/App-2 block decomposition of Figure 3**
(see the module docstring). -/
structure BlocksOK (n : ℕ) (𝓗 : Hypergraph (Fin n)) (β γ₂ σ δ : ℝ)
    (Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n))
    (k₁ : ℕ) (ord₁ : nonHuge 𝓗 β ≃ Fin k₁) (k₂ : ℕ) (ord₂ : Left₁ ≃ Fin k₂)
    (r₂ r₃ : ℕ) : Prop where
  hG₁sub : Good₁ ⊆ nonHuge 𝓗 β
  hL₁sub : Left₁ ⊆ nonHuge 𝓗 β
  hpart₁ : Good₁ ∪ Left₁ = nonHuge 𝓗 β
  hdisj₁ : Disjoint Good₁ Left₁
  /-- (a): every edge of `𝓗₁^good` has `𝓗'`-forward degree `≤ γ₂n/3`. -/
  hdeg₁ : ∀ e : nonHuge 𝓗 β, (e : Set (Fin n)) ∈ Good₁ →
    (precedingDegree (nonHuge 𝓗 β) ord₁ e : ℝ) ≤ (γ₂ / 3) * (n : ℝ)
  /-- the initial-segment property of `𝓗₁^left`. -/
  hseg₁ : ∀ f u : nonHuge 𝓗 β, (f : Set (Fin n)) ∈ Left₁ → (u : Set (Fin n)) ∈ Good₁ →
    (ord₁ f : ℕ) ≤ (ord₁ u : ℕ)
  /-- (d2): every edge of `𝓗₁^left` has size `≥ r₂`. -/
  hsize₁ : ∀ e : nonHuge 𝓗 β, (e : Set (Fin n)) ∈ Left₁ → r₂ ≤ edgeSize (e : Set (Fin n))
  /-- the App-1 threshold is an edge size (or `r₁`), hence at least `r₁`. -/
  hr₂ : 2 ≤ r₂
  hG₂sub : Good₂ ⊆ Left₁
  hL₂sub : Left₂ ⊆ Left₁
  hpart₂ : Good₂ ∪ Left₂ = Left₁
  hdisj₂ : Disjoint Good₂ Left₂
  /-- (b): every edge of `𝓗₂^good` has `𝓗₁^left`-forward degree `≤ (1−3σ)n`. -/
  hdeg₂ : ∀ e : Left₁, (e : Set (Fin n)) ∈ Good₂ →
    (precedingDegree Left₁ ord₂ e : ℝ) ≤ (1 - 3 * σ) * (n : ℝ)
  /-- the initial-segment property of `𝓗₂^left` inside `𝓗₁^left`. -/
  hseg₂ : ∀ f u : Left₁, (f : Set (Fin n)) ∈ Left₂ → (u : Set (Fin n)) ∈ Good₂ →
    (ord₂ f : ℕ) ≤ (ord₂ u : ℕ)
  /-- (d3): every edge of `𝓗₂^left` has size `≥ r₃`. -/
  hsize₂ : ∀ e : Left₁, (e : Set (Fin n)) ∈ Left₂ → r₃ ≤ edgeSize (e : Set (Fin n))
  /-- the App-2 threshold is an edge size (or `r₁`), hence at least `r₁`. -/
  hr₃ : 2 ≤ r₃
  /-- in the volume case, `r₃` is the size of a member of `W₂`. -/
  hW₂thr : W₂ = ∅ ∨ ∃ e : Set (Fin n), e ∈ W₂ ∧ edgeSize e = r₃
  hW₂sub : W₂ ⊆ Left₂
  hW₂size : ∀ e : Set (Fin n), e ∈ W₂ → r₃ ≤ edgeSize e
  /-- (W₂1): every edge of `W₂` has size at most `sizeFactor (3σ) 1 · r₃`. -/
  hW₂size_le : ∀ e : Set (Fin n), e ∈ W₂ →
    (edgeSize e : ℝ) ≤ sizeFactor (3 * σ) 1 * (r₃ : ℝ)
  /-- in the good case (`W₂ = ∅`) the App-2 firing has `𝓗₂^left = ∅`. -/
  hW₂empty : W₂ = ∅ → Left₂ = ∅
  /-- (W₂2): either the good case, or `vol(W₂) ≥ 1 − δ³`. -/
  hW₂vol : W₂ = ∅ ∨ (1 : ℝ) - δ ^ 3 ≤ volume n W₂
  hH₃sub : H₃ ⊆ 𝓗
  hH₃huge : 𝓗.hugeEdges β ⊆ H₃
  /-- `𝓗₂^left ∖ W₂ ⊆ 𝓗₃`. -/
  hH₃mem : ∀ e : Set (Fin n), e ∈ Left₂ → e ∉ W₂ → e ∈ H₃
  hH₃W₂disj : Disjoint H₃ W₂
  /-- `eq:large-edge-thm-partition`: `𝓗 = 𝓗₃ ⊔ W₂ ⊔ 𝓗₂^good ⊔ 𝓗₁^good`. -/
  hcover : H₃ ∪ W₂ ∪ Good₂ ∪ Good₁ = 𝓗
  hdisjH₃G₂ : Disjoint H₃ Good₂
  hdisjH₃G₁ : Disjoint H₃ Good₁
  hdisjW₂G₂ : Disjoint W₂ Good₂
  hdisjW₂G₁ : Disjoint W₂ Good₁
  hdisjG₂G₁ : Disjoint Good₂ Good₁
  /-- the App-1 volume set `W₁` (a `Finset` of `𝓗' = 𝓗 ∖ 𝓗_huge`) and its
  properties: `W₁ ⊆ 𝓗₁^left`, the good case empties `𝓗₁^left`, `(W₁-volume)`,
  `(W₁-max-size)`, and `r₂` is attained on `W₁` unless `W₁ = ∅`. -/
  hasW₁ : ∃ W₁ : Finset (nonHuge 𝓗 β),
    (∀ e : nonHuge 𝓗 β, e ∈ W₁ → (e : Set (Fin n)) ∈ Left₁) ∧
    (W₁ = ∅ → Left₁ = ∅) ∧
    (W₁ = ∅ ∨ volBound (app1tau γ₂) (app1K γ₂) ≤ Hypergraph.volume (nonHuge 𝓗 β) W₁) ∧
    (∀ e : nonHuge 𝓗 β, e ∈ W₁ →
      (edgeSize (e : Set (Fin n)) : ℝ) ≤ sizeFactor (app1tau γ₂) (app1K γ₂) * (r₂ : ℝ)) ∧
    (W₁ ≠ ∅ → ∃ e : nonHuge 𝓗 β, e ∈ W₁ ∧ edgeSize (e : Set (Fin n)) = r₂)

/-- **Firing App 1 and App 2** produces the `BlocksOK` decomposition. -/
theorem exists_largeEdgeBlocks
    {n r₁ : ℕ} {β γ₂ σ δ : ℝ} {𝓗 : Hypergraph (Fin n)}
    (hβ : 0 < β) (hγ₂0 : 0 < γ₂) (hγ₂1 : γ₂ ≤ 1 / 2000)
    (hσ0 : 0 < σ) (hσ1 : 3 * σ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h2n : 2 ≤ n) (hr₁ : 2 ≤ r₁)
    (hmarg₁ : ReorderingMargins r₁ (app1tau γ₂) (app1K γ₂))
    (hmarg₂ : ReorderingMargins r₁ (3 * σ) 1)
    (hV₂ : (1 : ℝ) - δ ^ 3 ≤ volBound (3 * σ) 1)
    (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ)) :
    ∃ (Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n))
      (k₁ : ℕ) (ord₁ : nonHuge 𝓗 β ≃ Fin k₁) (k₂ : ℕ) (ord₂ : Left₁ ≃ Fin k₂)
      (r₂ r₃ : ℕ),
      BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃ := by
  classical
  have hτ₁0 : 0 < app1tau γ₂ := by simp only [app1tau]; linarith
  have hτ₁1 : app1tau γ₂ < 1 := by simp only [app1tau]; linarith
  have hK₁ : 1 ≤ app1K γ₂ := by
    simp only [app1K]; exact Nat.one_le_ceil_iff.mpr (by positivity)
  obtain ⟨k₁, ord₁, Good₁, Left₁, r₂, W₁, hG₁sub, hL₁sub, hpart₁, hdisj₁, hdeg₁, hsize₁,
    hW₁subL, hW₁empL, hW₁volL, hW₁sizL, hseg₁, hthr₁⟩ :=
    reordering_split (τ := app1tau γ₂) (K := app1K γ₂) (𝓗 := 𝓗) (𝓖 := nonHuge 𝓗 β)
      (nonHuge_subset 𝓗 β) h2n hr₁ hτ₁0 hτ₁1 hK₁ hmarg₁ hlin hsize
  have hL₁𝓗 : Left₁ ⊆ 𝓗 := fun e he => nonHuge_subset 𝓗 β (hL₁sub he)
  obtain ⟨k₂, ord₂, Good₂, Left₂, r₃, W₂f, hG₂sub, hL₂sub, hpart₂, hdisj₂, hdeg₂, hsize₂,
    hW₂subf, hW₂ef, hW₂volf, hW₂sizef, hseg₂, hthr₂⟩ :=
    reordering_split (τ := 3 * σ) (K := 1) (𝓗 := 𝓗) (𝓖 := Left₁) hL₁𝓗 h2n hr₁
      (by linarith) hσ1
      le_rfl hmarg₂ hlin hsize
  have hdeg₁' : ∀ e : nonHuge 𝓗 β, (e : Set (Fin n)) ∈ Good₁ →
      (precedingDegree (nonHuge 𝓗 β) ord₁ e : ℝ) ≤ (γ₂ / 3) * (n : ℝ) := by
    intro e he
    have h := hdeg₁ e he
    rw [show (1 : ℝ) - app1tau γ₂ = γ₂ / 3 by simp only [app1tau]; ring] at h
    exact h
  -- the subfamily of `W₂`
  set W₂ : Hypergraph (Fin n) := finFam (𝓗 := Left₁) W₂f with hW₂def
  have hW₂sub : W₂ ⊆ Left₂ := by
    intro e he
    obtain ⟨hL₁e, hmem⟩ := mem_finFam.mp he
    exact hW₂subf ⟨e, hL₁e⟩ hmem
  have hW₂empty : W₂ = ∅ → Left₂ = ∅ := by
    intro hemp
    refine hW₂ef ?_
    by_contra hne'
    obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne'
    have hmem : (e : Set (Fin n)) ∈ W₂ := mem_finFam.mpr ⟨e.2, he⟩
    rw [hemp] at hmem
    exact hmem
  have hW₂vol : W₂ = ∅ ∨ (1 : ℝ) - δ ^ 3 ≤ volume n W₂ := by
    rcases hW₂volf with h | h
    · exact Or.inl (by rw [hW₂def, h, finFam_empty])
    · refine Or.inr (hV₂.trans ?_)
      rw [hW₂def, ← volume_finFam W₂f]
      exact h
  have hW₂size : ∀ e : Set (Fin n), e ∈ W₂ → r₃ ≤ edgeSize e := by
    intro e he
    have hsub := hW₂sub he
    exact hsize₂ ⟨e, hL₂sub hsub⟩ hsub
  have hW₂size_le : ∀ e : Set (Fin n), e ∈ W₂ →
      (edgeSize e : ℝ) ≤ sizeFactor (3 * σ) 1 * (r₃ : ℝ) := by
    intro e he
    obtain ⟨hL₁e, hmem⟩ := mem_finFam.mp he
    exact hW₂sizef ⟨e, hL₁e⟩ hmem
  -- `r₃` is an edge size, hence at least `r₁ ≥ 2`
  have hr₃ : 2 ≤ r₃ := by
    rcases hthr₂ with ⟨-, hr⟩ | ⟨e, he, heq⟩
    · rw [hr]; exact hr₁
    · have hsub := hW₂sub (mem_finFam.mpr ⟨e.2, he⟩)
      have hsizee : (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) :=
        hsize ⟨(e : Set (Fin n)), hL₁𝓗 (hL₂sub hsub)⟩
      rw [← heq]
      have h2 : (2 : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) := by
        have : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₁
        linarith
      exact_mod_cast h2
  have hW₂thr : W₂ = ∅ ∨ ∃ e : Set (Fin n), e ∈ W₂ ∧ edgeSize e = r₃ := by
    rcases hthr₂ with ⟨hemp, hr⟩ | ⟨e, he, heq⟩
    · refine Or.inl ?_
      rw [hW₂def, hemp]
      exact finFam_empty
    · exact Or.inr ⟨(e : Set (Fin n)), mem_finFam.mpr ⟨e.2, he⟩, heq⟩
  -- `r₂` is an edge size, hence at least `r₁ ≥ 2`
  have hr₂ : 2 ≤ r₂ := by
    rcases hthr₁ with ⟨-, hr⟩ | ⟨e, he, heq⟩
    · rw [hr]; exact hr₁
    · have hsub : (e : Set (Fin n)) ∈ Left₁ := hW₁subL e he
      have hsizee : (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) :=
        hsize ⟨(e : Set (Fin n)), hL₁𝓗 hsub⟩
      rw [← heq]
      have h2 : (2 : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) := by
        have : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₁
        linarith
      exact_mod_cast h2
  -- the residual family `𝓗₃`
  set H₃ : Hypergraph (Fin n) := 𝓗.hugeEdges β ∪ (Left₂ \ W₂) with hH₃def
  have hL₂𝓗 : Left₂ ⊆ 𝓗 := fun e he => hL₁𝓗 (hL₂sub he)
  have hH₃sub : H₃ ⊆ 𝓗 := by
    rintro e (he | he)
    · exact (mem_hugeEdges 𝓗 β e).mp he |>.1
    · exact hL₂𝓗 he.1
  have hH₃huge : 𝓗.hugeEdges β ⊆ H₃ := fun e he => Or.inl he
  have hH₃mem : ∀ e : Set (Fin n), e ∈ Left₂ → e ∉ W₂ → e ∈ H₃ := by
    intro e he1 he2
    exact Or.inr ⟨he1, he2⟩
  have hH₃W₂disj : Disjoint H₃ W₂ := by
    rw [Set.disjoint_left]
    intro e he heW
    rcases he with he | he
    · have hL₂ := hW₂sub heW
      exact (disjoint_hugeEdges_nonHuge 𝓗 β).le_bot ⟨he, hL₁sub (hL₂sub hL₂)⟩
    · exact he.2 heW
  have hcover : H₃ ∪ W₂ ∪ Good₂ ∪ Good₁ = 𝓗 := by
    ext e
    constructor
    · intro he
      rw [Set.mem_union] at he
      rcases he with he | hG₁
      · rw [Set.mem_union] at he
        rcases he with he | hG₂
        · rw [Set.mem_union] at he
          rcases he with h3 | hW
          · exact hH₃sub h3
          · exact hL₂𝓗 (hW₂sub hW)
        · exact hL₁𝓗 (hG₂sub hG₂)
      · exact nonHuge_subset 𝓗 β (hG₁sub hG₁)
    · intro he
      by_cases hh : β * (n : ℝ) / 4 ≤ (edgeSize e : ℝ)
      · have hmem : e ∈ H₃ := hH₃huge ((mem_hugeEdges 𝓗 β e).mpr ⟨he, hh⟩)
        rw [Set.mem_union]
        left; left; left
        exact hmem
      · have hnh : e ∈ nonHuge 𝓗 β := ⟨he, hh⟩
        rw [← hpart₁] at hnh
        rw [Set.mem_union] at hnh
        rcases hnh with hg | hl
        · rw [Set.mem_union]
          right
          exact hg
        · rw [← hpart₂] at hl
          rw [Set.mem_union] at hl
          rcases hl with hg₂ | hl₂
          · rw [Set.mem_union]
            left; right
            exact hg₂
          · by_cases hw : e ∈ W₂
            · rw [Set.mem_union]
              left; left; right
              exact hw
            · have h3 := hH₃mem e hl₂ hw
              rw [Set.mem_union]
              left; left; left
              exact h3
  refine ⟨Good₁, Left₁, Good₂, Left₂, W₂, H₃, k₁, ord₁, k₂, ord₂, r₂, r₃,
    hG₁sub, hL₁sub, hpart₁, hdisj₁, hdeg₁', hseg₁, hsize₁, hr₂,
    hG₂sub, hL₂sub, hpart₂, hdisj₂, hdeg₂, hseg₂, hsize₂,
    hr₃, hW₂thr, hW₂sub, hW₂size, hW₂size_le, hW₂empty, hW₂vol,
    hH₃sub, hH₃huge, hH₃mem, hH₃W₂disj, hcover, ?_, ?_, ?_, ?_, ?_,
    ⟨W₁, hW₁subL, hW₁empL, hW₁volL, hW₁sizL, ?_⟩⟩
  · -- `𝓗₃ ∩ 𝓗₂^good = ∅`
    rw [Set.disjoint_left]
    intro e he hg₂
    rcases he with he | he
    · exact (disjoint_hugeEdges_nonHuge 𝓗 β).le_bot
        ⟨he, hL₁sub (hG₂sub hg₂)⟩
    · exact (Set.disjoint_left.mp hdisj₂) hg₂ he.1
  · -- `𝓗₃ ∩ 𝓗₁^good = ∅`
    rw [Set.disjoint_left]
    intro e he hg₁
    rcases he with he | he
    · exact (disjoint_hugeEdges_nonHuge 𝓗 β).le_bot
        ⟨he, hG₁sub hg₁⟩
    · exact (Set.disjoint_left.mp hdisj₁) hg₁ (hL₂sub he.1)
  · rw [Set.disjoint_left]
    intro e heW heG₂
    exact (Set.disjoint_left.mp hdisj₂) heG₂ (hW₂sub heW)
  · rw [Set.disjoint_left]
    intro e heW heG₁
    exact (Set.disjoint_left.mp hdisj₁) heG₁ (hL₂sub (hW₂sub heW))
  · rw [Set.disjoint_left]
    intro e heG₂ heG₁
    exact (Set.disjoint_left.mp hdisj₁) heG₁ (hG₂sub heG₂)
  · intro hne
    rcases hthr₁ with ⟨hemp, -⟩ | h
    · exact absurd hemp hne
    · exact h

end

end ErdosFaberLovaszConjecture
