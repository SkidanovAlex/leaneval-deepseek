/-
# The position maps of the word shuffle, and the splitting of a tuple

This module fixes the *position maps* of the shuffle calculus of
`Work.Diff.EXT.evolX.mulOp` (the product of two packed operators of arities `K₁`, `K₂`).

For a binary word `w : Word j` (`Work.Diff.EXT.evolX.mulOpJetsDefs`), `wCntT w` (resp. `wCntF w`) is
the number of `true` (resp. `false`) entries, i.e. the number of the `j` covariant derivatives that
are applied to the first (resp. second) factor of the product.  The two sub-tuples of the level-`j`
tuple `F : Fin (K₁+K₂+j) → TField` are `wTupA K₁ K₂ j w F` (of arity `K₁ + wCntT w`) and
`wTupB K₁ K₂ j w F` (of arity `K₂ + wCntF w`).

Here we introduce the uniformly indexed position maps

* `wPA K₁ K₂ j w : Fin (K₁ + wCntT w) → Fin (K₁+K₂+j)` — the position in `F` of the `A`-entry,
* `wPB K₁ K₂ j w : Fin (K₂ + wCntF w) → Fin (K₁+K₂+j)` — the position in `F` of the `B`-entry,

so that `wTupA K₁ K₂ j w F = F ∘ wPA K₁ K₂ j w` and `wTupB K₁ K₂ j w F = F ∘ wPB K₁ K₂ j w`
(`wTupA_eq_comp_wPA`, `wTupB_eq_comp_wPB`), together with the two generic splitting lemmas for an
injective and disjoint pair of maps covering `Fin m`:

* `sum_split_of_inj`, `prod_split_of_inj`,

and the concrete splittings and update lemmas of the word shuffle *conditional on* the injectivity
and the disjointness of `wPA`, `wPB` (which is the content of
`Submission/Work/Diff/EXT/evolX/mulOpWordPos.lean`, `Work.Diff.EXT.evolX.mulOpWordPos`); everything
here is independent of that.
-/
import Mathlib
import Submission.Work.Diff.EXT.evolX.mulOpJetsDefs

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.Diff.EXT.evolX

open Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The position maps -/

/-- **The position of the `r`-th entry of the `A`-tuple** in the level-`j` tuple
`F : Fin (K₁+K₂+j)`: the map with `wTupA K₁ K₂ j w F = F ∘ wPA K₁ K₂ j w`. -/
noncomputable def wPA (K₁ K₂ : ℕ) : (n : ℕ) → (w : Word n) →
    Fin (K₁ + wCntT w) → Fin (K₁ + K₂ + n)
  | 0, Word.nil => fun i => Fin.castAdd K₂ i
  | n + 1, w => fun i => wPosA K₁ K₂ n w i.val

/-- **The position of the `q`-th entry of the `B`-tuple** in the level-`j` tuple
`F : Fin (K₁+K₂+j)`: the map with `wTupB K₁ K₂ j w F = F ∘ wPB K₁ K₂ j w`. -/
noncomputable def wPB (K₁ K₂ : ℕ) : (n : ℕ) → (w : Word n) →
    Fin (K₂ + wCntF w) → Fin (K₁ + K₂ + n)
  | 0, Word.nil => fun i => Fin.natAdd K₁ i
  | n + 1, w => fun i => wPosB K₁ K₂ n w i.val

@[simp] theorem wPA_nil (K₁ K₂ : ℕ) :
    wPA K₁ K₂ 0 Word.nil = fun i => Fin.castAdd K₂ i := rfl

@[simp] theorem wPB_nil (K₁ K₂ : ℕ) :
    wPB K₁ K₂ 0 Word.nil = fun i => Fin.natAdd K₁ i := rfl

theorem wPA_succ (K₁ K₂ n : ℕ) (w : Word (n + 1)) :
    wPA K₁ K₂ (n + 1) w = fun i => wPosA K₁ K₂ n w i.val := rfl

theorem wPB_succ (K₁ K₂ n : ℕ) (w : Word (n + 1)) :
    wPB K₁ K₂ (n + 1) w = fun i => wPosB K₁ K₂ n w i.val := rfl

/-- The `A`-tuple is the composition of the level-`j` tuple with the position map. -/
theorem wTupA_eq_comp_wPA (K₁ K₂ : ℕ) : ∀ (n : ℕ) (w : Word n)
    (F : Fin (K₁ + K₂ + n) → TField (I := I) (M := M)),
    wTupA (I := I) (M := M) K₁ K₂ n w F = fun i => F (wPA K₁ K₂ n w i)
  | 0, Word.nil, F => by
      funext i
      rfl
  | n + 1, w, F => rfl

/-- The `B`-tuple is the composition of the level-`j` tuple with the position map. -/
theorem wTupB_eq_comp_wPB (K₁ K₂ : ℕ) : ∀ (n : ℕ) (w : Word n)
    (F : Fin (K₁ + K₂ + n) → TField (I := I) (M := M)),
    wTupB (I := I) (M := M) K₁ K₂ n w F = fun i => F (wPB K₁ K₂ n w i)
  | 0, Word.nil, F => by
      funext i
      rfl
  | n + 1, w, F => rfl

/-! ## The generic splitting of a sum and of a product over two disjoint injective blocks -/

/-- **Splitting a sum over `Fin m` into two injective, disjoint blocks.** -/
theorem sum_split_of_inj {m nA nB : ℕ} (f : Fin nA → Fin m) (g : Fin nB → Fin m)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hd : ∀ r q, f r ≠ g q) (hcard : nA + nB = m) (Φ : Fin m → ℝ) :
    (∑ s : Fin m, Φ s) = (∑ r : Fin nA, Φ (f r)) + (∑ q : Fin nB, Φ (g q)) := by
  classical
  have hcardA : (Finset.univ.image f).card = nA := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have hcardB : (Finset.univ.image g).card = nB := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have hdisj : Disjoint (Finset.univ.image f) (Finset.univ.image g) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    rw [Finset.mem_image] at hs hs'
    obtain ⟨r, _, hr⟩ := hs
    obtain ⟨q, _, hq⟩ := hs'
    exact hd r q (hr.trans hq.symm)
  have hinter : Finset.univ.image f ∩ Finset.univ.image g = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp hdisj
  have hcover : Finset.univ.image f ∪ Finset.univ.image g = (Finset.univ : Finset (Fin m)) := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_union, hcardA, hcardB, hinter]
    simp only [Finset.card_empty, Nat.sub_zero, Fintype.card_fin]
    exact hcard
  have hsum_univ : (∑ s : Fin m, Φ s) = ∑ s ∈ Finset.univ.image f ∪ Finset.univ.image g, Φ s := by
    rw [hcover]
  rw [hsum_univ, Finset.sum_union hdisj,
    Finset.sum_image (f := Φ) (g := f) (s := Finset.univ) hf.injOn,
    Finset.sum_image (f := Φ) (g := g) (s := Finset.univ) hg.injOn]

/-- **Splitting a product over `Fin m` into two injective, disjoint blocks.** -/
theorem prod_split_of_inj {m nA nB : ℕ} (f : Fin nA → Fin m) (g : Fin nB → Fin m)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hd : ∀ r q, f r ≠ g q) (hcard : nA + nB = m) (Φ : Fin m → ℝ) :
    (∏ s : Fin m, Φ s) = (∏ r : Fin nA, Φ (f r)) * (∏ q : Fin nB, Φ (g q)) := by
  classical
  have hcardA : (Finset.univ.image f).card = nA := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have hcardB : (Finset.univ.image g).card = nB := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have hdisj : Disjoint (Finset.univ.image f) (Finset.univ.image g) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    rw [Finset.mem_image] at hs hs'
    obtain ⟨r, _, hr⟩ := hs
    obtain ⟨q, _, hq⟩ := hs'
    exact hd r q (hr.trans hq.symm)
  have hinter : Finset.univ.image f ∩ Finset.univ.image g = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp hdisj
  have hcover : Finset.univ.image f ∪ Finset.univ.image g = (Finset.univ : Finset (Fin m)) := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_union, hcardA, hcardB, hinter]
    simp only [Finset.card_empty, Nat.sub_zero, Fintype.card_fin]
    exact hcard
  have hprod_univ : (∏ s : Fin m, Φ s)
      = ∏ s ∈ Finset.univ.image f ∪ Finset.univ.image g, Φ s := by
    rw [hcover]
  rw [hprod_univ, Finset.prod_union hdisj,
    Finset.prod_image (f := Φ) (g := f) (s := Finset.univ) hf.injOn,
    Finset.prod_image (f := Φ) (g := g) (s := Finset.univ) hg.injOn]

/-! ## The concrete splittings of the word shuffle -/

/-- **The sum over the level-`j` tuple splits into the `A`-block and the `B`-block.** -/
theorem wSum_split {K₁ K₂ j : ℕ} (w : Word j) (Φ : Fin (K₁ + K₂ + j) → ℝ)
    (hA : Function.Injective (wPA K₁ K₂ j w)) (hB : Function.Injective (wPB K₁ K₂ j w))
    (hd : ∀ r q, wPA K₁ K₂ j w r ≠ wPB K₁ K₂ j w q) :
    (∑ s : Fin (K₁ + K₂ + j), Φ s)
      = (∑ r : Fin (K₁ + wCntT w), Φ (wPA K₁ K₂ j w r))
        + (∑ q : Fin (K₂ + wCntF w), Φ (wPB K₁ K₂ j w q)) :=
  sum_split_of_inj _ _ hA hB hd (by have := wCntT_add_wCntF w; omega) Φ

/-- **The product over the level-`j` tuple splits into the `A`-block and the `B`-block.** -/
theorem wProd_split {K₁ K₂ j : ℕ} (w : Word j) (Φ : Fin (K₁ + K₂ + j) → ℝ)
    (hA : Function.Injective (wPA K₁ K₂ j w)) (hB : Function.Injective (wPB K₁ K₂ j w))
    (hd : ∀ r q, wPA K₁ K₂ j w r ≠ wPB K₁ K₂ j w q) :
    (∏ s : Fin (K₁ + K₂ + j), Φ s)
      = (∏ r : Fin (K₁ + wCntT w), Φ (wPA K₁ K₂ j w r))
        * (∏ q : Fin (K₂ + wCntF w), Φ (wPB K₁ K₂ j w q)) :=
  prod_split_of_inj _ _ hA hB hd (by have := wCntT_add_wCntF w; omega) Φ

/-! ## The update lemmas -/

/-- **Updating an `A`-position updates the `A`-tuple.** -/
theorem wTupA_update_wPA {K₁ K₂ j : ℕ} (w : Word j)
    (F : Fin (K₁ + K₂ + j) → TField (I := I) (M := M)) (X : TField (I := I) (M := M))
    (hA : Function.Injective (wPA K₁ K₂ j w)) (r : Fin (K₁ + wCntT w)) :
    wTupA (I := I) (M := M) K₁ K₂ j w (Function.update F (wPA K₁ K₂ j w r) X)
      = Function.update (wTupA (I := I) (M := M) K₁ K₂ j w F) r X := by
  rw [wTupA_eq_comp_wPA, wTupA_eq_comp_wPA]
  funext i
  by_cases h : i = r
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne (fun h' => h (hA h')), Function.update_of_ne h]

/-- **Updating an `A`-position does not change the `B`-tuple.** -/
theorem wTupB_update_wPA {K₁ K₂ j : ℕ} (w : Word j)
    (F : Fin (K₁ + K₂ + j) → TField (I := I) (M := M)) (X : TField (I := I) (M := M))
    (hd : ∀ r q, wPA K₁ K₂ j w r ≠ wPB K₁ K₂ j w q) (r : Fin (K₁ + wCntT w)) :
    wTupB (I := I) (M := M) K₁ K₂ j w (Function.update F (wPA K₁ K₂ j w r) X)
      = wTupB (I := I) (M := M) K₁ K₂ j w F := by
  rw [wTupB_eq_comp_wPB, wTupB_eq_comp_wPB]
  funext q
  rw [Function.update_of_ne (Ne.symm (hd r q))]

/-- **Updating a `B`-position updates the `B`-tuple.** -/
theorem wTupB_update_wPB {K₁ K₂ j : ℕ} (w : Word j)
    (F : Fin (K₁ + K₂ + j) → TField (I := I) (M := M)) (X : TField (I := I) (M := M))
    (hB : Function.Injective (wPB K₁ K₂ j w)) (q : Fin (K₂ + wCntF w)) :
    wTupB (I := I) (M := M) K₁ K₂ j w (Function.update F (wPB K₁ K₂ j w q) X)
      = Function.update (wTupB (I := I) (M := M) K₁ K₂ j w F) q X := by
  rw [wTupB_eq_comp_wPB, wTupB_eq_comp_wPB]
  funext i
  by_cases h : i = q
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne (fun h' => h (hB h')), Function.update_of_ne h]

/-- **Updating a `B`-position does not change the `A`-tuple.** -/
theorem wTupA_update_wPB {K₁ K₂ j : ℕ} (w : Word j)
    (F : Fin (K₁ + K₂ + j) → TField (I := I) (M := M)) (X : TField (I := I) (M := M))
    (hd : ∀ r q, wPA K₁ K₂ j w r ≠ wPB K₁ K₂ j w q) (q : Fin (K₂ + wCntF w)) :
    wTupA (I := I) (M := M) K₁ K₂ j w (Function.update F (wPB K₁ K₂ j w q) X)
      = wTupA (I := I) (M := M) K₁ K₂ j w F := by
  rw [wTupA_eq_comp_wPA, wTupA_eq_comp_wPA]
  funext r
  rw [Function.update_of_ne (hd r q)]

/-! ## Smoothness of the sub-tuples -/

/-- **The `A`-tuple is smooth in the level-`j` tuple.** -/
theorem wTupA_smooth {K₁ K₂ j : ℕ} (w : Word j)
    (F : Fin (K₁ + K₂ + j) → TField (I := I) (M := M))
    (hF : ∀ i, SmoothF (I := I) (M := M) (F i)) :
    ∀ i, SmoothF (I := I) (M := M) (wTupA (I := I) (M := M) K₁ K₂ j w F i) := by
  rw [wTupA_eq_comp_wPA]
  intro i
  exact hF _

/-- **The `B`-tuple is smooth in the level-`j` tuple.** -/
theorem wTupB_smooth {K₁ K₂ j : ℕ} (w : Word j)
    (F : Fin (K₁ + K₂ + j) → TField (I := I) (M := M))
    (hF : ∀ i, SmoothF (I := I) (M := M) (F i)) :
    ∀ i, SmoothF (I := I) (M := M) (wTupB (I := I) (M := M) K₁ K₂ j w F i) := by
  rw [wTupB_eq_comp_wPB]
  intro i
  exact hF _

end Work.Diff.EXT.evolX
