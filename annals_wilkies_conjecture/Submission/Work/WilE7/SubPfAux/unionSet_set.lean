import Mathlib
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section
open Classical
open WilkiesConjecture WilkiesDesign WilkiesDesign.E
open Work.WilE7

namespace Work.WilE7.SubPfAux

/-! ## Concatenating two chains: evaluation consistency

`EAChain.cat c₁ c₂` is the chain whose `j`-th function is the `j`-th function of
`c₁` for `j < r₁` and the `(j - r₁)`-th function of `c₂` otherwise (via
`Fin.addCases`).  `EAPoly.inl Q` (resp. `EAPoly.inr Q`) views an `EA`-polynomial
of the `r₁`-chain (resp. the `r₂`-chain) as a polynomial of the concatenated
chain by reindexing the `exp`-variables.  The lemmas `cat_ell_inl`,
`cat_ell_inr`, `eaEval_cat_inl`, `eaEval_cat_inr` below record that this
reindexing is evaluation preserving, and `Basic.holds_cat_inl`,
`Basic.holds_cat_inr` upgrade this to basic sets.  These are the ingredients of
`SemiPf.unionSet`'s semantics: a piece coming from `X` is unaffected by the
functions of `Y`'s chain adjoined to the right of `X`'s chain, and conversely.
-/

/-- The chain functions of `c₁` inside the concatenation sit at `Fin.castAdd`. -/
lemma EAChain.cat_ell_inl {k r₁ r₂ : ℕ} (c₁ : EAChain k r₁) (c₂ : EAChain k r₂)
    (j : Fin r₁) (x : Fin k → ℝ) :
    (EAChain.cat c₁ c₂).ell (Fin.castAdd r₂ j) x = c₁.ell j x := by
  simp [EAChain.cat, EAChain.ell]

/-- The chain functions of `c₂` inside the concatenation sit at `Fin.natAdd`. -/
lemma EAChain.cat_ell_inr {k r₁ r₂ : ℕ} (c₁ : EAChain k r₁) (c₂ : EAChain k r₂)
    (j : Fin r₂) (x : Fin k → ℝ) :
    (EAChain.cat c₁ c₂).ell (Fin.natAdd r₁ j) x = c₂.ell j x := by
  simp [EAChain.cat, EAChain.ell]

/-- Evaluating the left inclusion of an `EA`-polynomial in the concatenated
chain agrees with its evaluation in the original chain. -/
lemma eaEval_cat_inl {k r₁ r₂ : ℕ} (c₁ : EAChain k r₁) (c₂ : EAChain k r₂)
    (Q : EAPoly k r₁) (x : Fin k → ℝ) :
    eaEval (EAChain.cat c₁ c₂) (EAPoly.inl Q) x = eaEval c₁ Q x := by
  have h : ((Sum.elim x fun j => Real.exp ((EAChain.cat c₁ c₂).ell j x)) ∘
        Sum.map id (Fin.castAdd r₂))
      = (Sum.elim x fun j => Real.exp (c₁.ell j x)) := by
    funext v
    cases v with
    | inl i => rfl
    | inr j => simp [Function.comp_apply, EAChain.cat_ell_inl]
  unfold eaEval EAPoly.inl
  rw [MvPolynomial.eval_rename, h]

/-- Evaluating the right inclusion of an `EA`-polynomial in the concatenated
chain agrees with its evaluation in the original chain. -/
lemma eaEval_cat_inr {k r₁ r₂ : ℕ} (c₁ : EAChain k r₁) (c₂ : EAChain k r₂)
    (Q : EAPoly k r₂) (x : Fin k → ℝ) :
    eaEval (EAChain.cat c₁ c₂) (EAPoly.inr Q) x = eaEval c₂ Q x := by
  have h : ((Sum.elim x fun j => Real.exp ((EAChain.cat c₁ c₂).ell j x)) ∘
        Sum.map id (Fin.natAdd r₁))
      = (Sum.elim x fun j => Real.exp (c₂.ell j x)) := by
    funext v
    cases v with
    | inl i => rfl
    | inr j => simp [Function.comp_apply, EAChain.cat_ell_inr]
  unfold eaEval EAPoly.inr
  rw [MvPolynomial.eval_rename, h]

/-- A basic set of the `r₁`-chain, viewed in the concatenated chain, holds
exactly when it holds in the original chain. -/
lemma Basic.holds_cat_inl {k r₁ r₂ : ℕ} (c₁ : EAChain k r₁) (c₂ : EAChain k r₂)
    (B : Basic k r₁) (x : Fin k → ℝ) :
    (Basic.inl (k := k) (r₂ := r₂) B).holds (EAChain.cat c₁ c₂) x ↔ B.holds c₁ x := by
  simp only [Basic.holds, Basic.inl]
  constructor
  · intro h
    exact ⟨fun f hf => by
        have h' := h.1 (EAPoly.inl f) (List.mem_map_of_mem hf)
        rwa [eaEval_cat_inl c₁ c₂ f x] at h',
      fun g hg => by
        have h' := h.2 (EAPoly.inl g) (List.mem_map_of_mem hg)
        rwa [eaEval_cat_inl c₁ c₂ g x] at h'⟩
  · intro h
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
      rw [eaEval_cat_inl c₁ c₂ f₀ x]
      exact h.1 f₀ hf₀
    · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
      rw [eaEval_cat_inl c₁ c₂ g₀ x]
      exact h.2 g₀ hg₀

/-- A basic set of the `r₂`-chain, viewed in the concatenated chain, holds
exactly when it holds in the original chain. -/
lemma Basic.holds_cat_inr {k r₁ r₂ : ℕ} (c₁ : EAChain k r₁) (c₂ : EAChain k r₂)
    (B : Basic k r₂) (x : Fin k → ℝ) :
    (Basic.inr (k := k) (r₁ := r₁) B).holds (EAChain.cat c₁ c₂) x ↔ B.holds c₂ x := by
  simp only [Basic.holds, Basic.inr]
  constructor
  · intro h
    exact ⟨fun f hf => by
        have h' := h.1 (EAPoly.inr f) (List.mem_map_of_mem hf)
        rwa [eaEval_cat_inr c₁ c₂ f x] at h',
      fun g hg => by
        have h' := h.2 (EAPoly.inr g) (List.mem_map_of_mem hg)
        rwa [eaEval_cat_inr c₁ c₂ g x] at h'⟩
  · intro h
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
      rw [eaEval_cat_inr c₁ c₂ f₀ x]
      exact h.1 f₀ hf₀
    · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
      rw [eaEval_cat_inr c₁ c₂ g₀ x]
      exact h.2 g₀ hg₀

/-- The underlying set of a concatenation of semi-Pfaffian sets is the union of
the two underlying sets.  This is the semantic content of `SemiPf.unionSet`. -/
theorem unionSet_set {k : ℕ} (X Y : WilkiesDesign.E.SemiPf k) :
    (Work.WilE7.SemiPf.unionSet X Y).set = X.set ∪ Y.set := by
  ext x
  simp only [SemiPf.set, SemiPf.unionSet, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, B, hB, hBh⟩
    rcases List.mem_append.mp hB with hB | hB
    · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
      exact Or.inl ⟨hx, B₀, hB₀, (Basic.holds_cat_inl X.c Y.c B₀ x).mp hBh⟩
    · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
      exact Or.inr ⟨hx, B₀, hB₀, (Basic.holds_cat_inr X.c Y.c B₀ x).mp hBh⟩
  · rintro (⟨hx, B, hB, hBh⟩ | ⟨hx, B, hB, hBh⟩)
    · exact ⟨hx, Basic.inl B, List.mem_append.mpr (Or.inl (List.mem_map_of_mem hB)),
        (Basic.holds_cat_inl X.c Y.c B x).mpr hBh⟩
    · exact ⟨hx, Basic.inr B, List.mem_append.mpr (Or.inr (List.mem_map_of_mem hB)),
        (Basic.holds_cat_inr X.c Y.c B x).mpr hBh⟩

end Work.WilE7.SubPfAux
