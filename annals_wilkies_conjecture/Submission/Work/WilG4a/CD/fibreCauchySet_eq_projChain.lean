/-
  WilG4a / CD / `fibreCauchySet_eq_projChain`.

  The two mathematical facts about the vocabulary of `Work.WilG4a.CD.fibreLimitDefs` are

  * `Work.WilG4a.CD.snocIt_mem_Gset` (sibling module `snocIt_mem_Gset`): reading the body
    `Gset` at a point of the shape `snocIt (p+3) 4 (Fin.snoc (Fin.snoc z ε) δ) w` is the
    same as `reading p A z ε δ (w 0) (w 1) (w 2) (w 3)`;
  * this module: the fibre-Cauchy set of `A` is the `Ω`-construction `projChain p A`.

  The proof is a pure unfolding of the `Ω`-construction.  `projChain` is

    `(projLast (posEps ∩ (projLast (posDel ∩ (projLastIter (p+3) 4 (Gset))ᶜ))ᶜ))ᶜ`,

  so its complement consists of the `z` such that for every `ε > 0` there is `δ > 0` such
  that *no* 4-tuple `w` makes
  `snocIt (p+3) 4 (Fin.snoc (Fin.snoc z ε) δ) w` lie in `Gset`.  Reading that body through
  `hread` and then negating the seven-fold conjunction gives: for all `t ≠ c`, `t' ≠ c`
  within `δ` of `c = z (Fin.last p)`, and all `v, v'` with
  `(init z, t, v), (init z, t', v') ∈ A`, one has `|v - v'| ≤ ε` — exactly the definition of
  `fibreCauchySet`.

  The pointwise step (converting the two quadratic atoms `δ² > (t-c)²`, `δ² > (t'-c)²` with
  `δ > 0` into `|t-c| < δ`, `|t'-c| < δ`, and the disjunction `ε < v - v' ∨ ε < v' - v` into
  the negation of `|v - v'| ≤ ε`, and then exchanging `¬` with the conjunction) is isolated in
  the sibling module `Work.WilG4a.CD.reading_compl_iff`.
-/
import Mathlib
import Submission.Work.WilG4a.CD.fibreLimitDefs
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG4a.CD.reading_compl_iff

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4a.CD

open WilkiesDesign

theorem fibreCauchySet_eq_projChain (p : ℕ) (A : Set (Fin (p + 2) → ℝ))
    (hread : ∀ (z : Fin (p + 1) → ℝ) (ε δ : ℝ) (w : Fin 4 → ℝ),
      Work.WilG0.snocIt (p + 3) 4 (Fin.snoc (Fin.snoc z ε) δ) w ∈ Gset p A ↔
        reading p A z ε δ (w 0) (w 1) (w 2) (w 3)) :
    fibreCauchySet p A = projChain p A := by
  -- Step 1: `projChain`, unwound: the complement of the `∃δ`-complement.
  have hPL : ∀ (n : ℕ) (X : Set (Fin (n+1) → ℝ)) (x : Fin n → ℝ),
      x ∉ projLast X ↔ ∀ t : ℝ, Fin.snoc x t ∉ X := by
    intro n X x; simp [projLast]
  have hproj : ∀ z : Fin (p + 1) → ℝ,
      z ∈ projChain p A ↔ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        Fin.snoc (Fin.snoc z ε) δ ∉ Work.WilG0.projLastIter (p + 3) 4 (Gset p A) := by
    intro z
    show z ∈ (projLast (posEpsSet p ∩ (projLast (posDelSet p ∩
      (Work.WilG0.projLastIter (p + 3) 4 (Gset p A))ᶜ))ᶜ))ᶜ ↔ _
    rw [Set.mem_compl_iff, hPL]
    constructor
    · intro h ε hε
      have h1 := h ε
      have hεmem : Fin.snoc z ε ∈ posEpsSet p := by simpa [posEpsSet] using hε
      have h2 : Fin.snoc z ε ∈ projLast (posDelSet p ∩
          (Work.WilG0.projLastIter (p + 3) 4 (Gset p A))ᶜ) := by
        by_contra hc
        exact h1 ⟨hεmem, hc⟩
      rw [projLast] at h2
      obtain ⟨δ, hδ⟩ := h2
      exact ⟨δ, by simpa [posDelSet] using hδ.1, hδ.2⟩
    · intro h ε
      rintro ⟨hε, hc⟩
      have hε' : 0 < ε := by simpa [posEpsSet] using hε
      obtain ⟨δ, hδ1, hδ2⟩ := h ε hε'
      apply hc
      rw [projLast]
      exact ⟨δ, by refine ⟨?_, hδ2⟩; simpa [posDelSet] using hδ1⟩
  -- Step 2: reading `Gset` through `hread`, and eliminating the `Fin 4`-quantifier.
  have hread' : ∀ (z : Fin (p + 1) → ℝ) (ε δ : ℝ),
      Fin.snoc (Fin.snoc z ε) δ ∉ Work.WilG0.projLastIter (p + 3) 4 (Gset p A) ↔
        ∀ t t' v v' : ℝ, ¬ reading p A z ε δ t t' v v' := by
    intro z ε δ
    rw [Work.WilG0.projLastIter_eq]
    simp only [Set.mem_ofPred_eq, not_exists]
    simp only [hread z ε δ]
    constructor
    · intro h a b c d
      have := h ![a,b,c,d]
      simpa using this
    · intro h w
      exact h (w 0) (w 1) (w 2) (w 3)
  -- Step 3: negating the body is exactly the Cauchy condition at scale `δ`.
  have hsnoc : ∀ (z : Fin (p + 1) → ℝ) (ε δ : ℝ), 0 < δ →
      ((Fin.snoc (Fin.snoc z ε) δ ∉ Work.WilG0.projLastIter (p + 3) 4 (Gset p A)) ↔
        (∀ t t' : ℝ, t ≠ z (Fin.last p) → t' ≠ z (Fin.last p) →
          |t - z (Fin.last p)| < δ → |t' - z (Fin.last p)| < δ →
          ∀ v v' : ℝ, Fin.snoc (Fin.snoc (Fin.init z) t) v ∈ A →
            Fin.snoc (Fin.snoc (Fin.init z) t') v' ∈ A → |v - v'| ≤ ε)) := by
    intro z ε δ hδ
    rw [hread' z ε δ]
    exact reading_compl_iff p A z ε δ hδ
  ext z
  rw [fibreCauchySet, Set.mem_ofPred_eq, hproj]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hcond⟩ := h ε hε
    exact ⟨δ, hδ, (hsnoc z ε δ hδ).mpr hcond⟩
  · intro h ε hε
    obtain ⟨δ, hδ, hcond⟩ := h ε hε
    exact ⟨δ, hδ, (hsnoc z ε δ hδ).mp hcond⟩

end Work.WilG4a.CD
