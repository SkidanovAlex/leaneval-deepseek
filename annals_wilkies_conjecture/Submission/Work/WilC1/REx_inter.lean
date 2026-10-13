import Mathlib
import Submission.Work.WilC1.Defs

/-!
  WilC1 — intersection closure of `REx`.

  If `X` is the projection of the zero set of an exp-polynomial `P` with witness block `γ`,
  and `Y` the projection of the zero set of `Q` with witness block `δ`, then `X ∩ Y` is the
  projection of the zero set of the single exp-polynomial `P'^2 + Q'^2` with witness block
  `γ ⊕ δ` (`P'`, `Q'` being `P`, `Q` with the witness index types merged into `γ ⊕ δ`), because
  a sum of two squares of reals vanishes exactly when both terms vanish.

  The two merging steps are the `polyMap`-renaming lemmas below: a coordinate type
  `ι ⊕ γ` sits inside `ι ⊕ (γ ⊕ δ)` via `Sum.map id Sum.inl : ι ⊕ γ → ι ⊕ (γ ⊕ δ)`
  (`Sum.inr` for the `δ`-block), and `rexpEval` is insensitive to renaming index types
  (`rexpEval_rename` in `Defs`).
-/

namespace Work.WilC1

variable {ι γ δ : Type*}

/-- Merging the `γ`-witness block of `P` into the block `γ ⊕ δ`: evaluating in the combined
witnesses `z` is the same as evaluating in `z ∘ Sum.inl`. -/
theorem rexpEval_rename_merge_left (x : ι → ℝ) (z : (γ ⊕ δ) → ℝ)
    (P : MvPolynomial ((ι ⊕ γ) ⊕ (ι ⊕ γ)) ℝ) :
    rexpEval (Sum.elim x z) (MvPolynomial.rename (polyMap (Sum.map id (Sum.inl : γ → γ ⊕ δ))) P)
      = rexpEval (Sum.elim x (z ∘ Sum.inl)) P := by
  rw [rexpEval_rename]
  congr 1
  funext q
  rcases q with i | g <;> rfl

/-- Merging the `δ`-witness block of `Q` into the block `γ ⊕ δ`: evaluating in the combined
witnesses `z` is the same as evaluating in `z ∘ Sum.inr`. -/
theorem rexpEval_rename_merge_right (x : ι → ℝ) (z : (γ ⊕ δ) → ℝ)
    (Q : MvPolynomial ((ι ⊕ δ) ⊕ (ι ⊕ δ)) ℝ) :
    rexpEval (Sum.elim x z) (MvPolynomial.rename (polyMap (Sum.map id (Sum.inr : δ → γ ⊕ δ))) Q)
      = rexpEval (Sum.elim x (z ∘ Sum.inr)) Q := by
  rw [rexpEval_rename]
  congr 1
  funext q
  rcases q with d | d <;> rfl

theorem REx_inter {ι : Type*} {X Y : Set (ι → ℝ)} (hX : REx ι X) (hY : REx ι Y) :
    REx ι (X ∩ Y) := by
  -- the local hypotheses `hγ`, `hδ` are instances, so `Fintype (γ ⊕ δ)` is found automatically
  obtain ⟨γ, hγ, P, hP⟩ := hX
  obtain ⟨δ, hδ, Q, hQ⟩ := hY
  refine ⟨γ ⊕ δ, inferInstance,
    (MvPolynomial.rename (polyMap (Sum.map id (Sum.inl : γ → γ ⊕ δ))) P) ^ 2
      + (MvPolynomial.rename (polyMap (Sum.map id (Sum.inr : δ → γ ⊕ δ))) Q) ^ 2, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · -- membership in both: use the two witness blocks side by side
    rintro ⟨hx, hy⟩
    rw [hP] at hx
    rw [hQ] at hy
    obtain ⟨y, hy0⟩ := hx
    obtain ⟨y', hy1⟩ := hy
    refine ⟨Sum.elim y y', ?_⟩
    rw [rexpEval_add, rexpEval_pow, rexpEval_pow,
      rexpEval_rename_merge_left x (Sum.elim y y') P,
      rexpEval_rename_merge_right x (Sum.elim y y') Q,
      Sum.elim_comp_inl, Sum.elim_comp_inr, hy0, hy1]
    norm_num
  · -- a vanishing sum of squares: both terms vanish
    rintro ⟨z, hz⟩
    rw [rexpEval_add, rexpEval_pow, rexpEval_pow,
      rexpEval_rename_merge_left x z P, rexpEval_rename_merge_right x z Q] at hz
    obtain ⟨h1, h2⟩ := sq_add_sq_eq_zero.mp hz
    constructor
    · rw [hP, Set.mem_ofPred_eq]
      exact ⟨z ∘ Sum.inl, h1⟩
    · rw [hQ, Set.mem_ofPred_eq]
      exact ⟨z ∘ Sum.inr, h2⟩

end Work.WilC1
