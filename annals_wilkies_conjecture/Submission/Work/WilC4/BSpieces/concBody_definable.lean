/-
  WilC4/BSpieces/concBody_definable : `Work.WilC4.BSAux.BSConcBody E` is `univ`-definable in
  `LRc` whenever `E ⊆ ℝ` is `∅`-definable (as a one-dimensional set, via `Set.Definable₁`).

  The body `BSConcBody E ⊆ ℝ^{BSC k}` (see `Submission/Work/WilC4/badScale_aux.lean`) is the
  quantifier-free conjunction

    `ρ ∈ E`, `0 < ρ`, `q = w / ρ`, `-ε ≤ q - 1`, `q - 1 ≤ ε`,

  where `ρ` is the slot `Sum.inr 0` of `BSC k = BSI k ⊕ Fin 2`, `q` the slot `Sum.inr 1`, and
  the remaining slots (`w` = `sw`, `ε` = `sEps`) are read off along `Sum.inl`.  This is the
  body of the conclusion clause `∃ ρ ∈ E, 0 < ρ ∧ |w/ρ - 1| ≤ ε` of `BadScale`.

  The five conjuncts are each `∅`/`univ`-definable:

  * the `E`-membership is the pullback of the `∅`-definable one-dimensional set `E` along the
    coordinate `Sum.inr 0` (`Definable.preimage_comp` + `Definable₁`);
  * `0 < ρ` and the two linear inequalities defining `|q - 1| ≤ ε` are polynomial inequalities
    with real coefficients (`definable_eval_pos_LRc`, `definable_le_LRc`);
  * the division relation `q = w/ρ` is `definable_isDivR`.

  Everything is proved with `univ` as parameter set, which is the conclusion as stated.
-/
import Mathlib
import Submission.Work.WilC4.badScale_aux

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC4.BSpieces

open Work.WilC4
open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc)

variable {k : ℕ}

/-! ## 1. The five conjuncts of `BSConcBody` -/

/-- The membership clause `ρ ∈ E` (the slot `Sum.inr 0` of `BSC k`), pulled back from the
`∅`-definable one-dimensional set `E ⊆ ℝ`. -/
lemma bsConcMemE_definable {E : Set ℝ}
    (hE : (∅ : Set ℝ).Definable₁ LRc E) :
    (Set.univ : Set ℝ).Definable LRc
      {g : BSAux.BSC k → ℝ | g (Sum.inr (0 : Fin 2)) ∈ E} := by
  rw [Set.Definable₁] at hE
  have h := hE.preimage_comp (fun _ : Fin 1 => (Sum.inr (0 : Fin 2) : BSAux.BSC k))
  have hset : ((fun g : BSAux.BSC k → ℝ =>
        g ∘ (fun _ : Fin 1 => (Sum.inr (0 : Fin 2) : BSAux.BSC k))) ⁻¹'
          {x : Fin 1 → ℝ | x 0 ∈ E}) =
      {g : BSAux.BSC k → ℝ | g (Sum.inr (0 : Fin 2)) ∈ E} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Function.comp_apply]
  rw [hset] at h
  exact h.mono (Set.empty_subset _)

/-- The positivity clause `0 < ρ`. -/
lemma bsConcPos_definable :
    (Set.univ : Set ℝ).Definable LRc
      {g : BSAux.BSC k → ℝ | 0 < g (Sum.inr (0 : Fin 2))} := by
  have h := definable_eval_pos_LRc (σ := BSAux.BSC k)
    (MvPolynomial.X ((Sum.inr (0 : Fin 2)) : BSAux.BSC k))
  convert h using 1
  ext u
  simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X]

/-- The division clause `q = w / ρ` (numerator slot `Sum.inl sw`, denominator slot `Sum.inr 0`,
quotient slot `Sum.inr 1`). -/
lemma bsConcDiv_definable :
    (Set.univ : Set ℝ).Definable LRc
      {g : BSAux.BSC k → ℝ |
        IsDivR (g (Sum.inl (BSAux.sw : BSAux.BSI k))) (g (Sum.inr (0 : Fin 2)))
          (g (Sum.inr (1 : Fin 2)))} :=
  definable_isDivR _ _ _

/-- The lower bound `-ε ≤ q - 1`. -/
lemma bsConcLo_definable :
    (Set.univ : Set ℝ).Definable LRc
      {g : BSAux.BSC k → ℝ |
        -(g (Sum.inl (BSAux.sEps : BSAux.BSI k))) ≤ g (Sum.inr (1 : Fin 2)) - 1} := by
  have h := definable_le_LRc (σ := BSAux.BSC k)
    (-(MvPolynomial.X ((Sum.inl (BSAux.sEps : BSAux.BSI k) : BSAux.BSC k))))
    (MvPolynomial.X ((Sum.inr (1 : Fin 2)) : BSAux.BSC k) - 1)
  convert h using 1
  ext g
  simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X, MvPolynomial.eval_neg,
    MvPolynomial.eval_sub, map_one]

/-- The upper bound `q - 1 ≤ ε`. -/
lemma bsConcHi_definable :
    (Set.univ : Set ℝ).Definable LRc
      {g : BSAux.BSC k → ℝ |
        g (Sum.inr (1 : Fin 2)) - 1 ≤ g (Sum.inl (BSAux.sEps : BSAux.BSI k))} := by
  have h := definable_le_LRc (σ := BSAux.BSC k)
    (MvPolynomial.X ((Sum.inr (1 : Fin 2)) : BSAux.BSC k) - 1)
    (MvPolynomial.X ((Sum.inl (BSAux.sEps : BSAux.BSI k) : BSAux.BSC k)))
  convert h using 1
  ext g
  simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X, MvPolynomial.eval_sub, map_one]

/-! ## 2. `BSConcBody` as a conjunction -/

lemma BSConcBody_eq (E : Set ℝ) :
    BSAux.BSConcBody (k := k) E =
      {g : BSAux.BSC k → ℝ | g (Sum.inr (0 : Fin 2)) ∈ E} ∩
      {g : BSAux.BSC k → ℝ | 0 < g (Sum.inr (0 : Fin 2))} ∩
      {g : BSAux.BSC k → ℝ |
        IsDivR (g (Sum.inl (BSAux.sw : BSAux.BSI k))) (g (Sum.inr (0 : Fin 2)))
          (g (Sum.inr (1 : Fin 2)))} ∩
      {g : BSAux.BSC k → ℝ |
        -(g (Sum.inl (BSAux.sEps : BSAux.BSI k))) ≤ g (Sum.inr (1 : Fin 2)) - 1} ∩
      {g : BSAux.BSC k → ℝ |
        g (Sum.inr (1 : Fin 2)) - 1 ≤ g (Sum.inl (BSAux.sEps : BSAux.BSI k))} := by
  ext g
  simp only [BSAux.BSConcBody, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

/-! ## 3. The theorem -/

theorem concBody_definable {k : ℕ} {E : Set ℝ}
    (hE : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc E) :
    (Set.univ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.BSAux.BSConcBody (k := k) E) := by
  have h1 := bsConcMemE_definable (k := k) hE
  have h2 := bsConcPos_definable (k := k)
  have h3 := bsConcDiv_definable (k := k)
  have h4 := bsConcLo_definable (k := k)
  have h5 := bsConcHi_definable (k := k)
  rw [BSConcBody_eq (k := k) E]
  exact (((h1.inter h2).inter h3).inter h4).inter h5

end Work.WilC4.BSpieces
