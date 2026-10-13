/-
  WilC4/BSpieces/deepBody_definable : `Work.WilC4.BSAux.BSDeepBody B` is `univ`-definable in
  `LRc` whenever `B` is `∅`-definable.

  The body `BSDeepBody B ⊆ ℝ^{BSD k}` (see `Submission/Work/WilC4/badScale_aux.lean`) is the
  quantifier-free conjunction

    `(b, c) ∈ B`, `q₁ = x / (2M)`, `q₁ ≤ b`, `b ≤ 2 M x`,

  where the parameter slots `c` are read along `bEmb k` and the extra slots `(b, q₁)` are
  `Sum.inr 0` and `Sum.inr 1` of `BSD k = BSI k ⊕ Fin 2`.

  The four conjuncts are each `∅`/`univ`-definable:

  * the `B`-membership is a plain reindexing read along `GrSub1` (`GrSub1_definable`);
  * the division relation `q₁ = x/(2M)` is `definable_isDivR_poly` (`IsDivR` with the polynomial
    denominator `2 · M`);
  * the two inequalities are polynomial inequalities (`definable_le_LRc`).

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

/-! ## 1. The four conjuncts of `BSDeepBody` -/

/-- The `B`-membership clause `(b, c) ∈ B` of the deepness body: the breakpoint `b` is the first
extra slot `Sum.inr 0` of `BSD k` and the parameters are read off along `bEmb k`. -/
lemma bsDeepMemB_definable {B : Set (Fin (k+1) → ℝ)}
    (hB : (∅ : Set ℝ).Definable LRc B) :
    (Set.univ : Set ℝ).Definable LRc
      (GrSub1 B (BSAux.bEmb k) (Sum.inr (0 : Fin 2) : BSAux.BSD k)) :=
  (GrSub1_definable (k := k) hB (BSAux.bEmb k)
    (Sum.inr (0 : Fin 2) : BSAux.BSD k)).mono (Set.empty_subset _)

/-- The division clause `q₁ = x / (2M)`: `q₁` is the second extra slot `Sum.inr 1`. -/
lemma bsDeepDiv_definable :
    (Set.univ : Set ℝ).Definable LRc
      {g : BSAux.BSD k → ℝ |
        IsDivR (g (Sum.inl (BSAux.sx : BSAux.BSI k)))
          (2 * g (Sum.inl (BSAux.sM : BSAux.BSI k))) (g (Sum.inr (1 : Fin 2)))} := by
  have h := BSAux.definable_isDivR_poly (σ := BSAux.BSD k)
    (MvPolynomial.X ((Sum.inl (BSAux.sx : BSAux.BSI k) : BSAux.BSD k)))
    (MvPolynomial.C 2 * MvPolynomial.X ((Sum.inl (BSAux.sM : BSAux.BSI k) : BSAux.BSD k)))
    ((Sum.inr (1 : Fin 2) : BSAux.BSD k))
  have hset : {u : BSAux.BSD k → ℝ |
        IsDivR ((MvPolynomial.eval u)
            (MvPolynomial.X ((Sum.inl (BSAux.sx : BSAux.BSI k) : BSAux.BSD k))))
          ((MvPolynomial.eval u)
            (MvPolynomial.C 2 *
              MvPolynomial.X ((Sum.inl (BSAux.sM : BSAux.BSI k) : BSAux.BSD k))))
          (u ((Sum.inr (1 : Fin 2) : BSAux.BSD k)))} =
      {g : BSAux.BSD k → ℝ |
        IsDivR (g (Sum.inl (BSAux.sx : BSAux.BSI k)))
          (2 * g (Sum.inl (BSAux.sM : BSAux.BSI k))) (g (Sum.inr (1 : Fin 2)))} := by
    ext u
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X, MvPolynomial.eval_C,
      MvPolynomial.eval_mul]
  rw [hset] at h
  exact h

/-- The lower bound `q₁ ≤ b`. -/
lemma bsDeepLo_definable :
    (Set.univ : Set ℝ).Definable LRc
      {g : BSAux.BSD k → ℝ | g (Sum.inr (1 : Fin 2)) ≤ g (Sum.inr (0 : Fin 2))} := by
  have h := definable_le_LRc (σ := BSAux.BSD k)
    (MvPolynomial.X ((Sum.inr (1 : Fin 2)) : BSAux.BSD k))
    (MvPolynomial.X ((Sum.inr (0 : Fin 2)) : BSAux.BSD k))
  have hset : {u : BSAux.BSD k → ℝ |
        (MvPolynomial.eval u) (MvPolynomial.X ((Sum.inr (1 : Fin 2)) : BSAux.BSD k))
        ≤ (MvPolynomial.eval u) (MvPolynomial.X ((Sum.inr (0 : Fin 2)) : BSAux.BSD k))} =
      {g : BSAux.BSD k → ℝ | g (Sum.inr (1 : Fin 2)) ≤ g (Sum.inr (0 : Fin 2))} := by
    ext u
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X]
  rw [hset] at h
  exact h

/-- The upper bound `b ≤ 2 M x`. -/
lemma bsDeepHi_definable :
    (Set.univ : Set ℝ).Definable LRc
      {g : BSAux.BSD k → ℝ |
        g (Sum.inr (0 : Fin 2)) ≤
          2 * g (Sum.inl (BSAux.sM : BSAux.BSI k)) * g (Sum.inl (BSAux.sx : BSAux.BSI k))} := by
  have h := definable_le_LRc (σ := BSAux.BSD k)
    (MvPolynomial.X ((Sum.inr (0 : Fin 2)) : BSAux.BSD k))
    (MvPolynomial.C 2 * MvPolynomial.X ((Sum.inl (BSAux.sM : BSAux.BSI k) : BSAux.BSD k)) *
      MvPolynomial.X ((Sum.inl (BSAux.sx : BSAux.BSI k) : BSAux.BSD k)))
  have hset : {u : BSAux.BSD k → ℝ |
        (MvPolynomial.eval u) (MvPolynomial.X ((Sum.inr (0 : Fin 2)) : BSAux.BSD k))
        ≤ (MvPolynomial.eval u)
          (MvPolynomial.C 2 * MvPolynomial.X ((Sum.inl (BSAux.sM : BSAux.BSI k) : BSAux.BSD k)) *
            MvPolynomial.X ((Sum.inl (BSAux.sx : BSAux.BSI k) : BSAux.BSD k)))} =
      {g : BSAux.BSD k → ℝ |
        g (Sum.inr (0 : Fin 2)) ≤
          2 * g (Sum.inl (BSAux.sM : BSAux.BSI k)) * g (Sum.inl (BSAux.sx : BSAux.BSI k))} := by
    ext u
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X, MvPolynomial.eval_C,
      MvPolynomial.eval_mul]
  rw [hset] at h
  exact h

/-! ## 2. `BSDeepBody` as a conjunction -/

lemma BSDeepBody_eq (B : Set (Fin (k+1) → ℝ)) :
    BSAux.BSDeepBody (k := k) B =
      GrSub1 B (BSAux.bEmb k) (Sum.inr (0 : Fin 2) : BSAux.BSD k) ∩
      {g : BSAux.BSD k → ℝ |
        IsDivR (g (Sum.inl (BSAux.sx : BSAux.BSI k)))
          (2 * g (Sum.inl (BSAux.sM : BSAux.BSI k))) (g (Sum.inr (1 : Fin 2)))} ∩
      {g : BSAux.BSD k → ℝ | g (Sum.inr (1 : Fin 2)) ≤ g (Sum.inr (0 : Fin 2))} ∩
      {g : BSAux.BSD k → ℝ |
        g (Sum.inr (0 : Fin 2)) ≤
          2 * g (Sum.inl (BSAux.sM : BSAux.BSI k)) * g (Sum.inl (BSAux.sx : BSAux.BSI k))} := by
  ext g
  simp only [BSAux.BSDeepBody, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

/-! ## 3. The theorem -/

theorem deepBody_definable {k : ℕ} {B : Set (Fin (k + 1) → ℝ)}
    (hB : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B) :
    (Set.univ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.BSAux.BSDeepBody B) := by
  have h1 := bsDeepMemB_definable (k := k) hB
  have h2 := bsDeepDiv_definable (k := k)
  have h3 := bsDeepLo_definable (k := k)
  have h4 := bsDeepHi_definable (k := k)
  rw [BSDeepBody_eq (k := k) B]
  exact ((h1.inter h2).inter h3).inter h4

end Work.WilC4.BSpieces
