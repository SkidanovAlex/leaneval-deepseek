/-
  WilC4/DRDeep_definable : `Work.WilC4.DRDeep B₀` is `∅`-definable in `LRc` whenever `B₀` is.

  `DRDeep B₀` (see `Submission/Work/WilC4/DeepThetaGDefs.lean`) is the *negation* of the deepness
  condition `IsDeepR B₀ c β x`, with the two auxiliary variables `(b, q₁)` universally quantified:

    `DRDeep B₀ = {g | ∀ u : Fin 2 → ℝ, Sum.elim g u ∉ DeepBodyNeg B₀}`

  where the quantifier-free body `DeepBodyNeg B₀ ⊆ ℝ^{DRIdx k ⊕ Fin 2}` is the conjunction

    `(b, c) ∈ B₀`, `q₁ = x / (2β)`, `q₁ ≤ b`, `b ≤ 2 β x`.

  The proof is a quantifier-bookkeeping exercise, exactly parallel to `DevDeep_definable`
  (`Submission/Work/WilC4/DevDeep_definable.lean`).

  * The body is a conjunction of four `∅`/`univ`-definable pieces: the `B₀`-membership is a plain
    reindexing read along `GrSub1` (`GrSub1_definable`), the division relation `q₁ = x/(2β)` is
    `definable_isDivR_poly` (`IsDivR` with a polynomial denominator `2 · β`), and the two
    inequalities are polynomial inequalities (`definable_le_LRc`, `real_definable_le`).  Hence
    `DeepBodyNeg B₀` is `univ`-definable.
  * The universal quantifier over `u : Fin 2 → ℝ` is handled by `Set.Definable.forall_of_finite`
    applied to the complement of the body.
  * Everything is proved with `univ` as parameter set and converted at the very end by
    `definable_univ_iff_empty` (every real is a constant of `LRc`).
-/
import Mathlib
import Submission.Work.WilC4.DeepThetaGDefs
import Submission.Work.WilC4.CandBody_definable

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc)

variable {k : ℕ}

/-! ## 1. The index type of the deepness body -/

/-- The index type of `DeepBodyNeg`: the free block `DRIdx k` extended by the two universally
quantified slots `(b, q₁)`. -/
abbrev DRDeepExt (k : ℕ) := DRIdx k ⊕ Fin 2

/-! ## 2. The four conjuncts of `DeepBodyNeg` -/

/-- The `B₀`-membership clause `b ∈ B₀` of the deepness body: the breakpoint `b` is the first
extra slot `Sum.inr 0` and the parameters are read off along `dc`. -/
def drDMemB (B₀ : Set (Fin (k+1) → ℝ)) : Set (DRDeepExt k → ℝ) :=
  GrSub1 B₀ (fun i : Fin k => (Sum.inl (dc i) : DRDeepExt k)) (Sum.inr (0 : Fin 2))

/-- The division clause `q₁ = x / (2β)`: `q₁` is the second extra slot `Sum.inr 1`. -/
def drDDiv : Set (DRDeepExt k → ℝ) :=
  {h | IsDivR (h (Sum.inl (dx : DRIdx k))) (2 * h (Sum.inl (dβ : DRIdx k)))
    (h (Sum.inr (1 : Fin 2)))}

/-- The lower bound `q₁ ≤ b`. -/
def drDLo : Set (DRDeepExt k → ℝ) := {h | h (Sum.inr (1 : Fin 2)) ≤ h (Sum.inr (0 : Fin 2))}

/-- The upper bound `b ≤ 2 β x`. -/
def drDHi : Set (DRDeepExt k → ℝ) :=
  {h | h (Sum.inr (0 : Fin 2)) ≤ 2 * h (Sum.inl (dβ : DRIdx k)) * h (Sum.inl (dx : DRIdx k))}

/-! ## 3. Definability of the four conjuncts -/

lemma drDMemB_definable {B₀ : Set (Fin (k+1) → ℝ)}
    (hB₀ : (∅ : Set ℝ).Definable LRc B₀) :
    (Set.univ : Set ℝ).Definable LRc (drDMemB (k := k) B₀) :=
  (GrSub1_definable (k := k) hB₀ (fun i : Fin k => (Sum.inl (dc i) : DRDeepExt k))
    (Sum.inr (0 : Fin 2))).mono (Set.empty_subset _)

lemma drDDiv_definable :
    (Set.univ : Set ℝ).Definable LRc (drDDiv (k := k)) := by
  have h := CandBodyDefs.definable_isDivR_poly (σ := DRDeepExt k)
    (MvPolynomial.X ((Sum.inl (dx (k := k)) : DRDeepExt k)))
    (MvPolynomial.C 2 * MvPolynomial.X ((Sum.inl (dβ (k := k)) : DRDeepExt k)))
    ((Sum.inr (1 : Fin 2) : DRDeepExt k))
  have hset : {u : DRDeepExt k → ℝ |
        IsDivR ((MvPolynomial.eval u) (MvPolynomial.X ((Sum.inl (dx (k := k)) : DRDeepExt k))))
          ((MvPolynomial.eval u) (MvPolynomial.C 2 *
            MvPolynomial.X ((Sum.inl (dβ (k := k)) : DRDeepExt k))))
          (u ((Sum.inr (1 : Fin 2) : DRDeepExt k)))}
      = drDDiv (k := k) := by
    ext u
    simp only [drDDiv, Set.mem_ofPred_eq, MvPolynomial.eval_X, MvPolynomial.eval_C,
      MvPolynomial.eval_mul]
  rw [hset] at h
  exact h

lemma drDLo_definable :
    (Set.univ : Set ℝ).Definable LRc (drDLo (k := k)) :=
  (real_definable_le (α := DRDeepExt k) (Sum.inr (1 : Fin 2) : DRDeepExt k)
    (Sum.inr (0 : Fin 2) : DRDeepExt k)).mono (Set.empty_subset _)

lemma drDHi_definable :
    (Set.univ : Set ℝ).Definable LRc (drDHi (k := k)) := by
  have h := definable_le_LRc (σ := DRDeepExt k) (MvPolynomial.X (Sum.inr (0 : Fin 2) : DRDeepExt k))
    (MvPolynomial.C 2 * MvPolynomial.X (Sum.inl (dβ (k := k)) : DRDeepExt k) *
      MvPolynomial.X (Sum.inl (dx (k := k)) : DRDeepExt k))
  have hset : {u : DRDeepExt k → ℝ |
        (MvPolynomial.eval u) (MvPolynomial.X (Sum.inr (0 : Fin 2) : DRDeepExt k))
        ≤ (MvPolynomial.eval u) (MvPolynomial.C 2 *
          MvPolynomial.X (Sum.inl (dβ (k := k)) : DRDeepExt k) *
            MvPolynomial.X (Sum.inl (dx (k := k)) : DRDeepExt k))}
      = drDHi (k := k) := by
    ext u
    simp only [drDHi, Set.mem_ofPred_eq, MvPolynomial.eval_X, MvPolynomial.eval_C,
      MvPolynomial.eval_mul]
  rw [hset] at h
  exact h

/-! ## 4. `DeepBodyNeg` as a conjunction -/

lemma DeepBodyNeg_eq (B₀ : Set (Fin (k+1) → ℝ)) :
    DeepBodyNeg (k := k) B₀ = drDMemB (k := k) B₀ ∩ drDDiv (k := k) ∩
      drDLo (k := k) ∩ drDHi (k := k) := by
  ext h
  simp only [DeepBodyNeg, drDMemB, drDDiv, drDLo, drDHi, GrSub1,
    Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

lemma deepBodyNeg_definable {B₀ : Set (Fin (k+1) → ℝ)}
    (hB₀ : (∅ : Set ℝ).Definable LRc B₀) :
    (Set.univ : Set ℝ).Definable LRc (DeepBodyNeg (k := k) B₀) := by
  have h1 := drDMemB_definable (k := k) hB₀
  have h2 := drDDiv_definable (k := k)
  have h3 := drDLo_definable (k := k)
  have h4 := drDHi_definable (k := k)
  rw [DeepBodyNeg_eq (k := k) B₀]
  exact ((h1.inter h2).inter h3).inter h4

/-! ## 5. The theorem -/

theorem DRDeep_definable {k : ℕ} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.DRDeep B₀) := by
  have hbody : (Set.univ : Set ℝ).Definable LRc ((DeepBodyNeg (k := k) B₀)ᶜ) :=
    (deepBodyNeg_definable (k := k) hB₀).compl
  have hset : (DRDeep (k := k) B₀)
      = {v : DRIdx k → ℝ | ∀ u : Fin 2 → ℝ, Sum.elim v u ∈ (DeepBodyNeg (k := k) B₀)ᶜ} := by
    ext g
    simp only [DRDeep, Set.mem_ofPred_eq, Set.mem_compl_iff]
  have huniv : (Set.univ : Set ℝ).Definable LRc (DRDeep (k := k) B₀) := by
    rw [hset]
    exact hbody.forall_of_finite (α := DRIdx k) (β := Fin 2)
  exact (definable_univ_iff_empty).mp huniv

end Work.WilC4
