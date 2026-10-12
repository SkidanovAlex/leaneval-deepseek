import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseBoxFock.SymBlocks
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open scoped BigOperators

/-- Splitting a lattice sum of a three-term summand with a constant scalar.  (The
grouping of the summand is the left-associated one, exactly as in the body of
`KzBogC`.) -/
private lemma SymKzBogC_sum_smul_add3 {Mode : Type*} [Fintype Mode]
    {M : Type*} [AddCommMonoid M] [Module ℂ M] (c : ℂ) (X Y Z : Mode → M) :
    (∑ k : Mode, c • (X k + Y k + Z k))
      = (∑ k : Mode, c • X k) + (∑ k : Mode, c • Y k) + ∑ k : Mode, c • Z k := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_add, smul_add]

theorem SymKzBogC_blocks {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ)
    (hτ : ∀ k : Mode, E.tau (-k) = E.tau k)
    (hχ : ∀ k : Mode, E.hatChi (-k) = E.hatChi k)
    (hW : ∀ k : Mode, E.W1 (-k) = E.W1 k) :
    Work.BoseBoxFock.KzBogC f E ρ =
      Work.BoseBoxFock.Bkin f E + (ρ : ℂ) • Work.BoseBoxFock.BNW f E
      + (((1 / 2) * ρ : ℝ) : ℂ) • Work.BoseBoxFock.BPa f E
      + (((1 / 2) * ρ : ℝ) : ℂ) • Work.BoseBoxFock.BPc f E
      + ((((ρ - E.mu) * E.W1 0 * Real.sqrt (ρ * E.ell ^ 3)) : ℝ) : ℂ)
          • (Work.BoseBoxFock.BchiC (Finset.univ : Finset Mode) E.hatChi 1 f
              + Work.BoseBoxFock.BchiA (Finset.univ : Finset Mode) E.hatChi 1 f) := by
  -- The three rows of `KzBogC` are split off, and each is normalised separately:
  --   (1) the number row `τ(k) + ρŴ₁(k)` against `n_k + n_{-k}` uses that `τ`, `Ŵ₁`
  --       are even (reindexing `k ↦ −k`) and gives `Bkin + ρ•BNW`;
  --   (2) the pairing row gives `(ρ/2)•BPa + (ρ/2)•BPc` (no evenness needed);
  --   (3) the `χ̂` row uses the evenness of `χ̂` (reindexing `k ↦ −k`) and gives the
  --       `χ̂`-blocks with the constant `(ρ − μ)Ŵ₁(0)√(ρℓ³)`.
  have e1 : (∑ k : Mode, ((1 / 2 : ℝ) : ℂ) •
        ((((E.tau k + ρ * E.W1 k : ℝ)) : ℂ) • (nOpC (f k) + nOpC (f (-k)))))
      = Bkin f E + (ρ : ℂ) • BNW f E := by
    rw [← Finset.smul_sum, ← sum_smul_const_left, sum_neg_smul_add]
    have hcoef : ∀ k : Mode, (((1 / 2 : ℝ) : ℂ) * ((E.tau k + ρ * E.W1 k : ℝ) : ℂ)
        + ((1 / 2 : ℝ) : ℂ) * ((E.tau (-k) + ρ * E.W1 (-k) : ℝ) : ℂ)) • nOpC (f k)
        = (((E.tau k : ℝ) : ℂ) + ((ρ * E.W1 k : ℝ) : ℂ)) • nOpC (f k) := by
      intro k
      rw [hτ k, hW k]
      congr 1
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun k _ => hcoef k)]
    rw [sum_add_smul_split, Bkin, BNW]
    congr 1
    rw [← sum_smul_const_left (c := (↑ρ : ℂ)) (b := fun k => ((E.W1 k : ℝ) : ℂ))
        (X := fun k => nmF f k)]
    exact Finset.sum_congr rfl (fun k _ => by simp only [nOpC, nmF]; congr 1; push_cast; ring)
  have e2 : (∑ k : Mode, ((1 / 2 : ℝ) : ℂ) •
        ((((ρ * E.W1 k : ℝ)) : ℂ) • ((annOfE (f k)).comp (annOfE (f (-k)))
          + (creOfE (f k)).comp (creOfE (f (-k))))))
      = (((1 / 2) * ρ : ℝ) : ℂ) • BPa f E + (((1 / 2) * ρ : ℝ) : ℂ) • BPc f E := by
    have h2 : (∑ k : Mode, (((ρ * E.W1 k : ℝ)) : ℂ) • ((annOfE (f k)).comp (annOfE (f (-k)))
        + (creOfE (f k)).comp (creOfE (f (-k)))))
        = (↑ρ : ℂ) • BPa f E + (↑ρ : ℂ) • BPc f E := by
      rw [BPa, BPc, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [smul_add, smul_smul, smul_smul]
      congr 1
      · congr 1; push_cast; ring
      · congr 1; push_cast; ring
    rw [← Finset.smul_sum, h2, smul_add, smul_smul, smul_smul]
    congr 1
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring
  have e3 : (∑ k : Mode, ((1 / 2 : ℝ) : ℂ) •
        (((((ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3) : ℝ)) : ℂ) •
          (annOfE (f k) + creOfE (f k) + annOfE (f (-k)) + creOfE (f (-k)))))
      = ((((ρ - E.mu) * E.W1 0 * Real.sqrt (ρ * E.ell ^ 3)) : ℝ) : ℂ) •
          (BchiC (Finset.univ : Finset Mode) E.hatChi 1 f
            + BchiA (Finset.univ : Finset Mode) E.hatChi 1 f) := by
    have hchi : (∑ k : Mode, ((E.hatChi k : ℝ) : ℂ) • (annOfE (f k) + creOfE (f k)))
        = BchiC (Finset.univ : Finset Mode) E.hatChi 1 f
          + BchiA (Finset.univ : Finset Mode) E.hatChi 1 f := by
      rw [BchiC, BchiA, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [smul_add, one_mul]
      abel
    have h3a : (∑ k : Mode, ((((ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3) : ℝ)) : ℂ) •
          (annOfE (f k) + creOfE (f k) + annOfE (f (-k)) + creOfE (f (-k))))
        = ((2 : ℂ) * ((((ρ - E.mu) * E.W1 0 * Real.sqrt (ρ * E.ell ^ 3)) : ℝ) : ℂ)) •
            (BchiC (Finset.univ : Finset Mode) E.hatChi 1 f
              + BchiA (Finset.univ : Finset Mode) E.hatChi 1 f) := by
      rw [sum_neg_smul_four]
      have hcoef : ∀ k : Mode,
          ((((ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3) : ℝ)) : ℂ)
          + ((((ρ - E.mu) * E.W1 0 * E.hatChi (-k) * Real.sqrt (ρ * E.ell ^ 3) : ℝ)) : ℂ)
          = ((2 : ℂ) * ((((ρ - E.mu) * E.W1 0 * Real.sqrt (ρ * E.ell ^ 3)) : ℝ) : ℂ)) * ↑(E.hatChi k) := by
        intro k
        rw [hχ k]
        push_cast
        ring
      rw [Finset.sum_congr rfl (fun k _ => by rw [hcoef k])]
      rw [sum_smul_const_left
        (c := (2 : ℂ) * ((((ρ - E.mu) * E.W1 0 * Real.sqrt (ρ * E.ell ^ 3)) : ℝ) : ℂ))
        (b := fun k => ((E.hatChi k : ℝ) : ℂ)) (X := fun k => annOfE (f k) + creOfE (f k)), hchi]
    rw [← Finset.smul_sum, h3a, smul_smul]
    rw [show (((1 / 2 : ℝ) : ℂ)
          * ((2 : ℂ) * ((((ρ - E.mu) * E.W1 0 * Real.sqrt (ρ * E.ell ^ 3)) : ℝ) : ℂ)))
        = ((((ρ - E.mu) * E.W1 0 * Real.sqrt (ρ * E.ell ^ 3)) : ℝ) : ℂ) by push_cast; ring]
  rw [KzBogC]
  rw [SymKzBogC_sum_smul_add3 (c := ((1 / 2 : ℝ) : ℂ))
    (X := fun k => ((((E.tau k + ρ * E.W1 k : ℝ)) : ℂ) • (nOpC (f k) + nOpC (f (-k)))))
    (Y := fun k => ((((ρ * E.W1 k : ℝ)) : ℂ) • ((annOfE (f k)).comp (annOfE (f (-k)))
          + (creOfE (f k)).comp (creOfE (f (-k))))))
    (Z := fun k => (((((ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3) : ℝ)) : ℂ) •
          (annOfE (f k) + creOfE (f k) + annOfE (f (-k)) + creOfE (f (-k)))))]
  rw [e1, e2, e3]
  abel

end Work.BoseBoxFock
