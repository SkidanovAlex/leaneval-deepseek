import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairDecompPairSetGen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotPairRowsAux` — the `1st`-quantised expansion of the FS `Q₂` row

Holder: `Submission/Work/BoseBoxFock/PotPairRows_exists.lean`.

`Work.BoseBoxFock.potPairRows` (`PotGroupDefs.lean`) is the `Q₂` group of FS
`lem:2ndQuand`: the `(W₁+W₁ω)a₀†a_k†a_ka₀` row, the Bogoliubov row and the
`(L₀+L₁)∘Σ_k a_k†a_k` row, all built from *compositions* of the first-quantised slot sums
`B(T) = boxSlotSum e T`.  The first step of the row's evaluation is the **slot
decomposition** of `B(T₁)∘B(T₂)` into its diagonal part `B(T₁∘T₂)` and the off-diagonal
`pairSet` sum; `Work.BoseBoxFock.pairDecompPairSetGen` (PROVED) supplies it for the two
rank-one operators, so the first two blocks of `potPairRows` collapse to explicit
`Σ_{p ∈ pairSet n}` sums of *two-slot* pairings.

The third block is **not** of the difference form (`B(rankOne evec0) ∘ B(rankOne (f k))` has no
subtracted term), so it keeps its two slot sums: it is the `n₀·n_k` / `−μ n_k` row.

This module is the entry point of the evaluation: after it, every summand of the row is a
`boxSlotOf`-chain, on which the slot dictionary
(`boxSlotOf_evec0_fk_eq`, `boxSlotOf_fk_evec0_eq`, `boxSlotOf_fk_fk_eq`,
`boxSlotOf_evec_zero_eq_aPC`, `qVec_eq_etaOf_of_pairing`) and then the finite lattice sum act.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-- **The slot (`pairSet`) decomposition of the `Q₂` row.**  For a measurable, everywhere bounded
`Θ` and the weak mode bundle (measurable / everywhere bounded / box-supported / orthonormal), the
`Q₂` row at the slot sum `B = boxSlotSum e` expands as

* the `(W₁+W₁ω)` block: `Σ_{p∈pairSet n} boxSlotOf e e₀ (f k) p.1 (boxSlotOf e (f k) e₀ p.2 Θ)`;
* the Bogoliubov block: the two sums
  `Σ_p boxSlotOf e e₀ (f k) p.1 (boxSlotOf e e₀ (f (−k)) p.2 Θ)` and
  `Σ_p boxSlotOf e (f k) e₀ p.1 (boxSlotOf e (f (−k)) e₀ p.2 Θ)`;
* the `(L₀+L₁)` block, unchanged except that `rankOne` is `rankOnePair · ·`.

Every summand is now a two-slot chain; this is the normal form on which the slot dictionary of
`Submission/Work/BoseBoxFock/boxSlotOf_*_eq.lean` acts. -/
theorem potPairRows_pairSet {m n : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode]
    [Fintype Mode] [DecidableEq Mode] {ℓ : ℝ} (e : Fin m → Ω → ℂ)
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode)
    (Θ : Xn n → ℂ) (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    potPairRows (fun T => boxSlotSum e T) f E Θ
      = (E.ell ^ (-(3 : ℝ))) • (∑ k : Mode, (E.W1 k + E.W1omega k) •
            (∑ p ∈ Submission.BoseGases.pairSet n,
              boxSlotOf e (evec0 m) (f k) p.1 (boxSlotOf e (f k) (evec0 m) p.2 Θ)))
        + ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ))) • (∑ k : Mode, E.W1 k •
            ((∑ p ∈ Submission.BoseGases.pairSet n,
                boxSlotOf e (evec0 m) (f k) p.1
                  (boxSlotOf e (evec0 m) (f (-k)) p.2 Θ))
              + (∑ p ∈ Submission.BoseGases.pairSet n,
                boxSlotOf e (f k) (evec0 m) p.1
                  (boxSlotOf e (f (-k)) (evec0 m) p.2 Θ))))
        + (∑ k : Mode,
            ((E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
                (boxSlotSum e (rankOnePair (evec0 m) (evec0 m))
                  (boxSlotSum e (rankOnePair (f k) (f k)) Θ))
              - (E.mu * E.W1 0) • (boxSlotSum e (rankOnePair (f k) (f k)) Θ))) := by
  have h1 : ∀ k : Mode,
      (E.W1 k + E.W1omega k) •
        (boxSlotSum e (rankOnePair (evec0 m) (f k))
            (boxSlotSum e (rankOnePair (f k) (evec0 m)) Θ)
          - boxSlotSum e ((rankOnePair (evec0 m) (f k)).comp
              (rankOnePair (f k) (evec0 m))) Θ)
      = (E.W1 k + E.W1omega k) •
        (∑ p ∈ Submission.BoseGases.pairSet n,
          boxSlotOf e (evec0 m) (f k) p.1 (boxSlotOf e (f k) (evec0 m) p.2 Θ)) := by
    intro k
    rw [pairDecompPairSetGen hmeas hbdd hsupp horth (evec0 m) (f k) (f k) (evec0 m)
      Θ hΘm hΘb]
  have h2 : ∀ k : Mode,
      E.W1 k •
        ((boxSlotSum e (rankOnePair (evec0 m) (f k))
              (boxSlotSum e (rankOnePair (evec0 m) (f (-k))) Θ)
            - boxSlotSum e ((rankOnePair (evec0 m) (f k)).comp
                (rankOnePair (evec0 m) (f (-k)))) Θ)
          + (boxSlotSum e (rankOnePair (f k) (evec0 m))
                (boxSlotSum e (rankOnePair (f (-k)) (evec0 m)) Θ)
              - boxSlotSum e ((rankOnePair (f k) (evec0 m)).comp
                  (rankOnePair (f (-k)) (evec0 m))) Θ))
      = E.W1 k •
        ((∑ p ∈ Submission.BoseGases.pairSet n,
            boxSlotOf e (evec0 m) (f k) p.1 (boxSlotOf e (evec0 m) (f (-k)) p.2 Θ))
          + (∑ p ∈ Submission.BoseGases.pairSet n,
            boxSlotOf e (f k) (evec0 m) p.1 (boxSlotOf e (f (-k)) (evec0 m) p.2 Θ))) := by
    intro k
    rw [pairDecompPairSetGen hmeas hbdd hsupp horth (evec0 m) (f k) (evec0 m) (f (-k))
        Θ hΘm hΘb,
      pairDecompPairSetGen hmeas hbdd hsupp horth (f k) (evec0 m) (f (-k)) (evec0 m)
        Θ hΘm hΘb]
  have h3 : ∀ k : Mode,
      ((E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
          (boxSlotSum e (rankOne (evec0 m)) (boxSlotSum e (rankOne (f k)) Θ))
        - (E.mu * E.W1 0) • (boxSlotSum e (rankOne (f k)) Θ))
      = ((E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
          (boxSlotSum e (rankOnePair (evec0 m) (evec0 m))
            (boxSlotSum e (rankOnePair (f k) (f k)) Θ))
        - (E.mu * E.W1 0) • (boxSlotSum e (rankOnePair (f k) (f k)) Θ)) :=
    fun _ => rfl
  simp only [potPairRows, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Finset.sum_apply,
    Function.comp_apply]
  rw [Finset.sum_congr rfl (fun k _ => h1 k),
    Finset.sum_congr rfl (fun k _ => h2 k),
    Finset.sum_congr rfl (fun k _ => h3 k)]

end Work.BoseBoxFock
