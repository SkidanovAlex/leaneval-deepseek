import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseBoxFock.NH_eq_dGamma
import Submission.Work.BoseBoxFock.slotPairDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dGamma_pairWord` — the commutator of two rank-one `dGamma`s

For one-particle rank-one operators `|w⟩⟨v|` (`Work.BoseBoxFock.rankOnePair`), the
second quantisation `dGamma m` is the two-letter ladder word
(`Work.BoseBoxFock.dGamma_rankOnePair`)

    `dGamma m (|w⟩⟨v|) = creOf m w ∘ annOf m v`.

`dGamma m` is *not* multiplicative: the defect is exactly the contraction of the
annihilator of the first factor with the creator of the second.  In the normal
ordering, with `T₁ = |w₁⟩⟨v₁|`, `T₂ = |w₂⟩⟨v₂|`,

    `dGamma T₁ ∘ dGamma T₂ − dGamma (T₁ ∘ T₂) = creOf w₁ ∘ creOf w₂ ∘ annOf v₁ ∘ annOf v₂`,

because `T₁ ∘ T₂ = gram v₁ w₂ • |w₁⟩⟨v₂|` (`Work.BoseBoxFock.rankOnePair_comp`,
`Work.BoseBoxFock.dGamma_smul`), while the mode CCR
(`Work.BoseB4.AnnOf_creOf_ccr`, FS `eq:Commutator_general`)

    `annOf m v₁ ∘ creOf m w₂ = creOf m w₂ ∘ annOf m v₁ + gram v₁ w₂ • 1`

shifts the second creator past the first annihilator at the price of the scalar
`gram v₁ w₂`, which is exactly the coefficient of `T₁ ∘ T₂`.  This is the model
form of the box identity `Work.BoseBoxFock.bW4slot_apply`'s normal-ordering step.

The reduction is abstract: in any `Module.End R M` over a commutative ring, if
`A₁ * C₂ = C₂ * A₁ + g • 1` then `(C₁ * A₁) * (C₂ * A₂) − g • (C₁ * A₂) = C₁ * (C₂ * (A₁ * A₂))`.

Everything here is `sorry`-free.
-/

noncomputable section

namespace Work.BoseBoxFock

open Work.BoseB4

/-! ## 1. The abstract normal-ordering step -/

/-- **The abstract commutator step.**  In the endomorphism ring `Module.End R M`, if the
commutator `[A₁, C₂] = g • 1` is a scalar multiple of the identity, then moving the creator
`C₂` to the left in `C₁ * A₁ * C₂ * A₂` produces exactly the counterterm `g • (C₁ * A₂)`. -/
private lemma end_pairWord {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (C₁ A₁ C₂ A₂ : Module.End R M) (g : R)
    (h : A₁ * C₂ = C₂ * A₁ + g • (1 : Module.End R M)) :
    (C₁ * A₁) * (C₂ * A₂) - g • (C₁ * A₂) = C₁ * (C₂ * (A₁ * A₂)) := by
  have h' : A₁ * C₂ - C₂ * A₁ = g • (1 : Module.End R M) := by
    rw [h]; abel
  calc (C₁ * A₁) * (C₂ * A₂) - g • (C₁ * A₂)
      = C₁ * (C₂ * (A₁ * A₂)) + C₁ * ((A₁ * C₂ - C₂ * A₁) * A₂) - g • (C₁ * A₂) := by
        noncomm_ring
    _ = C₁ * (C₂ * (A₁ * A₂)) + C₁ * ((g • (1 : Module.End R M)) * A₂) - g • (C₁ * A₂) := by
        rw [h']
    _ = C₁ * (C₂ * (A₁ * A₂)) := by
        rw [smul_mul_assoc, one_mul, mul_smul_comm]
        abel

/-! ## 2. The second quantisation of a product of two rank-one operators -/

/-- The second quantisation of the product of two rank-one operators, in normal-ordered
form: `dGamma (|w₁⟩⟨v₁| ∘ |w₂⟩⟨v₂|) = gram v₁ w₂ • (creOf w₁ ∘ annOf v₂)`. -/
private lemma dGamma_pair_lowRank {m : ℕ} (w₁ w₂ v₁ v₂ : Fin m → ℝ) :
    Work.BoseB4.dGamma m ((rankOnePair w₁ v₁).comp (rankOnePair w₂ v₂))
      = (Work.BoseB4.gram v₁ w₂) • ((Work.BoseB4.creOf m w₁).comp (Work.BoseB4.annOf m v₂)) := by
  rw [rankOnePair_comp, dGamma_smul, dGamma_rankOnePair]
  simp only [Work.BoseB4.gram]

/-! ## 3. The target -/

theorem dGamma_pairWord {m : ℕ} (w₁ w₂ v₁ v₂ : Fin m → ℝ) :
    (Work.BoseB4.dGamma m (Work.BoseBoxFock.rankOnePair w₁ v₁)).comp
        (Work.BoseB4.dGamma m (Work.BoseBoxFock.rankOnePair w₂ v₂))
      - Work.BoseB4.dGamma m ((Work.BoseBoxFock.rankOnePair w₁ v₁).comp
          (Work.BoseBoxFock.rankOnePair w₂ v₂))
      = (Work.BoseB4.creOf m w₁).comp ((Work.BoseB4.creOf m w₂).comp
          ((Work.BoseB4.annOf m v₁).comp (Work.BoseB4.annOf m v₂))) := by
  rw [dGamma_rankOnePair w₁ v₁, dGamma_rankOnePair w₂ v₂, dGamma_pair_lowRank]
  change (Work.BoseB4.creOf m w₁ * Work.BoseB4.annOf m v₁)
      * (Work.BoseB4.creOf m w₂ * Work.BoseB4.annOf m v₂)
      - Work.BoseB4.gram v₁ w₂ • (Work.BoseB4.creOf m w₁ * Work.BoseB4.annOf m v₂)
      = Work.BoseB4.creOf m w₁
        * (Work.BoseB4.creOf m w₂ * (Work.BoseB4.annOf m v₁ * Work.BoseB4.annOf m v₂))
  exact end_pairWord _ _ _ _ _ (Work.BoseB4.AnnOf_creOf_ccr v₁ w₂)

end Work.BoseBoxFock
