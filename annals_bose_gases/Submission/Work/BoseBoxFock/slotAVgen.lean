import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.slotFactsComp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotAVgen` — the *sector-friendly* form of the box twin of `H2ndF`

The box twin `Work.BoseBoxFock.AVf` of `H2ndF` is a nested sum of *ladder* words.  For the BF3c
selection it has to be replaced by an operator whose every summand is a **one-body slot sum**
`B T = boxSlotSum e T`, a **composition of two** of them, or the identity — because only those are
sector local (`Work.BoseBoxFock.SlotFacts`).

`AVgen B idop` is that operator, parametrised by the one-body slot operator `B` and the identity
`idop` so that *one* definition serves both sides of the selection: the box side
(`B T = boxSlotSum e T`, `idop = id`) and the slice side (`B T = slotSumSub e T S`, `idop = id`).

Two rows of `H2ndF` are **redistributed** with respect to `AVf` (they agree with `AVf` on every
*good* state, which is all the physical dictionary needs, but not as operators on arbitrary
functions): the `L₀/L₁`-linear rows and the `n₀n₊` row, whose `(L₀+L₁) ∘ Σ_k` is written as
`Σ_k ((L₀+L₁) ∘ ·)`.  This is forced by the *additivity* of the slot sums, which holds only on good
states.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

open Work.BoseB4 Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable {m : ℕ} [NeZero m]

/-- The **sector-friendly box twin** of `H2ndF`, parametrised by the one-body slot operator `B`
and the identity operator `idop` of the underlying state space `(ι → Ω) → ℂ`.

* `B T` plays the role of `boxSlotSum e T` (one-body rows) and of `dGamma m T`;
* a *pair* row is the composition `(B T₁) ∘ (B T₂)`, minus `B (T₁ ∘ T₂)`;
* `idop` plays the role of the model identity (the constant term of `L₀`).

Rows: kinetic `Σ_k τ_k B(|f_k⟩⟨f_k|)`; gap `(b/2ℓ²) B(1−n₀)`; `n₊^H`-gap; contact
`½ℓ⁻³(ĝ(0)+Ŵ₁ω(0)) (B(|e₀⟩⟨e₀|)² − B(|e₀⟩⟨e₀|²))`; chemical `−μĝ(0) n₀`; the
`(Ŵ₁+Ŵ₁ω)a₀†a_k†a_ka₀` row; the Bogoliubov pairs; the `χ̂`-linear and `χ̂²`-linear rows; the
`(L₀+L₁)∘Σ_k a_k†a_k` row (redistributed); the cubic `Q̃₃` row. -/
noncomputable def AVgen {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {ι : Type*} (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (idop : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (f g : Mode → Fin m → ℝ) (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ) :=
  (∑ k : Mode, E.tau k • (B (rankOne (f k))))
  + (E.b / (2 * E.ell ^ 2)) • (B (boxT0 m))
  + (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • (B T_NH)
  + ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ)) * (gHat0 + E.W1omega0)) •
      ((B (rankOne (evec0 m))) ∘ (B (rankOne (evec0 m)))
        - B ((rankOne (evec0 m)).comp (rankOne (evec0 m))))
  - (E.mu * gHat0) • (B (rankOne (evec0 m)))
  + (E.ell ^ (-(3 : ℝ))) • ∑ k : Mode, (E.W1 k + E.W1omega k) •
      ((B (rankOnePair (evec0 m) (f k))) ∘ (B (rankOnePair (f k) (evec0 m)))
        - B ((rankOnePair (evec0 m) (f k)).comp (rankOnePair (f k) (evec0 m))))
  + ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ))) • ∑ k : Mode, E.W1 k •
      (((B (rankOnePair (evec0 m) (f k))) ∘ (B (rankOnePair (evec0 m) (f (-k))))
          - B ((rankOnePair (evec0 m) (f k)).comp (rankOnePair (evec0 m) (f (-k)))))
        + ((B (rankOnePair (f k) (evec0 m))) ∘ (B (rankOnePair (f (-k)) (evec0 m)))
            - B ((rankOnePair (f k) (evec0 m)).comp (rankOnePair (f (-k)) (evec0 m)))))
  + ∑ k : Mode, E.hatChi k •
      ((E.ell ^ (-(3 : ℝ)) * E.W1 0) •
          ((B (rankOne (evec0 m))) ∘ (B (rankOnePair (f k) (evec0 m))))
        - (E.mu * E.W1 0) • (B (rankOnePair (f k) (evec0 m)))
        + ((E.ell ^ (-(3 : ℝ)) * E.W1 0) •
            ((B (rankOnePair (evec0 m) (f k))) ∘ (B (rankOne (evec0 m))))
          - (E.mu * E.W1 0) • (B (rankOnePair (evec0 m) (f k)))))
  + ∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s •
      ((E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
          ((B (rankOne (evec0 m))) ∘ (B (rankOnePair (g s) (evec0 m))))
        + (E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
            ((B (rankOnePair (evec0 m) (g s))) ∘ (B (rankOne (evec0 m)))))
  + ∑ k : Mode, ((E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
        ((B (rankOne (evec0 m))) ∘ (B (rankOne (f k))))
      - (E.mu * E.W1 0) • (B (rankOne (f k))))
  + (E.ell ^ (-(3 : ℝ))) • ∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ PHs,
      (E.fL s * E.W1 k) •
        (((B (rankOnePair (evec0 m) (f (s - k)))) ∘ (B (rankOnePair (g s) (f k))))
            - B ((rankOnePair (evec0 m) (f (s - k))).comp (rankOnePair (g s) (f k)))
          + ((B (rankOnePair (f k) (g s))) ∘ (B (rankOnePair (f (s - k)) (evec0 m))))
            - B ((rankOnePair (f k) (g s)).comp (rankOnePair (f (s - k)) (evec0 m))))

end Work.BoseBoxFock
