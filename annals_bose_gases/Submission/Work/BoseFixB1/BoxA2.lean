import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxQWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# FS's pairing word `A₂` at the box projections (`Work.BoseFixB1.boxA2`)

FS `eq:DefQ2`/`lm:appinteractionestimate` keep the *pairing* term
`A₂ = ½Σ_{i≠j}(P_{B,i}P_{B,j}w_{1,B}(x_i,x_j)Q_{B,j}Q_{B,i} + h.c.)` **displayed** on the right
of their interaction estimate: it is *not* paid by the excited-count error `Ca(μ+n₀|B|⁻¹)n₊`
(FS pay it later, by the kinetic word, in `lm:appbogolubov`).  At the box projections the
pairing is the *fourth summand* of `Work.BoseFixB1S.boxQ2`
(`Σ_p ∫(P_{p.1}P_{p.2}Φ)(Q_{p.2}Q_{p.1}Φ)w₁(x_{p.1},x_{p.2})`), which this module names.

Rationale (`PERBOXF_ANALYSIS.md` §20/§22/§26): any statement of the form
"`q₁+…+q₄ ≥ −C(a v)(μ+ρ₀)n₊`" — with the pairing *removed* — is false at `n = 1`, because the
`q₁`-µ-cross term is linear in the excited amplitude while the error is quadratic; the
compensation is FS's `eq:Q1n0`/completing-the-square, and it needs both the displayed pairing
and the `Q₀`-side (the `A₀` defect).  The rung-4 statement
(`Work.BoseFixB1.boxQSum_ge_a0Main_add_A2`) therefore bounds the **whole** `boxQSum` with
`boxA2` displayed.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **FS's pairing word `A₂` at the box projections `B(u)`** — the fourth summand of
`Work.BoseFixB1S.boxQ2`:

    boxA2 = Σ_{i≠j} ∫_{abox} (P_iP_jΦ)(x)·(Q_jQ_iΦ)(x)·w₁(x_i,x_j) .

(FS write it as `½Σ(P_iP_j w₁ Q_jQ_i + h.c.)`; for real `Φ` the Hermitian conjugate doubles the
quadratic form, so the plain sum is the same object.) -/
noncomputable def boxA2 {N : ℕ} (ℓ volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) (Φ : X N → ℝ) : ℝ :=
  ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
    (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
      * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
      * w1 (x p.1) (x p.2)

/-- `boxQ2` is the three cross fragments plus the pairing word `boxA2`. -/
theorem boxQ2_eq_fragments_add_boxA2 {N : ℕ} (volA ℓ μ : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) (Φ : X N → ℝ) :
    Work.BoseFixB1S.boxQ2 volA ℓ μ A w1 w2 Φ
      = (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
              * (Work.UBBInputs8.boxPInd volA A p.2
                  (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
              * w2 (x p.1) (x p.2))
          + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxQInd volA A p.2
                    (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
                * w2 (x p.1) (x p.2))
          - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * (w1Fibre ℓ w1 (x i)))
        + boxA2 ℓ volA A w1 Φ := by
  -- `boxA2` is *definitionally* the fourth summand of `boxQ2`, so the identity is the
  -- associativity regrouping of `boxQ2`'s displayed sum of four real terms.
  rw [Work.BoseFixB1S.boxQ2, boxA2]

end Work.BoseFixB1
