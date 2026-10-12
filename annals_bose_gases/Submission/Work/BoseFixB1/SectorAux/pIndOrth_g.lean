import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BddSector.pIndOrthBdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.SectorAux.pIndOrth_g`

The **orthogonality of the FS box projection to its complement** in the *measurable, bounded-on-the-box*
regularity needed by the bounded-sector argument (the `_g` family: `Φ` only measurable and bounded on
`abox N ℓ`, instead of the continuous version `Work.BoseFixB1S.Auxiliary.pIndOrth`).

With `Pᵢ = Work.UBBInputs8.boxPInd volA A i Φ` (FS `eq:HBU`, the box indicator in slot `i` times the
`A`-mean over that slot) and `1_A(· i)Φ − PᵢΦ` the complementary piece of `1_A(· i)Φ = (1_A(· i)Φ − PᵢΦ) + PᵢΦ`,
the claim is `∫_{abox N ℓ} PᵢΦ · (1_A(· i)Φ − PᵢΦ) = 0`.

Identical to `Work.BoseFixB1.BddSector.pIndOrthBdd`, which the corpus proves by reducing the integrand
to `Φ·PᵢΦ − (PᵢΦ)²` pointwise and identifying `∫ Φ·PᵢΦ = ∫ (PᵢΦ)²` through the `L¹`-regularity
self-adjointness `Work.BoseFixB1.boxPInd_adjoint_int` plus the idempotence
`Work.BoseFixB1.boxPInd_self_idem` — the measurable/bounded replacement for the continuous-case
`Work.BoseFixB1S.Q0C.one_self_N`.  We reuse that proved identity.
-/

namespace Work.BoseFixB1.SectorAux

theorem pIndOrth_g {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x)
          * ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
              - Work.UBBInputs8.boxPInd volA A i Φ x)) = 0 :=
  Work.BoseFixB1.BddSector.pIndOrthBdd hℓ hvol hA hvolA hAc i hΦm hΦb

end Work.BoseFixB1.SectorAux
