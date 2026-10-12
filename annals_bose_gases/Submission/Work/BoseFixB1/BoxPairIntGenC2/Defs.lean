import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxPairIntGen.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxPairIntGenC2.Defs` — the indicator-free box pair fibre

The peeled box pair fibre of `Work.BoseFixB1.boxPairFibreFun` is

    `boxPairFibreFun volA ℓ A Φ i j y z
       = ∫_{r2 ∈ abox N ℓ} boxPInd_i(boxPInd_j Φ)(ins2 i j' y z r2)
                            · boxQInd_j(boxQInd_i Φ)(ins2 i j' y z r2)`,

where `boxPInd_i = 1_A(x_i)·M_i`, `boxQInd_i = 1_A(x_i)·(1 − M_i)` and `M_i` is the
(unwindowed) slot mean over `A` (`Work.BoseFixB1.boxIndMean`).  Because `i ≠ j`, both
indicators produced by the two projections sit on the two distinguished slots `i`, `j`
whose values are `y`, `z`, and the whole integrand factors as

    `1_A(y)·1_A(z)·(M_i M_j Φ)(x)·((1 − M_i)(1 − M_j)Φ)(x)`,

the second factor being the inner product of the two slot-projections, i.e.

  `Φ(x) − M_iΦ(x) − M_jΦ(x) + M_j(M_iΦ)(x)`.

`boxPairFibreFree` below is that *indicator-free* factor: it is a smooth function of
`(y,z)` whenever `Φ` is smooth (the parametric integral over the compact box `abox N ℓ` of
a jointly smooth integrand).  This is the object whose smoothness drives the `C²`
smoothness of the box pair density `Work.BoseFixB1.boxPairDensSum` when the window `χ` is
only twice differentiable: in the density, the window `χ` absorbs the two factors `1_A`
(use `hχsupp : z ∉ A → χ z = 0`), so the density integrand is `χ(z+u)χ(z)` times the
smooth quantity `boxPairFibreFree`.

The factorisation itself (with the indicators restored) is
`Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFun_eq_indicator_mul_free`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1.BoxPairIntGenC2

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The indicator-free peeled box pair fibre at the slots `(i, i.succAbove j')` and the
distinguished values `y`, `z`: the `abox N ℓ`-integral of the product of the two
indicator-free slot projections `M_i M_j Φ` and `(1 − M_i)(1 − M_j)Φ` (with `M_k` the
unwindowed slot mean `Work.BoseFixB1.boxIndMean` over the region `A`). -/
noncomputable def boxPairFibreFree {N : ℕ} (volA ℓ : ℝ) (A : Set E3)
    (Φ : Submission.BoseGases.X (N + 2) → ℝ) (i : Fin (N + 2)) (j' : Fin (N + 1))
    (y z : E3) : ℝ :=
  ∫ r2 in Submission.BoseGases.abox N ℓ,
    (Work.BoseFixB1.boxIndMean volA A i
        (Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ)
        (Submission.BoseGases.ins2 i j' y z r2))
      * (Φ (Submission.BoseGases.ins2 i j' y z r2)
          - Work.BoseFixB1.boxIndMean volA A (i.succAbove j') Φ
              (Submission.BoseGases.ins2 i j' y z r2)
          - Work.BoseFixB1.boxIndMean volA A i Φ
              (Submission.BoseGases.ins2 i j' y z r2)
          + Work.BoseFixB1.boxIndMean volA A (i.succAbove j')
              (Work.BoseFixB1.boxIndMean volA A i Φ)
              (Submission.BoseGases.ins2 i j' y z r2))

end Work.BoseFixB1.BoxPairIntGenC2
