import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Submission.Work.BlockBound4.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The named rung of Door 4: the D1 input as a bundle field

R3 (`diagW_block_bound_of_D1`, `smallbox_block_bound_diagW`) is stated over the
bundle `DiagWD1BoxData`, which carries — on top of all the standing fields of
`DiagWBoxData` — the D1 conclusion in the *pure-pairing* shape consumed by the
`cS1 > 0` chain `diagW_cS1_pos_chain`:

    −½(1+η)·D·m²/s³ − Bq − Eq·n₊ ≤ pDiagForm s (fsKinCoeff c₀) Φ + q4PairWord Φ ,

at the data's own `η := d4Eta`, `Bq := d4Bracket`, `Eq := d4BogErr` and at FS's
mass coefficient `m² = d4MassCoeff (N+1) s = (N̂+1)N̂/s³` (`N̂ = N+1` the particle
count).

The field is **count-universal** (`∀ N ≥ 1`): FS's `lm:appbogolubov` has no
count restriction, and the FS-shaped statement `smallbox_block_bound_diagW`
needs the rung at the *group* counts `n′`, `n″` of the grouping trick, not only
at the datum's own count.

The only part of the rung that is not count-uniform is the *state*, which lives
on `X (N+1)` and is normalised in `abox (N+1) D.s`.

Nothing else in the door is a rung: the superadditivity half is PROVED
(`Work.BlockBound4.door4Superadd`), the potential side and the convexity
arithmetic are PROVED in the corpus.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BlockBound4

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The Door-4 D1 rung at a datum** (count-universal), in the pure-pairing
shape of the `cS1 > 0` chain: `pDiagForm + q4PairWord` dominates the negative
mass term, D1's error bracket and D1's `n₊`-coefficient. -/
def diagWD1Prop (D : DiagWBoxData) : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (Φ : X (N + 1) → ℝ), ContDiff ℝ ∞ Φ →
    (∫ x in abox (N + 1) D.s, (Φ x) ^ 2) = 1 →
    -((1 / 2) * (1 + d4Eta D.Ct D.R0 D.s D.c₀ D.v) * (g0w0Mass (v := D.v) D.h)
        * d4MassCoeff (N + 1) D.s)
      - d4Bracket D.Ct N D.s D.c₀ D.v
      - d4BogErr D.Ct N D.s D.v * cnPlus D.s Φ
    ≤ pDiagForm D.s (fsKinCoeff D.c₀) Φ + q4PairWord (ℓ := D.s) (v := D.v) D.h (Φ := Φ)

/-- **The Door-4 bundle with the D1 rung named.**  All of `DiagWBoxData`'s
fields, plus FS's `lm:appbogolubov` at the faithful word (in the shape the chain
consumes), uniformly in the particle count. -/
structure DiagWD1BoxData extends DiagWBoxData where
  /-- the D1 rung (count-universal) -/
  hD1 : diagWD1Prop toKinPBoxData

lemma DiagWD1BoxData.d1 (D : DiagWD1BoxData) : diagWD1Prop D.toKinPBoxData := D.hD1

end Work.BlockBound4
