import Submission.Work.MotC5N3.RulingX2.SliceFinal

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3.RulingX2

/-- **The `X₂ = 1` chart leaf of the `hS` clause**, now *derived* rather than stated.

The proof is `ZiasSliceNeTop_aux` (`RulingX2/SliceFinal.lean`): `Slice.map_slicePhi_ZIAS` identifies
the slice of `ZIAS a b g` at `X 2 = 1` with the span of the five slice cubics (`ZiasSliceFhatEq`,
proved), `ASRulV2.zias_shift_reduce` transports properness, and `Slice.slice_ne_top` pushes it to the
three-generator ideal `(Phisq, Gam, PhatPoly)`.  The `sorryAx` of the char-5 wire therefore flows
through the two finer statements `Work.MotC5N3.RulingX2.ZiasSliceGamMem` and
`Work.MotC5N3.RulingX2.ZiasSliceGamNeTop` (see `RulingX2/NOTES_ZSST.md` and
`NOTE_MOTC5N3_LASTMILE_BRICKS.md`). -/
theorem ZiasSliceNeTop (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hab : a * b ≠ 0)
    (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    Work.MotAS.ZIAS a b g ⊔
      Ideal.span {(MvPolynomial.X 2 - (1 : MvPolynomial (Fin 3) K))} ≠ ⊤ :=
  ZiasSliceNeTop_aux K a b g ha hab hg

end Work.MotC5N3.RulingX2
