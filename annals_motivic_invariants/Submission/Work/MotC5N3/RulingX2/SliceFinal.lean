import Submission.Work.MotC5N3.RulingX2.SliceMain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

namespace Work.MotC5N3.RulingX2

open MvPolynomial

/-- **`ZiasSliceNeTop`, proved directly.**  The `X 2 = 1` plane meets the AS residual curve: the
slice of `ZIAS a b g` at `X 2 = 1` is the ideal spanned by the five slice cubics, and that ideal is
contained in the proper ideal `(Phisq, Gam, PhatPoly)`. -/
theorem ZiasSliceNeTop_aux (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hab : a * b ≠ 0)
    (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    Work.MotAS.ZIAS a b g ⊔
      Ideal.span {(MvPolynomial.X 2 - (1 : MvPolynomial (Fin 3) K))} ≠ ⊤ := by
  refine Work.MotAS.ASRulV2.zias_shift_reduce K (Work.MotAS.ZIAS a b g) ?_
  change Ideal.map (Work.MotC5N3.slicePhi K) (Work.MotAS.ZIAS a b g) ≠ ⊤
  rw [Slice.map_slicePhi_ZIAS K a b g]
  exact Slice.slice_ne_top K a b g ha hab

end Work.MotC5N3.RulingX2
