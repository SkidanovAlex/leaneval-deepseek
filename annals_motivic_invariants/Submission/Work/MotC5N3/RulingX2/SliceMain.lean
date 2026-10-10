import Submission.Work.MotC5N3.RulingX2.SlicePhi
import Submission.Work.MotC5N3.RulingX2.ZiasSliceGamMem
import Submission.Work.MotC5N3.RulingX2.ZiasSliceGamNeTop
import Submission.Work.MotC5N3.RulingX2.ZiasSliceFhatEq
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASRulV2.zias_shift_reduce

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

/-- The `X 2 = 1` slice of the AS residual ideal is spanned by the five slice cubics. -/
theorem Slice.map_slicePhi_ZIAS (K : Type) [Field K] [CharP K 5] (a b g : K) :
    Ideal.map (Work.MotC5N3.slicePhi K) (Work.MotAS.ZIAS a b g)
      = Ideal.span (Set.range (Slice.fhatF a b g)) := by
  rw [Work.MotAS.ZIAS, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
    refine ⟨k, ?_⟩
    change Slice.fhatF a b g k = Work.MotC5N3.slice a b g k
    exact (ZiasSliceFhatEq K a b g k).symm
  · rintro ⟨k, rfl⟩
    refine ⟨Work.MotAS.zcubAS a b g k, ⟨k, rfl⟩, ?_⟩
    change Work.MotC5N3.slice a b g k = Slice.fhatF a b g k
    exact ZiasSliceFhatEq K a b g k

/-- **The slice ideal is proper** — the numerical heart of the argument. -/
theorem Slice.slice_ne_top (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hab : a * b ≠ 0) :
    Ideal.span (Set.range (Slice.fhatF a b g)) ≠ ⊤ := by
  intro htop
  have hsub : Ideal.span (Set.range (Slice.fhatF a b g)) ≤
      Ideal.span {Slice.Phisq a b g, Slice.Gam a b g, Slice.PhatPoly a b g} := by
    rw [Ideal.span_le]
    rintro x ⟨k, rfl⟩
    exact ZiasSliceGamMem K a b g ha hab k
  have hI : Ideal.span {Slice.Phisq a b g, Slice.Gam a b g, Slice.PhatPoly a b g} = ⊤ := by
    apply top_unique
    rw [← htop]
    exact hsub
  exact ZiasSliceGamNeTop K a b g ha hab hI

end Work.MotC5N3.RulingX2
