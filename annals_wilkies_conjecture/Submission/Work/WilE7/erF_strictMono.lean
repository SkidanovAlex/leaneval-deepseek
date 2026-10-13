import Mathlib
import Submission.Work.WilE7.SelDefs

namespace Work.WilE7

/-- Mathlib inverts `Real.tanh` on `(-1,1)` by the strictly monotone `Real.artanh`, but does
not record the strict monotonicity of `tanh` itself; it follows because `artanh` cannot reverse
a strict inequality. -/
private theorem strictMono_tanh : StrictMono Real.tanh := by
  intro a b hab
  have ha : Real.tanh a ∈ Set.Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh a, Real.tanh_lt_one a⟩
  have hb : Real.tanh b ∈ Set.Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh b, Real.tanh_lt_one b⟩
  rw [← Real.artanh_lt_artanh_iff ha hb]
  simpa [Real.artanh_tanh] using hab

/-- `erF` (defined by `⊥ ↦ -1`, `⊤ ↦ 1`, and `x ↦ Real.tanh x` on the finite part, see
`Submission/Work/WilE7/SelDefs.lean`, namespace `Work.WilE7`) is strictly increasing as a map
`EReal → ℝ`; together with `erF_continuous` this makes it the order isomorphism of `EReal` onto
`[-1,1]`.  In particular the strict monotonicity on the finite part is `StrictMono Real.tanh`
(which Mathlib does not provide directly, but which follows from `Real.strictMonoOn_artanh`,
`Real.artanh_tanh`, `Real.neg_one_lt_tanh`, `Real.tanh_lt_one`). -/
theorem erF_strictMono : StrictMono Work.WilE7.erF := by
  intro a b hab
  induction a using EReal.rec with
  | bot =>
    -- `⊥ ↦ -1`, and every other value of `erF` is `> -1`
    induction b using EReal.rec with
    | bot => exact absurd hab not_lt_bot
    | coe y => simpa using Real.neg_one_lt_tanh y
    | top => norm_num
  | coe x =>
    -- `x ↦ tanh x`, and `erF` takes values in `(-1,1]` above `tanh x`
    induction b using EReal.rec with
    | bot => exact absurd hab not_lt_bot
    | coe y =>
      have hxy : x < y := EReal.coe_lt_coe_iff.mp hab
      simpa using strictMono_tanh hxy
    | top => simpa using Real.tanh_lt_one x
  | top => exact absurd hab not_top_lt

end Work.WilE7
