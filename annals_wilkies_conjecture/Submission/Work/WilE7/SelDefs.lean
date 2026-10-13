/-
  Vocabulary for `Work.WilE7.exists_continuous_selection`.

  The selection `m` between two continuous `EReal`-valued functions `a < b` is built from an
  order isomorphism of `EReal` onto `[-1,1]`: on the finite part it is `Real.tanh`, and it sends
  `⊥ ↦ -1`, `⊤ ↦ 1`.  Its inverse on the open interval `(-1,1)` is `Real.artanh`, which is
  already in Mathlib together with `Real.tanh_artanh`.

  This file only fixes the vocabulary; the global properties of `erF` (`Continuous`,
  `StrictMono`) are proved in the sibling files `erF_continuous` and `erF_strictMono`.
-/
import Mathlib

namespace Work.WilE7

/-- The strictly increasing map `EReal → ℝ` sending `⊥` to `-1`, `⊤` to `1` and the finite
extended real `x` to `tanh x`.  With `Real.artanh` as its inverse on `(-1,1)` it turns the
pointwise condition `a x < b x` into an ordinary real inequality. -/
noncomputable def erF : EReal → ℝ := EReal.rec (-1) Real.tanh 1

@[simp] theorem erF_bot : erF ⊥ = -1 := rfl

@[simp] theorem erF_coe (x : ℝ) : erF (x : EReal) = Real.tanh x := rfl

@[simp] theorem erF_top : erF ⊤ = 1 := rfl

end Work.WilE7
