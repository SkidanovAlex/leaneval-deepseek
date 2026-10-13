import Mathlib
import Submission.Work.WilC5.LogDefSetModel
import Submission.Work.WilC5.LogFunMap
import Submission.Work.WilC5.expE_add_of_model
import Submission.Work.WilC5.posE_mulE_of_model

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Work.WilC5

/-!
  The definable logarithm (`ExpLog.lean`, whose graph is `logDefSet`) is additive on positive
  elements in every model of `TE = Th(ℝ_exp)`:

      `log(x * y) = log x + log y`   for `0 < x`, `0 < y`.

  Since `logDefSet` is the graph of a *function* in a model of `TE`
  (`LogDefSetModel.lean`, `logFun_spec_of_model` / `logDefSet_unique_of_model`), it suffices to
  show `logDefSet (x * y) (log x + log y)`.  Unfolding, this means

  * `0 < x * y` — the product of two positive elements is positive
    (`Work.WilC5.posE_mulE_of_model`), and
  * `exp (log x + log y) = x * y` — the additive law of the exponential
    (`Work.WilC5.expE_add_of_model`) together with `exp (log x) = x` and `exp (log y) = y`
    (`Work.WilC5.expE_logFun_of_pos` below).

  All three are `LEc`-sentences true in `ℝ`, hence hold in every model of `TE`.
-/

/-- **`exp (log x) = x` for a positive `x` in a model of `TE`.**  Directly from the definition of
`logDefSet` (`LogDefSetModel.lean`): the second (non-positive) clause is excluded by positivity. -/
theorem expE_logFun_of_pos {M : Type} [WilkiesDesign.CG.LEc.Structure M]
    (hM : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE) {x : M}
    (hx : Work.WilC5.leE Work.WilC5.zeroE x ∧ ¬ Work.WilC5.leE x Work.WilC5.zeroE) :
    Work.WilC5.expE (Work.WilC5.logFun x) = x := by
  have h := Work.WilC5.logFun_spec_of_model hM x
  rw [Work.WilC5.logDefSet] at h
  rcases h with ⟨_, he⟩ | ⟨hne, _⟩
  · exact he
  · exact absurd hx hne

theorem logFun_mul {M : Type} [FirstOrder.Language.Structure WilkiesDesign.CG.LEc M]
    (hM : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE) {x y : M}
    (hx : Work.WilC5.leE Work.WilC5.zeroE x ∧ ¬ Work.WilC5.leE x Work.WilC5.zeroE)
    (hy : Work.WilC5.leE Work.WilC5.zeroE y ∧ ¬ Work.WilC5.leE y Work.WilC5.zeroE) :
    Work.WilC5.logFun (Work.WilC5.mulE x y) =
      Work.WilC5.addE (Work.WilC5.logFun x) (Work.WilC5.logFun y) := by
  -- `log (x*y)` is a logarithm of `x*y` (`logFun_spec_of_model`), and so is `log x + log y`;
  -- uniqueness (`logDefSet_unique_of_model`) identifies them.
  have hspec := Work.WilC5.logFun_spec_of_model hM (Work.WilC5.mulE x y)
  have hkey : Work.WilC5.logDefSet (Work.WilC5.mulE x y)
      (Work.WilC5.addE (Work.WilC5.logFun x) (Work.WilC5.logFun y)) := by
    refine Or.inl ⟨posE_mulE_of_model hM hx hy, ?_⟩
    rw [expE_add_of_model hM, expE_logFun_of_pos hM hx, expE_logFun_of_pos hM hy]
  exact Work.WilC5.logDefSet_unique_of_model hM hspec hkey

end Work.WilC5
