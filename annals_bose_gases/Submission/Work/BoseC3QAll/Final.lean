import Mathlib.Data.Real.Basic
import Submission.Work.BoseC3QAll.errA_le
import Submission.Work.BoseC3QAll.estQ3fourA
import Submission.Work.BoseC3QAll.estQ3oneA
import Submission.Work.BoseC3QAll.estQ3twoThreeAd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7AK.Final` — FS `thm:Control3Q` with absolute constants

The unconditional end-to-end theorem of the chapter.  All the pieces are proved:

* `ErrALe` (`errA_le`), the arithmetic leg;
* `EstQ3oneA` (`estQ3oneA`), FS `eq:EstimateQ3Tilde1`;
* `EstQ3twoThreeA` (`estQ3twoThreeA`), FS `eq:EstimateQ3Tilde2+3`;
* `EstQ3fourA` (`estQ3fourA`), FS `eq:EstimateQ3Tilde4`;
* `SplitQ3A` (`Glue.splitQ3A`), the Bogoliubov split and `𝓁² ≤ 1`;
* and the assembly `Assembly.control3QA_of_three` /
  `Glue.control3QA_of_estimates_and_arithmetic`.

`control3QA` is FS `thm:Control3Q` (`eq:Q3Cancels`) with the **absolute** constant
`1`: for every `K₀` and `b₀ > 0` there is `t₀ > 0` such that for every Fock
system `F`, θ-mode data `T`, parameter point `E` and every `Φ` in the
`n₊`-window,

`⟨Φ, controlWord Φ⟩ ≥ −μ²aℓ³(μa³)^{1/2+1/323}·‖Φ‖²`

whenever `μa³ ≤ t₀`, `b ≥ b₀` and the kernel interface `Q3KernelFSAll K₀ F T E`
holds.  Neither `C` nor `t₀` is defined from an instance, and no statement of
the chapter mentions an `L ≥ 1` or a bound `R ≤ L·c`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

open Work.BoseB7

universe u v

/-- **FS `thm:Control3Q` (`eq:Q3Cancels`) with absolute constants**: there are
`C = 1` and `t₀ > 0`, depending only on `(K₀, b₀)`, such that for every Fock
system, every `Q3KernelFSAll` and every state in the `n₊`-window,
`⟨Φ, controlWord Φ⟩ ≥ −controlErrA·‖Φ‖²`. -/
theorem control3QFS (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Control3QFS.{u, v} K₀ b₀ hb₀ :=
  control3QFS_of_estimates_and_arithmetic.{u, v} K₀ b₀ hb₀
    (estQ3oneA K₀ b₀ hb₀) (estQ3twoThreeA K₀ b₀ hb₀) (estQ3fourA K₀ b₀ hb₀)
    (fun C₁ C₂₃ C₄ => errA_le b₀ hb₀ C₁ C₂₃ C₄)

end Work.BoseC3QAll
