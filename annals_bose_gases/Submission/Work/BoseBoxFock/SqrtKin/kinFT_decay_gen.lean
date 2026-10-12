import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.SqrtKinDefs
import Submission.Work.OneBodyKin.kinFT_decay_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Polynomial decay of the one-body kinetic Fourier transform (`kinFT_decay_gen`)

For a smooth compactly supported `g : ℝ³ → ℂ` the `p`-convention Fourier transform
`kinFT g p = ∫_y e^{−i⟪p,y⟫} g y dy` (`Submission.BoseGases.kinFT`) decays faster than
any power of `‖p‖`: for every `n` there is `K ≥ 0` with `‖kinFT g p‖ ≤ K (1 + ‖p‖)^{-n}`.

This is the sharp form needed downstream (e.g. to make `p ↦ ‖p‖^j ‖kinFT g p‖²`
integrable for large `j`).  The mathematics is the standard one: `g` is a Schwartz function,
`𝓕 g` is Schwartz, so `‖𝓕 g ξ‖ ≲ (1 + ‖ξ‖)^{-n}`; converting to the corpus's `p`-convention
is the harmless rescaling `ξ = (2π)⁻¹ • p`.  That argument is carried out once for all in
`Work.OneBodyKin.kinFT_decay_le` (via `HasCompactSupport.toSchwartzMap`,
`SchwartzMap.fourierTransformCLM` and `SchwartzMap.one_add_le_sup_seminorm_apply`), and this
file is the interface the request needs.
-/

namespace Work.BoseBoxFock.SqrtKin

theorem kinFT_decay_gen {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖Submission.BoseGases.kinFT g p‖ ≤ K / (1 + ‖p‖) ^ n :=
  Work.OneBodyKin.kinFT_decay_le n hg hgc

end Work.BoseBoxFock.SqrtKin
