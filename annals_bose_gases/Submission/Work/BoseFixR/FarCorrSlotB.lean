import ChallengeDeps
import Submission.Work.BoseFixR.EpsCorrArith
import Submission.Work.BoseFixR.EpsFarCorrLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/FarCorrSlotB.lean` — a slack variant of the `ε`-correction slot

The far leg pays the `ε`-correction out of the crude budget `ErrRes` through the scalar
comparison `256·ρ·ε^{-1/2}·a·𝓜 ≤ ErrRes v μ ρ`
(`Work.BoseFixR.EpsCorrArith`, FS §9 `lem:Roughbounds`, `eq:Rough2`).

This module records the *weaker* constant-`16` form of that comparison, in the shape in
which the far-leg assembly consumes it: `16·ρ·ε^{-1/2}·a·𝓜 ≤ ErrRes v μ ρ / 4`, i.e.
`64·ρ·ε^{-1/2}·a·𝓜 ≤ ErrRes v μ ρ`, which is immediate from the `256`-form because
`64 ≤ 256` and `ρ·ε^{-1/2}·a·𝓜 ≥ 0` (`ρ ≥ 0`, `a v > 0`, `𝓜 ≥ 0`, and `ε^{-1/2} ≥ 0` as a
nonnegative real power of `ε = √(𝓜/((ρ+μ)ℓ³)) ≥ 0`).

The only input beyond `EpsCorrArith` is `ℓ = ell v μ > 0`, which is
`Work.BoseBox.sideAt_pos` at the FS parameters.
-/

namespace Work.BoseFixR

/-- `ℓ = ell v μ = sideAt μ (a v) > 0` at the FS parameters, used to instantiate the
scalar comparisons of the far leg. -/
lemma ell_pos_farCorrSlotB {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) : 0 < ell v μ :=
  Work.BoseBox.sideAt_pos hμ hav

/-- The slack form of the far-leg `ε`-correction comparison: the constant-`16` version
`16·ρ·ε^{-1/2}·a·𝓜 ≤ ErrRes v μ ρ / 4` of `Work.BoseFixR.EpsCorrArith`'s
`256·ρ·ε^{-1/2}·a·𝓜 ≤ ErrRes v μ ρ`. -/
theorem FarCorrSlotB {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < BoseGases.a v)
    {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 ≤ ρ) :
    16 * ρ * (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v
        * Work.BoseFixR.bigMV v μ
      ≤ Work.BoseFixR.ErrRes v μ ρ / 4 := by
  have hℓ : 0 < ell v μ := ell_pos_farCorrSlotB hμ hav
  -- nonnegativity of the correction monomial
  have he : 0 ≤ (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hX : 0 ≤ ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v * bigMV v μ :=
    mul_nonneg (mul_nonneg (mul_nonneg hρ he) hav.le) (bigMV_nonneg hμ hav)
  -- the `256`-form of `EpsCorrArith`, in grouped shape
  have h256 := EpsCorrArith (v := v) hμ hav hρ hℓ
  rw [show (256 : ℝ) * ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v * bigMV v μ
      = 256 * (ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v * bigMV v μ) by ring]
    at h256
  rw [show (16 : ℝ) * ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v * bigMV v μ
      = 16 * (ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v * bigMV v μ) by ring]
  linarith

end Work.BoseFixR
