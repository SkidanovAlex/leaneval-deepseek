import Mathlib
import Submission.Work.TorsorExistence.Twist

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.TorsorExistence

/-- The cocycle `σ ↦ P` is `5`-torsion *before* passing to cohomology: it is the constant
cocycle with value the `5`-torsion point `D.PL ∈ E(L)`. -/
theorem five_smul_cocycle {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) :
    (5 : ℕ) • (⟨D.PL, D.norm_PL⟩ : D.cocycles) = 0 := by
  apply Subtype.ext
  simp [D.five_smul_PL]

/-- The class of the cocycle `σ ↦ P` in `H¹(ℤ/5, E(L)) = ker N / (σ - 1)E(L)` is
`5`-torsion: this is the "period divides `5`" half of the orbit-divisor statement (D) of the
paper's proof of Lemma `lem:torsors`. -/
theorem five_smul_cls {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) :
    (5 : ℕ) • D.cls = 0 := by
  calc (5 : ℕ) • D.cls
      = (QuotientAddGroup.mk' D.coboundaries) ((5 : ℕ) • ⟨D.PL, D.norm_PL⟩) :=
        (map_nsmul (QuotientAddGroup.mk' D.coboundaries) 5 ⟨D.PL, D.norm_PL⟩).symm
    _ = (QuotientAddGroup.mk' D.coboundaries) 0 := by rw [five_smul_cocycle D]
    _ = 0 := map_zero _

end Work.TorsorExistence
