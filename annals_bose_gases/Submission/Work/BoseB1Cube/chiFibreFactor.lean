import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB1Cube.chiFibreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Factorisation of the product of two `chiSmall` bumps into fibre kernels

`chiSmall M` is the L²-normalised cosine-`M`-th-power bump
`chiSmall M z = chiSmallNormFactor M * (ζ(z₀)ζ(z₁)ζ(z₂))^M`
(see `Submission.Work.ChiSmall`).  Because both the normalisation and the
product structure are *coordinatewise*, the product of two shifted bumps is a
positive constant times the coordinatewise product of the one-dimensional
fibre kernels `chiFibreK`:

    chiSmall M (a - u) · chiSmall M (b - u)
      = (chiSmallNormFactor M)² · ∏ j, chiFibreK M (a_j) (b_j) (u_j) .

This is the `Fubini over the fibre cube` bookkeeping step used by
`chiFibreProd`/`chiFibreMass`/`chiFibreWing`.
-/

noncomputable section

open scoped BigOperators

set_option linter.unusedVariables false

namespace Work.BoseB1Cube

/-- `chiSmall` is its normalisation factor times the unnormalised base bump. -/
lemma chiSmall_eq_normFactor_mul_base (M : ℕ) (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.chiSmall M z
      = Submission.BoseGases.chiSmallNormFactor M * Submission.BoseGases.chiSmallBase M z := by
  rw [Submission.BoseGases.chiSmall, Submission.BoseGases.chiSmallNormFactor,
    div_eq_mul_inv, mul_comm]

/-- **The coordinatewise product form of `chiSmall`**: the base bump is a product
over the three coordinates, so `chiSmall M z = chiSmallNormFactor M · ∏ j, ζ(z_j)^M`. -/
lemma chiSmall_eq_normFactor_mul_prod (M : ℕ) (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.chiSmall M z
      = Submission.BoseGases.chiSmallNormFactor M *
        ∏ j : Fin 3, Submission.BoseGases.zeta1d (z.ofLp j) ^ M := by
  rw [chiSmall_eq_normFactor_mul_base, Submission.BoseGases.chiSmallBase,
    Fin.prod_univ_three, mul_pow, mul_pow]

/-- **Fibre factorisation of the product of two `chiSmall` bumps.** -/
theorem chiFibreFactor {M : ℕ} (hM : 1 ≤ M) (a b u : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.chiSmall M (a - u) * Submission.BoseGases.chiSmall M (b - u)
      = (Submission.BoseGases.chiSmallNormFactor M) ^ 2
        * ∏ j : Fin 3, Work.BoseB1Cube.chiFibreK M (a.ofLp j) (b.ofLp j) (u.ofLp j) := by
  have hsub : ∀ j : Fin 3, (a - u).ofLp j = a.ofLp j - u.ofLp j := fun j => by simp
  have hsub' : ∀ j : Fin 3, (b - u).ofLp j = b.ofLp j - u.ofLp j := fun j => by simp
  rw [chiSmall_eq_normFactor_mul_prod M (a - u), chiSmall_eq_normFactor_mul_prod M (b - u)]
  simp only [hsub, hsub', chiFibreK, mul_pow, Fin.prod_univ_three]
  ring

end Work.BoseB1Cube
