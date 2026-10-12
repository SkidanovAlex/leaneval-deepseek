import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.UBB.Arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBB

open Work.UBB Submission.BoseGases BoseGases

set_option linter.style.haveILetI false

/-- **From the per-state spectral input to its infimum form.**

If every *low* state `Φ` of the box `(N, L)` at density `ρ := dens N L`
(shifted energy density at most the a-priori threshold `Theta A J ρ`) already
obeys the target bound `Lambda A C η₀ ρ ≤ WordDens N L ρ v h Φ`, then the same
bound holds for the infimum `wordInf N L ρ v h` over all box states.

The two side hypotheses are exactly the arithmetic ones: `0 ≤ A` and `0 ≤ C`
(to have non-negative prefactors) together with `J ≥ c = 128/(15√π)`, which
makes the a-priori threshold dominate the target (`theta_ge_lambda`).  A state
that is *not* low has shifted energy density strictly above `Theta ≥ Lambda`,
so it satisfies the bound without any spectral input. -/
theorem lambda_le_wordInf_of_spectral {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {J C ε₀ η₀ A : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hJ : Work.UBB.lhyC ≤ J)
    (hspec : ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * A ^ 3 ≤ ε₀ →
      ∀ Φ : CSBox N L,
        WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta A J (dens N L) →
        Lambda A C η₀ (dens N L) ≤ WordDens N L (dens N L) v h (Φ : X N → ℝ)) :
    ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * A ^ 3 ≤ ε₀ →
      Lambda A C η₀ (dens N L) ≤ wordInf N L (dens N L) v h := by
  intro L hL N hN
  have hLpos : (0 : ℝ) < L := by linarith
  haveI : Nonempty (CSBox N L) := nonempty_CSBox N hLpos
  have hρ : 0 ≤ dens N L := dens_nonneg N (le_of_lt hLpos)
  -- the a-priori threshold dominates the target
  have hkey : Lambda A C η₀ (dens N L) ≤ Theta A J (dens N L) :=
    theta_ge_lambda hA hρ hC hJ
  unfold wordInf
  refine le_ciInf (fun Φ => ?_)
  by_cases hlow :
      WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta A J (dens N L)
  · -- a low state: use the spectral input
    exact hspec L hL N hN Φ hlow
  · -- a high state: it already dominates `Theta`, hence `Lambda`
    exact le_trans hkey (le_of_lt (not_le.mp hlow))

end Work.UBB
