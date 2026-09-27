import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.pairStabDefs

/-!
# `Work.Mostow.pairStab_pairStab` -- the stabiliser of two distinct boundary points

For two distinct boundary points `ξ ≠ η` of `ℍⁿ` there is a point `p` (namely `pairPoint ξ η`,
the foot of the perpendicular from the base point `0` to the geodesic joining `ξ` and `η`)
such that every `g : PO n 1` fixing `ξ` and `η` translates `p` by `|busemann ξ (g • 0)|`,
and such that a third fixed boundary point forces the Busemann cocycle `busemann ξ (g • 0)`
to vanish.

The proof normalises with the two null vectors `θ ξ = (ξ,1)`, `θ η = (η,1)`: fixing `ξ`
(resp. `η`) makes `θ ξ` (resp. `θ η`) an eigenvector of the lift `emat g` with eigenvalue
`lam` (resp. `μ`), and `hdist p (g • p) = |log lam|`, while a third fixed point forces
`lam = μ`, hence `lam = 1` and `busemann ξ (g • 0) = 0`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Matrix
open scoped Matrix

theorem pairStab_pairStab (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (ξ η : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) (hne : ξ ≠ η) :
    ∃ p : E n, ∀ g : PO n 1, bd g ξ = ξ → bd g η = η →
      hdist p (g • p) = |busemann ξ (g • (0 : E n))| ∧
      ∀ ζ ∈ Sph n, ζ ≠ ξ → ζ ≠ η → bd g ζ = ζ → busemann ξ (g • (0 : E n)) = 0 := by
  refine ⟨pairPoint ξ η, ?_⟩
  intro g hgξ hgη
  obtain ⟨lam, hlamne, hlam⟩ := emat_eigen_of_bd g hξ hgξ
  obtain ⟨μ, hμne, hμ⟩ := emat_eigen_of_bd g hη hgη
  have hlamμ : lam * μ = 1 := eigen_mul_eq_one g hξ hη hne hlam hμ
  obtain ⟨hlev, hlampos, hbus⟩ := lev_emat_eigen g hξ hlam
  refine ⟨?_, ?_⟩
  · rw [hdist_pairPoint g ξ η hξ hη hne hlam hμ hlamμ hlampos, hbus, abs_neg]
  · intro ζ hζ hζξ hζη hgζ
    obtain ⟨ρ, hρne, hρ⟩ := emat_eigen_of_bd g hζ hgζ
    have hlamμeq : lam = μ := eigen_eq_of_third g hξ hη hζ hζξ hζη hlam hμ hρ
    have hsq : lam ^ 2 = 1 := by
      have h : lam * lam = 1 := by
        rw [← hlamμeq] at hlamμ
        exact hlamμ
      rwa [pow_two]
    have hlam1 : lam = 1 := by
      rcases sq_eq_one_iff.1 hsq with h | h
      · exact h
      · rw [h] at hlampos; norm_num at hlampos
    rw [hbus, hlam1, Real.log_one, neg_zero]

end Work.Mostow
