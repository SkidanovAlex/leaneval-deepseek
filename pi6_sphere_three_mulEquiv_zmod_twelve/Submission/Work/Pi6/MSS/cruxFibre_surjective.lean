import Mathlib
import Submission.Work.Pi6.MSS.CruxDefs
import Submission.Work.SSSR.exists_cycleMk
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The fibre comparison of the mixed-product formula is surjective.**

The map `cruxFibre` sends a cycle `z` of the fibre chain complex over the vertex `σ(0)` of a simplex
`σ : Δ[s] ⟶ Sing B` to the element of `coefM p e₀ q = H_q(F_{p e₀})` obtained by transporting its
homology class along the trivialisation `triv p e₀ hfib hconn` of the local system
`b ↦ H_q(p⁻¹b)`.  Since that trivialisation is an isomorphism and every homology class has a cycle
representative, `cruxFibre` is a surjection.

Concretely: given `w`, apply the inverse of the isomorphism
`triv ... σ ≪≫ (triv ... (p e₀)).symm : H_q(F_{σ(0)}) ≅ H_q(F_{p e₀})` to `w`, realise the resulting
homology class by a cycle `z` (`Work.SSSR.exists_cycleMk`), and cancel the two isomorphisms. -/
theorem cruxFibre_surjective (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (w : Work.SSSR.coefM (R := 𝕜) p e₀ q) :
    ∃ (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q)
      (hz : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).d q
        ((ComplexShape.down ℕ).next q) z = 0),
      Work.Pi6.MSS.cruxFibre 𝕜 p e₀ hfib hconn s q σ z hz = w := by
  -- The trivialisation comparison `H_q(F_{σ(0)}) ≅ H_q(F_{p e₀})` attached to `σ`.
  obtain ⟨z, hz, hy⟩ := Work.SSSR.exists_cycleMk (R := 𝕜)
    (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)) q
    ((Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (Work.SSS.sigmaVert σ) ≪≫
      (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).symm).inv.hom w)
  refine ⟨z, hz, ?_⟩
  unfold Work.Pi6.MSS.cruxFibre
  rw [← hy]
  exact LinearEquiv.apply_symm_apply
    (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (Work.SSS.sigmaVert σ) ≪≫
      (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).symm).toLinearEquiv w

end Work.Pi6.MSS
