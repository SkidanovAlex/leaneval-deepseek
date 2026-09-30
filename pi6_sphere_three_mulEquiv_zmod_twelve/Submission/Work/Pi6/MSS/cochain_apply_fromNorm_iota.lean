import Mathlib
import Submission.Work.Cohomology.CupRing
import Submission.Work.Pi6.MSS.normalizedCoboundary
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.MSS

noncomputable section

/-- Degree-independent form of `PInfty_fixed_of_kills_degenerate`: a cochain killing all
degenerate `n`-simplices is fixed by the projection `PInfty`. -/
lemma PInfty_fixed_of_kills_degenerate' (𝕜 : Type) [Field 𝕜] (X : SSet.{0}) (n : ℕ)
    (β : Work.Cohomology.Cochain 𝕜 X n)
    (hv : ∀ y : X.obj (Opposite.op (SimplexCategory.mk n)), y ∈ X.degenerate n →
      Work.Cohomology.genEval 𝕜 X β y = 0) :
    (ModuleCat.ofHom β : (X.chainComplex (ModuleCat.of 𝕜 𝕜)).X n ⟶ ModuleCat.of 𝕜 𝕜)
      = (DoldKan.PInfty (X := X ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).f n
        ≫ ModuleCat.ofHom β := by
  cases n with
  | zero => simp
  | succ m => exact PInfty_fixed_of_kills_degenerate 𝕜 X m β hv

/-- A cochain `β` which vanishes on degenerate `n`-simplices has the same value on the raw
normalized generator `ιNormalizedChainComplex x` (of the normalized chain complex, mapped back
into the alternating face map complex by `fromNormalizedChainComplex`) as on the raw simplex chain
`ιChainComplex x`. -/
theorem cochain_apply_fromNorm_iota (𝕜 : Type) [Field 𝕜] (X : SSet.{0}) (n : ℕ)
    (x : X.obj (Opposite.op (SimplexCategory.mk n))) (β : Work.Cohomology.Cochain 𝕜 X n)
    (hdeg : ∀ y : X.obj (Opposite.op (SimplexCategory.mk n)), y ∈ X.degenerate n →
      β ((ModuleCat.Hom.hom (X.ιChainComplex (R := ModuleCat.of 𝕜 𝕜) y)) 1) = 0) :
    β ((ModuleCat.Hom.hom ((SSet.fromNormalizedChainComplex X (ModuleCat.of 𝕜 𝕜)).f n))
        ((ModuleCat.Hom.hom (X.ιNormalizedChainComplex (R := ModuleCat.of 𝕜 𝕜) x)) 1))
      = β ((ModuleCat.Hom.hom (X.ιChainComplex (R := ModuleCat.of 𝕜 𝕜) x)) 1) := by
  have hkey := congrArg (fun (g : ModuleCat.of 𝕜 𝕜 ⟶
      (X.chainComplex (ModuleCat.of 𝕜 𝕜)).X n) => ModuleCat.Hom.hom g 1)
    (SSet.ιNormalizedChainComplex_fromNormalizedChainComplex_f (X := X)
      (R := ModuleCat.of 𝕜 𝕜) x)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hkey
  rw [hkey]
  have hP := PInfty_fixed_of_kills_degenerate' 𝕜 X n β hdeg
  have hPc := congrArg (fun (g : (X.chainComplex (ModuleCat.of 𝕜 𝕜)).X n ⟶
      ModuleCat.of 𝕜 𝕜) =>
      ModuleCat.Hom.hom g ((ModuleCat.Hom.hom (X.ιChainComplex (R := ModuleCat.of 𝕜 𝕜) x)) 1))
    hP
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at hPc
  exact hPc.symm

end

end Work.Pi6.MSS
