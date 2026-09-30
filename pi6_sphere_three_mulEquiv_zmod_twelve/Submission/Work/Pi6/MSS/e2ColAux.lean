import Mathlib
import Submission.Work.Pi6.MSS.e2Aux
import Submission.Work.Pi6.MSS.AssembleCore
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.convPage
import Submission.Work.Pi6.MSS.pagesData
import Submission.Work.Pi6.MSS.pageUnitSpec
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# Auxiliary machinery for the fibre-edge map of the column of the Serre spectral sequence

This file starts the **from-scratch** route to `Work.Pi6.MSS.e2Col_exists` (the column map
`H^q(F) → E_2^{0,q}`): the deliverable currently derives its three clauses from
`Work.Pi6.MSS.e2Mul` (see the docstring there and `e2Col_exists.lean`), which is circular with the
plan of using `e2Col_exists` to *prove* `e2Mul`.  The from-scratch route defines the **fibre-edge
map**

`rho : pEraw 𝕜 (serreCF 𝕜 E B p) 2 0 q →ₗ[𝕜] Coh 𝕜 (fibre p (p e₀)) q`

by restricting a `Z_2^0`-cochain to the fibre (this is well defined because `pDen 2 0 q` consists
of cochains vanishing on the fibre and of coboundaries), and then proves:

* `rho` is a **unital ring map** (page product ↦ cup): `resCochain_cup` + `pd_mulZ_val`;
* `rho` is **injective** — `Work.Pi6.MSS.e2Col_fibre_kernel` (delegated; the geometric content:
  if the restriction of a `Z_2^0`-cochain to the fibre is a coboundary then the cochain already
  vanishes in `E_2^{0,q}`, by propagating the vanishing from the fibre `F_{b₀}` to all fibres along
  paths using `δx ∈ F²`);
* `rho` is **surjective** — either from the additive fibre-edge isomorphism
  (`Work.Pi6.MSS.e2Add`, whose `s = 0` instance is `Nonempty (pEraw 2 0 q ≅ Coh 𝕜 F q)`) plus
  finite-dimensionality, or by an explicit "spreading" construction;
* hence `col := rho⁻¹` is a unital ring map and clauses 1, 2 of `e2Col_exists` follow; clause 3
  additionally needs `range (mssColIter 𝕜 E B p q q) = {classes of genuine cocycles}` (a page
  chase using `conv_pZ_eq`, `mssCol_spec`, `mssProj_inj_col`) together with
  `rho (class of a cocycle w) = j^* w`.

What is already here and compiles: the cochain-level restriction `resCochain` (the dual of
`SSet.chainComplexMap (sSing (fibreIncl p (p e₀)))`) and its evaluation rule `genEval_resCochain`.
The remaining steps are `resCochain_d` (chain-map commutation), `resCochain_cup`
(`cup_apply'` + `frontFace_app`/`backFace_app`), the fact that `coFilt 𝕜 (sSingP p) 1 q` is
contained in the kernel of the restriction (needs `ess` of a fibre simplex: use
`Work.SSSR.sSingP_fibreIncl_comp` and `ess = 0` for a constant simplex), and the descent of
`resCochain` to the page.
-/

namespace Work.Pi6.MSS
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial Topology

noncomputable section

variable (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
  (p : C(E, B)) (e₀ : E)

/-- The cochain-level restriction of cochains of `E` to the fibre. -/
def resCochain (q : ℕ) :
    Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q →ₗ[𝕜]
      Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q where
  toFun := fun α => α.comp ((SSet.chainComplexMap
    (Work.SSS.sSingP (Work.StemsB.fibreIncl p (p e₀))) (ModuleCat.of 𝕜 𝕜)).f q).hom
  map_add' := by
    intro a b
    apply Work.Cohomology.genEval_ext
    intro σ
    simp only [Work.Cohomology.genEval, LinearMap.add_comp, LinearMap.comp_apply,
      map_add, LinearMap.add_apply]
  map_smul' := by
    intro c a
    apply Work.Cohomology.genEval_ext
    intro σ
    simp only [Work.Cohomology.genEval, LinearMap.smul_comp, LinearMap.comp_apply,
      RingHom.id_apply, map_smul, LinearMap.smul_apply]

@[simp]
theorem genEval_resCochain (q : ℕ) (α : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q)
    (σ : (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) _⦋q⦌) :
    Work.Cohomology.genEval 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) (resCochain 𝕜 E B p e₀ q α) σ =
      Work.Cohomology.genEval 𝕜 (Work.SSS.sSing E) α
        ((Work.SSS.sSingP (Work.StemsB.fibreIncl p (p e₀))).app (Opposite.op ⦋q⦌) σ) := by
  show α (((SSet.chainComplexMap (Work.SSS.sSingP (Work.StemsB.fibreIncl p (p e₀))) (ModuleCat.of 𝕜 𝕜)).f q).hom
      (((Work.SSS.sSing (Work.StemsB.fibre p (p e₀))).ιChainComplex (R := ModuleCat.of 𝕜 𝕜) σ).hom 1)) = _
  rw [← ConcreteCategory.comp_apply,
    SSet.ι_chainComplexMap_f (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) (Work.SSS.sSing E) (Work.SSS.sSingP (Work.StemsB.fibreIncl p (p e₀)))
      (ModuleCat.of 𝕜 𝕜) σ]
  rfl


/-- The restriction map commutes with the coboundary. -/
theorem resCochain_d (q : ℕ) (α : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q) :
    resCochain 𝕜 E B p e₀ (q + 1) (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) α) =
      Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))
        (resCochain 𝕜 E B p e₀ q α) := by
  show (α.comp (((Work.SSS.sSing E).chainComplex (ModuleCat.of 𝕜 𝕜)).d (q + 1) q).hom).comp
      ((SSet.chainComplexMap (Work.SSS.sSingP (Work.StemsB.fibreIncl p (p e₀)))
        (ModuleCat.of 𝕜 𝕜)).f (q + 1)).hom
    = (α.comp ((SSet.chainComplexMap (Work.SSS.sSingP (Work.StemsB.fibreIncl p (p e₀)))
        (ModuleCat.of 𝕜 𝕜)).f q).hom).comp
      (((Work.SSS.sSing (Work.StemsB.fibre p (p e₀))).chainComplex
        (ModuleCat.of 𝕜 𝕜)).d (q + 1) q).hom
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc]
  congr 1
  rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp]
  exact congrArg ModuleCat.Hom.hom (HomologicalComplex.Hom.comm (SSet.chainComplexMap
    (Work.SSS.sSingP (Work.StemsB.fibreIncl p (p e₀))) (ModuleCat.of 𝕜 𝕜)) (q + 1) q)

/-- The restriction map is a ring homomorphism for the Alexander–Whitney cup product. -/
theorem resCochain_cup (q q' : ℕ)
    (α : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q)
    (β : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q') :
    resCochain 𝕜 E B p e₀ (q + q')
        (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) α β) =
      Work.Cohomology.cup 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))
        (resCochain 𝕜 E B p e₀ q α) (resCochain 𝕜 E B p e₀ q' β) := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [genEval_resCochain, Work.Cohomology.cup_apply', Work.Cohomology.cup_apply',
    genEval_resCochain, genEval_resCochain, Work.Pi6.MSS.frontFace_app,
    Work.Pi6.MSS.backFace_app]

end

end Work.Pi6.MSS
