import Mathlib
import Submission.Work.Kunneth.Basic
import Submission.Work.Kunneth.ezSummand
import Submission.Work.KunnethEZ.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Eilenberg–Zilber shuffle map

`Work.Kunneth.ezHom X Y n : (C_*(X) ⊗_ℤ C_*(Y))_n ⟶ C_n(X ⊗ Y)` is the Eilenberg–Zilber
(shuffle) map, whose `(p,q)`-summand is the bilinear extension of the shuffle chain
`Work.KunnethEZ.ezChain p q X Y` / `Work.Cohomology.Crux33.ezGen p q X Y σ τ`
(`Work.Kunneth.ezSummand`).  Its chain-map property (that it commutes with the Koszul
differential) is the companion statement `Work.Kunneth.ezHom_d`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The `(p,q)`-component of the Eilenberg–Zilber shuffle map, obtained from `ezSummand`. -/
noncomputable def ezSummandLin (X Y : SSet) (p q : ℕ) :
    tpSummand (sChain X) (sChain Y) p q →ₗ[ℤ] ↥((sChain (sProd X Y)).X (p + q)) :=
  Classical.choose (ezSummand X Y p q)

/-- The defining property of `ezSummandLin`. -/
theorem ezSummandLin_tmul (X Y : SSet) (p q : ℕ)
    (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    ezSummandLin X Y p q
        ((X.ιChainComplex (R := zz) σ).hom 1 ⊗ₜ[ℤ] (Y.ιChainComplex (R := zz) τ).hom 1)
      = Work.KunnethEZ.ezChain p q X Y ((X.ιChainComplex (R := zz) σ).hom 1)
          ((Y.ιChainComplex (R := zz) τ).hom 1) :=
  Classical.choose_spec (ezSummand X Y p q) σ τ

/-- The **Eilenberg–Zilber shuffle map** in degree `n`:
`⨁_{p+q=n} C_p(X) ⊗_ℤ C_q(Y) ⟶ C_n(X ⊗ Y)`. -/
noncomputable def ezHom (X Y : SSet) (n : ℕ) :
    (tChain X Y).X n ⟶ (sChain (sProd X Y)).X n :=
  ModuleCat.ofHom (DirectSum.toModule ℤ (tpIdx n) ↥((sChain (sProd X Y)).X n)
    (fun pq => ((eqToIso (congrArg (fun k => (sChain (sProd X Y)).X k) pq.2)).hom.hom).comp
      (ezSummandLin X Y pq.1.1 pq.1.2)))

end

end Work.Kunneth
