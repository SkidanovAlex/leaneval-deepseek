import Mathlib
import Submission.Work.Kunneth.CohKunneth.Value

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# Support of bidegree: the two elementary steps of the Künneth isomorphism

The cohomological Künneth isomorphism `Work.Kunneth.kunnethCoh_value` is the composite

`eEZ ≪≪ eHS ≪≪ eCT ≪≪ eC ≪≪ eUCT`

of `Submission/Work/Kunneth/CohKunneth/`.  The present file records the two *elementary* steps
that preserve the bidegree of a *cycle* along this composite: the "replace `D` by its homology"
step `Work.Kunneth.homSumDualMap` and the hom–tensor adjunction `Work.Kunneth.tpDualEquiv`.

* `Work.Kunneth.Asm.homSumDualMap_support`: the transpose of `tpMap 𝟙 ι` is *bidegree-preserving*
  on the level of the underlying cochains, so a cochain that annihilates all summands except the
  `pq`-th has an image with the same property;
* `Work.Kunneth.Asm.tpDualEquiv_support`: `Work.Kunneth.tpDualEquiv_apply_proj` shows that the
  `rs`-component of `tpDualEquiv C M n f` only depends on `f` composed with the `rs`-th structure
  map `tpLof`, so the same conclusion holds for the adjunction step.

These two lemmas are what upgrades the "diagonal" value rule of the Künneth isomorphism to the
full statement that `e (crossH a b)` is *supported* at the bidegree `(p,q)`.
-/

namespace Work.Kunneth.Asm

open CategoryTheory CategoryTheory.Limits HomologicalComplex Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization MonoidalCategory TensorProduct Simplicial

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The transpose of `Work.Kunneth.tpMap 𝟙 ι` preserves the bidegree support of a cochain. -/
theorem homSumDualMap_support {C D : ChainComplex (ModuleCat ℤ) ℕ} {M : ℕ → ModuleCat ℤ}
    (ι : Work.Kunneth.sumShift M ⟶ D) (n : ℕ) (pq : Work.Kunneth.tpIdx n)
    (γ : ↥((Work.Cohomology.dualComplex ℤ (Work.Kunneth.tpC C D)).X n))
    (hγ : ∀ rs : Work.Kunneth.tpIdx n, rs ≠ pq →
      γ.comp (Work.Kunneth.tpLof C D n rs) = 0)
    (rs : Work.Kunneth.tpIdx n) (hrs : rs ≠ pq) :
    (((Work.Kunneth.homSumDualMap (C := C) (D := D) ι).f n).hom γ).comp
      (Work.Kunneth.tpLof C (Work.Kunneth.sumShift M) n rs) = 0 := by
  apply LinearMap.ext
  intro z
  change (show Work.Kunneth.tpX C D n →ₗ[ℤ] ℤ from γ)
    (Work.Kunneth.tpMapLin C C (Work.Kunneth.sumShift M) D (𝟙 C) ι n
      (Work.Kunneth.tpLof C (Work.Kunneth.sumShift M) n rs z)) = 0
  rw [Work.Kunneth.tpMapLin_tpLof]
  exact LinearMap.congr_fun (hγ rs hrs) _

/-- The hom–tensor adjunction `Work.Kunneth.tpDualEquiv` preserves the bidegree support of a
functional. -/
theorem tpDualEquiv_support (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    [∀ q, Module.Free ℤ ↥(M q)] [∀ q, Module.Finite ℤ ↥(M q)]
    (n : ℕ) (pq : Work.Kunneth.tpIdx n)
    (f : Work.Kunneth.tpX C (Work.Kunneth.sumShift M) n →ₗ[ℤ] ℤ)
    (hf : ∀ rs : Work.Kunneth.tpIdx n, rs ≠ pq →
      f.comp (Work.Kunneth.tpLof C (Work.Kunneth.sumShift M) n rs) = 0)
    (rs : Work.Kunneth.tpIdx n) (hrs : rs ≠ pq) :
    Work.Kunneth.tpDualEquiv C M n f rs = 0 := by
  rw [Work.Kunneth.tpDualEquiv_apply_proj, hf rs hrs, map_zero]

end

end Work.Kunneth.Asm
