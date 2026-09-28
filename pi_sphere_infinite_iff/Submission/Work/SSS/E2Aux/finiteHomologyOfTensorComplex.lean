import Mathlib
import Submission.Work.SSS.TensorFG

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS.E2Aux

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory MonoidalCategory

set_option linter.style.haveILetI false

/-- The chain complex concentrated in degree `0` at `M`, as a functor of `M`.  This is the functor
whose image at `M` is the degree-zero complex appearing in `Work.SSS.tensorComplex`. -/
noncomputable abbrev coeffComplex : ModuleCat ℤ ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
  HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0

/-- **A split unit in the coefficients splits off the homology of the tensor complex.**  Let
`K : ChainComplex (ModuleCat ℤ) ℕ` be a chain complex of `ℤ`-modules and `M` a `ℤ`-module equipped
with a coefficient map `e : 𝟙_ (ModuleCat ℤ) ⟶ M` and a retraction `ψ : M ⟶ 𝟙_ (ModuleCat ℤ)`
satisfying `e ≫ ψ = 𝟙`.  Then finiteness of `H_n(K ⊗ M)` implies finiteness of `H_n(K)`.

Reason: `Work.SSS.tensorComplex K (𝟙_ (ModuleCat ℤ)) = K ⊗ (tensorUnit)` is `K` up to the monoidal
right unitor `HomologicalComplex.rightUnitor`; applying the coefficient map `e` gives a chain map
`K ⟶ K ⊗ M`, and applying `ψ` gives a left inverse of it (`whiskerLeft_comp`, `Functor.map_comp`).
Hence `H_n(K) → H_n(K ⊗ M)` is injective with a left inverse, so `H_n(K)` is a submodule of the
finitely generated module `H_n(K ⊗ M)`, hence finitely generated (ℤ is Noetherian). -/
theorem finiteHomologyOfTensorComplex {K : ChainComplex (ModuleCat ℤ) ℕ} {M : ModuleCat ℤ}
    (e : 𝟙_ (ModuleCat ℤ) ⟶ M) (ψ : M ⟶ 𝟙_ (ModuleCat ℤ))
    (h : e ≫ ψ = 𝟙 (𝟙_ (ModuleCat ℤ))) (n : ℕ)
    (hfin : Module.Finite ℤ ((Work.SSS.tensorComplex K M).homology n)) :
    Module.Finite ℤ (K.homology n) := by
  -- Rewrite `hfin` in terms of the explicitly displayed tensor complex `K ⊗ coeffComplex.obj M`.
  have hfin' : Module.Finite ℤ ((K ⊗ coeffComplex.obj M).homology n) := hfin
  haveI : Module.Finite ℤ ((K ⊗ coeffComplex.obj M).homology n) := hfin'
  -- The chain map `f : K ⟶ K ⊗ M` induced by the coefficient map `e`, using the right unitor to
  -- identify `K` with `K ⊗ 𝟙`.
  -- The chain map `g : K ⊗ M ⟶ K` induced by the retraction `ψ`, again through the right unitor.
  have hfg : ((HomologicalComplex.rightUnitor K).inv ≫ (K ◁ coeffComplex.map e)) ≫
      ((K ◁ coeffComplex.map ψ) ≫ (HomologicalComplex.rightUnitor K).hom) = 𝟙 K := by
    simp only [Category.assoc]
    rw [← Category.assoc (K ◁ coeffComplex.map e) (K ◁ coeffComplex.map ψ)
        (HomologicalComplex.rightUnitor K).hom,
      ← MonoidalCategory.whiskerLeft_comp, ← Functor.map_comp, h]
    simp
  -- Induced split epimorphism on homology.
  have hmap : HomologicalComplex.homologyMap ((HomologicalComplex.rightUnitor K).inv ≫
        (K ◁ coeffComplex.map e)) n ≫
      HomologicalComplex.homologyMap ((K ◁ coeffComplex.map ψ) ≫
        (HomologicalComplex.rightUnitor K).hom) n = 𝟙 (K.homology n) := by
    rw [← HomologicalComplex.homologyMap_comp, hfg, HomologicalComplex.homologyMap_id]
  -- `H_n(K)` is a quotient of the finitely generated `H_n(K ⊗ M)`, hence finitely generated.
  refine Module.Finite.of_surjective
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap ((K ◁ coeffComplex.map ψ) ≫
      (HomologicalComplex.rightUnitor K).hom) n)) ?_
  intro y
  refine ⟨(ModuleCat.Hom.hom (HomologicalComplex.homologyMap ((HomologicalComplex.rightUnitor K).inv ≫
    (K ◁ coeffComplex.map e)) n)) y, ?_⟩
  rw [← ModuleCat.comp_apply, hmap]
  simp

end Work.SSS.E2Aux
