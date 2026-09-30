import Mathlib
import Submission.Work.Pi6.MSS.TensorAux

/-!
# The canonical Künneth map `H_s(C) ⊗ M ⟶ H_s(C ⊗ M)`

For a chain complex `C` of `𝕜`-modules and a `𝕜`-module `M`, the coefficient-unit chain map
`tensUnit C M m : C ⟶ C ⊗ M` (`x ↦ x ⊗ m`) induces on homology the "Künneth" map
`[z] ⊗ m ↦ [z ⊗ m]`.

Over a field this map is an isomorphism (the canonical Künneth map, see the companion lemma
`Work.Pi6.MSS.kunneth_exists`); it is the direction used in the identification of the `E²` page of
the Serre spectral sequence with `H_s(B) ⊗ H_q(F)`.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open scoped MonoidalCategory

namespace Work.Pi6.MSS

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- The **coefficient-unit chain map** `C ⟶ C ⊗ M`, `x ↦ x ⊗ m`. -/
noncomputable def tensUnit (C : ChainComplex (ModuleCat 𝕜) ℕ) (M : ModuleCat 𝕜) (m : M) :
    C ⟶ expTens 𝕜 C M where
  f n := ModuleCat.ofHom ((TensorProduct.mk 𝕜 (C.X n) M).flip m)
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [expTens_d]
    ext x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      ModuleCat.hom_whiskerRight, TensorProduct.mk_apply, LinearMap.flip_apply]
    rfl

/-- `tensUnit` is additive in the coefficient. -/
theorem tensUnit_add (C : ChainComplex (ModuleCat 𝕜) ℕ) (M : ModuleCat 𝕜) (m m' : M) :
    tensUnit C M (m + m') = tensUnit C M m + tensUnit C M m' := by
  ext n x
  simp only [HomologicalComplex.add_f_apply, ModuleCat.hom_add, LinearMap.add_apply, tensUnit,
    ModuleCat.hom_ofHom, TensorProduct.mk_apply, LinearMap.flip_apply]
  rw [TensorProduct.tmul_add]

/-- `tensUnit` is `𝕜`-linear in the coefficient. -/
theorem tensUnit_smul (C : ChainComplex (ModuleCat 𝕜) ℕ) (M : ModuleCat 𝕜) (c : 𝕜) (m : M) :
    tensUnit C M (c • m) = c • tensUnit C M m := by
  ext n x
  simp only [HomologicalComplex.smul_f_apply, ModuleCat.hom_smul, LinearMap.smul_apply, tensUnit,
    ModuleCat.hom_ofHom, TensorProduct.mk_apply, LinearMap.flip_apply]
  rw [TensorProduct.tmul_smul]

end

end Work.Pi6.MSS
