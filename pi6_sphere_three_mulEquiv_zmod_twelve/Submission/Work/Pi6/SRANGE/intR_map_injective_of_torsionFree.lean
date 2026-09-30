import Mathlib
import Submission.Work.Pi6.SRANGE.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Injectivity of `ℤ ⊗ -` on an inclusion with torsion-free cokernel

Let `ι : B ↪ Z` be an inclusion of `ℤ`-modules whose cokernel `Z ⧸ range ι` is torsion free.
Over the principal ideal domain `ℤ`, torsion freeness is equivalent to flatness, so the short
exact sequence `0 → B → Z → Z ⧸ range ι → 0` remains exact after applying `- ⊗[ℤ] R`: the map
`ι ⊗ R` is injective.

The map appearing in the statement, `(IntR R).map (ModuleCat.ofHom ι)`, is nothing but the
extension of scalars along `ℤ → R` applied to `ι`, i.e. the `R`-linear map
`R ⊗[ℤ] B → R ⊗[ℤ] Z`.  Its underlying `ℤ`-linear map is `intRBaseChange` below, which is
definitionally `LinearMap.lTensor` of `R` viewed as a `ℤ`-module (`ℤ` acting through
`Int.castRingHom R`).  The statement therefore reduces to
`LinearMap.lTensor_injective_of_exact_of_flat` applied to `0 → B → Z → Z ⧸ range ι → 0`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Work.Pi6.SRANGE

noncomputable section

/-- `R` viewed as a `ℤ`-module through `Int.castRingHom R`, in the exact form in which
`ModuleCat.extendScalars` produces it (via `ModuleCat.restrictScalars`). -/
private abbrev IntRCoeff (R : Type) [CommRing R] : Type :=
  ↥((ModuleCat.restrictScalars (Int.castRingHom R)).obj (ModuleCat.of R R))

/-- The base change `R ⊗[ℤ] M ⟶ R ⊗[ℤ] N` of a `ℤ`-linear map `f`, written in the exact form
produced by `ModuleCat.extendScalars (Int.castRingHom R)`. -/
private def intRBaseChange (R : Type) [CommRing R] {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) :=
  @LinearMap.baseChange ℤ R M N _ _ ((algebraMap R R).comp (Int.castRingHom R)).toAlgebra _ _ _ _ f

/-- The underlying function of `intRBaseChange R f` is `LinearMap.lTensor` of `R` as a
`ℤ`-module (`LinearMap.baseChange_eq_ltensor`, whose two sides are definitionally equal). -/
private lemma intRBaseChange_fun_eq_lTensor (R : Type) [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) :
    ⇑(intRBaseChange R f) = ⇑(LinearMap.lTensor (IntRCoeff R) f) := by
  rw [intRBaseChange]
  exact @LinearMap.baseChange_eq_ltensor ℤ R M N _ _
    ((algebraMap R R).comp (Int.castRingHom R)).toAlgebra _ _ _ _ f

theorem intR_map_injective_of_torsionFree (R : Type) [CommRing R]
    {B Z : Type} [AddCommGroup B] [Module ℤ B] [AddCommGroup Z] [Module ℤ Z]
    (ι : B →ₗ[ℤ] Z) (hι : Function.Injective ι) (hZ : Module.IsTorsionFree ℤ Z)
    (h : Module.IsTorsionFree ℤ (Z ⧸ LinearMap.range ι)) :
    Function.Injective (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map (ModuleCat.ofHom ι))) := by
  -- Fix the canonical `ℤ`-module structure on the quotient; all `Module` structures on a fixed
  -- additive group are equal, so torsion freeness transports from the instance in the statement.
  letI : Module ℤ (Z ⧸ LinearMap.range ι) := Submodule.Quotient.module _
  have h' : Module.IsTorsionFree ℤ (Z ⧸ LinearMap.range ι) := by
    convert h using 1
    exact Subsingleton.elim _ _
  haveI : Module.IsTorsionFree ℤ (Z ⧸ LinearMap.range ι) := h'
  -- Over the PID `ℤ`, torsion free means flat.
  haveI : Module.Flat ℤ (Z ⧸ LinearMap.range ι) := inferInstance
  -- `0 → B →ᵢ Z → Z ⧸ range ι → 0` has flat cokernel, so `- ⊗[ℤ] R` keeps it exact; the
  -- map `ι.lTensor R` — which is definitionally the underlying function of the goal — is
  -- therefore injective.
  exact LinearMap.lTensor_injective_of_exact_of_flat (Submodule.mkQ (LinearMap.range ι))
    (Submodule.mkQ_surjective _) ι hι (by rw [LinearMap.exact_iff]; simp) (IntRCoeff R)

end

end Work.Pi6.SRANGE
