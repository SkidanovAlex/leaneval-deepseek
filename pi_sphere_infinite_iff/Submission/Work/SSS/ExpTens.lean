import Mathlib
import Submission.Work.SSS.TensorFG

/-!
# The naive tensor complex `expTens K M`

`Work.SSS.tensorComplex K M = K ⊗ M` is Mathlib's tensor product of the chain complex `K` with
the chain complex concentrated in degree `0` at `M`.  For the universal-coefficient argument of
`Work.SSS.tensorHomology` we need the complex in the *naive* form: `n`-th term `K.X n ⊗ M` with
differential `K.d n (n-1) ⊗ 𝟙 M`.  This file defines that complex (`expTens K M`) and proves the
elementary functoriality properties that are used by the assembly.

The comparison `Work.SSS.tensorComplex K M ≅ Work.SSS.expTens K M` is the (separately proved)
lemma `Work.SSS.tensorComplexIsoExpTens`.
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

noncomputable section

/-- The "naive" tensor complex of a chain complex `K` with a module `M` placed in degree `0`:
`(expTens K M).X n = K.X n ⊗ M`, with differential `K.d n (n-1) ⊗ 𝟙 M`. -/
abbrev expTens (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun n => K.X n ⊗ M) (fun n => K.d (n + 1) n ▷ M) (fun n => by
    rw [← MonoidalCategory.comp_whiskerRight,
      HomologicalComplex.d_comp_d K (n + 1 + 1) (n + 1) n]
    simp)

@[simp]
theorem expTens_X (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) (n : ℕ) :
    (expTens K M).X n = K.X n ⊗ M := rfl

@[simp]
theorem expTens_d (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) (n : ℕ) :
    (expTens K M).d (n + 1) n = K.d (n + 1) n ▷ M :=
  ChainComplex.of_d (fun n => K.X n ⊗ M) (fun n => K.d (n + 1) n ▷ M) n

/-- The key naturality computation: whiskering a differential on the left is the same as whiskering
on the right (both are `K.d (j+1) j ⊗ f`). -/
theorem whiskerLeft_d (K : ChainComplex (ModuleCat ℤ) ℕ) {M N : ModuleCat ℤ} (f : M ⟶ N)
    (j : ℕ) :
    (K.X (j + 1) ◁ f) ≫ (K.d (j + 1) j ▷ N) = (K.d (j + 1) j ▷ M) ≫ (K.X j ◁ f) := by
  have h1 : (K.X (j + 1) ◁ f) ≫ (K.d (j + 1) j ▷ N) =
      MonoidalCategory.tensorHom (K.d (j + 1) j) f := by
    rw [← MonoidalCategory.id_tensorHom, ← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  have h2 : (K.d (j + 1) j ▷ M) ≫ (K.X j ◁ f) =
      MonoidalCategory.tensorHom (K.d (j + 1) j) f := by
    rw [← MonoidalCategory.id_tensorHom, ← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  rw [h1, h2]

/-- The morphism of tensor complexes induced by a morphism of modules `M ⟶ N`. -/
def expTensHom (K : ChainComplex (ModuleCat ℤ) ℕ) {M N : ModuleCat ℤ} (f : M ⟶ N) :
    expTens K M ⟶ expTens K N where
  f n := K.X n ◁ f
  comm' i j hij := by
    have hij' : j + 1 = i := (ComplexShape.down_Rel ℕ i j).mp hij
    rw [← hij', expTens_d, expTens_d, whiskerLeft_d]

@[simp]
theorem expTensHom_f (K : ChainComplex (ModuleCat ℤ) ℕ) {M N : ModuleCat ℤ} (f : M ⟶ N)
    (n : ℕ) : (expTensHom K f).f n = K.X n ◁ f := rfl


/-- `expTens K -` is functorial in the coefficients: an isomorphism `M ≅ N` induces an isomorphism
of the tensor complexes. -/
def expTensIso {M N : ModuleCat ℤ} (e : M ≅ N) (K : ChainComplex (ModuleCat ℤ) ℕ) :
    expTens K M ≅ expTens K N :=
  Hom.isoOfComponents (fun n => MonoidalCategory.whiskerLeftIso (K.X n) e) (fun i j hij => by
    have hij' : j + 1 = i := (ComplexShape.down_Rel ℕ i j).mp hij
    subst hij'
    rw [expTens_d, expTens_d]
    exact whiskerLeft_d K e.hom j)

/-- `expTens K ℤ ≅ K`: the tensor complex with the unit coefficients is the complex itself. -/
def expTensUnitIso (K : ChainComplex (ModuleCat ℤ) ℕ) :
    expTens K (𝟙_ (ModuleCat ℤ)) ≅ K :=
  Hom.isoOfComponents (fun n => ρ_ (K.X n)) (fun i j hij => by
    have hij' : j + 1 = i := (ComplexShape.down_Rel ℕ i j).mp hij
    rw [← hij', expTens_d]
    exact (MonoidalCategory.rightUnitor_naturality (K.d (j + 1) j)).symm)

end

end Work.SSS
