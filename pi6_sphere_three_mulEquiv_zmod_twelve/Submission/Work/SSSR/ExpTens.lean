import Mathlib
import Submission.Work.SSSR.TensorFG
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory
noncomputable section

/-- The "naive" tensor complex of a chain complex `K` with a module `M` placed in degree `0`:
`(expTens K M).X n = K.X n ⊗ M`, with differential `K.d n (n-1) ⊗ 𝟙 M`. -/
abbrev expTens (K : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) :
    ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n => K.X n ⊗ M) (fun n => K.d (n + 1) n ▷ M) (fun n => by
    rw [← MonoidalCategory.comp_whiskerRight,
      HomologicalComplex.d_comp_d K (n + 1 + 1) (n + 1) n]
    simp)

@[simp]
theorem expTens_d (K : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    (expTens K M).d (n + 1) n = K.d (n + 1) n ▷ M :=
  ChainComplex.of_d (fun n => K.X n ⊗ M) (fun n => K.d (n + 1) n ▷ M) n

/-- The key naturality computation: whiskering a differential on the left is the same as whiskering
on the right (both are `K.d (j+1) j ⊗ f`). -/
theorem whiskerLeft_d (K : ChainComplex (ModuleCat R) ℕ) {M N : ModuleCat R} (f : M ⟶ N)
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

end

end Work.SSSR
