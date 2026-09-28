import Mathlib
import Submission.Work.SSS.ExpTens

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory MonoidalCategory

/-- For a chain complex `K` of modules indexed by `ℕ`, the `0`-th opcycles is the cokernel of the
differential `K.d 1 0 : K.X 1 ⟶ K.X 0` (there is nothing below degree `0`). -/
noncomputable def opcyclesZeroIsoCokernel (K : ChainComplex (ModuleCat ℤ) ℕ) :
    K.opcycles 0 ≅ cokernel (K.d 1 0) :=
  HomologicalComplex.opcyclesIsoSc' K 1 0 0 (by simp) (by simp) ≪≫
    ShortComplex.opcyclesIsoCokernel (K.sc' 1 0 0)

/-- `H_0(K ⊗ N) ≅ H_0(K) ⊗ N`: `H_0` is the cokernel of `K.d 1 0`, and `- ⊗ N` is right exact.  (No flatness hypothesis on `N`.) -/
theorem expTensHomologyZero (K : ChainComplex (ModuleCat ℤ) ℕ) (N : ModuleCat ℤ) :
    Nonempty ((Work.SSS.expTens K N).homology 0 ≅ K.homology 0 ⊗ N) := by
  refine ⟨?e⟩
  -- `H_0` of a complex concentrated in degrees `≥ 0` is the cokernel of `d 1 0`.
  have hd : (Work.SSS.expTens K N).d 1 0 = K.d 1 0 ▷ N := Work.SSS.expTens_d K N 0
  have e1 : (Work.SSS.expTens K N).homology 0 ≅ cokernel ((Work.SSS.expTens K N).d 1 0) :=
    ChainComplex.isoHomologyι₀ (Work.SSS.expTens K N) ≪≫
      opcyclesZeroIsoCokernel (Work.SSS.expTens K N)
  -- right exactness of `- ⊗ N` identifies this cokernel with `cokernel (K.d 1 0) ⊗ N`.
  have e2 : cokernel ((Work.SSS.expTens K N).d 1 0) ≅ cokernel (K.d 1 0) ⊗ N := by
    rw [hd]
    exact (PreservesCokernel.iso (MonoidalCategory.tensorRight N) (K.d 1 0)).symm
  have e3 : cokernel (K.d 1 0) ⊗ N ≅ K.opcycles 0 ⊗ N :=
    MonoidalCategory.tensorIso (opcyclesZeroIsoCokernel K).symm (Iso.refl N)
  have e4 : K.opcycles 0 ⊗ N ≅ K.homology 0 ⊗ N :=
    MonoidalCategory.tensorIso (ChainComplex.isoHomologyι₀ K).symm (Iso.refl N)
  exact e1 ≪≫ e2 ≪≫ e3 ≪≫ e4

end Work.SSS
