import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.fixedField_iInf_eq_iSup

set_option linter.style.haveILetI false

namespace Work.Tower.CyclotomicBase

theorem Mfield_eq_iSup_Lfield {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) [NeZero (D r)] :
    Mfield r hr hr3 = ⨆ i, Lfield r hr hr3 i := by
  haveI : IsCyclotomicExtension ({(D r : ℕ)} : Set ℕ) ℚ (Cyc r) := isCyclotomicExtension_cyc r
  haveI : IsGalois ℚ (Cyc r) := IsCyclotomicExtension.isGalois {(D r : ℕ)} ℚ (Cyc r)
  -- The kernel of the product map `galMap` is the intersection of the kernels of its
  -- coordinates `galCoord i`, since `galMap σ i = galCoord i σ` definitionally.
  have hker : (galMap r hr hr3).ker = ⨅ i, (galCoord r hr hr3 i).ker := by
    ext σ
    rw [MonoidHom.mem_ker, Subgroup.mem_iInf]
    constructor
    · intro h i
      show galCoord r hr hr3 i σ = 1
      exact congrFun h i
    · intro h
      funext i
      exact h i
  -- Now apply the Galois correspondence: `fixedField` (an antitone equivalence) sends an
  -- intersection of subgroups to the supremum of the fixed fields.
  show IntermediateField.fixedField (galMap r hr hr3).ker =
    ⨆ i, IntermediateField.fixedField ((galCoord r hr hr3 i).ker)
  rw [hker,
    ← IsGalois.intermediateFieldEquivSubgroup_symm_apply_toDual (F := ℚ) (E := Cyc r)
      (H := ⨅ i, (galCoord r hr hr3 i).ker),
    toDual_iInf, OrderIso.map_iSup]
  simp only [IsGalois.intermediateFieldEquivSubgroup_symm_apply_toDual]

end Work.Tower.CyclotomicBase
