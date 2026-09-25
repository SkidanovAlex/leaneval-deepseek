import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.exists_mulEquiv_Mfield_gal
import Submission.Work.Tower.CyclotomicBase.finrank_Mfield
import Submission.Work.Tower.CyclotomicBase.finrank_Ffield_eq_three

set_option linter.style.haveILetI false

namespace Work.Tower.CyclotomicBase

/-- The relative degree `[M : F] = 3 ^ (ℓ - 1)`: by the tower law
`[M : ℚ] = [F : ℚ] · [M : F]` with `[M : ℚ] = 3 ^ ℓ` (`finrank_Mfield`) and
`[F : ℚ] = 3` (`finrank_Ffield_eq_three`, transported along the restriction
`FMfield ≃ Ffield` by `finrank_FMfield`). -/
theorem finrank_Mfield_over_FMfield {ℓ : ℕ} (hℓ : 0 < ℓ) (r : Fin ℓ → ℕ)
    (hr : ∀ i, Nat.Prime (r i)) (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r)
    [NeZero (D r)] :
    Module.finrank ↥(FMfield r hr hr3) ↥(Mfield r hr hr3) = 3 ^ (ℓ - 1) := by
  have hM : Module.finrank ℚ ↥(Mfield r hr hr3) = 3 ^ ℓ :=
    finrank_Mfield r hr hr3 hrinj
  have hF : Module.finrank ℚ ↥(FMfield r hr hr3) = 3 := by
    rw [finrank_FMfield r hr hr3]
    exact finrank_Ffield_eq_three hℓ r hr hr3 hrinj
  have htower : Module.finrank ℚ ↥(FMfield r hr hr3) *
      Module.finrank ↥(FMfield r hr hr3) ↥(Mfield r hr hr3) =
      Module.finrank ℚ ↥(Mfield r hr hr3) :=
    Module.finrank_mul_finrank ℚ ↥(FMfield r hr hr3) ↥(Mfield r hr hr3)
  rw [hM, hF] at htower
  have hp : (3 : ℕ) * 3 ^ (ℓ - 1) = 3 ^ ℓ := by
    rw [← pow_succ', Nat.sub_add_cancel hℓ]
  exact Nat.mul_left_cancel (show 0 < 3 by norm_num) (htower.trans hp.symm)

end Work.Tower.CyclotomicBase
