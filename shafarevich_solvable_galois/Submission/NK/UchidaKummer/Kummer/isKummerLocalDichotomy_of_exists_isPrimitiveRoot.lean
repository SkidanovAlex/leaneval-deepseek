import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.UchidaKummer.Kummer

theorem isKummerLocalDichotomy_of_exists_isPrimitiveRoot {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hμ : ∃ ζ : K, IsPrimitiveRoot ζ ℓ) :
    NK.UchidaKummer.IsKummerLocalDichotomy K K' ℓ := by
  obtain ⟨ζ, hζ⟩ := hμ
  intro a L hfin hnf hL 𝔮
  haveI := hfin
  haveI := hnf
  exact localDeg_kummerField_eq_one_iff ℓ hℓ hζ a L hL 𝔮

end NK.UchidaKummer.Kummer
