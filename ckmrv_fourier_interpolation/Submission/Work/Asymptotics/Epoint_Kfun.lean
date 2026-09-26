import Mathlib
import Submission.Work.Asymptotics.EpointAux
import Submission.Work.Asymptotics.Xi8_bound_E
import Submission.Work.Asymptotics.Xi24_bound_E
import Submission.Work.Asymptotics.KMinus_slash_bound_E
import Submission.Work.Asymptotics.divisor_lower_E
import Submission.Work.Asymptotics.near_diag_bound_E
import Submission.Work.Asymptotics.EFlat_of_bounds

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics

/-- **The two pointwise inputs on `E`.**  `EFlat` and `EPolyWin` for the CKMRV kernel `K` on the
cusp-`0` neighbourhood `E`: the flatness is assembled in `Work.Asymptotics.EFlat_of_bounds` from
the `(quotientbounds1new)` slash estimates on `E` (`Work.Asymptotics.Xi8_bound_E`,
`Work.Asymptotics.Xi24_bound_E` through the `Ξ`-identities, and
`Work.Asymptotics.KMinus_slash_bound_E`), the divisor lower bound away from the orbit
(`Work.Asymptotics.divisor_lower_E`) and the near-orbit bound (`Work.Asymptotics.near_diag_bound_E`);
`EPolyWin` follows from `EFlat` with window `N₀ = 0` (`EPolyWin_of_EFlat`). -/
theorem Epoint_Kfun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    Work.Asymptotics.EFlat ℓ d ∧ Work.Asymptotics.EPolyWin ℓ d := by
  rcases hd with rfl | rfl
  · have hflat : Work.Asymptotics.EFlat ℓ 8 :=
      EFlat_of_bounds ℓ 8 (Or.inl rfl)
        (KPlus8_slash_bound_of_Xi8 Xi8_bound_E)
        (KMinus_slash_bound_E ℓ 8 (Or.inl rfl))
        divisor_lower_E (near_diag_bound_E ℓ 8 (Or.inl rfl))
    exact ⟨hflat, EPolyWin_of_EFlat ℓ 8 hflat⟩
  · have hflat : Work.Asymptotics.EFlat ℓ 24 :=
      EFlat_of_bounds ℓ 24 (Or.inr rfl)
        (KPlus24_slash_bound_of_Xi24 Xi24_bound_E)
        (KMinus_slash_bound_E ℓ 24 (Or.inr rfl))
        divisor_lower_E (near_diag_bound_E ℓ 24 (Or.inr rfl))
    exact ⟨hflat, EPolyWin_of_EFlat ℓ 24 hflat⟩

end Work.Asymptotics
