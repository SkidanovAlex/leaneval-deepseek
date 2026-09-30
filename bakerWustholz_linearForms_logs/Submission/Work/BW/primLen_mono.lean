import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `primLen` is antitone in the ideal: for `I ≤ J` the localization of `R/I` at `p` surjects onto
that of `R/J`, so the lengths can only decrease. -/
theorem primLen_mono {N : ℕ} {I J : Ideal (MR N)} (h : I ≤ J) (p : Ideal (MR N)) :
    primLen J p ≤ primLen I p := by
  unfold primLen
  split_ifs with hp
  · -- `p` is prime: `(R/I)_p` surjects onto `(R/J)_p`, so lengths decrease.
    have hmap : I.map (algebraMap (MR N) (Localization.AtPrime p)) ≤
        J.map (algebraMap (MR N) (Localization.AtPrime p)) := Ideal.map_mono h
    exact Module.length_le_of_surjective (Submodule.factor hmap)
      (Submodule.factor_surjective hmap)
  · -- `p` is not prime: both sides are the junk value `0`.
    exact le_refl 0

end Work.BW
