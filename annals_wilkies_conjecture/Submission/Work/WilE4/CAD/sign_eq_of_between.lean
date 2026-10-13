import Mathlib

namespace Work.WilE4.CAD

theorem sign_eq_of_between {x z y : ℝ} (hxz : x < z) (hzy : z < y)
    (hs : SignType.sign x = SignType.sign y) : SignType.sign z = SignType.sign x := by
  -- `SignType.sign` is monotone, so it is squeezed between its values at `x` and `y`,
  -- which are equal by hypothesis.
  have h1 : SignType.sign x ≤ SignType.sign z :=
    SignType.sign.monotone (le_of_lt hxz)
  have h2 : SignType.sign z ≤ SignType.sign x := by
    have h := SignType.sign.monotone (le_of_lt hzy)
    rwa [← hs] at h
  exact le_antisymm h2 h1

end Work.WilE4.CAD
