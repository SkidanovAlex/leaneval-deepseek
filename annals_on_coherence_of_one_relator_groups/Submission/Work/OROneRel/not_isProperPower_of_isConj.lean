import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

/-- Being a proper power is a conjugacy invariant for free groups: if `v` is not a proper power and
`X` is conjugate to `v`, then `X` is not a proper power.  Indeed `v = c * X * c⁻¹` for some `c`, so
`X = u ^ k` would give `v = (c * u * c⁻¹) ^ k`. -/
theorem not_isProperPower_of_isConj {α : Type u} {X v : FreeGroup α}
    (h : ¬ Work.OROneRel.IsProperPower v) (hc : IsConj v X) : ¬ Work.OROneRel.IsProperPower X := by
  -- `X = u ^ k` with `k ≥ 2` and `c * v * c⁻¹ = X` would give `v = (c⁻¹ * u * c) ^ k`,
  -- since `(c⁻¹ * u * c) ^ k = c⁻¹ * u ^ k * c`.
  intro hX
  apply h
  obtain ⟨u, k, hk, hUk⟩ := hX
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  refine ⟨c⁻¹ * u * c, k, hk, ?_⟩
  have h2 : (c⁻¹ * u * c) ^ k = c⁻¹ * u ^ k * c := by
    simpa using conj_pow (i := k) (a := c⁻¹) (b := u)
  have hcv : c * v * c⁻¹ = u ^ k := hc.trans hUk
  rw [h2, ← hcv]
  group

end Work.OROneRel
