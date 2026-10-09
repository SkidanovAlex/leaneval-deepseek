import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- `HasRootsOfUnity` is monotone in the exponent: if `μ_{p^{i+1}} ⊆ K` and `i' ≤ i`, then
`μ_{p^{i'+1}} ⊆ K`, since `ζ ↦ ζ^{p^{i-i'}}` raises a primitive `p^{i+1}`-st root of unity to a
primitive `p^{i'+1}`-st one. -/
theorem hasRootsOfUnity_mono {p : ℕ} {K : IntermediateField ℚ SSGRoute.QBar} {i i' : ℕ}
    (h : i' ≤ i) (hμ : SSGRoute.HasRootsOfUnity p K i) : SSGRoute.HasRootsOfUnity p K i' := by
  obtain ⟨ζ, hζK, hζ⟩ := hμ
  rcases Nat.eq_zero_or_pos p with hp | hp
  · -- `p = 0`: both exponents `0 ^ (i+1)` and `0 ^ (i'+1)` are `0`, so `ζ` itself works.
    subst hp
    exact ⟨ζ, hζK, by simpa using hζ⟩
  · -- `p > 0`: `ζ ^ p^(i-i')` is a primitive `p^(i'+1)`-st root of unity, lying in `K`.
    refine ⟨ζ ^ (p ^ (i - i')), ?_, ?_⟩
    · exact K.toSubfield.pow_mem hζK (p ^ (i - i'))
    · have hprod : p ^ (i + 1) = p ^ (i - i') * p ^ (i' + 1) := by
        rw [← pow_add]
        congr 1
        omega
      exact hζ.pow (pow_pos hp (i + 1)) hprod

end Work.SSGRoute
