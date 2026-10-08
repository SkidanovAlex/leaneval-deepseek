import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.InvertCentralizes.sq_commute

namespace Work.CORE4

/-- **A4i (pure group theory, design pass 15).** If an involution `s` inverts every element of a
subgroup `I` and of a subgroup `R` of odd order, and `R` normalizes `I`, then `R` centralizes `I`.

(Unfolded form of `Work.CORE4.C15.InvCentralizesProp`; the same statement as `inv_centralizes` in
`_design_gw/Core15C4.lean`.  Statement copied verbatim from the design file, in the area's
vocabulary `Work.GW2.Inverts`.)

Proof (design pass 15 §1.3, A4i): for `k ∈ R`, `x ∈ I`, put `y := k x⁻¹ k⁻¹ ∈ I`.  Then
`s y s⁻¹ = y⁻¹ = k x k⁻¹`, while expanding the left side (using `s k s⁻¹ = k⁻¹`, `s x s⁻¹ = x⁻¹`)
gives `k⁻¹ x k`.  So `k²` centralizes `x`, and since `k` has odd order, `k ∈ ⟨k²⟩`. -/
theorem A4i : Work.CORE4.C15.InvCentralizesProp := by
  intro G _ _ s I R hI hR hRI hodd
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  -- The computation `k⁻¹ * x * k = k * x * k⁻¹`, i.e. `Commute (k ^ 2) x`
  -- (colleague's lemma, `Submission/Work/CORE4/InvertCentralizes/sq_commute.lean`).
  have hc : Commute (k ^ 2) x := sq_commute hI hR hRI hk hx
  -- `orderOf k` is odd, because `k` lies in the odd-order group `R`.
  have hoddk : Odd (orderOf k) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard R hk)
  -- An element of odd order is a power of its square, hence `k` commutes with `x` too.
  obtain ⟨j, hj⟩ := hoddk
  have hk_pow : (k ^ 2) ^ (j + 1) = k := by
    rw [← pow_mul, show 2 * (j + 1) = orderOf k + 1 from by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hcomm : Commute k x := by
    have h := hc.pow_left (j + 1)
    rwa [hk_pow] at h
  exact hcomm.eq.symm

end Work.CORE4
