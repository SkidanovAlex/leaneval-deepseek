import Mathlib
import Submission.Work.CORE3.Case1aFrattiniApi

/-!
# `Work.CORE3.oddInvertedLeFittingIn`

`U = O(H)` (`H = C_G(t)`), `S` a Sylow `2`-subgroup and `SActsTriviallyModFitting B` says
`[S, U] ⊆ F(U)`.  An odd-order subgroup `X ≤ U` inverted by an element `s ∈ S` must then lie in
`F(U) = F(U)`.

The point is one elementary computation: for `x ∈ X`, the commutator `x⁻¹ (s x s⁻¹) = x⁻²` lies in
`F(U)` because `s ∈ S` and `x ∈ U`; so `x² ∈ F(U)`.  Since `orderOf x` is odd (`|X|` is odd and
`orderOf x ∣ |X|`), write `orderOf x = 2j + 1`; then `x = ((x²)^j)⁻¹ ∈ F(U)`.
-/

namespace Work.CORE3

theorem oddInvertedLeFittingIn {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (hSAct : Work.CORE3.SActsTriviallyModFitting B) {s : G} (hs : s ∈ (B.S : Subgroup G))
    {X : Subgroup G} (hXU : X ≤ B.U) (hodd : Odd (Nat.card X)) (hinv : Work.GW2.Inverts s X) :
    X ≤ Work.GW2.fittingIn B.U := by
  intro x hx
  have hxU : x ∈ B.U := hXU hx
  -- `x² ∈ F(U)`: the commutator `x⁻¹ (s x s⁻¹) = x⁻²` lies in `F(U)` by `hSAct`.
  have hF : x ^ 2 ∈ Work.GW2.fittingIn B.U := by
    have h1 : x⁻¹ * (s * x * s⁻¹) ∈ Work.GW2.fittingIn B.U := hSAct s hs x hxU
    rw [hinv x hx] at h1
    have h2 : (x ^ 2)⁻¹ ∈ Work.GW2.fittingIn B.U := by
      rwa [pow_two, mul_inv_rev]
    simpa using (Work.GW2.fittingIn B.U).inv_mem h2
  -- `orderOf x` is odd, so `x = ((x²)^j)⁻¹` with `orderOf x = 2j + 1`.
  have hoddx : Odd (orderOf x) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard X hx)
  obtain ⟨j, hj⟩ := hoddx
  have hxj : x = ((x ^ 2) ^ j)⁻¹ := by
    have hmul : x * (x ^ 2) ^ j = 1 := by
      rw [← pow_mul, ← pow_succ']
      rw [show 2 * j + 1 = orderOf x by omega, pow_orderOf_eq_one]
    exact eq_inv_of_mul_eq_one_left hmul
  rw [hxj]
  exact (Work.GW2.fittingIn B.U).inv_mem ((Work.GW2.fittingIn B.U).pow_mem hF j)

end Work.CORE3
