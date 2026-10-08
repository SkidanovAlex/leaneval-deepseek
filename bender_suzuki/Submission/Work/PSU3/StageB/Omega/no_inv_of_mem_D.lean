import Mathlib
import Submission.Work.PSU3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.Omega

/-!
# `Work.PSU3.StageB.Omega.no_inv_of_mem_D` — `D` inverts no element of `Q` of order `> 2`

In the rank-one situation `H = Q ⋊ D` of `PSU3Hyp H Q t` the two-point stabiliser
`D = twoPoint H t = H ∩ H^t` has **odd** order (`Work.ThmF.split_odd_card_twoPoint`, which is
just strong embeddedness at `t ∉ H`).  In a group, an element of odd order never inverts an
element of order `> 2`: if `d` has odd order and `d⁻¹ * x * d = x⁻¹`, then `d ^ 2` centralises
`x`, and since `d` is a power of `d ^ 2` (odd order) `d` itself centralises `x`, whence
`x = x⁻¹`.  This is the arithmetic content of the file; the group-theoretic statement
requested then follows at once from `d ∈ D`.
-/

/-- **Odd order inverts only involutions.**  If `d` has odd order and conjugation by `d`
inverts `x`, then `x` is an involution.

Proof: `d⁻¹ x d = x⁻¹` gives `(d²)⁻¹ x d² = d⁻¹ x⁻¹ d = (d⁻¹ x d)⁻¹ = x`, so `d ^ 2` commutes
with `x`.  Writing `orderOf d = 2k+1`, we have `2 * (k+1) = orderOf d + 1`, hence
`d = d ^ (orderOf d + 1) = (d ^ 2) ^ (k + 1)` is a power of `d ^ 2` and therefore also commutes
with `x`.  So `x⁻¹ = d⁻¹ x d = x`. -/
theorem sq_eq_one_of_conj_eq_inv {G : Type} [Group G] {x d : G} (hodd : Odd (orderOf d))
    (hcon : d⁻¹ * x * d = x⁻¹) : x ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := hodd
  set e : G := d ^ 2 with he
  -- `d ^ 2` commutes with `x`
  have hd2 : e⁻¹ * x * e = x := by
    rw [he]
    have h1 : (d ^ 2)⁻¹ * x * (d ^ 2) = d⁻¹ * (d⁻¹ * x * d) * d := by
      rw [pow_two]; group
    rw [h1, hcon]
    have h2 : d⁻¹ * x⁻¹ * d = (d⁻¹ * x * d)⁻¹ := by group
    rw [h2, hcon, inv_inv]
  have hcomm2 : x * e = e * x := by
    have h1 : e * (e⁻¹ * x * e) = e * x := by rw [hd2]
    have h2 : e * (e⁻¹ * x * e) = x * e := by group
    rw [h2] at h1
    exact h1
  -- `d` is a power of `d ^ 2` because its order is odd
  have hpow : d = e ^ (k + 1) := by
    rw [he]
    have h2 : 2 * (k + 1) = orderOf d + 1 := by omega
    rw [← pow_mul, h2, pow_succ, pow_orderOf_eq_one, one_mul]
  have hcomm_pow : ∀ m : ℕ, x * e ^ m = e ^ m * x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc x * e ^ (m + 1) = (x * e ^ m) * e := by group
        _ = (e ^ m * x) * e := by rw [ih]
        _ = e ^ m * (x * e) := by group
        _ = e ^ m * (e * x) := by rw [hcomm2]
        _ = e ^ (m + 1) * x := by group
  -- hence `d` commutes with `x` as well
  have hcomm : x * d = d * x := by
    rw [hpow]
    exact hcomm_pow (k + 1)
  have hxd : d⁻¹ * x * d = x := by
    have h : d⁻¹ * x * d = d⁻¹ * (x * d) := by rw [mul_assoc]
    rw [h, hcomm]
    group
  have hxinv : x⁻¹ = x := by rw [← hcon, hxd]
  rw [pow_two]
  calc x * x = x * x⁻¹ := by rw [hxinv]
    _ = 1 := mul_inv_cancel x

/-- `PSU3Hyp` version: no element of `D = twoPoint H t` inverts an element of order `> 2`. -/
theorem no_inv_of_mem_D {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {x : G} (hx : x ∈ Q) (hx2 : x ^ 2 ≠ 1)
    {d : G} (hd : d ∈ Submission.Blueprint.twoPoint H t) :
    d⁻¹ * x * d ≠ x⁻¹ := by
  intro hcon
  -- `D` has odd order, hence so does `d ∈ D`
  have hDodd : Odd (Nat.card (Submission.Blueprint.twoPoint H t)) :=
    Work.ThmF.split_odd_card_twoPoint hS.split
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf (⟨d, hd⟩ : ↥(Submission.Blueprint.twoPoint H t)) ∣
        Nat.card ↥(Submission.Blueprint.twoPoint H t) := orderOf_dvd_natCard _
    have h2 : orderOf d = orderOf (⟨d, hd⟩ : ↥(Submission.Blueprint.twoPoint H t)) := by
      simpa using (Subgroup.orderOf_coe (⟨d, hd⟩ : ↥(Submission.Blueprint.twoPoint H t)))
    rw [h2]
    exact Odd.of_dvd_nat hDodd h1
  exact hx2 (sq_eq_one_of_conj_eq_inv hodd hcon)

end Work.PSU3.StageB.Omega
