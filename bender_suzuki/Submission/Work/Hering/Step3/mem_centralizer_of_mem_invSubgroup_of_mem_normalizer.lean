import Mathlib
import Submission.Work.Hering.InvSubgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# An element of `V = Inv(G) ∪ {1}` normalising an odd-order subgroup centralises it

Peterfalvi I §2, Step 3 (p. 191).  Since the involutions of `G` commute pairwise (`Step 1`,
`comm_of_dtinv`), an involution `v` cannot normalise a subgroup `Q` of odd order without
centralising it: if `q ∈ Q` with `v q v⁻¹ ≠ q`, then `w = v q v⁻¹ q⁻¹` is a non-trivial element of
`Q` with `v w v⁻¹ = w⁻¹`; hence `v * w` is an involution that does **not** commute with `v`,
contradicting `comm_of_dtinv`.  A non-trivial element of `Q` is not inverted by an involution
precisely because `Q` has odd order.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Hering.Step3

open LeanEval.GroupTheory.Defs

theorem mem_centralizer_of_mem_invSubgroup_of_mem_normalizer {G : Type*} [Group G]
    (hDT : DTInv G) (h4 : HasFourGroup G) {Q : Subgroup G} (hQ : Odd (Nat.card Q)) {v : G}
    (hv : v ∈ invSubgroup hDT h4) (hn : v ∈ Subgroup.normalizer (Q : Set G)) :
    v ∈ Subgroup.centralizer (Q : Set G) := by
  rw [mem_invSubgroup] at hv
  rcases hv with hv | hv1
  · -- `v` is an involution
    have hv2 : v * v = 1 := sq_eq_one_of_orderOf_eq_two hv
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    have hvv : v⁻¹ * v⁻¹ = 1 := by rw [hvinv, hv2]
    let φ : MulAut G := MulAut.conj v
    have hφ : ∀ x : G, φ x = v * x * v⁻¹ := fun x => MulAut.conj_apply v x
    have hφ2 : ∀ x : G, φ (φ x) = x := by
      intro x
      rw [hφ, hφ]
      calc v * (v * x * v⁻¹) * v⁻¹ = (v * v) * x * (v⁻¹ * v⁻¹) := by group
        _ = x := by rw [hv2, hvv, one_mul, mul_one]
    rw [Subgroup.mem_centralizer_iff]
    intro h hmem
    by_contra hc
    -- `v` does not fix `h`; set `w = v h v⁻¹ h⁻¹ ∈ Q`, a non-trivial element inverted by `v`.
    have hd : φ h ≠ h := by
      rw [hφ]
      intro heq
      apply hc
      have h1 : v * h = h * v := by
        have hconj := congrArg (fun t => t * v) heq
        simpa [mul_assoc] using hconj
      exact h1.symm
    have hφhQ : φ h ∈ Q := by
      rw [hφ]
      exact (Subgroup.mem_normalizer_iff.mp hn h).mp hmem
    let w : G := φ h * h⁻¹
    have hwQ : w ∈ Q := by
      show φ h * h⁻¹ ∈ Q
      exact Q.mul_mem hφhQ (Q.inv_mem hmem)
    have hw1 : w ≠ 1 := by
      show φ h * h⁻¹ ≠ 1
      intro hw
      exact hd (mul_inv_eq_one.mp hw)
    have hwinv : φ w = w⁻¹ := by
      show φ (φ h * h⁻¹) = (φ h * h⁻¹)⁻¹
      rw [map_mul, map_inv, hφ2]
      group
    have hwv : v * w * v⁻¹ = w⁻¹ := by rw [← hφ w, hwinv]
    have hvww : v * w * v = w⁻¹ := by rw [← hwv, hvinv]
    -- a non-trivial element of the odd-order group `Q` is not inverted by an involution
    have hwne : w ≠ w⁻¹ := by
      intro hw
      have hww : w * w = 1 := by
        have hconj := congrArg (fun t => w * t) hw
        simpa using hconj
      have hord : orderOf w = 2 := orderOf_eq_two_of_sq_eq_one hww hw1
      have hdvd : 2 ∣ Nat.card Q := by
        rw [← hord]
        exact Subgroup.orderOf_dvd_natCard Q hwQ
      exact (Nat.not_even_iff_odd.mpr hQ) (even_iff_two_dvd.mpr hdvd)
    have hvw2 : (v * w) * (v * w) = 1 := by
      calc (v * w) * (v * w) = (v * w * v) * w := by group
        _ = w⁻¹ * w := by rw [hvww]
        _ = 1 := by simp
    have hvw_ne1 : v * w ≠ 1 := by
      intro hw
      have hwv' : w = v := mul_left_cancel (by rw [hw, hv2])
      exact hwne (by rw [hwv', hvinv])
    have hordvw : orderOf (v * w) = 2 := orderOf_eq_two_of_sq_eq_one hvw2 hvw_ne1
    -- `v` and the involution `v * w` do not commute: contradiction with Step 1
    have hne2 : v * (v * w) ≠ (v * w) * v := by
      intro heq
      exact hwne (by
        calc w = v * (v * w) := by rw [← mul_assoc, hv2, one_mul]
          _ = (v * w) * v := heq
          _ = w⁻¹ := hvww)
    exact hne2 (comm_of_dtinv hDT h4 v (v * w) hv hordvw)
  · -- `v = 1` centralises everything
    rw [hv1]
    exact Subgroup.one_mem _

end Work.Hering.Step3
