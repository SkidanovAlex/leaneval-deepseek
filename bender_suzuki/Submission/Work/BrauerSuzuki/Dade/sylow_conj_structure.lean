import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_mem_or
import Submission.Work.BrauerSuzuki.Quaternion.rho_mul_pow_order
import Submission.Work.BrauerSuzuki.Sylow.genQuaternion_sylow_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Dade

open Classical

/-!
# The centre and the involutions of a Sylow `2`-subgroup of a group with `Q_{2^n}` Sylows

Let `G` be a finite group whose Sylow `2`-subgroup `S` is generalized quaternion
(`d : GenQuaternionData ↥S`).  Then *every* Sylow `2`-subgroup `T` of `G` is isomorphic to `S`
(all Sylow `2`-subgroups are conjugate), hence generalized quaternion, and consequently

* every element of `T` which is central in `T` is an involution, and
* `T` contains at most one involution.

These are the two structural facts about a Sylow `2`-subgroup used in Dade's argument.

The auxiliary lemma `genQuaternionData_center_sq` isolates the group-theoretic content: in a
generalized quaternion group the centre consists of involutions (its centre is
`{1, τ ^ (2 ^ (n-1))}`).
-/

/-- In a generalized quaternion group the central elements are involutions.

Every element is `τ ^ k` or `ρ * τ ^ i` (`genQuaternionData_mem_or`).  In the second case
`ρ * τ ^ i` conjugates `τ` to `τ⁻¹` (`rho_mul_pow_order`), so it cannot be central, since
`orderOf τ = 2 ^ n` with `n ≥ 2` forces `τ ≠ τ⁻¹`.  In the first case, centrality with respect
to `ρ` gives `ρ * τ ^ k * ρ⁻¹ = τ ^ k`, while `ρ * τ ^ k * ρ⁻¹ = (τ ^ k)⁻¹`, so
`x = x⁻¹`, i.e. `x ^ 2 = 1`. -/
theorem genQuaternionData_center_sq {P : Type*} [Group P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) {x : P}
    (hx : ∀ y : P, x * y = y * x) : x ^ 2 = 1 := by
  rcases Work.BrauerSuzuki.Quaternion.genQuaternionData_mem_or P d x with hzp | ⟨i, rfl⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzp
    have h1 : d.rho * x * d.rho⁻¹ = x := by rw [← hx d.rho]; group
    rw [← hk] at h1
    have h2 : d.rho * d.tau ^ k * d.rho⁻¹ = (d.tau ^ k)⁻¹ := by
      have hh := map_zpow (MulAut.conj d.rho) d.tau k
      rw [MulAut.conj_apply, MulAut.conj_apply, d.rho_conj, inv_zpow] at hh
      exact hh
    have hxinv : x = x⁻¹ := by
      rw [← hk]
      exact h1.symm.trans h2
    rw [pow_two]
    exact inv_eq_iff_mul_eq_one.mp hxinv.symm
  · have hconj : (d.rho * d.tau ^ i) * d.tau * (d.rho * d.tau ^ i)⁻¹ = d.tau⁻¹ :=
      (Work.BrauerSuzuki.Quaternion.rho_mul_pow_order d i).2
    have hcen : (d.rho * d.tau ^ i) * d.tau * (d.rho * d.tau ^ i)⁻¹ = d.tau := by
      rw [hx d.tau]; group
    have htau : d.tau = d.tau⁻¹ := hcen.symm.trans hconj
    have htau2 : d.tau ^ 2 = 1 := by
      rw [pow_two]
      exact inv_eq_iff_mul_eq_one.mp htau.symm
    exfalso
    have hdvd : 2 ^ d.n ∣ 2 := by
      rw [← d.tau_order]
      exact orderOf_dvd_iff_pow_eq_one.mpr htau2
    have hle : 2 ^ d.n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 4 ≤ 2 ^ d.n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ d.n := Nat.pow_le_pow_right (by norm_num) d.hn
    omega

/-- A Sylow `2`-subgroup `T` of a finite group `G` whose Sylow `2`-subgroup `S` (not
necessarily equal to `T`) is generalized quaternion has the structure used by Dade: the
central elements of `T` are involutions, and `T` has at most one involution.

Indeed, `S` and `T` are conjugate, so `Sylow.equiv S T` pushes the generalized quaternion
presentation of `S` to one of `T`; then `genQuaternionData_basic` gives the (unique) involution
of `↥T` and `genQuaternionData_center_sq` gives the square of a central element. -/
theorem sylow_conj_structure {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (T : Sylow 2 G) :
    (∀ x : G, x ∈ (T : Subgroup G) → (∀ y ∈ (T : Subgroup G), x * y = y * x) → x ^ 2 = 1) ∧
    (∀ u v : G, u ∈ (T : Subgroup G) → v ∈ (T : Subgroup G) → orderOf u = 2 → orderOf v = 2 → u = v) := by
  classical
  -- `T` is conjugate to `S`, hence generalized quaternion as well
  have hgen : Work.BrauerSuzuki.IsGenQuaternion ↥T :=
    Work.BrauerSuzuki.Sylow.isGenQuaternion_of_mulEquiv (Sylow.equiv S T) ⟨d⟩
  obtain ⟨dT⟩ := hgen
  have hbasic := Work.BrauerSuzuki.Quaternion.genQuaternionData_basic dT
  constructor
  · intro x hxT hxc
    -- in `↥T`, the element `x` is central, so its square is `1` there
    have hsq : (⟨x, hxT⟩ : ↥T) ^ 2 = 1 := by
      have hcent : ∀ y : ↥T, (⟨x, hxT⟩ : ↥T) * y = y * ⟨x, hxT⟩ := by
        intro y
        exact Subtype.ext (hxc (y : G) y.2)
      exact genQuaternionData_center_sq dT hcent
    have := congrArg Subtype.val hsq
    simpa [Subgroup.coe_pow] using this
  · intro u v hu hv hu2 hv2
    -- both `u` and `v` equal the unique involution of `↥T`
    have hu2' : orderOf (⟨u, hu⟩ : ↥T) = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
    have hv2' : orderOf (⟨v, hv⟩ : ↥T) = 2 := by rw [Subgroup.orderOf_mk]; exact hv2
    have huniq := hbasic.2.2.2.1
    have h1 := huniq ⟨u, hu⟩ hu2'
    have h2 := huniq ⟨v, hv⟩ hv2'
    exact congrArg Subtype.val (h1.trans h2.symm)

end Work.BrauerSuzuki.Dade
