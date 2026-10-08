import Mathlib
import Submission.Work.BrauerSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

variable {P : Type*} [Group P]
variable (d : Work.BrauerSuzuki.GenQuaternionData P)

/-! ## Conjugation by `rho` on `⟨tau⟩`

In the generalized quaternion presentation `d`, conjugation by `rho` inverts every power of
`tau`, hence every element of the cyclic subgroup `⟨tau⟩`.  Since `rho * rho = tau ^ (2 ^ (n-1))`
lies in `⟨tau⟩` as well, this is everything needed to see that `⟨tau⟩` (together with the single
coset `⟨tau⟩ * rho`) exhausts `P`, which is the content of the final induction. -/

/-- If a fixed element `x` conjugates `tau` to `tau⁻¹`, then it conjugates every integral power
of `tau` to the inverse power. -/
private theorem conj_zpow_of_conj {x : P} (h : x * d.tau * x⁻¹ = d.tau⁻¹) (i : ℤ) :
    x * d.tau ^ i * x⁻¹ = d.tau ^ (-i) := by
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h, inv_zpow, zpow_neg]

/-- `rho` conjugates every integral power of `tau` to the inverse power. -/
theorem genQuaternionData_rho_conj_zpow (i : ℤ) :
    d.rho * d.tau ^ i * d.rho⁻¹ = d.tau ^ (-i) :=
  conj_zpow_of_conj d d.rho_conj i

/-- `rho⁻¹` also conjugates every integral power of `tau` to the inverse power: conjugation by
`rho` is inversion on `⟨tau⟩`, which is an involution, so its inverse does the same. -/
theorem genQuaternionData_rho_inv_conj_zpow (i : ℤ) :
    d.rho⁻¹ * d.tau ^ i * d.rho = d.tau ^ (-i) := by
  have h1 : d.rho⁻¹ * d.tau * (d.rho⁻¹)⁻¹ = d.tau⁻¹ := by
    rw [inv_inv]
    have h2 : d.rho⁻¹ * d.tau⁻¹ * d.rho = d.tau := by rw [← d.rho_conj]; group
    calc d.rho⁻¹ * d.tau * d.rho = (d.rho⁻¹ * d.tau⁻¹ * d.rho)⁻¹ := by group
      _ = d.tau⁻¹ := by rw [h2]
  simpa using conj_zpow_of_conj d h1 i

/-- Conjugation by `rho` inverts the elements of `⟨tau⟩`. -/
theorem genQuaternionData_rho_conj_mem_inv {h : P}
    (hh : h ∈ Subgroup.zpowers d.tau) : d.rho * h * d.rho⁻¹ = h⁻¹ := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  rw [genQuaternionData_rho_conj_zpow, zpow_neg]

/-- Conjugation by `rho⁻¹` inverts the elements of `⟨tau⟩`. -/
theorem genQuaternionData_rho_inv_conj_mem_inv {h : P}
    (hh : h ∈ Subgroup.zpowers d.tau) : d.rho⁻¹ * h * d.rho = h⁻¹ := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  rw [genQuaternionData_rho_inv_conj_zpow, zpow_neg]

/-- The square of `rho` lies in `⟨tau⟩`: it is the central involution `tau ^ (2 ^ (n-1))`. -/
theorem genQuaternionData_rho_sq_mem : d.rho ^ 2 ∈ Subgroup.zpowers d.tau := by
  rw [d.rho_sq]
  exact Subgroup.mem_zpowers_iff.mpr ⟨(2 ^ (d.n - 1) : ℤ), zpow_natCast _ _⟩

/-- `rho` is not a power of `tau`: otherwise conjugation by `rho` and conjugation by a power of
`tau` would agree on `tau`, forcing `tau = tau⁻¹` and hence `2 ^ n ∣ 2`, contrary to `n ≥ 2`. -/
theorem genQuaternionData_rho_notMem_zpowers_tau : d.rho ∉ Subgroup.zpowers d.tau := by
  intro hr
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hr
  -- Conjugation by `rho = tau ^ i` is conjugation by a power of `tau`, hence trivial on `tau`,
  -- while it also sends `tau` to `tau⁻¹`.
  have hconj : (MulAut.conj (d.tau ^ i)) d.tau = d.tau⁻¹ := by
    rw [hi, MulAut.conj_apply, d.rho_conj]
  have hid : (MulAut.conj (d.tau ^ i)) d.tau = d.tau := by
    rw [MulAut.conj_apply]; group
  have htau : d.tau⁻¹ = d.tau := hconj.symm.trans hid
  have h2 : d.tau ^ 2 = 1 := by
    rw [pow_two]; nth_rewrite 2 [← htau]; rw [mul_inv_cancel]
  have hdvd : 2 ^ d.n ∣ 2 := by
    rw [← d.tau_order]
    exact orderOf_dvd_iff_pow_eq_one.mpr h2
  have hle : 2 ^ d.n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 2 ^ 2 ≤ 2 ^ d.n := Nat.pow_le_pow_right (by norm_num) d.hn
  omega

/-- Multiplication step of the final induction: the set of `b` with `b * rho ∈ ⟨tau⟩` or
`b ∈ ⟨tau⟩` is closed under products. -/
private theorem genQuaternionData_coset_step (x y : P)
    (hx : x * d.rho ∈ Subgroup.zpowers d.tau ∨ x ∈ Subgroup.zpowers d.tau)
    (hy : y * d.rho ∈ Subgroup.zpowers d.tau ∨ y ∈ Subgroup.zpowers d.tau) :
    x * y * d.rho ∈ Subgroup.zpowers d.tau ∨ x * y ∈ Subgroup.zpowers d.tau := by
  rcases hx with hx1 | hx0
  · rcases hy with hy1 | hy0
    · -- `x * rho` and `y * rho` both lie in `⟨tau⟩`: then `x = (x * rho) * rho⁻¹` and
      -- `y = (y * rho) * rho⁻¹`, so `x * y = (x * rho) * (y * rho)⁻¹ * rho⁻²` lies in `⟨tau⟩`.
      right
      have hidx : x = (x * d.rho) * d.rho⁻¹ := by group
      have hidy : y = (y * d.rho) * d.rho⁻¹ := by group
      have hz2 : d.rho⁻¹ * (y * d.rho) = (y * d.rho)⁻¹ * d.rho⁻¹ := by
        rw [← genQuaternionData_rho_inv_conj_mem_inv d hy1]; group
      have heq : x * y = (x * d.rho) * (y * d.rho)⁻¹ * (d.rho ^ 2)⁻¹ := by
        have h2 : x * y = ((x * d.rho) * d.rho⁻¹) * ((y * d.rho) * d.rho⁻¹) := by
          rw [← hidx, ← hidy]
        rw [h2]
        have h3 : ((x * d.rho) * d.rho⁻¹) * ((y * d.rho) * d.rho⁻¹)
            = (x * d.rho) * (d.rho⁻¹ * (y * d.rho)) * d.rho⁻¹ := by group
        rw [h3, hz2]
        group
      rw [heq]
      exact mul_mem (mul_mem hx1 (Subgroup.inv_mem _ hy1))
        (Subgroup.inv_mem _ (genQuaternionData_rho_sq_mem d))
    · -- `x * rho ∈ ⟨tau⟩` and `y ∈ ⟨tau⟩`: `x * y * rho = (x * rho) * y⁻¹ ∈ ⟨tau⟩`.
      left
      have heq : x * y * d.rho = (x * d.rho) * (d.rho⁻¹ * y * d.rho) := by group
      rw [heq, genQuaternionData_rho_inv_conj_mem_inv d hy0]
      exact mul_mem hx1 (Subgroup.inv_mem _ hy0)
  · rcases hy with hy1 | hy0
    · -- `x ∈ ⟨tau⟩` and `y * rho ∈ ⟨tau⟩`: `x * y * rho = x * (y * rho) ∈ ⟨tau⟩`.
      left
      rw [mul_assoc]
      exact mul_mem hx0 hy1
    · -- both in `⟨tau⟩`.
      right
      exact mul_mem hx0 hy0

/-- In a generalized quaternion group `d : GenQuaternionData P`, the cyclic subgroup `⟨tau⟩` has
index two.  Indeed `P = ⟨tau, rho⟩` and the image of `rho` generates `P/⟨tau⟩`, with
`(rho ⟨tau⟩)^2 = rho^2 ⟨tau⟩ = tau^(2^(n-1)) ⟨tau⟩ = ⟨tau⟩`, while `rho ∉ ⟨tau⟩` because
otherwise `rho_conj` would give `tau = tau⁻¹`, contradicting `orderOf tau = 2^n ≥ 4`. -/
theorem genQuaternionData_index_zpowers_tau (P : Type*) [Group P] [Finite P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) : (Subgroup.zpowers d.tau).index = 2 := by
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨d.rho, genQuaternionData_rho_notMem_zpowers_tau d, fun b => ?_⟩
  -- It remains to show that every `b` lies in `⟨tau⟩ * rho⁻¹ = ⟨tau⟩ * rho` or in `⟨tau⟩`;
  -- equivalently, that the predicate `b ↦ (b * rho ∈ ⟨tau⟩ ∨ b ∈ ⟨tau⟩)` holds for all `b`.
  have hb : b ∈ Subgroup.closure ({d.tau, d.rho} : Set P) := by
    rw [d.closure_eq_top]; exact Subgroup.mem_top b
  refine Subgroup.closure_induction (p := fun g _ =>
    g * d.rho ∈ Subgroup.zpowers d.tau ∨ g ∈ Subgroup.zpowers d.tau) ?_ ?_ ?_ ?_ hb
  · -- the generators `tau` and `rho`
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (Subgroup.mem_zpowers d.tau)
    · exact Or.inl (by rw [← pow_two]; exact genQuaternionData_rho_sq_mem d)
  · exact Or.inr (Subgroup.one_mem _)
  · intro x y _ _ hpx hpy
    exact genQuaternionData_coset_step d x y hpx hpy
  · -- if `x * rho ∈ ⟨tau⟩` then `x⁻¹ * rho = ((x * rho) * rho²) ∈ ⟨tau⟩`, since
    -- `x⁻¹ * rho = rho * (x * rho)⁻¹ * rho = (rho * (x * rho)⁻¹ * rho⁻¹) * rho²`.
    intro x _ hpx
    rcases hpx with hx1 | hx0
    · left
      have hxeq : x = (x * d.rho) * d.rho⁻¹ := by group
      have heq : x⁻¹ * d.rho = d.rho * (x * d.rho)⁻¹ * d.rho := by
        conv_lhs => rw [hxeq]
        group
      rw [heq]
      have heq2 : d.rho * (x * d.rho)⁻¹ * d.rho
          = (d.rho * (x * d.rho)⁻¹ * d.rho⁻¹) * d.rho ^ 2 := by group
      rw [heq2, genQuaternionData_rho_conj_mem_inv d (Subgroup.inv_mem _ hx1), inv_inv]
      exact mul_mem hx1 (genQuaternionData_rho_sq_mem d)
    · right
      exact Subgroup.inv_mem _ hx0

end Work.BrauerSuzuki.Quaternion
