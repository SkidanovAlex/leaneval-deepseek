import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

/-- If `φ : F →* Y` has kernel contained in the center of `F`, and `s, t ∈ F` are
involutions (`s * s = 1`, `t * t = 1`) such that `s * t` has odd order, then `φ`
preserves the order of `s * t`.

The point is that `s` inverts `s * t`; hence any central element lying in the
cyclic subgroup `⟨s * t⟩` is fixed by `s` and simultaneously inverted, so it
satisfies `z = z⁻¹` and, because `orderOf (s * t)` is odd, must be trivial.
Thus `φ` is injective on `⟨s * t⟩`. -/
theorem orderOfMapEq {F : Type} [Group F] {Y : Type} [Group Y] {φ : F →* Y}
    (hker : φ.ker ≤ Subgroup.center F) {s t : F} (hs : s * s = 1) (ht : t * t = 1)
    (hodd : Odd (orderOf (s * t))) :
    orderOf (φ (s * t)) = orderOf (s * t) := by
  -- The order always divides down along a homomorphism.
  have hdiv1 : orderOf (φ (s * t)) ∣ orderOf (s * t) := orderOf_map_dvd φ (s * t)
  set m := orderOf (φ (s * t)) with hm
  -- `(s * t)^m` lies in the kernel, hence is central.
  have hmem : (s * t) ^ m ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    rw [show φ (s * t) ^ m = 1 from by rw [hm]; exact pow_orderOf_eq_one (φ (s * t))]
  have hcentral : (s * t) ^ m ∈ Subgroup.center F := hker hmem
  have hcomm : ∀ g : F, g * (s * t) ^ m = (s * t) ^ m * g :=
    Subgroup.mem_center_iff.mp hcentral
  -- `s` conjugates `s * t` to its inverse.
  have hconj : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hs, inv_eq_of_mul_eq_one_right ht]
    rw [← mul_assoc s s t, hs, one_mul]
  -- Centrality fixes `(s * t)^m` under this conjugation ...
  have step1 : s * (s * t) ^ m * s⁻¹ = (s * t) ^ m := by
    rw [hcomm s, mul_assoc, mul_inv_cancel, mul_one]
  -- ... while conjugation inverts it.
  have step2 : s * (s * t) ^ m * s⁻¹ = ((s * t) ^ m)⁻¹ := by
    rw [← conj_pow, hconj, inv_pow]
  have hy : (s * t) ^ m = ((s * t) ^ m)⁻¹ := step1.symm.trans step2
  have hsq : (s * t) ^ m * (s * t) ^ m = 1 := by
    have h := mul_inv_cancel ((s * t) ^ m)
    rwa [← hy] at h
  -- Hence `orderOf (s * t) ∣ 2 * m`, and oddness forces `orderOf (s * t) ∣ m`.
  have hp : (s * t) ^ (2 * m) = 1 := by
    rw [show 2 * m = m * 2 from Nat.mul_comm 2 m, pow_mul, pow_two, hsq]
  have hdiv2 : orderOf (s * t) ∣ 2 * m := orderOf_dvd_iff_pow_eq_one.mpr hp
  have hdiv2' : orderOf (s * t) ∣ m * 2 := by rw [Nat.mul_comm]; exact hdiv2
  have hcop : (orderOf (s * t)).Coprime 2 := hodd.coprime_two_right
  have hdiv3 : orderOf (s * t) ∣ m := hcop.dvd_of_dvd_mul_right hdiv2'
  have hba : orderOf (s * t) ∣ orderOf (φ (s * t)) := by rw [← hm]; exact hdiv3
  have heq : orderOf (φ (s * t)) = orderOf (s * t) := Nat.dvd_antisymm hdiv1 hba
  rw [hm]
  exact heq

end Work.PSU3.StageA
