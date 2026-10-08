import Mathlib
import Submission.Work.Models.Port.PSU3.Involutions
import Submission.Work.Models.Port.PSU3.Main
import Submission.Work.Models.Port.PSU3.Simple
import Submission.Work.Models.Port.PSU3.Torus
import Submission.Work.Models.Port.PSU3.Borel

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.ModelCentralizer

open Matrix LeanEval.GroupTheory.Defs

/-- In a subgroup of odd order every element is a square: for `x ∈ K` there is `y ∈ K` with
`y * y = x`.  (Indeed `x ^ Nat.card K = 1`, so `x ^ 1` is an even power of `x`.) -/
lemma exists_sq_eq_of_odd_card {G : Type*} [Group G] {K : Subgroup G}
    (hK : Odd (Nat.card K)) {x : G} (hx : x ∈ K) : ∃ y : G, y ∈ K ∧ y * y = x := by
  have hxcard : x ^ Nat.card K = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard K hx)
  obtain ⟨m, hm⟩ := exists_pow_eq_pow_two_mul hxcard hK 1
  refine ⟨x ^ m, Subgroup.pow_mem K hx m, ?_⟩
  calc x ^ m * x ^ m = x ^ (m + m) := by rw [pow_add]
    _ = x ^ (2 * m) := by congr 1; omega
    _ = x ^ 1 := hm.symm
    _ = x := by simp

/-- Every involution of the Borel subgroup `psu3B n` of `PSU(3,2ⁿ)` (the image of `B = U ⋊ T`
in `PSU(3,2ⁿ)`) is the image of a unipotent element `u(0,c)` with `c` in the fixed field of the
Frobenius `x ↦ x^(2ⁿ)`, i.e. in the additive group `Z(U) = Ω₁(U)` (of order `2ⁿ`). -/
theorem involution_psu3B_eq_image_uUg {n : ℕ} (hn : 1 ≤ n) {s : LeanEval.GroupTheory.Defs.PSU3Model n}
    (hs : s ∈ Submission.PSU3.psu3B n) (hs2 : orderOf s = 2) :
    ∃ (c : Submission.PSU3.F n) (hc : c ^ (2 ^ n) = c),
      s = Submission.PSU3.psu3Hom n
        ⟨Submission.PSU3.suUg n 0 c, Submission.PSU3.suU_le_SU3 n
          (Submission.PSU3.suUg_zero_mem n c hc)⟩ := by
  -- Lift `s` to an element `x` of the Borel subgroup `B ≤ SU(3,2ⁿ)`.
  obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp hs
  have hs2' : s * s = 1 := by
    have h : s ^ 2 = 1 := by
      have h1 := pow_orderOf_eq_one s
      rw [hs2] at h1
      exact h1
    simpa [pow_two] using h
  -- `x²` lies in the kernel `Z` of the projection; `Z` is central of odd order,
  -- so `x²` is a square in `Z` and `x` can be adjusted by a central element to an involution.
  have hx2ker : x * x ∈ (Submission.PSU3.psu3Hom n).ker := by
    rw [MonoidHom.mem_ker, map_mul, hxs, hs2']
  have hkerOdd : Odd (Nat.card ↥((Submission.PSU3.psu3Hom n).ker)) :=
    Submission.PSU3.odd_card_psu3Hom_ker n hn
  obtain ⟨z, hzk, hzz⟩ := exists_sq_eq_of_odd_card (K := (Submission.PSU3.psu3Hom n).ker)
    hkerOdd ((Submission.PSU3.psu3Hom n).ker.inv_mem hx2ker)
  have hzcent : ∀ g : ↥(Submission.PSU3.SU3 n), g * z = z * g :=
    Subgroup.mem_center_iff.mp ((Submission.PSU3.psu3Hom_ker_le_center n) hzk)
  set y : ↥(Submission.PSU3.SU3 n) := x * z with hy_def
  have hy2 : y * y = 1 := by
    rw [hy_def]
    calc (x * z) * (x * z) = x * (z * x) * z := by group
      _ = x * (x * z) * z := by rw [hzcent x]
      _ = (x * x) * (z * z) := by group
      _ = (x * x) * (x * x)⁻¹ := by rw [hzz]
      _ = 1 := mul_inv_cancel _
  have hyφ : Submission.PSU3.psu3Hom n y = s := by
    rw [hy_def, map_mul, hxs, MonoidHom.mem_ker.mp hzk, mul_one]
  have hyB : y ∈ Submission.PSU3.suBS n := by
    rw [hy_def]
    exact (Submission.PSU3.suBS n).mul_mem hx (Submission.PSU3.psu3Hom_ker_le_borel n hzk)
  -- An involution of the Borel subgroup of `SU(3,2ⁿ)` is unipotent.
  have hyU : y ∈ Submission.PSU3.suUS n :=
    Submission.PSU3.mem_suUS_of_sq_eq_one n hn hyB hy2
  -- Parametrise and use `u(b,c)² = 1 ↔ b = 0`.
  obtain ⟨b, c, hcond, hybc⟩ :=
    (Subgroup.mem_subgroupOf.mp hyU :
      (y : GL (Fin 3) (Submission.PSU3.F n)) ∈ Submission.PSU3.suU n)
  have hb0 : b = 0 := by
    apply (Submission.PSU3.suUg_sq_eq_one_iff n b c).mp
    have hygl : (y : GL (Fin 3) (Submission.PSU3.F n)) *
        (y : GL (Fin 3) (Submission.PSU3.F n)) = 1 := by
      have := congrArg Subtype.val hy2
      simpa using this
    rw [pow_two, ← hybc]
    exact hygl
  have hc : c ^ (2 ^ n) = c := by
    have h : c + c ^ (2 ^ n) = 0 := by
      rw [hcond, hb0, zero_pow (by positivity)]
    have h5 : c = - c ^ (2 ^ n) := eq_neg_of_add_eq_zero_left h
    rw [CharTwo.neg_eq] at h5
    exact h5.symm
  refine ⟨c, hc, ?_⟩
  rw [← hyφ]
  congr 1
  apply Subtype.ext
  rw [hybc, hb0]

end Work.PSU3.ModelCentralizer
