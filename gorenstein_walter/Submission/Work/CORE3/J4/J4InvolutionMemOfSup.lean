import Mathlib
import Submission.Work.CORE3.Defs

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.CORE3.J4

/-- In `U ⊔ V` with `V` normalised by `U`, `V ⊓ U = ⊥` and `|U|` odd, every involution of the
subgroup `U ⊔ V` lies in `V`.

Proof: `U ⊔ V = V·U`, so write `s = b·a` with `b ∈ V`, `a ∈ U`.  From `s² = 1` we get
`b·a·b·a = 1`, i.e. `a·b·a = b⁻¹`.  Since `b∈V`, `a∈U` and `U` normalises `V`, the element
`a b a⁻¹ = (a b a)(a a)⁻¹` lies in `V`, whence `a² = (a b a⁻¹)⁻¹ b⁻¹ ∈ V`; also `a² ∈ U`, so
`a² ∈ V ⊓ U = ⊥`, i.e. `a² = 1`.  As `|U|` is odd this forces `a = 1`, and then `s = b ∈ V`. -/
theorem involution_mem_of_mem_sup {G : Type} [Group G] [Finite G] {V U : Subgroup G} {s : G}
    (hVUdisj : V ⊓ U = ⊥) (hUV : U ≤ Subgroup.normalizer (V : Set G)) (hUodd : Odd (Nat.card U))
    (hsW : s ∈ V ⊔ U) (hs2 : orderOf s = 2) : s ∈ V := by
  -- work inside the group `U ⊔ V`
  have hW : s ∈ U ⊔ V := by
    rw [sup_comm]
    exact hsW
  have hVnorm : (V.subgroupOf (U ⊔ V)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hUV
  haveI := hVnorm
  have hsup : (V.subgroupOf (U ⊔ V)) ⊔ (U.subgroupOf (U ⊔ V)) = ⊤ := by
    have h := Subgroup.codisjoint_subgroupOf_sup U V
    rw [codisjoint_comm] at h
    rw [codisjoint_iff] at h
    exact h
  have huniv : (Set.univ : Set ↥(U ⊔ V)) =
      (V.subgroupOf (U ⊔ V) : Set ↥(U ⊔ V)) * (U.subgroupOf (U ⊔ V) : Set ↥(U ⊔ V)) := by
    rw [← Subgroup.coe_top, ← hsup]
    exact Subgroup.normal_mul (V.subgroupOf (U ⊔ V)) (U.subgroupOf (U ⊔ V))
  -- decompose `s = b * a` with `b ∈ V`, `a ∈ U`
  set sN : ↥(U ⊔ V) := ⟨s, hW⟩ with hsN
  have hsNmem : sN ∈ (V.subgroupOf (U ⊔ V) : Set ↥(U ⊔ V)) *
      (U.subgroupOf (U ⊔ V) : Set ↥(U ⊔ V)) := by
    rw [← huniv]
    exact Set.mem_univ sN
  obtain ⟨b, hb, a, ha, hba⟩ := Set.mem_mul.mp hsNmem
  have hbV : (b : G) ∈ V := Subgroup.mem_subgroupOf.mp hb
  have haU : (a : G) ∈ U := Subgroup.mem_subgroupOf.mp ha
  have hbaG : (b : G) * (a : G) = s := by
    have h := congrArg (fun x : ↥(U ⊔ V) => (x : G)) hba
    simpa [hsN] using h
  -- `s ^ 2 = 1`
  have hsq : s ^ 2 = 1 := by
    rw [← hs2]
    exact pow_orderOf_eq_one s
  have hmul : ((b : G) * (a : G)) ^ 2 = 1 := by
    rw [hbaG]
    exact hsq
  -- `a * b * a = b⁻¹`
  have hmain : (a : G) * (b : G) * (a : G) = (b : G)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hmul, pow_two]
    simp only [mul_assoc]
  have hsplit : (a : G) * (b : G) * (a : G) =
      ((a : G) * (b : G) * (a : G)⁻¹) * (a : G) ^ 2 := by
    group
  -- the conjugate `a * b * a⁻¹` lies in `V` since `a ∈ U` normalises `V`
  have hconj : (a : G) * (b : G) * (a : G)⁻¹ ∈ V := by
    have haN : (a : G) ∈ Subgroup.normalizer (V : Set G) := hUV haU
    exact (Subgroup.mem_normalizer_iff.mp haN (b : G)).mp hbV
  have ha2V : (a : G) ^ 2 ∈ V := by
    have hkey : ((a : G) * (b : G) * (a : G)⁻¹) * (a : G) ^ 2 = (b : G)⁻¹ := by
      rw [← hsplit]
      exact hmain
    have ha2eq : (a : G) ^ 2 =
        ((a : G) * (b : G) * (a : G)⁻¹)⁻¹ * (b : G)⁻¹ := by
      rw [← hkey]
      group
    rw [ha2eq]
    exact V.mul_mem (V.inv_mem hconj) (V.inv_mem hbV)
  have ha2U : (a : G) ^ 2 ∈ U := U.pow_mem haU 2
  -- hence `a² = 1` as `V ⊓ U = ⊥`
  have ha2one : (a : G) ^ 2 = 1 := by
    have hmem : (a : G) ^ 2 ∈ V ⊓ U := ⟨ha2V, ha2U⟩
    rw [hVUdisj] at hmem
    exact Subgroup.mem_bot.mp hmem
  -- and `a = 1` since `|U|` is odd
  have haU2 : (⟨(a : G), haU⟩ : ↥U) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using ha2one
  have hone : orderOf (⟨(a : G), haU⟩ : ↥U) = 1 := by
    have hdvd2 : orderOf (⟨(a : G), haU⟩ : ↥U) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr haU2
    have hdvdU : orderOf (⟨(a : G), haU⟩ : ↥U) ∣ Nat.card U :=
      orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact h
    · exfalso
      have h2 : 2 ∣ Nat.card U := h ▸ hdvdU
      rw [Nat.dvd_iff_mod_eq_zero] at h2
      have hodd : Nat.card U % 2 = 1 := Nat.odd_iff.mp hUodd
      omega
  have ha1 : (a : G) = 1 := by
    have h := congrArg (fun x : ↥U => (x : G)) (orderOf_eq_one_iff.mp hone)
    simpa using h
  rw [← hbaG, ha1, mul_one]
  exact hbV

theorem J4InvolutionMemOfSup {G : Type} [Group G] [Finite G] {V U : Subgroup G} {s : G}
    (hV4 : Work.GW2.IsFourGroup V) (hVUdisj : V ⊓ U = ⊥)
    (hUV : U ≤ Subgroup.normalizer (V : Set G)) (hUodd : Odd (Nat.card U))
    (hsW : s ∈ V ⊔ U) (hs2 : orderOf s = 2) : s ∈ V :=
  involution_mem_of_mem_sup hVUdisj hUV hUodd hsW hs2

end Work.CORE3.J4
