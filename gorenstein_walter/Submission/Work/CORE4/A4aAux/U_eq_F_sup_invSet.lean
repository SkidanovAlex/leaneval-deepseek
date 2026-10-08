import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot

namespace Work.CORE4.A4aAux

open Work.GW2 Subgroup

/-- **Bender 1.5, decomposition form.**  If the involution `s` normalizes the odd-order subgroup
`U`, then every `u ∈ U` is a product `c · i` with `c ∈ C_U(s)` and
`i ∈ I_U(s) = {i ∈ U | s i s⁻¹ = i⁻¹}`; equivalently `U = C_U(s) · I_U(s)`.

Route.  Conjugation by `s` is an involutive automorphism `φ` of `G` preserving `U`.  Put
`d = (φ u)⁻¹ u ∈ U`; then `φ d = d⁻¹`, and since `|U|` is odd, `(k+1)·2 = |U| + 1` where
`|U| = 2k+1`, so `i = d^(k+1)` satisfies `i² = d` and `φ i = i⁻¹`.  Then `c = u i⁻¹` is fixed by
`φ`, i.e. centralized by `s`, and `u = c · i`. -/
theorem exists_centralizer_mul_of_odd {G : Type} [Group G] (U : Subgroup G) {s : G}
    (hN : s ∈ Subgroup.normalizer (U : Set G)) (hss : s * s = 1) (hodd : Odd (Nat.card U))
    {u : G} (hu : u ∈ U) :
    ∃ c ∈ U ⊓ Subgroup.centralizer ({s} : Set G),
      ∃ i ∈ Work.GW2.invSet U s, u = c * i := by
  obtain ⟨k, hk⟩ := hodd
  -- conjugation by `s`, as an automorphism of `G`
  let φ : MulAut G := MulAut.conj s
  have hφ : ∀ x : G, φ x = s * x * s⁻¹ := fun x => MulAut.conj_apply s x
  have hφφ : ∀ x : G, φ (φ x) = x := by
    intro x
    rw [hφ, hφ]
    rw [show s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s⁻¹ * s⁻¹) by group, hss]
    have h2 : s⁻¹ * s⁻¹ = 1 := by rw [← mul_inv_rev, hss, inv_one]
    rw [h2, mul_one, one_mul]
  have hφU : ∀ x ∈ U, φ x ∈ U := fun x hx => by
    rw [hφ]
    exact (Subgroup.mem_normalizer_iff.mp hN x).mp hx
  -- the element `d` whose square root is the `I_U(s)`-factor
  set d : G := (φ u)⁻¹ * u with hd
  have hdU : d ∈ U := U.mul_mem (U.inv_mem (hφU u hu)) hu
  have hd1 : d ^ Nat.card U = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact Subgroup.orderOf_dvd_natCard U hdU
  have hφd : φ d = d⁻¹ := by
    have h1 : φ d = u⁻¹ * φ u := by rw [hd, map_mul, map_inv, hφφ]
    have h2 : d⁻¹ = u⁻¹ * φ u := by rw [hd, mul_inv_rev, inv_inv]
    rw [h1, h2]
  -- `i = d^(k+1)` satisfies `i² = d` and `s i s⁻¹ = i⁻¹`
  set i : G := d ^ (k + 1) with hi
  have hiU : i ∈ U := U.pow_mem hdU (k + 1)
  have hi2 : i ^ 2 = d := by
    rw [hi, ← pow_mul]
    have hexp : (k + 1) * 2 = Nat.card U + 1 := by omega
    rw [hexp, pow_succ, hd1, one_mul]
  have hφi : φ i = i⁻¹ := by rw [hi, map_pow, hφd, inv_pow]
  have hiI : s * i * s⁻¹ = i⁻¹ := by rw [← hφ i, hφi]
  -- the `C_U(s)`-factor `c = u i⁻¹`
  have hi_eq : i ^ 2 * i⁻¹ = i := by rw [pow_two, mul_assoc, mul_inv_cancel, mul_one]
  have hφu : φ u * i = u * i⁻¹ := by
    conv_lhs => rw [← hi_eq]
    rw [hi2, hd, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have hφc : φ (u * i⁻¹) = u * i⁻¹ := by
    rw [map_mul, map_inv, hφi, inv_inv]
    exact hφu
  have hfix : s * (u * i⁻¹) * s⁻¹ = u * i⁻¹ := (hφ (u * i⁻¹)).symm.trans hφc
  have hcomm : s * (u * i⁻¹) = (u * i⁻¹) * s := by
    have h1 : (s * (u * i⁻¹) * s⁻¹) * s = s * (u * i⁻¹) := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [← h1, hfix]
  refine ⟨u * i⁻¹, ?_, i, ⟨hiU, hiI⟩, by group⟩
  refine Subgroup.mem_inf.mpr ⟨U.mul_mem hu (U.inv_mem hiU), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact hcomm

/-- **`U = F ⊔ I_U(s)`** in the §4 configuration with `B₀ = F`.

Under `Case2Pre B D` the centralizer `C_U(s) = B.U ⊓ C(s)` is exactly `D.B0`, and the extra
hypothesis `D.B0 = D.F` makes it `D.F`.  Bender 1.5 (`exists_centralizer_mul_of_odd`) turns every
`u ∈ B.U` into a product of an element of `C_U(s) = D.F` and an element of
`I_U(s) = invSet B.U D.s`, whose underlying set is `Is`; hence `B.U ≤ D.F ⊔ Is`.  The reverse
inclusion is `D.F ≤ B.U` and `Is ⊆ B.U`. -/
theorem U_eq_F_sup_invSet (Ip : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B),
      Work.GW2.Case2Pre B D → D.B0 = D.F → ∀ Is : Subgroup G,
        (Is : Set G) = Work.GW2.invSet B.U D.s → B.U = D.F ⊔ Is := by
  intro G _ _ B D hPre hB0F Is hIs
  refine le_antisymm ?_ ?_
  · -- `B.U ≤ D.F ⊔ Is`
    intro u hu
    -- `s ∈ S ≤ H` normalizes `U = O(H)`.
    have hsS : D.s ∈ (B.S : Subgroup G) := Work.GW2.Case2Data.s_mem_S B D
    have hsN : D.s ∈ Subgroup.normalizer ((B.U : Subgroup G) : Set G) := by
      have hsH : D.s ∈ B.H := B.S_le_H hsS
      have hUnorm : ∀ y ∈ B.U, ∀ k ∈ B.H, k * y * k⁻¹ ∈ B.U := fun y hy k hk =>
        (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal y k hy hk
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => hUnorm y hy D.s hsH, fun hy => ?_⟩
      have h2 := hUnorm (D.s * y * D.s⁻¹) hy D.s⁻¹ (B.H.inv_mem hsH)
      have h3 : D.s⁻¹ * (D.s * y * D.s⁻¹) * (D.s⁻¹)⁻¹ = y := by group
      rwa [h3] at h2
    have hss : D.s * D.s = 1 := by
      have h : D.s ^ 2 = 1 := by rw [← D.s_order]; exact pow_orderOf_eq_one D.s
      simpa [pow_two] using h
    obtain ⟨c, hc, i, hi, hci⟩ :=
      exists_centralizer_mul_of_odd B.U hsN hss B.U_odd hu
    -- `C_U(s) = B₀ = F`, so the centralizing factor lands in `D.F`.
    have hcF : c ∈ D.F := by
      have hcB0 : c ∈ D.B0 := by
        rw [Work.GW2.Case2Pre.B0_eq B D hPre]
        exact hc
      rwa [hB0F] at hcB0
    have hiIs : i ∈ Is := by
      show i ∈ (Is : Set G)
      rw [hIs]
      exact hi
    rw [hci]
    exact Subgroup.mul_mem_sup hcF hiIs
  · -- `D.F ⊔ Is ≤ B.U`
    refine sup_le (Work.GW2.Case2Data.F_le_U B D) ?_
    intro x hx
    have hx' : x ∈ Work.GW2.invSet B.U D.s := by rw [← hIs]; exact hx
    exact hx'.1

end Work.CORE4.A4aAux
