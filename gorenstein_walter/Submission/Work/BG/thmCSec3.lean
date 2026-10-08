import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.GLUE.Defs
import Submission.Work.GLUE.PiCoreApi
import Submission.Work.GLUE.InBridge
import Submission.Work.BG.commutator_sup_inf_eq
import Submission.Work.BG.inf_commutator_sup_self
import Submission.Work.BG.B_normalizes_K
import Submission.Work.BG.t1t2_sq_centralizes_U

/-!
# BG Theorem C, §3 hypothesis (`ThmCSec3Prop`, design leaf "G6")

Under the hypotheses of Theorem C of Bender–Glauberman, the §3 situation holds:

* `S' = ⟨x² | x ∈ S₀⟩` centralizes `U` (i.e. `x² u = u x²` for `x ∈ S₀`, `u ∈ U`), and
* `B ⊄ U'`.

The first part is proved from the internal direct decomposition
`U = (B₁ ⊓ K₂) × (B ⊔ (K₁ ⊓ K₂))`: the generator `t₁t₂` of `S₀` *inverts* the first factor
(`B₁ ⊓ K₂` is centralized by `t₁` and inverted by `t₂`) and *centralizes* the second
(`B` is centralized by `t₁, t₂` and `K₁ ⊓ K₂` is inverted by both).  Hence `(t₁t₂)²`, and so
every `x²` with `x ∈ S₀ = zpowers (t₁t₂)`, centralizes `U`.

The second part reduces to a general group-theoretic fact about `C := B ⊔ K` (`K = K₁ ⊓ K₂`):
maximality of `Kᵢ` forces `B` to normalize `K` (`B_normalizes_K`), so `K ◁ C` and
`C/K ≅ B`; since `U' ⊓ C = C'` (as `U` is the internal direct product of `B₁ ⊓ K₂` and `C`),
`B ≤ U'` would force `B = B ⊓ C' = B'`, contradicting `B' ≠ B`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

theorem thmCSec3_zpow_sq {G : Type} [Group G] (a : G) (m : ℤ) :
    (a ^ m) ^ 2 = (a ^ 2) ^ m := by
  rw [show (a ^ m) ^ 2 = (a ^ m) ^ (2 : ℤ) from (zpow_natCast _ _).symm]
  rw [← zpow_mul]
  rw [show m * (2 : ℤ) = (2 : ℤ) * m from by ring]
  rw [zpow_mul]
  rw [show a ^ (2 : ℤ) = a ^ 2 from zpow_natCast _ _]

/-- `B ⊓ K₁ = ⊥`: an element of `B₁ = U ⊓ C_G(t₁)` lying in `K₁` (odd, `t₁`-inverted) must
be `1`, because it is both centralized and inverted by `t₁`. -/
theorem thmCSec3_B_inf_K1 {G : Type} [Group G] [Finite G] (D : BGData G) (K1 : Subgroup G)
    (h1 : IsMaxInverted D.H D.t1 K1) : D.B ⊓ K1 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxB, hxK1⟩ := hx
  have hxB1 : x ∈ D.B1 := (Subgroup.mem_inf.mp hxB).1
  have hxcent : x ∈ Subgroup.centralizer ({D.t1} : Set G) := (Subgroup.mem_inf.mp hxB1).2
  have hcomm : x * D.t1 = D.t1 * x := Subgroup.mem_centralizer_singleton_iff.mp hxcent
  have hfix : D.t1 * x * D.t1⁻¹ = x := by
    rw [hcomm.symm, mul_assoc, mul_inv_cancel, mul_one]
  have hinv : D.t1 * x * D.t1⁻¹ = x⁻¹ := h1.2.2.1 x hxK1
  have hxinv : x = x⁻¹ := hfix.symm.trans hinv
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hxinv]
    exact mul_inv_cancel x
  have hzx : Subgroup.zpowers x ≤ K1 := by rw [Subgroup.zpowers_le]; exact hxK1
  have hdvd : orderOf x ∣ Nat.card K1 := by
    rw [← Nat.card_zpowers]; exact Subgroup.card_dvd_of_le hzx
  have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
  have hodd : Odd (orderOf x) := Odd.of_dvd_nat h1.2.1 hdvd
  have hone : orderOf x = 1 := by
    obtain ⟨k, hk⟩ := hodd
    have hle : orderOf x ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    omega
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.mp hone

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem thmCSec3 : Work.GW2.C16.ThmCSec3Prop := by
  intro G _ _ D K1 K2 h1 h2 hd hB'
  refine ⟨?_, ?_⟩
  · -- `S'` centralizes `U`
    intro x hx u hu
    have hmem := t1t2_sq_centralizes_U D K1 K2 h1 h2 hd
    rw [D.gen] at hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hpow : x ^ 2 = ((D.t1 * D.t2) ^ 2) ^ m := by
      rw [← hm]; exact thmCSec3_zpow_sq _ _
    have hx2c : x ^ 2 ∈ Subgroup.centralizer ((D.U : Subgroup G) : Set G) := by
      rw [hpow]; exact Subgroup.zpow_mem _ hmem m
    rw [Subgroup.mem_centralizer_iff] at hx2c
    exact (hx2c u hu).symm
  · -- `B ⊄ U'`
    intro hBle
    have hAC : ⁅D.B1 ⊓ K2, D.B ⊔ (K1 ⊓ K2)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (hd.2.2 a ha c hc).symm
    have hcomm := commutator_sup_inf_eq (D.B1 ⊓ K2) (D.B ⊔ (K1 ⊓ K2)) hAC hd.2.1
    rw [hd.1] at hcomm
    have hBC : D.B ≤ D.B ⊔ (K1 ⊓ K2) := le_sup_left
    have hBleC : D.B ≤ ⁅D.B ⊔ (K1 ⊓ K2), D.B ⊔ (K1 ⊓ K2)⁆ := by
      have : D.B ≤ ⁅D.U, D.U⁆ ⊓ (D.B ⊔ (K1 ⊓ K2)) := le_inf hBle hBC
      rwa [hcomm] at this
    have hBK := B_normalizes_K D K1 K2 h1 h2
    have hBKinf : D.B ⊓ (K1 ⊓ K2) = ⊥ := by
      rw [eq_bot_iff]; intro x hx
      have h := thmCSec3_B_inf_K1 D K1 h1
      rw [eq_bot_iff] at h
      exact h ⟨(Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2.1⟩
    have hC' := inf_commutator_sup_self D.B (K1 ⊓ K2) hBK hBKinf
    have hEq : D.B = ⁅D.B, D.B⁆ := (inf_of_le_left hBleC).symm.trans hC'
    exact hB' hEq.symm

end Work.BG
