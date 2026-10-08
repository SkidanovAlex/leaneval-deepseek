import Mathlib
import Submission.Work.GLUE.Defs
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.B_normalizes_K
import Submission.Work.BG.thmCSec3
import Submission.Work.BG.indexEqCardOfNormalSup

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16

/-- If `K` is the largest odd-order subgroup of `H` inverted by `s`, then every `x ∈ H`
commuting with `s` (i.e. `s * x * s⁻¹ = x`) normalizes `K`: conjugation by such an `x` maps
`K` onto an odd-order subgroup of `H` inverted by `s`, to which maximality of `K` applies. -/
private lemma conj_mem_of_isMaxInverted {G : Type*} [Group G] {H K : Subgroup G} {s x : G}
    (h : IsMaxInverted H s K) (hxH : x ∈ H) (hxs : s * x * s⁻¹ = x) {y : G} (hy : y ∈ K) :
    x * y * x⁻¹ ∈ K := by
  have hmap : K.map (MulAut.conj x).toMonoidHom ≤ K := by
    refine h.2.2.2 _ ?_ ?_ ?_
    · intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact H.mul_mem (H.mul_mem hxH (h.1 hw)) (H.inv_mem hxH)
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom)
        (MulAut.conj x).injective]
      exact h.2.1
    · intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc s * (x * w * x⁻¹) * s⁻¹
          = (s * x * s⁻¹) * (s * w * s⁻¹) * (s * x * s⁻¹)⁻¹ := by group
        _ = x * w⁻¹ * x⁻¹ := by rw [hxs, h.2.2.1 w hw]
        _ = (x * w * x⁻¹)⁻¹ := by group
  have hmem := hmap (Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hy)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmem
  exact hmem

/-- Under the hypotheses `Work.GW2.C16.ThmCHyps D K1 K2` of Bender–Glauberman's Theorem C, the
number `|K₁ ⊓ K₂|` divides `|U : B₁|` (so that `2 * |K₁ ⊓ K₂|` divides `k = k₁ + k₂`, BG p. 211).

Route.  Let `K = K₁ ⊓ K₂`.  Write `U = (B₁ ⊓ K₂) × (B ⊔ K)`, the internal direct decomposition
furnished by `ThmCHyps`.

* `K ◁ U`: both direct factors of `U` normalize `K`.  `B` does by `Work.BG.B_normalizes_K`
  (maximality of `K₁`, `K₂`), and `B₁ ⊓ K₂` does because it lies in `B₁ ≤ N_G(K₁)`
  (`conj_mem_of_isMaxInverted`: an element of `H` commuting with `t₁` conjugates the odd
  `t₁`-inverted subgroup `K₁` into itself) and in `K₂ ≤ N_G(K₂)`.
* `B₁ ⊓ K = ⊥`: `K ≤ K₁`, `B₁ ≤ C_G(t₁)`, and an element of `K₁` is inverted by `t₁`; an
  element that is simultaneously centralized and inverted satisfies `x = x⁻¹`, hence `x² = 1`,
  while it has odd order (`K₁` is odd), so `x = 1`.
* `U = B₁ ⊔ K`: `U = (B₁ ⊓ K₂) ⊔ (B ⊔ K)`, and `B ≤ B₁ ≤ U`, `K ≤ U`.

Inside the group `↥U` the subgroups `B₁` and `K` are therefore complementary (`⊔ = ⊤`,
`⊓ = ⊥`), with `K` normal; the internal direct product decomposition
(`Work.BG.indexEqCardOfNormalSup`) gives `|U : B₁| = |K|`, whence the divisibility. -/
theorem cardKdvdRelIndexUB1 {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G)
    (K1 K2 : Subgroup G) (hHyps : Work.GW2.C16.ThmCHyps D K1 K2) :
    Nat.card (K1 ⊓ K2 : Subgroup G) ∣ D.B1.relIndex D.U := by
  obtain ⟨hmax1, hmax2, hdir, -, -, -⟩ := hHyps
  -- ### `B₁ ≤ N_G(K₁)`
  have hB1N : ∀ x ∈ D.B1, ∀ y ∈ K1, x * y * x⁻¹ ∈ K1 := by
    intro x hx y hy
    obtain ⟨hxU, hxc⟩ := Subgroup.mem_inf.mp hx
    have hxH : x ∈ D.H := oddCoreIn_le D.H hxU
    have hcomm : x * D.t1 = D.t1 * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
    have hfix : D.t1 * x * D.t1⁻¹ = x := by
      rw [hcomm.symm, mul_assoc, mul_inv_cancel, mul_one]
    exact conj_mem_of_isMaxInverted hmax1 hxH hfix hy
  -- ### `K = K₁ ⊓ K₂` is normal in `U`
  have hUN : D.U ≤ Subgroup.normalizer ((K1 ⊓ K2 : Subgroup G) : Set G) := by
    rw [← hdir.1]
    refine sup_le ?_ ?_
    · -- `B₁ ⊓ K₂ ≤ N_G(K₁ ⊓ K₂)`
      rw [Subgroup.le_normalizer_iff]
      intro x hx y hy
      obtain ⟨hxB1, hxK2⟩ := Subgroup.mem_inf.mp hx
      exact ⟨hB1N x hxB1 y hy.1,
        K2.mul_mem (K2.mul_mem hxK2 hy.2) (K2.inv_mem hxK2)⟩
    · -- `B ⊔ (K₁ ⊓ K₂) ≤ N_G(K₁ ⊓ K₂)`
      exact sup_le
        (Subgroup.le_normalizer_iff_commutator_le_right.mpr (B_normalizes_K D K1 K2 hmax1 hmax2))
        Subgroup.le_normalizer
  -- ### `B₁ ⊓ K = ⊥`
  have hB1K1 : D.B1 ⊓ K1 = ⊥ := by
    have hK1 : K1 ⊓ Subgroup.centralizer ({D.t1} : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxK1, hxcent⟩ := hx
      have hcomm : x * D.t1 = D.t1 * x :=
        Subgroup.mem_centralizer_singleton_iff.mp hxcent
      have hfix : D.t1 * x * D.t1⁻¹ = x := by
        rw [hcomm.symm, mul_assoc, mul_inv_cancel, mul_one]
      have hinv : D.t1 * x * D.t1⁻¹ = x⁻¹ := hmax1.2.2.1 x hxK1
      have hxinv : x = x⁻¹ := hfix.symm.trans hinv
      have hx2 : x ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 2 [hxinv]
        exact mul_inv_cancel x
      have hzx : Subgroup.zpowers x ≤ K1 := by rw [Subgroup.zpowers_le]; exact hxK1
      have hdvd : orderOf x ∣ Nat.card K1 := by
        rw [← Nat.card_zpowers]; exact Subgroup.card_dvd_of_le hzx
      have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
      have hodd : Odd (orderOf x) := Odd.of_dvd_nat hmax1.2.1 hdvd
      have hone : orderOf x = 1 := by
        obtain ⟨k, hk⟩ := hodd
        have hle : orderOf x ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
        omega
      rw [Subgroup.mem_bot]
      exact orderOf_eq_one_iff.mp hone
    refine le_bot_iff.mp ?_
    calc D.B1 ⊓ K1 ≤ K1 ⊓ Subgroup.centralizer ({D.t1} : Set G) :=
          le_inf inf_le_right (le_trans inf_le_left inf_le_right)
      _ = ⊥ := hK1
  have hinf : D.B1 ⊓ (K1 ⊓ K2) = ⊥ := by
    refine le_bot_iff.mp ?_
    calc D.B1 ⊓ (K1 ⊓ K2) ≤ D.B1 ⊓ K1 := inf_le_inf_left D.B1 inf_le_left
      _ = ⊥ := hB1K1
  -- ### `U = B₁ ⊔ K`
  have hB1U : D.B1 ≤ D.U := inf_le_left
  have hKU : K1 ⊓ K2 ≤ D.U := by
    rw [← hdir.1]
    exact le_trans le_sup_right le_sup_right
  have hsup : D.U = D.B1 ⊔ (K1 ⊓ K2) := by
    refine le_antisymm ?_ (sup_le hB1U hKU)
    rw [← hdir.1]
    exact sup_le (le_trans inf_le_left le_sup_left)
      (sup_le (le_trans inf_le_left le_sup_left) le_sup_right)
  -- ### `B₁` and `K` are complementary in `↥U`, with `K` normal
  have hKnU : ((K1 ⊓ K2).subgroupOf D.U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKU).mpr hUN
  have hsup' : D.B1.subgroupOf D.U ⊔ (K1 ⊓ K2).subgroupOf D.U = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hB1U hKU, hsup]
    exact Subgroup.subgroupOf_self _
  have hinf' : D.B1.subgroupOf D.U ⊓ (K1 ⊓ K2).subgroupOf D.U = ⊥ := by
    have h : (D.B1 ⊓ (K1 ⊓ K2)).subgroupOf D.U =
        D.B1.subgroupOf D.U ⊓ (K1 ⊓ K2).subgroupOf D.U :=
      Subgroup.comap_inf D.B1 (K1 ⊓ K2) (D.U).subtype
    rw [hinf] at h
    rw [← h]
    exact Subgroup.bot_subgroupOf D.U
  have hidx : D.B1.relIndex D.U = Nat.card ↥((K1 ⊓ K2).subgroupOf D.U) :=
    indexEqCardOfNormalSup (D.B1.subgroupOf D.U) ((K1 ⊓ K2).subgroupOf D.U) hKnU hsup' hinf'
  have hcard : Nat.card ↥((K1 ⊓ K2).subgroupOf D.U) = Nat.card ↥(K1 ⊓ K2 : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKU).toEquiv
  have hEq : D.B1.relIndex D.U = Nat.card ↥(K1 ⊓ K2 : Subgroup G) := by
    rw [hidx]
    exact hcard
  exact ⟨1, by simp [hEq]⟩

end Work.BG
