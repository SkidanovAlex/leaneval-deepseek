import Mathlib
import Submission.Work.GLUE.Defs

namespace Work.BG

open Work.GW2

/-- If `K` is the largest odd-order subgroup of `H` inverted by `s`, then every `x ∈ H`
commuting with `s` normalizes `K`: conjugation by such an `x` maps `K` onto an odd-order
subgroup of `H` inverted by `s`, to which maximality of `K` applies:
`t (x y x⁻¹) t⁻¹ = (t x t⁻¹)(t y t⁻¹)(t x t⁻¹)⁻¹ = x y⁻¹ x⁻¹ = (x y x⁻¹)⁻¹`. -/
private lemma conj_mem_of_isMaxInverted {G : Type} [Group G] {H K : Subgroup G} {s x : G}
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

/-- **BG 1981, Theorem C, §3 structural input.**  Let `D : Work.GW2.BGData G` be a
dihedral-Sylow-2 configuration, `K₁`, `K₂` the maximal odd-order subgroups of `H = C_G(t)`
inverted by the involutions `t₁`, `t₂`, and assume `U = O(H)` is the internal direct product
`U = (B₁ ⊓ K₂) × (B ⊔ (K₁ ⊓ K₂))`.  Then `K = K₁ ⊓ K₂` is a normal subgroup of `U` as well as
of `C = B ⊔ K`, it meets `B` trivially, and `C/K ≅ B`, i.e. `|C : K| = |B|`.

The single group-theoretic point is that `N_G(K₁)` contains `B₁ = U ⊓ C_G(t₁)` and `N_G(K₂)`
contains `B₂ = U ⊓ C_G(t₂)`: an element `x ∈ H` commuting with `tᵢ` conjugates every odd-order
`tᵢ`-inverted subgroup of `H` to another one, so maximality of `Kᵢ` forces `x Kᵢ x⁻¹ = Kᵢ`.
Since `B ⊓ K = ⊥` follows directly from `(B₁ ⊓ K₂) ⊓ (B ⊔ K) = ⊥`, the quotient of
`C = B ⊔ K` by the normal subgroup `K` is `B`. -/
theorem c3vbBKData {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G)
    (K1 K2 : Subgroup G) (h1 : Work.GW2.IsMaxInverted D.H D.t1 K1)
    (h2 : Work.GW2.IsMaxInverted D.H D.t2 K2)
    (hdir : Work.GW2.IsInternalDirect D.U (D.B1 ⊓ K2) (D.B ⊔ (K1 ⊓ K2))) :
    D.B ⊓ (K1 ⊓ K2) = ⊥ ∧
    ((K1 ⊓ K2).subgroupOf D.U).Normal ∧
    ((K1 ⊓ K2).subgroupOf (D.B ⊔ (K1 ⊓ K2))).Normal ∧
    ((K1 ⊓ K2).subgroupOf (D.B ⊔ (K1 ⊓ K2))).index = Nat.card ↥D.B := by
  -- `U ≤ H`
  have hUleH : D.U ≤ D.H := by
    show (oddCore ↥D.H).map D.H.subtype ≤ D.H
    exact Subgroup.map_subtype_le _
  have hsup : (D.B1 ⊓ K2) ⊔ (D.B ⊔ (K1 ⊓ K2)) = D.U := hdir.1
  have hdisj : (D.B1 ⊓ K2) ⊓ (D.B ⊔ (K1 ⊓ K2)) = ⊥ := hdir.2.1
  -- (1) `B ⊓ (K₁ ⊓ K₂) = ⊥`, since `D.B ⊓ (K₁ ⊓ K₂) ≤ B₁ ⊓ K₂` and `≤ B ⊔ (K₁ ⊓ K₂)`.
  have hBinK : D.B ⊓ (K1 ⊓ K2) = ⊥ := by
    have hle : D.B ⊓ (K1 ⊓ K2) ≤ (D.B1 ⊓ K2) ⊓ (D.B ⊔ (K1 ⊓ K2)) := by
      intro x hx
      exact ⟨⟨hx.1.1, hx.2.2⟩, Subgroup.mem_sup_left hx.1⟩
    rw [hdisj] at hle
    exact le_bot_iff.mp hle
  -- `K = K₁ ⊓ K₂ ≤ U`
  have hKleU : K1 ⊓ K2 ≤ D.U := by
    rw [← hsup]
    exact le_trans (le_sup_right : K1 ⊓ K2 ≤ D.B ⊔ (K1 ⊓ K2)) le_sup_right
  -- `B₁ ⊓ K₂` normalizes `K₁ ⊓ K₂`: `x ∈ B₁ ⊓ K₂` commutes with `t₁`, so it normalizes `K₁`
  -- by maximality, and it normalizes `K₂` since it lies in `K₂`.
  have hlocA : D.B1 ⊓ K2 ≤ Subgroup.normalizer ((K1 ⊓ K2 : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    have hxB1 : x ∈ D.B1 := hx.1
    have hxK2 : x ∈ K2 := hx.2
    have hxU : x ∈ D.U := hxB1.1
    have hxc1 : x ∈ Subgroup.centralizer ({D.t1} : Set G) := hxB1.2
    have hxH : x ∈ D.H := hUleH hxU
    have hcomm : x * D.t1 = D.t1 * x := Subgroup.mem_centralizer_singleton_iff.mp hxc1
    have hfix : D.t1 * x * D.t1⁻¹ = x := by
      rw [hcomm.symm, mul_assoc, mul_inv_cancel, mul_one]
    exact ⟨conj_mem_of_isMaxInverted h1 hxH hfix hy.1,
      K2.mul_mem (K2.mul_mem hxK2 hy.2) (K2.inv_mem hxK2)⟩
  -- `B = B₁ ⊓ B₂` normalizes `K₁` (via `B₁ ≤ C(t₁)`) and `K₂` (via `B₂ ≤ C(t₂)`).
  have hlocB : D.B ≤ Subgroup.normalizer ((K1 ⊓ K2 : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    have hxB1 : x ∈ D.B1 := hx.1
    have hxB2 : x ∈ D.B2 := hx.2
    have hxU : x ∈ D.U := hxB1.1
    have hxc1 : x ∈ Subgroup.centralizer ({D.t1} : Set G) := hxB1.2
    have hxc2 : x ∈ Subgroup.centralizer ({D.t2} : Set G) := hxB2.2
    have hxH : x ∈ D.H := hUleH hxU
    have hfix1 : D.t1 * x * D.t1⁻¹ = x := by
      have hcomm : x * D.t1 = D.t1 * x := Subgroup.mem_centralizer_singleton_iff.mp hxc1
      rw [hcomm.symm, mul_assoc, mul_inv_cancel, mul_one]
    have hfix2 : D.t2 * x * D.t2⁻¹ = x := by
      have hcomm : x * D.t2 = D.t2 * x := Subgroup.mem_centralizer_singleton_iff.mp hxc2
      rw [hcomm.symm, mul_assoc, mul_inv_cancel, mul_one]
    exact ⟨conj_mem_of_isMaxInverted h1 hxH hfix1 hy.1,
      conj_mem_of_isMaxInverted h2 hxH hfix2 hy.2⟩
  -- (2) `K₁ ⊓ K₂ ◁ U`, because `U = (B₁ ⊓ K₂) ⊔ (B ⊔ (K₁ ⊓ K₂))` and each factor
  -- normalizes `K₁ ⊓ K₂`.
  have hnU : ((K1 ⊓ K2).subgroupOf D.U).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKleU, ← hsup]
    exact sup_le hlocA (sup_le hlocB Subgroup.le_normalizer)
  -- (3) `K₁ ⊓ K₂ ◁ B ⊔ (K₁ ⊓ K₂)`, because `B` normalizes `K₁ ⊓ K₂`.
  have hnX : ((K1 ⊓ K2).subgroupOf (D.B ⊔ (K1 ⊓ K2))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer
      (le_sup_right : K1 ⊓ K2 ≤ D.B ⊔ (K1 ⊓ K2))]
    exact sup_le hlocB Subgroup.le_normalizer
  -- (4) `|B ⊔ (K₁ ⊓ K₂) : K₁ ⊓ K₂| = |B|`: in `X = B ⊔ (K₁ ⊓ K₂)` the subgroups `B` and
  -- `K₁ ⊓ K₂` are complementary, and the index of `K` in a complement `B * K` is `|B|`.
  have hidx : ((K1 ⊓ K2).subgroupOf (D.B ⊔ (K1 ⊓ K2))).index = Nat.card ↥D.B := by
    let X : Subgroup G := D.B ⊔ (K1 ⊓ K2)
    have hBX : D.B ≤ X := le_sup_left
    have hKX : K1 ⊓ K2 ≤ X := le_sup_right
    have hK'normal : ((K1 ⊓ K2).subgroupOf X).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKX]
      exact sup_le hlocB Subgroup.le_normalizer
    have hsup' : D.B.subgroupOf X ⊔ (K1 ⊓ K2).subgroupOf X = ⊤ := by
      have h : X.subgroupOf X = D.B.subgroupOf X ⊔ (K1 ⊓ K2).subgroupOf X :=
        Subgroup.subgroupOf_sup hBX hKX
      rw [Subgroup.subgroupOf_self X] at h
      exact h.symm
    have hinf' : D.B.subgroupOf X ⊓ (K1 ⊓ K2).subgroupOf X = ⊥ := by
      have h : (D.B ⊓ (K1 ⊓ K2)).subgroupOf X
          = D.B.subgroupOf X ⊓ (K1 ⊓ K2).subgroupOf X :=
        Subgroup.comap_inf D.B (K1 ⊓ K2) X.subtype
      rw [hBinK, Subgroup.bot_subgroupOf X] at h
      exact h.symm
    have hcomp : (D.B.subgroupOf X).IsComplement' ((K1 ⊓ K2).subgroupOf X) :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf')
        (by rw [← Subgroup.mul_normal (D.B.subgroupOf X) ((K1 ⊓ K2).subgroupOf X)
              (hN := hK'normal), hsup']; rfl)
    have hcardB : Nat.card ↥(D.B.subgroupOf X) = Nat.card ↥D.B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
    have hidx' : ((K1 ⊓ K2).subgroupOf X).index = Nat.card ↥D.B := by
      rw [hcomp.index_eq_card, hcardB]
    exact hidx'
  exact ⟨hBinK, hnU, hnX, hidx⟩

end Work.BG
