import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.B_normalizes_K

namespace Work.BG

open Work.GW2 Work.BG Work.GW2.C16 Subgroup

/-- If `K` is the largest odd-order subgroup of `H` inverted by `s`, then every `x ∈ H`
commuting with `s` normalizes `K`: conjugation by such an `x` maps `K` onto an odd-order
subgroup of `H` inverted by `s`, to which maximality of `K` applies. -/
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

/-- In a `ThmCHyps` configuration the intersection `K₁ ⊓ K₂` is a normal subgroup of
`U = C.P.U` (for any compatible §2 context `C`) on which `σ_U` (conjugation by `s`) acts as
inversion.

The containment `K₁ ⊓ K₂ ≤ U` is the first component of the internal direct decomposition
`U = (B₁ ⊓ K₂) · (B · (K₁ ⊓ K₂))` of `ThmCHyps`.  For the normality it suffices to note
that both factors of this decomposition normalize `K₁ ⊓ K₂`: `B` does (this is
`B_normalizes_K`), and `B₁ ⊓ K₂` does because an element `x ∈ B₁` commutes with `t₁ = s`,
so conjugation by it preserves "inverted by `t₁` inside `H`" and hence, by maximality of
`K₁`, preserves `K₁`, while it preserves `K₂` since `x ∈ K₂`.  The inversion statement is
then immediate from `K₁ ⊓ K₂ ≤ K₁` and `IsMaxInverted D.H D.t1 K1` (using `C.s = D.t1`). -/
theorem infKNormalInU {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (K1 K2 : Subgroup G) :
    Work.GW2.C16.Compat D C → Work.GW2.C16.ThmCHyps D K1 K2 → D.n = 2 →
    K1 ⊓ K2 ≤ C.P.U ∧ ((K1 ⊓ K2).subgroupOf C.P.U).Normal ∧
    (∀ k : ↥C.P.U, (k : G) ∈ K1 ⊓ K2 → Work.BG.sigmaU C k = k⁻¹) := by
  intro hC hH _
  obtain ⟨hmax1, hmax2, hdir, -, -, -⟩ := hH
  obtain ⟨hdir_sup, -, -⟩ := hdir
  -- `K₁` is inverted by `t₁ = s`.
  have hK1inv : ∀ x ∈ K1, D.t1 * x * D.t1⁻¹ = x⁻¹ := fun x hx => hmax1.2.2.1 x hx
  -- 1. Containment `K₁ ⊓ K₂ ≤ U`.
  have hleU : K1 ⊓ K2 ≤ C.P.U := by
    rw [hC.U_eq, ← hdir_sup]
    exact le_trans le_sup_right le_sup_right
  refine ⟨hleU, ?_, ?_⟩
  · -- 2. Normality of `K₁ ⊓ K₂` in `U`.
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hleU, hC.U_eq, ← hdir_sup]
    refine sup_le ?_ ?_
    · -- `B₁ ⊓ K₂` normalizes `K₁ ⊓ K₂`.
      rw [Subgroup.le_normalizer_iff]
      intro x hx y hy
      have hxB1 : x ∈ D.B1 := hx.1
      have hxK2 : x ∈ K2 := hx.2
      have hxH : x ∈ D.H := oddCoreIn_le D.H hxB1.1
      have hxs : D.t1 * x * D.t1⁻¹ = x := by
        have hc : D.t1 * x = x * D.t1 :=
          (Subgroup.mem_centralizer_iff.mp hxB1.2) D.t1 (by simp)
        rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      exact ⟨conj_mem_of_isMaxInverted hmax1 hxH hxs hy.1,
        K2.mul_mem (K2.mul_mem hxK2 hy.2) (K2.inv_mem hxK2)⟩
    · -- `B ⊔ (K₁ ⊓ K₂)` normalizes `K₁ ⊓ K₂`.
      refine sup_le ?_ Subgroup.le_normalizer
      exact Subgroup.le_normalizer_iff_commutator_le_right.mpr (B_normalizes_K D K1 K2 hmax1 hmax2)
  · -- 3. `σ_U` inverts `K₁ ⊓ K₂`.
    intro k hk
    apply Subtype.ext
    rw [sigmaU_apply_coe, Subgroup.coe_inv, hC.s_eq]
    exact hK1inv (k : G) hk.1

end Work.BG
