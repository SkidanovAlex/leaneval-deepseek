import Mathlib
import Submission.Work.BG.Core24
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.B_normalizes_K
import Submission.Work.BG.thmCSec3
import Submission.Work.BG.b1InfK2EqBot

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C24 Subgroup

/-- If `K` is the largest odd-order subgroup of `H` inverted by `s`, then every `x ∈ H`
commuting with `s` normalizes `K`: conjugation by `x` carries `K` onto an odd-order subgroup
of `H` inverted by `s` (`s (x y x⁻¹) s⁻¹ = (s x s⁻¹)(s y s⁻¹)(s x s⁻¹)⁻¹ = x y⁻¹ x⁻¹`), to
which maximality of `K` applies.  Local copy of the (private) helper of `B_normalizes_K`. -/
private lemma conj_mem_of_isMaxInverted' {G : Type*} [Group G] {H K : Subgroup G} {s x : G}
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

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C24 in
theorem kInvNormal : Work.GW2.C24.KInvNormalProp := by
  intro G _ _ D K1 K2 hT
  obtain ⟨hmax1, hmax2, hdir, -, -, -⟩ := hT
  obtain ⟨hsup, -, -⟩ := hdir
  -- Both factors of the internal direct decomposition `U = (B₁ ⊓ K₂) · (B · (K₁ ⊓ K₂))`
  -- normalize `K₁ ⊓ K₂`.
  have hnorm : (D.B1 ⊓ K2) ⊔ (D.B ⊔ (K1 ⊓ K2)) ≤
      Subgroup.normalizer ((K1 ⊓ K2 : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · -- `B₁ ⊓ K₂`: an `x ∈ B₁` commutes with `t₁` and lies in `H`, so it normalizes `K₁`
      -- (maximality of `K₁`), while `x ∈ K₂` normalizes `K₂`.
      rw [Subgroup.le_normalizer_iff]
      intro x hx y hy
      have hxB1 : x ∈ D.B1 := hx.1
      have hxK2 : x ∈ K2 := hx.2
      have hxH : x ∈ D.H := oddCoreIn_le D.H hxB1.1
      have hxt1 : D.t1 * x * D.t1⁻¹ = x := by
        have hc : D.t1 * x = x * D.t1 :=
          (Subgroup.mem_centralizer_iff.mp hxB1.2) D.t1 (by simp)
        rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      exact ⟨conj_mem_of_isMaxInverted' hmax1 hxH hxt1 hy.1,
        K2.mul_mem (K2.mul_mem hxK2 hy.2) (K2.inv_mem hxK2)⟩
    · -- `B ⊔ (K₁ ⊓ K₂)`: `B_normalizes_K` and `K₁ ⊓ K₂ ≤ N(K₁ ⊓ K₂)`.
      refine sup_le ?_ (K1 ⊓ K2).le_normalizer
      exact Subgroup.le_normalizer_iff_commutator_le_right.mpr
        (B_normalizes_K D K1 K2 hmax1 hmax2)
  have hnorm' := Subgroup.le_normalizer_iff.mp hnorm
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `K₁ ⊓ K₂ ≤ U`, from the decomposition.
    rw [← hsup]
    exact le_trans le_sup_right le_sup_right
  · -- `U` normalizes `K₁ ⊓ K₂`.
    intro u hu x hx
    exact hnorm' u (by rw [hsup]; exact hu) x hx
  · -- `t₁` inverts `K₁` and hence `K₁ ⊓ K₂`.
    intro x hx
    exact hmax1.2.2.1 x hx.1
  · -- `t₂` inverts `K₂` and hence `K₁ ⊓ K₂`.
    intro x hx
    exact hmax2.2.2.1 x hx.2

end Work.BG
