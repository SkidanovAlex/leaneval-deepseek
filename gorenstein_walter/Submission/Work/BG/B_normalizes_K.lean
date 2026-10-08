import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.GLUE.PiCoreApi
import Submission.Work.GLUE.InBridge

namespace Work.BG

/-!
# `B` normalizes `K₁ ∩ K₂` (BG Theorem C, G8/§3 input)

`B = B₁ ⊓ B₂` with `Bᵢ = U ⊓ C_G(tᵢ)` (`U = O(H)`, `H = C_G(t)`), and `Kᵢ` is the largest
odd-order subgroup of `H` inverted by the involution `tᵢ`.  The claim is that `B` normalizes
`K₁ ⊓ K₂`, equivalently `⁅B, K₁ ⊓ K₂⁆ ≤ K₁ ⊓ K₂`.

The mathematical point is that maximality of `Kᵢ` makes it *invariant* under `C_U(tᵢ)`: if
`x ∈ H` satisfies `tᵢ x tᵢ⁻¹ = x`, then conjugation by `x` carries the elements of `H`
inverted by `tᵢ` to elements inverted by `tᵢ`:

`tᵢ (x y x⁻¹) tᵢ⁻¹ = (tᵢ x tᵢ⁻¹) (tᵢ y tᵢ⁻¹) (tᵢ x tᵢ⁻¹)⁻¹ = x y⁻¹ x⁻¹ = (x y x⁻¹)⁻¹`,

so `x Kᵢ x⁻¹` is again an odd-order subgroup of `H` inverted by `tᵢ`, hence lies in `Kᵢ`;
the reverse inclusion comes from applying the same argument to `x⁻¹`.  Consequently
`B₁ ≤ N_G(K₁)` and `B₂ ≤ N_G(K₂)`, and `N_G(K₁) ⊓ N_G(K₂) ≤ N_G(K₁ ⊓ K₂)`.

(Note that `x` does *not* invert `Kᵢ` elementwise: `tᵢ ⁅x, y⁆ tᵢ⁻¹ = ⁅x, y⁆^{-y⁻¹}` in
general, which is why the maximality/normalizer argument is needed rather than a direct
computation of `⁅B, Kᵢ⁆`.)
-/

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16 in
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

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16 in
theorem B_normalizes_K {G : Type} [Group G] [Finite G] (D : BGData G) (K1 K2 : Subgroup G)
    (h1 : IsMaxInverted D.H D.t1 K1) (h2 : IsMaxInverted D.H D.t2 K2) :
    ⁅D.B, K1 ⊓ K2⁆ ≤ K1 ⊓ K2 := by
  rw [← Subgroup.le_normalizer_iff_commutator_le_right, Subgroup.le_normalizer_iff]
  intro b hb k hk
  have hb1 : b ∈ D.B1 := hb.1
  have hb2 : b ∈ D.B2 := hb.2
  have hbU : b ∈ D.U := hb1.1
  have hbH : b ∈ D.H := oddCoreIn_le D.H hbU
  have hc1 : D.t1 * b = b * D.t1 := (Subgroup.mem_centralizer_iff.mp hb1.2) D.t1 (by simp)
  have hc2 : D.t2 * b = b * D.t2 := (Subgroup.mem_centralizer_iff.mp hb2.2) D.t2 (by simp)
  refine ⟨conj_mem_of_isMaxInverted h1 hbH ?_ hk.1, conj_mem_of_isMaxInverted h2 hbH ?_ hk.2⟩
  · rw [hc1, mul_assoc, mul_inv_cancel, mul_one]
  · rw [hc2, mul_assoc, mul_inv_cancel, mul_one]

end Work.BG
