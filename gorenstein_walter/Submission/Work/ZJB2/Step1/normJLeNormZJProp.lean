import Mathlib
import Submission.Work.ZJB.Step1.Defs

/-!
# **F4.** `N_G(J(P)) ≤ N_G(Z(J(P)))`

The paper's leaf **F4** (`Work.ZJB.NormJLeNormZJProp`): for every subgroup `P` of a finite group
`G`, the normalizer of the Thompson subgroup `J(P)` is contained in the normalizer of
`Z(J(P)) = J(P) ∩ C_G(J(P))`.

This is the general group-theoretic fact that the "centre" `J ∩ C_G(J)` is invariant under every
automorphism of `G` that preserves `J` — in particular under conjugation by any element of
`N_G(J)`.  It does not use any special property of `thompsonJ`; it is stated and proved here for
an arbitrary subgroup `J`, which is all that is needed since `ZJ P` unfolds to
`thompsonJ P ⊓ centralizer (thompsonJ P)`.

Concretely: if `g ∈ N_G(J)` and `x ∈ J ∩ C_G(J)`, then `g x g⁻¹ ∈ J` because `g` normalises `J`,
and `g x g⁻¹ ∈ C_G(J)` because every `y ∈ J` may be written `y = g y' g⁻¹` with `y' ∈ J`, and `x`
commutes with `y'`.  The converse is identical.
-/

namespace Work.ZJB2.Step1

open Subgroup

/-- For an arbitrary subgroup `J`, the normalizer of `J` is contained in the normalizer of
`J ⊓ C_G(J)`: the "centre of `J`" is invariant under every conjugation preserving `J`. -/
theorem normalizer_le_normalizer_inf_centralizer {G : Type*} [Group G] (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (J ⊓ Subgroup.centralizer (J : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff] at hg ⊢
  intro x
  change (x ∈ J ∧ x ∈ Subgroup.centralizer (J : Set G)) ↔
    (g * x * g⁻¹ ∈ J ∧ g * x * g⁻¹ ∈ Subgroup.centralizer (J : Set G))
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hxJ, hxC⟩
    refine ⟨(hg x).mp hxJ, ?_⟩
    intro y hy
    have hyJ : g⁻¹ * y * g ∈ J := (hg (g⁻¹ * y * g)).mpr (by
      show g * (g⁻¹ * y * g) * g⁻¹ ∈ J
      rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
      exact hy)
    have hcomm := hxC (g⁻¹ * y * g) hyJ
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * x * g⁻¹) * y := by group
  · rintro ⟨hxJ, hxC⟩
    refine ⟨(hg x).mpr hxJ, ?_⟩
    intro y hy
    have hyJ : g * y * g⁻¹ ∈ J := (hg y).mp hy
    have hcomm := hxC (g * y * g⁻¹) hyJ
    calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [hcomm]
      _ = x * y := by group

/-- **F4.** `N_G(J(P)) ≤ N_G(Z(J(P)))`. -/
theorem normJLeNormZJProp {G : Type*} [Group G] [Finite G] : Work.ZJB.NormJLeNormZJProp G := by
  intro P
  exact normalizer_le_normalizer_inf_centralizer (Work.GW2.thompsonJ P)

end Work.ZJB2.Step1
