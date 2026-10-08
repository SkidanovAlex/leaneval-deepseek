import Mathlib
import Submission.Work.CORE2A.TorusDefs
import Submission.Work.CORE2A.Thm26bVocab

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-- **Auxiliary (design pass 14, Q1).**  Involutions of the layer `E := E(Ĥ) = layerIn B.Hhat`
are conjugate by elements of `E`.

Proof.  `hE : layerIn B.Hhat ≠ ⊥` produces, by `exists_layer_eq`, a normal quasisimple
`E : Subgroup ↥B.Hhat` with `layer ↥B.Hhat = E` and `layerIn B.Hhat = E.map B.Hhat.subtype`.
Since `↥B.Hhat` has dihedral or cyclic Sylow `2`-subgroups (heredity of the Sylow shape, `DS1`,
from `hbc.sylow`), `layerOneInvClass_inst` gives `C3OneInvClassIn E`: any two involutions of `E`
are `E`-conjugate.  Transport along the injective `B.Hhat.subtype`, using that the order of an
element of `↥B.Hhat` is its order in `G` (`orderOf_coe_subtype_eq`), gives the claim. -/
private theorem layerIn_involutions_conj_aux (T : Work.GW2.LocalToolkit)
    (hFT : Work.GW2.FeitThompsonProp) {G : Type} [Group G] [Finite G]
    (hbc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (hE : Work.GW2.layerIn B.Hhat ≠ ⊥) :
    ∀ x ∈ Work.GW2.layerIn B.Hhat, orderOf x = 2 →
      ∀ y ∈ Work.GW2.layerIn B.Hhat, orderOf y = 2 →
        ∃ g ∈ Work.GW2.layerIn B.Hhat, g * x * g⁻¹ = y := by
  classical
  obtain ⟨E, hEnorm, hEquasi, -, -, hlayerIn_eq⟩ := exists_layer_eq T hFT hbc B hE
  have hsyHhat : DihOrCycSylow ↥B.Hhat := by
    have hhered : DihOrCycHeredProp :=
      Work.DSTR.dihOrCycHered Work.DSTR.dihedralSubgroup Work.DSTR.dihedralQuotient
    exact (hhered G hbc.sylow).1 B.Hhat
  have hC3 : C3OneInvClassIn E := layerOneInvClass_inst ↥B.Hhat hFT hsyHhat E hEnorm hEquasi
  intro x hx hx2 y hy hy2
  rw [hlayerIn_eq] at hx hy
  obtain ⟨x', hx'E, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨y', hy'E, rfl⟩ := Subgroup.mem_map.mp hy
  have hx'2 : orderOf x' = 2 := by rw [orderOf_coe_subtype_eq B.Hhat x']; exact hx2
  have hy'2 : orderOf y' = 2 := by rw [orderOf_coe_subtype_eq B.Hhat y']; exact hy2
  obtain ⟨g, hgE, hg⟩ := hC3 x' hx'E y' hy'E hx'2 hy'2
  refine ⟨g, ?_, ?_⟩
  · rw [hlayerIn_eq]
    exact Subgroup.mem_map.mpr ⟨g, hgE, rfl⟩
  · simpa using congrArg (fun z : ↥B.Hhat => (z : G)) hg

theorem c14_conj_t (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp) {G : Type} [Group G] [Finite G] (hbc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (ht : B.t ∈ Work.GW2.layerIn B.Hhat) : ∀ m ∈ B.Hhat, ∃ e ∈ Work.GW2.layerIn B.Hhat, m * B.t * m⁻¹ = e * B.t * e⁻¹ := by
  intro m hm
  -- `t ≠ 1`, so the layer is nontrivial.
  have ht1 : B.t ≠ 1 := bSetup_t_ne_one B
  have hE : layerIn B.Hhat ≠ ⊥ := fun h => ht1 (Subgroup.mem_bot.mp (h ▸ ht))
  -- `E(Ĥ)` is normalized by `Ĥ`, so `m t m⁻¹ ∈ E(Ĥ)`.
  have hmt : m * B.t * m⁻¹ ∈ layerIn B.Hhat := layerIn_normal T hFT hbc B hE m hm B.t ht
  -- `m t m⁻¹` is again an involution.
  have hmt2 : orderOf (m * B.t * m⁻¹) = 2 := by
    rw [show orderOf (m * B.t * m⁻¹) = orderOf B.t by
          rw [← MulAut.conj_apply]
          exact orderOf_injective (MulAut.conj m).toMonoidHom (MulAut.conj m).injective B.t,
        B.t_order]
  -- Every involution of `E(Ĥ)` is `E(Ĥ)`-conjugate to `t`.
  obtain ⟨g, hg, hgt⟩ :=
    layerIn_involutions_conj_aux T hFT hbc B hE (m * B.t * m⁻¹) hmt hmt2 B.t ht B.t_order
  refine ⟨g⁻¹, Subgroup.inv_mem _ hg, ?_⟩
  have h1 : m * B.t * m⁻¹ = g⁻¹ * (g * (m * B.t * m⁻¹) * g⁻¹) * g := by group
  rw [h1, hgt]
  group

end Work.CORE2A
