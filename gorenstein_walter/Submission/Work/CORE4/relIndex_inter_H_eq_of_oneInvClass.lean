import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.M_eq_layerIn_sup_of_oneInvClass

/-!
# `|M : M ⊓ C_G(t)| = |E(M) : E(M) ⊓ C_G(t)|` for `E(M)` one class of involutions

Let `M ≤ G` be a finite group, `E = E(M) = layerIn M` its layer, `t` an involution of `E`, and
suppose that `E` has a single class of involutions (under `E`-conjugation).  Then

  `M = E · C_M(t)`,

because for `g ∈ M` the conjugate `g t g⁻¹` is an involution of `E` (as `E ⊴ M`), hence an
`E`-conjugate `d t d⁻¹` of `t`; thus `d⁻¹ g ∈ C_G(t)` and `g = d · (d⁻¹ g) ∈ E · C_M(t)`.

Since moreover `E ⊴ M`, the second isomorphism theorem for indices
(`Work.CORE4.relIndex_eq_relIndex_inf_of_normal_sup_eq`) applied to `E`, `M ⊓ C_G(t)` and `M`
turns that into the index identity

  `|M : M ⊓ C_G(t)| = |E : E ⊓ C_G(t)|`

(Bender 1981, §4, p. 224: `M = E C_M(t)`, hence `C_M(t)` meets every coset of `E`).
-/

namespace Work.CORE4

open Subgroup

/-- `E = layerIn M` is normal in `M`: `M` normalises `E` (`Work.CORE4.layerIn_le_normalizer`). -/
private theorem layerIn_subgroupOf_normal_loc {G : Type} [Group G] (M : Subgroup G) :
    ((Work.GW2.layerIn M).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Work.CORE4.layerIn_le M)).mpr
    (Work.CORE4.layerIn_le_normalizer M)

/-- `M = E(M) · C_M(t)` when `t ∈ E(M)` is an involution and `E(M)` has a single class of
involutions. -/
private theorem M_eq_layerIn_sup_loc {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (M : Subgroup G)
    (hone : Work.GW2.OneInvClassIn (Work.GW2.layerIn M)) (ht : B.t ∈ Work.GW2.layerIn M) :
    M = Work.GW2.layerIn M ⊔ (M ⊓ B.H) := by
  set E : Subgroup G := Work.GW2.layerIn M with hE
  have hEM : E ≤ M := by rw [hE]; exact layerIn_le M
  have hnorm : M ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE]; exact layerIn_le_normalizer M
  have htE : B.t ∈ E := by rw [hE]; exact ht
  refine le_antisymm ?_ (sup_le hEM inf_le_left)
  intro g hg
  -- `g t g⁻¹` is an involution of `E`
  have hconj : g * B.t * g⁻¹ ∈ E :=
    Subgroup.le_normalizer_iff.mp hnorm g hg B.t htE
  have horder : orderOf (g * B.t * g⁻¹) = 2 := by
    have hconj_eq : g * B.t * g⁻¹ = (MulAut.conj g) B.t := by simp [MulAut.conj_apply]
    rw [hconj_eq, ← B.t_order, orderOf_eq_orderOf_iff]
    intro n
    rw [← map_pow]
    exact (MulAut.conj g).map_eq_one_iff
  -- it is an `E`-conjugate of `t`, because `E` has one class of involutions
  obtain ⟨d, hd, hdconj⟩ := hone (g * B.t * g⁻¹) ⟨hconj, horder⟩ B.t ⟨htE, B.t_order⟩
  have hdM : d ∈ M := hEM hd
  -- hence `d * g` centralises `t`
  have hcen : d * g ∈ B.H := by
    show d * g ∈ Subgroup.centralizer ({B.t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hX : (d * g) * B.t * (d * g)⁻¹ = B.t := by
      rw [show (d * g) * B.t * (d * g)⁻¹ = d * (g * B.t * g⁻¹) * d⁻¹ by group]
      exact hdconj
    calc (d * g) * B.t = ((d * g) * B.t * (d * g)⁻¹) * (d * g) := by group
      _ = B.t * (d * g) := by rw [hX]
  have hmem : d * g ∈ M ⊓ B.H := ⟨M.mul_mem hdM hg, hcen⟩
  have hgoal : g = d⁻¹ * (d * g) := by group
  rw [hgoal]
  exact Subgroup.mul_mem_sup (E.inv_mem hd) hmem

theorem relIndex_inter_H_eq_of_oneInvClass {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (M : Subgroup G)
    (hone : Work.GW2.OneInvClassIn (Work.GW2.layerIn M)) (ht : B.t ∈ Work.GW2.layerIn M) :
    (M ⊓ B.H).relIndex M = (Work.GW2.layerIn M ⊓ B.H).relIndex (Work.GW2.layerIn M) := by
  have hsup : M = Work.GW2.layerIn M ⊔ (M ⊓ B.H) := M_eq_layerIn_sup_loc M hone ht
  have hnorm : ((Work.GW2.layerIn M).subgroupOf M).Normal := layerIn_subgroupOf_normal_loc M
  have hkey := relIndex_eq_relIndex_inf_of_normal_sup_eq (Work.GW2.layerIn M) (M ⊓ B.H) M
    (layerIn_le M) inf_le_left hsup.symm hnorm
  rwa [show Work.GW2.layerIn M ⊓ (M ⊓ B.H) = Work.GW2.layerIn M ⊓ B.H from by
    rw [← inf_assoc, inf_eq_left.mpr (layerIn_le M)]] at hkey

end Work.CORE4
