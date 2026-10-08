import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2S0_comm_U

namespace Work.CORE4

open scoped MatrixGroups

open Subgroup

/-- **`[K, S₀] = 1`** in the §4 configuration (Bender 1981, §4, pp. 224 and 227).

`S ≤ E := layerIn h.D.M` by §4 (9) (`Case2Ctx.nine`), so `S ≤ H ⊓ E`, and by `I.toolkit.l2cent`
the group `E ⊓ H` is dihedral of order `q ± 1` with `S` as a Sylow 2-subgroup and `S₀` as its
cyclic index-two (rotation) subgroup.  `K = U ⊓ E` is cyclic of odd order, `C_E(K)` is cyclic of
order `k` containing `S₀`, and the elements of `S ∖ S₀` invert `K` (`K = I_{U⊓M}(s)`), so
`C_S(K) = S₀`.

NOTE: the same argument is already carried out *inline* inside the proof of
`Work.CORE4.Case2S0_comm_U` (`Submission/Work/CORE4/Case2S0_comm_U.lean`, the local `have hKS0`),
which is sorry-free — the intended proof is to extract it. -/
theorem S0CentK (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B), ⁅h.D.K, B.S0⁆ = ⊥ := by
  intro G _ _ _ B h
  have hS0leS : B.S0 ≤ (B.S : Subgroup G) := B.S0_le
  obtain ⟨p, m, hp, hpodd, _h7le, ⟨φ⟩, hSE9⟩ := h.nine
  haveI := hp
  have htE : B.t ∈ Work.GW2.layerIn h.D.M := h.D.t_mem
  have htE2 : orderOf (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn h.D.M)) = 2 := by
    rw [Subgroup.orderOf_mk, B.t_order]
  have ht' : orderOf (φ ⟨B.t, htE⟩) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact htE2
  obtain ⟨n, _hn, ⟨ψ⟩⟩ :=
    I.toolkit.l2cent p m hpodd (by omega : 5 ≤ p ^ m) (φ ⟨B.t, htE⟩) ht'
  let Ψ : ↥(Work.GW2.layerIn h.D.M ⊓ B.H) ≃* DihedralGroup n :=
    (((Subgroup.subgroupOfEquivOfLe (inf_le_left : Work.GW2.layerIn h.D.M ⊓ B.H ≤
        Work.GW2.layerIn h.D.M)).symm.trans
      (MulEquiv.subgroupCongr (subgroupOf_inf_centralizer (Work.GW2.layerIn h.D.M) B.t htE))).trans
      (centralizerSingletonMulEquiv (φ : ↥(Work.GW2.layerIn h.D.M) ≃* PSL(2, GaloisField p m))
        ⟨B.t, htE⟩)).trans ψ
  have hKle : h.D.K ≤ Work.GW2.layerIn h.D.M ⊓ B.H := fun k hk =>
    ⟨K_le_layerIn B h hk, B.U_le_H (h.D.K_le_U B hk)⟩
  have hS0le : B.S0 ≤ Work.GW2.layerIn h.D.M ⊓ B.H := fun s hs =>
    ⟨hSE9 (hS0leS hs), B.S_le_H (hS0leS hs)⟩
  set A : Subgroup (DihedralGroup n) :=
    (h.D.K.subgroupOf (Work.GW2.layerIn h.D.M ⊓ B.H)).map
      (Ψ : ↥(Work.GW2.layerIn h.D.M ⊓ B.H) →* DihedralGroup n) with hA
  set B' : Subgroup (DihedralGroup n) :=
    (B.S0.subgroupOf (Work.GW2.layerIn h.D.M ⊓ B.H)).map
      (Ψ : ↥(Work.GW2.layerIn h.D.M ⊓ B.H) →* DihedralGroup n) with hB'
  have hAodd : Odd (Nat.card A) := by
    rw [hA, Subgroup.card_map_of_injective Ψ.injective]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv]
    exact Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le (h.D.K_le_U B))
  have hBcyc : IsCyclic B' := by
    rw [hB']
    exact (Subgroup.equivMapOfInjective (B.S0.subgroupOf (Work.GW2.layerIn h.D.M ⊓ B.H))
      Ψ.toMonoidHom Ψ.injective).isCyclic.mp
      ((Subgroup.subgroupOfEquivOfLe hS0le).isCyclic.mpr B.S0_cyclic)
  have htB : Ψ ⟨B.t, hS0le B.t_mem⟩ ∈ B' := by
    rw [hB']
    exact Subgroup.mem_map.mpr
      ⟨⟨B.t, hS0le B.t_mem⟩, by rw [Subgroup.mem_subgroupOf]; exact B.t_mem, rfl⟩
  have ht2 : orderOf (Ψ ⟨B.t, hS0le B.t_mem⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, B.t_order]
  have hcent : A ≤ Subgroup.centralizer ({Ψ ⟨B.t, hS0le B.t_mem⟩} :
      Set (DihedralGroup n)) := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    have hk : (x : G) ∈ h.D.K := Subgroup.mem_subgroupOf.mp hx
    have hct : B.t * (x : G) = (x : G) * B.t :=
      Subgroup.mem_centralizer_iff.mp (show (x : G) ∈ Subgroup.centralizer ({B.t} : Set G) from
        B.U_le_H (h.D.K_le_U B hk)) B.t (by simp)
    have h2 : (⟨B.t, hS0le B.t_mem⟩ : ↥(Work.GW2.layerIn h.D.M ⊓ B.H)) * x =
        x * ⟨B.t, hS0le B.t_mem⟩ := by
      apply Subtype.ext
      simpa using hct
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    calc Ψ ⟨B.t, hS0le B.t_mem⟩ * Ψ x
        = Ψ (⟨B.t, hS0le B.t_mem⟩ * x) := by rw [map_mul]
      _ = Ψ (x * ⟨B.t, hS0le B.t_mem⟩) := by rw [h2]
      _ = Ψ x * Ψ ⟨B.t, hS0le B.t_mem⟩ := by rw [map_mul]
  have hAB : ⁅A, B'⁆ = ⊥ := dihedral_odd_cyclic_comm A B' hAodd hBcyc htB ht2 hcent
  have hAcen : A ≤ Subgroup.centralizer (B' : Set (DihedralGroup n)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAB
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hAmem : Ψ ⟨k, hKle hk⟩ ∈ A := by
    rw [hA]
    exact Subgroup.mem_map.mpr
      ⟨⟨k, hKle hk⟩, by rw [Subgroup.mem_subgroupOf]; exact hk, rfl⟩
  have hBmem : Ψ ⟨s, hS0le hs⟩ ∈ B' := by
    rw [hB']
    exact Subgroup.mem_map.mpr
      ⟨⟨s, hS0le hs⟩, by rw [Subgroup.mem_subgroupOf]; exact hs, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.mp (hAcen hAmem) (Ψ ⟨s, hS0le hs⟩) hBmem
  have h2 : Ψ ((⟨s, hS0le hs⟩ : ↥(Work.GW2.layerIn h.D.M ⊓ B.H)) * ⟨k, hKle hk⟩) =
      Ψ (⟨k, hKle hk⟩ * ⟨s, hS0le hs⟩) := by
    rw [map_mul, map_mul]
    exact h1
  exact congrArg Subtype.val (Ψ.injective h2)

end Work.CORE4
