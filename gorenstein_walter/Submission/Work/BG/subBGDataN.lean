/-
Area BG (Gorenstein–Walter / Bender–Glauberman): `Work.BG.subBGDataN`, the
`n`-strengthened form of the leaf `SubBGDataProp` of BG Theorem B.

Given the data `D` of Bender–Glauberman Hypothesis 1.1 on `G` and a subgroup `G₁ ≥ H = C_G(t)`
in which the involutions still form a single conjugacy class, the same dihedral Sylow
2-subgroup `S` is a Sylow 2-subgroup of `G₁` — indeed `S ≤ H ≤ G₁`, because the central
involution `t` of `S₀` (cyclic of index two in `S`) is central in `S`
(`Work.BG.BGData_S_le_centralizer_t`) — and the restricted data `D'` on `G₁` satisfies

* `D'.n = D.n`  (the restricted Sylow is the *same* dihedral group, so the parameter `n` is
  literally unchanged: the construction below takes `n := D.n`),
* `D'.H.index = D.H.relIndex G₁` (since `D'.H = H ∩ G₁` as subgroups of `G₁`),
* `D'.k = D.k` (because `C_{G₁}(tᵢ) = C_G(tᵢ) ∩ G₁` and `C_G(tᵢ) ⊓ C_G(t)` is unchanged).
-/
import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.subBGData

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

theorem subBGDataN {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (G1 : Subgroup G)
    (hle : D.H ≤ G1)
    (hcl : ∀ x y : G, x ∈ G1 → y ∈ G1 → orderOf x = 2 → orderOf y = 2 →
      ∃ g ∈ G1, g * x * g⁻¹ = y) :
    ∃ D' : Work.GW2.BGData ↥G1, D'.n = D.n ∧ D'.H.index = D.H.relIndex G1 ∧ D'.k = D.k := by
  -- The central involution `t` is central in the dihedral Sylow subgroup `S`, so `S ≤ H ≤ G₁`
  -- and hence `S₀`, `t`, `t₁`, `t₂` all lie in `G₁`.
  have hSH : (D.S : Subgroup G) ≤ D.H := BGData_S_le_centralizer_t D
  have hS : (D.S : Subgroup G) ≤ G1 := hSH.trans hle
  have hS0 : D.S0 ≤ G1 := D.S0_le.trans hS
  have ht : D.t ∈ G1 := hS0 D.t_mem
  have ht1 : D.t1 ∈ G1 := hS D.t1_mem
  have ht2 : D.t2 ∈ G1 := hS D.t2_mem
  -- The index and the `k` computations.
  have hidx : (Subgroup.centralizer ({⟨D.t, ht⟩} : Set ↥G1)).index = D.H.relIndex G1 := by
    rw [centralizer_singleton_subgroupOf ht]
    rfl
  have hk1 : (Subgroup.centralizer ({⟨D.t1, ht1⟩} : Set ↥G1)).relIndex
        (Subgroup.centralizer ({⟨D.t, ht⟩} : Set ↥G1)) =
      (Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H := by
    rw [centralizer_singleton_subgroupOf ht, centralizer_singleton_subgroupOf ht1,
      Subgroup.relIndex_subgroupOf hle]
  have hk2 : (Subgroup.centralizer ({⟨D.t2, ht2⟩} : Set ↥G1)).relIndex
        (Subgroup.centralizer ({⟨D.t, ht⟩} : Set ↥G1)) =
      (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H := by
    rw [centralizer_singleton_subgroupOf ht, centralizer_singleton_subgroupOf ht2,
      Subgroup.relIndex_subgroupOf hle]
  have hk : (Subgroup.centralizer ({⟨D.t1, ht1⟩} : Set ↥G1)).relIndex
        (Subgroup.centralizer ({⟨D.t, ht⟩} : Set ↥G1)) +
      (Subgroup.centralizer ({⟨D.t2, ht2⟩} : Set ↥G1)).relIndex
        (Subgroup.centralizer ({⟨D.t, ht⟩} : Set ↥G1)) = D.k := by
    rw [hk1, hk2]
  have ht12 : D.t1 * D.t2 ∈ G1 :=
    hS0 (by rw [D.gen]; exact Subgroup.mem_zpowers (D.t1 * D.t2))
  refine ⟨{ S := D.S.subtype hS, n := D.n, two_le := D.two_le, dih := ?_,
             oneClass := ?_, S0 := D.S0.subgroupOf G1, S0_le := ?_, S0_cyclic := ?_,
             S0_index := ?_, t := ⟨D.t, ht⟩, t_mem := ?_, t_order := ?_,
             t1 := ⟨D.t1, ht1⟩, t2 := ⟨D.t2, ht2⟩, t1_mem := ?_, t2_mem := ?_,
             t1_nmem := ?_, t2_nmem := ?_, t1_order := ?_, t2_order := ?_,
             gen := ?_ }, rfl, ?_, ?_⟩
  · -- `dih`: transport the isomorphism `S ≃* DihedralGroup n` along `S ∩ G₁ = S`.
    obtain ⟨e⟩ := D.dih
    exact ⟨(Subgroup.subgroupOfEquivOfLe hS).trans e⟩
  · -- `oneClass`: the class of involutions of `G₁` given by the hypothesis `hcl`.
    intro x y hx hy
    have hx' : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    have hy' : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
    obtain ⟨g, hg, hgxy⟩ := hcl (x : G) (y : G) x.2 y.2 hx' hy'
    rw [isConj_iff]
    exact ⟨⟨g, hg⟩, Subtype.ext (by simpa using hgxy)⟩
  · -- `S0_le`
    simpa only [Sylow.coe_subtype] using Subgroup.subgroupOf_mono G1 D.S0_le
  · -- `S0_cyclic`
    exact (Subgroup.subgroupOfEquivOfLe hS0).isCyclic.mpr D.S0_cyclic
  · -- `S0_index`
    rw [show ((D.S.subtype hS : Sylow 2 ↥G1) : Subgroup ↥G1) =
        (D.S : Subgroup G).subgroupOf G1 from Sylow.coe_subtype (P := D.S) (N := G1) hS,
      Subgroup.relIndex_subgroupOf hS]
    exact D.S0_index
  · -- `t_mem`
    exact Subgroup.mem_subgroupOf.mpr D.t_mem
  · -- `t_order`
    exact (Subgroup.orderOf_mk (H := G1) D.t ht).trans D.t_order
  · -- `t1_mem`
    simpa only [Sylow.coe_subtype] using Subgroup.mem_subgroupOf.mpr D.t1_mem
  · -- `t2_mem`
    simpa only [Sylow.coe_subtype] using Subgroup.mem_subgroupOf.mpr D.t2_mem
  · -- `t1_nmem`
    exact fun h => D.t1_nmem (Subgroup.mem_subgroupOf.mp h)
  · -- `t2_nmem`
    exact fun h => D.t2_nmem (Subgroup.mem_subgroupOf.mp h)
  · -- `t1_order`
    exact (Subgroup.orderOf_mk (H := G1) D.t1 ht1).trans D.t1_order
  · -- `t2_order`
    exact (Subgroup.orderOf_mk (H := G1) D.t2 ht2).trans D.t2_order
  · -- `gen`
    rw [D.gen, zpowers_subgroupOf (H := G1) (g := D.t1 * D.t2) ht12]
    rfl
  · -- `D'.H.index = D.H.relIndex G₁`
    show (Subgroup.centralizer ({⟨D.t, ht⟩} : Set ↥G1)).index = D.H.relIndex G1
    exact hidx
  · -- `D'.k = D.k`
    show (Subgroup.centralizer ({⟨D.t1, ht1⟩} : Set ↥G1)).relIndex
          (Subgroup.centralizer ({⟨D.t, ht⟩} : Set ↥G1)) +
        (Subgroup.centralizer ({⟨D.t2, ht2⟩} : Set ↥G1)).relIndex
          (Subgroup.centralizer ({⟨D.t, ht⟩} : Set ↥G1)) = D.k
    exact hk

end Work.BG
