import Mathlib
import Submission.Work.CORE2A.TorusDefs
import Submission.Work.CORE2A.Thm26bVocab
import Submission.Work.L2F.Defs

/-!
# CORE2A, design pass 14: `R_u` is abelian

Bender's torus `R_u = [t, C_{E(Ĥ)}(u)]` (`Work.GW2.torusR B u`, `u ∈ S ∖ E(Ĥ)`) is abelian.

The point is that the natural map `φ : SE → PGL₂(q)` (`D : PGLData B p k`, kernel `Z(E(Ĥ))`)
carries `R_u` onto the commutator–torus `⁅⟨φ t⟩, L₂(q) ∩ C(φ u)⁆` (`hmap`, the statement
`Work.CORE2A.c14_R_map`), which is *cyclic* by `PGL2CommutatorTorusProp` (`hCom`); while on
`R_u` itself `φ` is injective up to the center of `R_u`: `R_u ≤ E` and `R_u ∩ Z(E) ≤ Z(R_u)`.
So `R_u / Z(R_u)` is a quotient of the cyclic group `φ(R_u)`, and a group whose central
quotient is cyclic is abelian (`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`).

`zE_odd` enters only to see that `φ t` (and `φ u`) really have order `2`: a generator of
`R_u`'s ambient layer that died in `φ` would lie in the odd group `Z(E)`.
-/

open scoped MatrixGroups
open scoped commutatorElement

namespace Work.CORE2A

open Subgroup
open Work.GW2

theorem c14_R_abelian (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp) {G : Type} [Group G] [Finite G] (hbc : Work.GW2.BenderCtx G) {B : Work.GW2.BenderSetup G} {p k : ℕ} [Fact p.Prime] (hCom : Work.L2F.PGL2CommutatorTorusProp) (D : Work.GW2.PGLData B p k) (hp : Odd p) (hk : 5 ≤ p ^ k) (ht : B.t ∈ Work.GW2.layerIn B.Hhat) {u : G} (huS : u ∈ (B.S : Subgroup G)) (hu2 : orderOf u = 2) (huE : u ∉ Work.GW2.layerIn B.Hhat) (htSE : B.t ∈ Work.GW2.SE B) (huSE : u ∈ Work.GW2.SE B) (hmap : ((Work.GW2.torusR B u).subgroupOf (Work.GW2.SE B)).map D.φ = ⁅Subgroup.zpowers (D.φ ⟨B.t, htSE⟩), Work.GW2.Lsub p k ⊓ Subgroup.centralizer ({D.φ ⟨u, huSE⟩} : Set _)⁆) : IsMulCommutative ↥(Work.GW2.torusR B u) := by
  -- `R_u = [t, C_E(u)] ≤ E`, hence `R_u ≤ SE`.
  have hRE : torusR B u ≤ layerIn B.Hhat := by
    rw [torusR]
    refine Subgroup.commutator_le.mpr (fun g1 hg1 g2 hg2 => ?_)
    have h1 : g1 ∈ layerIn B.Hhat := Subgroup.zpowers_le.mpr ht hg1
    have h2 : g2 ∈ layerIn B.Hhat := (Subgroup.mem_inf.mp hg2).1
    rw [commutatorElement_def]
    exact (layerIn B.Hhat).mul_mem
      ((layerIn B.Hhat).mul_mem ((layerIn B.Hhat).mul_mem h1 h2) ((layerIn B.Hhat).inv_mem h1))
      ((layerIn B.Hhat).inv_mem h2)
  have hRSE : torusR B u ≤ SE B := hRE.trans layerIn_le_SE
  set R : Subgroup G := torusR B u with hRdef
  -- the map `φ` restricted to `R`.
  let f : ↥R →* PGL(2, GaloisField p k) := D.φ.comp (Subgroup.inclusion hRSE)
  have hf_def : f = D.φ.comp (Subgroup.inclusion hRSE) := rfl
  have hrange : f.range = ⁅Subgroup.zpowers (D.φ ⟨B.t, htSE⟩),
      Lsub p k ⊓ Subgroup.centralizer ({D.φ ⟨u, huSE⟩} : Set _)⁆ := by
    rw [hf_def, MonoidHom.range_comp, Subgroup.inclusion_range]
    exact hmap
  -- `B.t ∉ Z(E)`: `Z(E)` has odd order, `B.t` has order two.
  have ht_not_zE : B.t ∉ zE B := by
    intro htmem
    have hE : layerIn B.Hhat ≠ ⊥ := by
      intro h
      exact bSetup_t_ne_one B (by rw [h] at ht; simpa using ht)
    have hodd : Odd (Nat.card ↥(zE B)) := zE_odd T hFT hbc B hE
    have h2dvd : 2 ∣ Nat.card ↥(zE B) := by
      have h := Subgroup.orderOf_dvd_natCard (zE B) htmem
      rwa [B.t_order] at h
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h2dvd)
  -- `φ t` has order two.
  have htord : orderOf (D.φ ⟨B.t, htSE⟩) = 2 := by
    have hdvd : orderOf (D.φ ⟨B.t, htSE⟩) ∣ orderOf (⟨B.t, htSE⟩ : ↥(SE B)) :=
      orderOf_map_dvd D.φ _
    rw [Subgroup.orderOf_mk, B.t_order] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      have h1 : D.φ ⟨B.t, htSE⟩ = 1 := orderOf_eq_one_iff.mp h
      have hmem : (⟨B.t, htSE⟩ : ↥(SE B)) ∈ D.φ.ker := MonoidHom.mem_ker.mpr h1
      rw [D.ker] at hmem
      exact ht_not_zE (Subgroup.mem_subgroupOf.mp hmem)
    · exact h
  -- `φ u` has order two (`u ∉ E ⊇ Z(E)`).
  have hu_not_zE : u ∉ zE B := fun h => huE (zE_le h)
  have huord : orderOf (D.φ ⟨u, huSE⟩) = 2 := by
    have hdvd : orderOf (D.φ ⟨u, huSE⟩) ∣ orderOf (⟨u, huSE⟩ : ↥(SE B)) :=
      orderOf_map_dvd D.φ _
    rw [Subgroup.orderOf_mk, hu2] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      have h1 : D.φ ⟨u, huSE⟩ = 1 := orderOf_eq_one_iff.mp h
      have hmem : (⟨u, huSE⟩ : ↥(SE B)) ∈ D.φ.ker := MonoidHom.mem_ker.mpr h1
      rw [D.ker] at hmem
      exact hu_not_zE (Subgroup.mem_subgroupOf.mp hmem)
    · exact h
  have hu_comm : (⟨u, huSE⟩ : ↥(SE B)) * ⟨B.t, htSE⟩ = ⟨B.t, htSE⟩ * ⟨u, huSE⟩ :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (bSetup_S_le_H B huS))
  have hcomm : D.φ ⟨B.t, htSE⟩ * D.φ ⟨u, huSE⟩ = D.φ ⟨u, huSE⟩ * D.φ ⟨B.t, htSE⟩ := by
    rw [← map_mul, ← map_mul, hu_comm]
  have htL : D.φ ⟨B.t, htSE⟩ ∈ Lsub p k := (D.mem_layer_iff ⟨B.t, htSE⟩).mp ht
  have huL : D.φ ⟨u, huSE⟩ ∉ Lsub p k := fun h => huE ((D.mem_layer_iff ⟨u, huSE⟩).mpr h)
  -- the image `φ(R)` is cyclic.
  have hcyc : IsCyclic f.range :=
    hrange ▸ (hCom p k hp hk (D.φ ⟨B.t, htSE⟩) (D.φ ⟨u, huSE⟩) htord huord hcomm htL huL).1
  -- the kernel of `φ` on `R` lies in the center of `R`.
  have hkerf : f.ker ≤ Subgroup.center ↥R := by
    intro x hx
    have hxZ : (x : G) ∈ zE B := by
      have h1 : Subgroup.inclusion hRSE x ∈ D.φ.ker :=
        MonoidHom.mem_ker.mpr (show D.φ (Subgroup.inclusion hRSE x) = 1 from hx)
      rw [D.ker] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    show (y : G) * (x : G) = (x : G) * (y : G)
    obtain ⟨z, hzcenter, hzx⟩ := Subgroup.mem_map.mp hxZ
    have hzy : (y : G) * (z : G) = (z : G) * (y : G) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcenter ⟨(y : G), hRE y.2⟩)
    rw [← hzx]
    exact hzy
  have hff : f.rangeRestrict.ker ≤ Subgroup.center ↥R := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hkerf
  haveI : IsCyclic f.range := hcyc
  exact MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f.rangeRestrict hff

end Work.CORE2A
