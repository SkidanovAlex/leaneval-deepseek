/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 / Helper : an involution outside `pslImage` when the index is even

Let `Q ≤ Sym(ℙ¹(F))` contain `pslImage F` and have cyclic or dihedral Sylow 2-subgroups
(`Work.GW2.DihOrCycSylow ↥Q`). Suppose `pslImage F` contains a Klein four group `V`
(`Nat.card V = 4` and `v * v = 1` for all `v ∈ V`) and the index of `pslImage F` in `Q` is
even. Then `Q` contains an involution outside `pslImage F`.

The mathematics is the following. `V` is a `2`-subgroup of `Q`, so `V ≤ P` for a Sylow
`2`-subgroup `P` of `Q`. Because `P` contains a Klein four group, `P` is not cyclic, so
`P ≅ DihedralGroup n`. The Sylow `P` cannot be contained in `pslImage F`: otherwise
`pslImage F` would have odd index in `Q` (the index of a Sylow `2`-subgroup is odd, and the
index of a subgroup is a multiple of the index of any subgroup containing it). Hence
`T := P ⊓ pslImage F` is a *proper* subgroup of `P`, and it even contains the Klein four
group `V`, so `T` is not cyclic. Finally, a non-cyclic proper subgroup `T` of a cyclic-or-
dihedral group `P` does not contain all involutions of `P`
(`Work.AUTL2.A5.exists_involution_outside_of_ne_of_not_cyclic`); such an involution lies in
`Q` but outside `pslImage F`.

The general-group statement is isolated as
`Work.AUTL2.Helper.exists_involution_outside_of_card_four_of_dihOrCycSylow`, and the module
`Work.AUTL2.Helper.exists_involution_outside_of_sub_of_dihOrCycSylow` is its translation to
the `PSL(2,q)`-setting (`relIndex` vs. the index of `subgroupOf`).
-/
import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.A5.basic

set_option linter.style.haveILetI false

namespace Work.AUTL2.Helper

/-- A Klein four group (`Nat.card = 4`, every element an involution) is not cyclic: a
generator would have order `4` but square `1`. -/
lemma not_isCyclic_of_card_four_sq_eq_one {G : Type*} [Group G] (V : Subgroup G)
    (hcard : Nat.card V = 4) (hsq : ∀ v ∈ V, v * v = 1) : ¬ IsCyclic ↥V := by
  intro hcyc
  haveI := hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥V)
  have hord : orderOf g = Nat.card ↥V := orderOf_eq_card_of_forall_mem_zpowers hg
  have hg2 : g ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext (hsq (g : G) g.2)
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hg2
  rw [hord, hcard] at hdvd
  omega

/-- **Main group-theoretic input.** Let `G` be a finite group with cyclic or dihedral Sylow
`2`-subgroups, let `H ≤ G` be a subgroup of even index containing a Klein four group `V`
(`Nat.card V = 4`, all elements of `V` involutions). Then `G` contains an involution outside
`H`. -/
theorem exists_involution_outside_of_card_four_of_dihOrCycSylow {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (hHeven : Even H.index)
    (hdih : Work.GW2.DihOrCycSylow G)
    (V : Subgroup G) (hVH : V ≤ H) (hVcard : Nat.card V = 4)
    (hVsq : ∀ v ∈ V, v * v = 1) :
    ∃ z : G, z ∉ H ∧ z * z = 1 := by
  classical
  -- `V` is a `2`-subgroup, so it is contained in a Sylow `2`-subgroup `P` of `G`.
  have hVpg : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hVcard]; norm_num)
  obtain ⟨P, hVP⟩ := hVpg.exists_le_sylow
  have hdihP : IsCyclic ↥(P : Subgroup G) ∨
      ∃ m, Nonempty (↥(P : Subgroup G) ≃* DihedralGroup m) := hdih P
  -- The Klein four group survives the passage to the subgroup `P`.
  have hVcardP : Nat.card (V.subgroupOf (P : Subgroup G)) = 4 := by
    have h1 : (V.subgroupOf (P : Subgroup G)).map (P : Subgroup G).subtype = V :=
      Subgroup.map_subgroupOf_eq_of_le hVP
    have h2 := Subgroup.card_map_of_injective (K := V.subgroupOf (P : Subgroup G))
      (f := (P : Subgroup G).subtype) (Subgroup.subtype_injective (P : Subgroup G))
    rw [h1] at h2
    rw [← h2, hVcard]
  have hVsqP : ∀ v ∈ V.subgroupOf (P : Subgroup G), v * v = 1 := by
    intro v hv
    exact Subtype.ext (by simpa using hVsq ((v : ↥(P : Subgroup G)) : G) hv)
  have hVnotcycP : ¬ IsCyclic ↥(V.subgroupOf (P : Subgroup G)) :=
    not_isCyclic_of_card_four_sq_eq_one _ hVcardP hVsqP
  -- `P` is not contained in `H`, because `P` is a Sylow `2`-subgroup.
  have hTne : H.subgroupOf (P : Subgroup G) ≠ ⊤ := by
    intro htop
    have hPH : (P : Subgroup G) ≤ H := Subgroup.subgroupOf_eq_top.mp htop
    have hPodd : ¬ 2 ∣ (P : Subgroup G).index := Sylow.not_dvd_index P
    have h2 : 2 ∣ H.index := even_iff_two_dvd.mp hHeven
    exact hPodd (dvd_trans h2 (Subgroup.index_dvd_of_le hPH))
  -- `T := H ⊓ P` is not cyclic, since it contains the Klein four group `V`.
  have hTnotcyc : ¬ IsCyclic ↥(H.subgroupOf (P : Subgroup G)) := by
    have hle : V.subgroupOf (P : Subgroup G) ≤ H.subgroupOf (P : Subgroup G) := by
      intro x hx
      exact hVH hx
    intro hc
    haveI : IsCyclic ↥(H.subgroupOf (P : Subgroup G)) := hc
    exact hVnotcycP (Subgroup.isCyclic_of_le (H := V.subgroupOf (P : Subgroup G))
      (H' := H.subgroupOf (P : Subgroup G)) hle)
  obtain ⟨z, -, hzT, hz2⟩ := Work.AUTL2.A5.exists_involution_outside_of_ne_of_not_cyclic
    (H.subgroupOf (P : Subgroup G)) ⊤ hdihP le_top hTnotcyc hTne
  exact ⟨(z : G), fun h => hzT (Subgroup.mem_subgroupOf.mpr h),
    by simpa using congrArg (fun w : ↥(P : Subgroup G) => (w : G)) hz2⟩

/-- **Requested lemma.** If `Q ≤ Sym(ℙ¹(F))` contains `pslImage F`, has cyclic or dihedral
Sylow `2`-subgroups, `pslImage F` contains a Klein four group `V` and the index of `pslImage F`
in `Q` is even, then `Q` has an involution outside `pslImage F`. -/
theorem exists_involution_outside_of_sub_of_dihOrCycSylow (F : Type*) [Field F] [Fintype F]
    [DecidableEq F]
    (Q : Subgroup (Equiv.Perm (Work.AUTL2.P1 F)))
    (hpsl : Work.AUTL2.pslImage F ≤ Q)
    (hdih : Work.GW2.DihOrCycSylow ↥Q)
    (V : Subgroup (Equiv.Perm (Work.AUTL2.P1 F)))
    (hVL : V ≤ Work.AUTL2.pslImage F) (hVcard : Nat.card V = 4)
    (hVsq : ∀ v ∈ V, v * v = 1)
    (hEven : Even ((Work.AUTL2.pslImage F).relIndex Q)) :
    ∃ z ∈ Q, z ∉ Work.AUTL2.pslImage F ∧ z * z = 1 := by
  classical
  -- Transport `V` and `pslImage F` to subgroups of `Q`; `relIndex` is the index of
  -- `subgroupOf` by definition.
  have hVLQ : V ≤ Q := hVL.trans hpsl
  have hVcard' : Nat.card (V.subgroupOf Q) = 4 := by
    have h1 : (V.subgroupOf Q).map Q.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVLQ
    have h2 := Subgroup.card_map_of_injective (K := V.subgroupOf Q) (f := Q.subtype)
      (Subgroup.subtype_injective Q)
    rw [h1] at h2
    rw [← h2, hVcard]
  have hVsq' : ∀ v ∈ V.subgroupOf Q, v * v = 1 := by
    intro v hv
    exact Subtype.ext (by simpa using hVsq ((v : ↥Q) : Equiv.Perm (Work.AUTL2.P1 F)) hv)
  have hVH' : V.subgroupOf Q ≤ (Work.AUTL2.pslImage F).subgroupOf Q := by
    intro x hx
    exact hVL hx
  have hEven' : Even ((Work.AUTL2.pslImage F).subgroupOf Q).index := hEven
  obtain ⟨z, hzH, hz2⟩ := exists_involution_outside_of_card_four_of_dihOrCycSylow
    ((Work.AUTL2.pslImage F).subgroupOf Q) hEven' hdih (V.subgroupOf Q) hVH' hVcard' hVsq'
  exact ⟨(z : Equiv.Perm (Work.AUTL2.P1 F)), z.2,
    fun h => hzH (Subgroup.mem_subgroupOf.mpr h),
    by simpa using congrArg (fun w : ↥Q => (w : Equiv.Perm (Work.AUTL2.P1 F))) hz2⟩

end Work.AUTL2.Helper
