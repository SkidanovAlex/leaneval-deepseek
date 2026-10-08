import Mathlib
import Submission.Work.ASM.Defs
import Submission.Work.CORE2A.dihedral_index_two

/-!
# CORE2A: assembling a `BGData` from Bender's setup

Bender's Hypothesis 1.1 (BG = Bender–Glauberman) asks, given a Sylow `2`-subgroup `S` of a
finite group `G` which is dihedral of order `2n` (`n ≥ 2`), a cyclic subgroup `S₀ ≤ S` of index
two, an involution `t ∈ S₀`, and the hypothesis that all involutions of `G` are conjugate, for
two further involutions `t₁, t₂ ∈ S \ S₀` with `S₀ = ⟨t₁ t₂⟩`.

Mathematically this is immediate.  Let `c` be a generator of the cyclic group `S₀` and let
`s ∈ S \ S₀` (which exists since `S₀` has index `2` in `S`).  Set `t₁ = s` and `t₂ = s c`.
Every element of `S \ S₀` is an involution (`Work.CORE2A.dihedral_index_two`, a consequence of
`S ≅ DihedralGroup n`), so `t₁` and `t₂` both have order `2`; both lie in `S`, and neither lies
in `S₀` (from `t₂ ∈ S₀` one would get `s = t₂ c⁻¹ ∈ S₀`).  Finally `t₁ t₂ = s (s c) = c`, so
`⟨t₁ t₂⟩ = ⟨c⟩ = S₀`.

The result fills in the remaining fields of `Work.GW2.BGData`: `S, n`, the dihedral structure,
the single-conjugacy-class hypothesis (taken verbatim from the input), `S₀` with its properties
and `t` with `t² = 1`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup

theorem bgData_of_setup {G : Type} [Group G] [Finite G] (S : Sylow 2 G) (S0 : Subgroup G)
    (t : G) (hS0 : S0 ≤ S) (hcyc : IsCyclic S0) (hidx : S0.relIndex (S : Subgroup G) = 2)
    (ht : t ∈ S0) (ht2 : orderOf t = 2)
    (hdihedral : ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((S : Subgroup G) ≃* DihedralGroup n))
    (hclass : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) :
    ∃ D : Work.GW2.BGData G, (D.S : Subgroup G) = S ∧ D.S0 = S0 ∧ D.t = t := by
  classical
  obtain ⟨n, hn, hD⟩ := hdihedral
  -- A generator `g` of the cyclic group `S₀`.
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top S0).mp hcyc
  have hS0_gen : S0 = Subgroup.zpowers g := hg.symm
  have hg_mem : g ∈ S0 := hS0_gen ▸ Subgroup.mem_zpowers g
  -- `S₀` is a proper subgroup of `S`, because its index is two.
  have hne : S0 ≠ (S : Subgroup G) := by
    intro h
    have h1 : S0.relIndex (S : Subgroup G) = 1 := by
      rw [h]; exact Subgroup.relIndex_self (S : Subgroup G)
    rw [h1] at hidx
    exact absurd hidx (by norm_num)
  have hsle : ¬ (S : Subgroup G) ≤ S0 := fun hle => hne (le_antisymm hS0 hle)
  -- An element `s ∈ S \ S₀`.
  obtain ⟨s, hsS, hs0⟩ : ∃ s, s ∈ (S : Subgroup G) ∧ s ∉ S0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hsle fun x hx => hcon x hx
  -- Every element of `S \ S₀` is an involution.
  have hord_s : orderOf s = 2 :=
    dihedral_index_two n hn (S : Subgroup G) S0 hD hS0 hcyc hidx s hsS hs0
  -- `t₂ = s * g` lies in `S` and outside `S₀`, hence is an involution too.
  have ht2_mem : s * g ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem hsS (hS0 hg_mem)
  have ht2_nmem : s * g ∉ S0 := by
    intro hmem
    refine hs0 ?_
    have h1 : (s * g) * g⁻¹ ∈ S0 := S0.mul_mem hmem (S0.inv_mem hg_mem)
    have h2 : (s * g) * g⁻¹ = s := by group
    rwa [h2] at h1
  have hord_t2 : orderOf (s * g) = 2 :=
    dihedral_index_two n hn (S : Subgroup G) S0 hD hS0 hcyc hidx (s * g) ht2_mem ht2_nmem
  -- `s * s = 1`, so that `t₁ t₂ = s (s g) = g` generates `S₀`.
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hord_s] at h
    simpa [pow_two] using h
  have hgen : S0 = Subgroup.zpowers (s * (s * g)) := by
    rw [hS0_gen]
    congr 1
    rw [← mul_assoc, hs2, one_mul]
  refine ⟨{ S := S, n := n, two_le := hn, dih := hD, oneClass := hclass,
            S0 := S0, S0_le := hS0, S0_cyclic := hcyc, S0_index := hidx,
            t := t, t_mem := ht, t_order := ht2,
            t1 := s, t2 := s * g,
            t1_mem := hsS, t2_mem := ht2_mem, t1_nmem := hs0, t2_nmem := ht2_nmem,
            t1_order := hord_s, t2_order := hord_t2, gen := hgen }, rfl, rfl, rfl⟩

end Work.CORE2A
