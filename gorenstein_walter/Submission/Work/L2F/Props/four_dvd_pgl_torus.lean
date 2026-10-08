/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Work.L2F.Props.four_dvd_pgl_torus`

Two distinct cyclic subgroups `R ≠ R'` of `PGL(2,F)` of order `m` (the order of a maximal torus's
odd part: `m = (q+1)/2` for `q ≡ 1 mod 4`, `m = (q-1)/2` for `q ≡ 3 mod 4`) which are both
inverted by one involution `t` generate a group whose order is divisible by `4`.

Structure of the argument (all pieces are separate lemmas):

* `q` is odd (`odd_of_two_ne_zero`), hence `m` is odd (`odd_torus_order`) and `1 < m`
  (since `R ≠ R'`);
* if `4 ∤ |⟨t,R,R'⟩|` then `|⟨t,R,R'⟩| = 2k` with `k` odd, so the odd-order elements form a normal
  subgroup `K` of index two (`odd_part_of_two_odd`), which contains `R` and `R'` and is normalized
  by `t`;
* in an odd-order subgroup of `PGL(2,F)` normalized by an involution `t`, any two `t`-inverted
  elements commute (`inverted_commute`), so generators of `R` and `R'` commute;
* the centralizer of an element of order `m` is cyclic (`centralizer_torus_cyclic`), so the two
  commuting generators lie in a cyclic group and, having the same order, generate the same
  subgroup: `R = R'`, contradiction.
-/
import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Props.odd_part_of_two_odd
import Submission.Work.L2F.Props.centralizer_torus_cyclic
import Submission.Work.L2F.Props.inverted_commute

open scoped MatrixGroups
open Matrix
open Subgroup (centralizer normalizer zpowers)

namespace Work.L2F.Props

/-- The cardinality `q` of a finite field of characteristic `≠ 2` is odd. -/
theorem odd_of_two_ne_zero (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (q : ℕ)
    (hq : Nat.card F = q) : Odd q := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hp2 : ringChar F ≠ 2 := by
    intro h
    haveI : CharP F 2 := h ▸ inferInstance
    exact h2 (CharP.cast_eq_zero F 2)
  have hq' : q = ringChar F ^ (n : ℕ) := by rw [← hq, ← hcard, Nat.card_eq_fintype_card]
  rw [hq']
  exact (hp.odd_of_ne_two hp2).pow

/-- The torus order `m = (q+1)/2` (`q ≡ 1 mod 4`) resp. `(q-1)/2` is odd for `q` odd. -/
theorem odd_torus_order (q : ℕ) (hq : Odd q) :
    Odd (if q % 4 = 1 then (q + 1) / 2 else (q - 1) / 2) := by
  rcases hq with ⟨k, rfl⟩
  by_cases h : (2 * k + 1) % 4 = 1
  · rw [ite_eq_left h]
    have hk : k % 2 = 0 := by omega
    exact ⟨k / 2, by omega⟩
  · rw [ite_eq_right h]
    have hk : k % 2 = 1 := by omega
    exact ⟨k / 2, by omega⟩

/-- **Structure of `L₂(q)`**: two distinct cyclic subgroups `R ≠ R'` of `PGL(2,F)` of order
`m = (q+1)/2` (`q ≡ 1 mod 4`) resp. `(q-1)/2` (`q ≡ 3 mod 4`) — i.e. maximal tori of `L₂(q)` —
which are both inverted by an involution `t` generate a group of order divisible by `4`.
In the source (Gorenstein–Walter, Thm 2.6 (2)) this is used as "by the structure of `L₂(q)`";
the mechanism is that such a subgroup is `A₄`, `S₄`, `A₅` or all of `L₂(q)`, or a joint dihedral
normalizer, in every case of order divisible by `4`.  A proof may proceed through the action of
`L₂(q)` on the projective line: a split torus (order `(q-1)/2`) has two fixed points and two
orbits of size `(q-1)/2`, a non-split torus (order `(q+1)/2`) acts freely with two orbits of size
`(q+1)/2`, an involution has two fixed points iff `-1` is a square (i.e. `q ≡ 1 mod 4`) and is
fixed point free otherwise, point stabilizers are Borel subgroups `C_q ⋊ C_m` whose nonidentity
`C_q`-part has odd order `p`, and the stabilizer of a two-point set has order `q-1`. -/
theorem four_dvd_pgl_torus (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (q : ℕ)
    (hq : Nat.card F = q)
    (R R' : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F))
    (hR : Nat.card R = (if q % 4 = 1 then (q + 1) / 2 else (q - 1) / 2))
    (hR' : Nat.card R' = (if q % 4 = 1 then (q + 1) / 2 else (q - 1) / 2))
    (hcyc : IsCyclic R) (hcyc' : IsCyclic R') (hne : R ≠ R')
    (t : Matrix.ProjGenLinGroup (Fin 2) F) (ht : orderOf t = 2)
    (hinv : Work.L2F.Inverts t R) (hinv' : Work.L2F.Inverts t R') :
    4 ∣ Nat.card (Subgroup.zpowers t ⊔ R ⊔ R' :
      Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) := by
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 2) F) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk (n := Fin 2) (R := F))
      (Matrix.ProjGenLinGroup.mk_surjective (n := Fin 2) (R := F))
  haveI : Nonempty ↥R := ⟨1⟩
  haveI : Nonempty ↥R' := ⟨1⟩
  set m : ℕ := (if q % 4 = 1 then (q + 1) / 2 else (q - 1) / 2) with hmdef
  have hqodd : Odd q := odd_of_two_ne_zero F h2 q hq
  have hmodd : Odd m := odd_torus_order q hqodd
  have hRm : Nat.card R = m := hR
  have hR'm : Nat.card R' = m := hR'
  -- `1 < m`
  have hm1 : 1 < m := by
    have h0 : 0 < m := by rw [← hRm]; exact Nat.card_pos
    rcases Nat.lt_or_ge 1 m with h | h
    · exact h
    · exfalso
      have hm1' : m = 1 := by omega
      have hb : ∀ S : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F), Nat.card S = 1 → S = ⊥ := by
        intro S hS
        rw [Subgroup.eq_bot_iff_forall]
        intro z hz
        have hzS : orderOf (⟨z, hz⟩ : S) ∣ Nat.card S := orderOf_dvd_natCard _
        rw [hS] at hzS
        exact Subtype.ext_iff.mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hzS))
      exact hne ((hb R (by rw [hRm, hm1'])).trans (hb R' (by rw [hR'm, hm1'])).symm)
  -- generators of `R` and `R'`
  obtain ⟨x₀, hx₀⟩ := hcyc.exists_generator
  obtain ⟨y₀, hy₀⟩ := hcyc'.exists_generator
  set x : Matrix.ProjGenLinGroup (Fin 2) F := (x₀ : Matrix.ProjGenLinGroup (Fin 2) F) with hxdef
  set y : Matrix.ProjGenLinGroup (Fin 2) F := (y₀ : Matrix.ProjGenLinGroup (Fin 2) F) with hydef
  have hxord : orderOf x = m := by
    have h := orderOf_eq_card_of_forall_mem_zpowers hx₀
    simp only [hxdef]
    rw [Subgroup.orderOf_coe, h, hRm]
  have hyord : orderOf y = m := by
    have h := orderOf_eq_card_of_forall_mem_zpowers hy₀
    simp only [hydef]
    rw [Subgroup.orderOf_coe, h, hR'm]
  have hxmem : x ∈ R := by simp only [hxdef]; exact x₀.2
  have hymem : y ∈ R' := by simp only [hydef]; exact y₀.2
  by_contra h4
  set H : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F) := Subgroup.zpowers t ⊔ R ⊔ R' with hHdef
  have htH : t ∈ H := by
    rw [hHdef]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have ht2 : orderOf (⟨t, htH⟩ : H) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht
  have h2dvd : 2 ∣ Nat.card ↥H := by
    have h := orderOf_dvd_natCard (⟨t, htH⟩ : H)
    rwa [ht2] at h
  obtain ⟨K₀, hK₀n, hK₀card, hK₀odd⟩ := odd_part_of_two_odd ↥H h2dvd h4
  set K : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F) := K₀.map H.subtype with hKdef
  have hKcard : Nat.card ↥K = Nat.card ↥K₀ :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hKodd : Odd (Nat.card ↥K) := by
    rw [hKcard, ← Nat.not_even_iff_odd]
    intro heven
    rw [even_iff_two_dvd] at heven
    obtain ⟨c, hc⟩ := heven
    refine h4 ⟨c, ?_⟩
    rw [← hK₀card, hc]
    ring
  have hxH : x ∈ H := by
    rw [hHdef]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hxmem)
  have hyH : y ∈ H := by
    rw [hHdef]
    exact Subgroup.mem_sup_right hymem
  have hxK : x ∈ K := by
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    exact (hK₀odd ⟨x, hxH⟩).mpr (by rw [← Subgroup.orderOf_coe, hxord]; exact hmodd)
  have hyK : y ∈ K := by
    refine ⟨⟨y, hyH⟩, ?_, rfl⟩
    exact (hK₀odd ⟨y, hyH⟩).mpr (by rw [← Subgroup.orderOf_coe, hyord]; exact hmodd)
  have hN : ∀ k ∈ K, t * k * t⁻¹ ∈ K := by
    intro k hk
    obtain ⟨k₀, hk₀, rfl⟩ := hk
    refine ⟨⟨t, htH⟩ * k₀ * ⟨t, htH⟩⁻¹, hK₀n.conj_mem k₀ hk₀ ⟨t, htH⟩, ?_⟩
    simp
  have hcomm : x * y = y * x :=
    inverted_commute F K hKodd t ht hN x y hxK hyK (hinv x hxmem) (hinv' y hymem)
  -- the centralizer of `x` is cyclic and contains both `x` and `y`
  have hCcyc : IsCyclic (Subgroup.centralizer ({x} :
      Set (Matrix.ProjGenLinGroup (Fin 2) F))) :=
    centralizer_torus_cyclic F h2 q hq hm1 x hxord
  haveI hCinst : IsCyclic ↥(Subgroup.centralizer ({x} : Set (Matrix.ProjGenLinGroup (Fin 2) F))) :=
    hCcyc
  have hyC : y ∈ Subgroup.centralizer ({x} : Set (Matrix.ProjGenLinGroup (Fin 2) F)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hcomm
  have hxC : x ∈ Subgroup.centralizer ({x} : Set (Matrix.ProjGenLinGroup (Fin 2) F)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rfl
  -- both generators have the same order `m`, so they generate the same subgroup of the cyclic
  -- centralizer, hence `R = R'`
  have hRx : Subgroup.zpowers x = R := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.zpowers_le]; exact hxmem
    · intro z hz
      have h := hx₀ ⟨z, hz⟩
      rw [Subgroup.mem_zpowers_iff] at h ⊢
      obtain ⟨k, hk⟩ := h
      exact ⟨k, congrArg Subtype.val hk⟩
  have hRy : Subgroup.zpowers y = R' := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.zpowers_le]; exact hymem
    · intro z hz
      have h := hy₀ ⟨z, hz⟩
      rw [Subgroup.mem_zpowers_iff] at h ⊢
      obtain ⟨k, hk⟩ := h
      exact ⟨k, congrArg Subtype.val hk⟩
  have hzp : Subgroup.zpowers x = Subgroup.zpowers y := by
    have heq : (Subgroup.zpowers (⟨x, hxC⟩ : ↥(Subgroup.centralizer ({x} :
            Set (Matrix.ProjGenLinGroup (Fin 2) F)))))
        = Subgroup.zpowers (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({x} :
            Set (Matrix.ProjGenLinGroup (Fin 2) F)))) := by
      rw [IsCyclic.subgroup_eq_iff_card_eq]
      rw [Nat.card_zpowers, Nat.card_zpowers, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe,
        hxord, hyord]
    have hmapx : Subgroup.map (Subgroup.centralizer ({x} :
          Set (Matrix.ProjGenLinGroup (Fin 2) F))).subtype
        (Subgroup.zpowers (⟨x, hxC⟩ : ↥(Subgroup.centralizer ({x} :
          Set (Matrix.ProjGenLinGroup (Fin 2) F))))) = Subgroup.zpowers x := by
      rw [MonoidHom.map_zpowers]
      rfl
    have hmapy : Subgroup.map (Subgroup.centralizer ({x} :
          Set (Matrix.ProjGenLinGroup (Fin 2) F))).subtype
        (Subgroup.zpowers (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({x} :
          Set (Matrix.ProjGenLinGroup (Fin 2) F))))) = Subgroup.zpowers y := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [← hmapx, ← hmapy, heq]
  exact hne (by rw [← hRx, ← hRy, hzp])

end Work.L2F.Props
