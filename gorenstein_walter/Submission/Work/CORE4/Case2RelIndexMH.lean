import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.PSL2.Card

namespace Work.CORE4

open scoped MatrixGroups
open Subgroup

/-! ## Auxiliary group-theoretic facts

Two elementary transport lemmas and the pure arithmetic of Bender §4 (10).  They are stated
generically so that they do not depend on the §4 configuration. -/

/-- `C_E(t)`, written as a subgroup of `E`, is `E ⊓ C_G(t)` (viewed inside `E`). -/
theorem subgroupOf_inf_centralizer {G : Type*} [Group G] (E : Subgroup G) (t : G) (ht : t ∈ E) :
    (E ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf E =
      Subgroup.centralizer ({⟨t, ht⟩} : Set ↥E) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, hx⟩
    exact Subtype.ext hx
  · intro hx
    exact ⟨x.2, congrArg Subtype.val hx⟩

/-- Centralizers of singletons have the same cardinality under a group isomorphism. -/
theorem card_centralizer_singleton_map {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) (z : G) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({ψ z} : Set H)) := by
  have hmap : (Subgroup.centralizer ({z} : Set G)).map ψ.toMonoidHom =
      Subgroup.centralizer ({ψ z} : Set H) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa using congrArg ψ.toMonoidHom (Subgroup.mem_centralizer_singleton_iff.mp hy)
    · intro hx
      refine Subgroup.mem_map.mpr ⟨ψ.symm x, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply ψ.injective
      simpa using (Subgroup.mem_centralizer_singleton_iff.mp hx)
  rw [← hmap, Subgroup.card_map_of_injective ψ.injective]

/-- **Bender §4 (10), arithmetic core.**  If `2n` and `2k'` are the two halves `q ∓ 1` of `q ± 1`
(in one order or the other) and `r · 2n = N` where `2N = q (q² - 1)`, then `r = q k'`. -/
theorem eq_mul_half_of_relIndex {q n k' r N : ℕ} (hq : 2 ≤ q)
    (hnk : (2 * n = q - 1 ∧ 2 * k' = q + 1) ∨ (2 * n = q + 1 ∧ 2 * k' = q - 1))
    (hN : 2 * N = q * (q ^ 2 - 1))
    (hr : r * (2 * n) = N) : r = q * k' := by
  have h2n_pos : 0 < 2 * n := by rcases hnk with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hmul : (2 * n) * (2 * k') = q ^ 2 - 1 := by
    have hsq : (q + 1) * (q - 1) = q ^ 2 - 1 := by
      simpa using (Nat.sq_sub_sq q 1).symm
    rcases hnk with ⟨h, h'⟩ | ⟨h, h'⟩
    · rw [h, h', mul_comm (q - 1) (q + 1)]; exact hsq
    · rw [h, h']; exact hsq
  have h1 : (2 * r) * (2 * n) = (q * (2 * k')) * (2 * n) := by
    calc (2 * r) * (2 * n) = 2 * (r * (2 * n)) := by ring
      _ = 2 * N := by rw [hr]
      _ = q * (q ^ 2 - 1) := hN
      _ = q * ((2 * n) * (2 * k')) := by rw [hmul]
      _ = (q * (2 * k')) * (2 * n) := by ring
  have h2 : 2 * r = q * (2 * k') := Nat.eq_of_mul_eq_mul_right h2n_pos h1
  have h3 : q * (2 * k') = 2 * (q * k') := by ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) (h2.trans h3)

/-! ## The main theorem -/

/-- Bender §4 (10), first half, in the form needed below.  If `E = E(M) ≅ L₂(q)` with
`q = p ^ k` as in §4 (9) (`Case2Ctx.nine` gives exactly this data), then `|M : M ⊓ H|`
equals `|E : C_E(t)|` (`Case2Ctx.relIndex_M_inter_H`), and `|C_E(t)| = 2 n` with
`2 n = q ± 1` for the involution `t ∈ E` (`h.D.t_mem`) by `I.toolkit.l2cent`; hence
`|M : M ⊓ H| = q k'` where `k'` is the *other* half of `q ± 1`, i.e. `2 k' = q ∓ 1`.
(So `k'` satisfies `2 * k' = p ^ k + 1` or `2 * k' = p ^ k - 1`, the disjunct opposite to
the one for `|C_E(t)|`.) -/
theorem Case2RelIndexMH :
    ∀ (G : Type) [Group G] [Finite G] (I : Work.GW2.C4Inputs), Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∃ (p k k' : ℕ) (_ : Fact p.Prime), Odd p ∧ 7 ≤ p ^ k ∧
          (Nonempty (Work.GW2.layerIn h.D.M ≃* PSL(2, GaloisField p k))) ∧
          (2 * k' = p ^ k + 1 ∨ 2 * k' = p ^ k - 1) ∧
          (h.D.M ⊓ B.H).relIndex h.D.M = p ^ k * k' := by
  intro G _ _ I hbc B h
  classical
  obtain ⟨p, k, hpp, hpodd, h7, hiso, _hSE⟩ := h.nine
  haveI := hpp
  obtain ⟨φ⟩ := hiso
  have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at h7; omega
  have h2q : 2 ≤ p ^ k := by omega
  -- the involution `t` inside `E = E(M)`
  have htE : B.t ∈ Work.GW2.layerIn h.D.M := h.D.t_mem
  have htE2 : orderOf (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn h.D.M)) = 2 := by
    rw [Subgroup.orderOf_mk, B.t_order]
  have ht' : orderOf (φ ⟨B.t, htE⟩) = 2 := by
    rw [MulEquiv.orderOf_eq]; exact htE2
  -- `|C_E(t)| = 2 n` with `2 n = q ± 1`
  obtain ⟨n, hn, ⟨ψ⟩⟩ :=
    I.toolkit.l2cent p k hpodd (by omega : 5 ≤ p ^ k) (φ ⟨B.t, htE⟩) ht'
  have hcardC : Nat.card ↥(Work.GW2.layerIn h.D.M ⊓ B.H) = 2 * n := by
    have h1 : Nat.card ↥((Work.GW2.layerIn h.D.M ⊓ B.H).subgroupOf (Work.GW2.layerIn h.D.M)) =
        Nat.card ↥(Subgroup.centralizer ({⟨B.t, htE⟩} :
          Set ↥(Work.GW2.layerIn h.D.M))) := by
      rw [subgroupOf_inf_centralizer (Work.GW2.layerIn h.D.M) B.t htE]
    have h2 : Nat.card ↥(Subgroup.centralizer ({⟨B.t, htE⟩} :
          Set ↥(Work.GW2.layerIn h.D.M))) =
        Nat.card ↥(Subgroup.centralizer ({φ ⟨B.t, htE⟩} :
          Set (PSL(2, GaloisField p k)))) :=
      card_centralizer_singleton_map φ ⟨B.t, htE⟩
    have h3 : Nat.card ↥(Subgroup.centralizer ({φ ⟨B.t, htE⟩} :
          Set (PSL(2, GaloisField p k)))) = 2 * n := by
      haveI : NeZero n := ⟨by rcases hn with hn | hn <;> omega⟩
      rw [Nat.card_congr ψ.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    calc Nat.card ↥(Work.GW2.layerIn h.D.M ⊓ B.H)
        = Nat.card ↥((Work.GW2.layerIn h.D.M ⊓ B.H).subgroupOf
            (Work.GW2.layerIn h.D.M)) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
      _ = Nat.card ↥(Subgroup.centralizer ({⟨B.t, htE⟩} :
            Set ↥(Work.GW2.layerIn h.D.M))) := h1
      _ = Nat.card ↥(Subgroup.centralizer ({φ ⟨B.t, htE⟩} :
            Set (PSL(2, GaloisField p k)))) := h2
      _ = 2 * n := h3
  -- `r · 2n = N` where `N = |PSL(2, q)|` and `2 N = q (q² - 1)`
  have hr : (Work.GW2.layerIn h.D.M ⊓ B.H).relIndex (Work.GW2.layerIn h.D.M) * (2 * n) =
      Nat.card (PSL(2, GaloisField p k)) := by
    have hmul := Subgroup.relIndex_mul_card (Work.GW2.layerIn h.D.M ⊓ B.H)
      (Work.GW2.layerIn h.D.M)
    rw [inf_eq_left.mpr inf_le_left, hcardC] at hmul
    rw [Nat.card_congr φ.toEquiv] at hmul
    exact hmul
  have hN : 2 * Nat.card (PSL(2, GaloisField p k)) = p ^ k * ((p ^ k) ^ 2 - 1) := by
    have hh := Work.PSL2.card_PSL2_galoisField p k hpodd hk0
    rw [show p ^ (2 * k) = (p ^ k) ^ 2 from by rw [← pow_mul, Nat.mul_comm k 2]] at hh
    exact hh
  have hrel := Work.GW2.Case2Ctx.relIndex_M_inter_H hbc h
  rcases hn with hn | hn
  · -- `2 n = q - 1`: the complementary half is `k' = n + 1`, `2 k' = q + 1`
    have hk' : 2 * (n + 1) = p ^ k + 1 := by omega
    refine ⟨p, k, n + 1, hpp, hpodd, h7, ⟨φ⟩, Or.inl hk', ?_⟩
    rw [hrel]
    exact eq_mul_half_of_relIndex h2q (Or.inl ⟨hn, hk'⟩) hN hr
  · -- `2 n = q + 1`: the complementary half is `k' = n - 1`, `2 k' = q - 1`
    have hk' : 2 * (n - 1) = p ^ k - 1 := by omega
    refine ⟨p, k, n - 1, hpp, hpodd, h7, ⟨φ⟩, Or.inr hk', ?_⟩
    rw [hrel]
    exact eq_mul_half_of_relIndex h2q (Or.inr ⟨hn, hk'⟩) hN hr

end Work.CORE4
