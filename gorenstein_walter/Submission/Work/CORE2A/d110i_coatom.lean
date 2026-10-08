import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.dihOrCycSylow_subgroup

/-!
# CORE2A: Bender 1.10(i) in a coatom

Bender 1981, p. 221, (1.10)(i) (`Work.GW2.D110iProp`, i.e. the field `LocalToolkit.d110i`) is
stated for a D-group `X`: if `t ∈ X` is an involution, `p ≠ 2` a prime and `P ≤ X` a `p`-subgroup
normalized by `C_X(t)`, then `⁅P, ⟨t⟩⁆ ≤ O_p(X)`.

This file records the form in which the CORE2/CORE3 arguments consume it: the ambient group `G`
is a minimal counterexample (`BenderCtx G`), `N < G` is a **maximal** subgroup (a coatom),
`u ∈ N` is an involution, `Q ≤ N` an odd `p`-subgroup and `C_G(u) ∩ N ≤ N_G(Q)`.  The conclusion
is `⁅Q, ⟨u⟩⁆ ≤ O_p(N)` (in the ambient group, `Work.GW2.pCoreIn p N`).

The point is that all the hypotheses restrict to `N`: `N` is a proper subgroup of a group with
dihedral/cyclic Sylow 2-subgroups, so by `BenderCtx.ih` it is a D-group
(`dihOrCycSylow_subgroup`), and `C_N(u) = C_G(u) ∩ N`; hence 1.10(i) applies inside `↥N` and the
conclusion is pushed back to `G` along `N.subtype`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-- A coatom of the subgroup lattice of a finite group is a proper subgroup, hence has strictly
smaller cardinality. -/
theorem natCard_lt_card_of_coatom {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (h : IsCoatom K) : Nat.card ↥K < Nat.card G := by
  have hidx : 1 < K.index := Subgroup.one_lt_index_of_ne_top h.ne_top
  have hcm := Subgroup.card_mul_index K
  have hpos : 0 < Nat.card ↥K := Nat.card_pos
  rw [← hcm]
  nlinarith

theorem d110i_coatom (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    (G : Type) [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G)
    (u : G) (hu : orderOf u = 2) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : Subgroup G) (hQ : IsPGroup p Q)
    (N : Subgroup G) (hN : IsCoatom N) (huN : u ∈ N) (hQN : Q ≤ N)
    (hcen : Subgroup.centralizer ({u} : Set G) ⊓ N ≤ Subgroup.normalizer (Q : Set G)) :
    ⁅Q, Subgroup.zpowers u⁆ ≤ Work.GW2.pCoreIn p N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- `N` is a proper subgroup of the minimal counterexample, so a D-group with a
  -- dihedral/cyclic Sylow 2-subgroup.
  have hlt : Nat.card ↥N < Nat.card G := natCard_lt_card_of_coatom hN
  have hdih : Work.GW2.DihOrCycSylow ↥N := dihOrCycSylow_subgroup hctx.sylow N
  have hDG : Work.GW2.IsDGroup ↥N := hctx.ih ↥N hlt hdih
  -- Bender's hypotheses transported to `↥N`.
  let uN : ↥N := ⟨u, huN⟩
  have huN2 : orderOf uN = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  let QN : Subgroup ↥N := Q.subgroupOf N
  have hQNp : IsPGroup p QN := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
  -- `C_N(u) = C_G(u) ∩ N ≤ N_G(Q) ∩ N = N_N(Q ∩ N)`.
  have hcenN : Subgroup.centralizer ({uN} : Set ↥N) ≤ Subgroup.normalizer (QN : Set ↥N) := by
    intro x hx
    have hxG : (x : G) ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h1 : uN * x = x * uN := (Subgroup.mem_centralizer_iff.mp hx) uN (by simp)
      have h2 := congrArg (Subtype.val) h1
      simpa [uN] using h2
    have hxn : (x : G) ∈ Subgroup.normalizer (Q : Set G) := hcen ⟨hxG, x.2⟩
    rw [Subgroup.mem_normalizer_iff] at hxn ⊢
    intro y
    exact hxn (y : G)
  -- Bender 1.10(i) inside the D-group `↥N`.
  have hcomm := T.d110i ↥N hFT hdih hDG uN huN2 p hp2 QN hQNp hcenN
  -- Push the conclusion back to `G` along `N.subtype`.
  have hmap := Subgroup.map_mono (f := N.subtype) hcomm
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQN, MonoidHom.map_zpowers] at hmap
  simpa [Work.GW2.pCoreIn] using hmap

end Work.CORE2A
