import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2LayerOneInvClass
import Submission.Work.CORE4.Case2NotHLeM
import Submission.Work.CORE4.Layer
import Submission.Work.CORE4.Case2Setup9Odd
import Submission.Work.CORE4.Case2Setup9S
import Submission.Work.CORE4.Case2SixThreeRaw
import Submission.Work.CORE4.Case2Setup9Ecent2
import Submission.Work.CORE4.Case2Setup9Fprops
import Submission.Work.CORE4.Case2CU_s

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## 1. `M = E(M) · C_M(t)` at the weak hypothesis list

`Submission.Work.CORE4.CountSetup.M_eq_layerIn_sup` states this for a `Case2Ctx`; its proof only
uses `IsCoatom M`, `t ∈ E(M)` and `OneInvClassIn (E(M))`, so we restate it here. -/

/-- **§4, p. 224.**  If `t ∈ E(M)` is an involution and `E(M)` has one class of involutions, then
`M = E(M) · C_M(t)`. -/
theorem M_eq_layerIn_sup_of (B : Work.GW2.BenderSetup G) (M : Subgroup G)
    (hone : Work.GW2.OneInvClassIn (Work.GW2.layerIn M)) (ht : B.t ∈ Work.GW2.layerIn M) :
    M = Work.GW2.layerIn M ⊔ (M ⊓ B.H) := by
  set E : Subgroup G := Work.GW2.layerIn M with hE
  have hEM : E ≤ M := by rw [hE]; exact layerIn_le M
  have hnorm : M ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE]; exact layerIn_le_normalizer M
  have htE : B.t ∈ E := by rw [hE]; exact ht
  refine le_antisymm ?_ (sup_le hEM inf_le_left)
  intro g hg
  have hconj : g * B.t * g⁻¹ ∈ E :=
    Subgroup.le_normalizer_iff.mp hnorm g hg B.t htE
  have horder : orderOf (g * B.t * g⁻¹) = 2 := by
    have hconj_eq : g * B.t * g⁻¹ = (MulAut.conj g) B.t := by simp [MulAut.conj_apply]
    rw [hconj_eq, ← B.t_order, orderOf_eq_orderOf_iff]
    intro n
    rw [← map_pow]
    exact (MulAut.conj g).map_eq_one_iff
  obtain ⟨d, hd, hconjd⟩ :=
    hone (g * B.t * g⁻¹) ⟨hconj, horder⟩ B.t ⟨htE, B.t_order⟩
  have hdM : d ∈ M := hEM hd
  have hcen : d * g ∈ B.H := by
    show d * g ∈ Subgroup.centralizer ({B.t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hX : (d * g) * B.t * (d * g)⁻¹ = B.t := by
      rw [show (d * g) * B.t * (d * g)⁻¹ = d * (g * B.t * g⁻¹) * d⁻¹ by group]
      exact hconjd
    calc (d * g) * B.t = ((d * g) * B.t * (d * g)⁻¹) * (d * g) := by group
      _ = B.t * (d * g) := by rw [hX]
  have hmem : d * g ∈ M ⊓ B.H := ⟨M.mul_mem hdM hg, hcen⟩
  have hgoal : g = d⁻¹ * (d * g) := by group
  rw [hgoal]
  exact Subgroup.mul_mem_sup (E.inv_mem hd) hmem

/-! ## 2. Bender's choice of the Sylow 2-subgroup (§4, p. 224)

`Case2PrePlus` carries the condition `¬ 2 ∣ |M : S ∩ M|`, i.e. `S ∩ M ∈ Syl₂(M)`.  Bender obtains
it by replacing `S` with a suitable `H`-conjugate: `|M : C_M(t)|` is odd
(`Submission.Work.CORE4.Case2Setup9Odd`), hence `C_M(t)` contains a Sylow 2-subgroup `P` of `M`;
`P ≤ C_M(t) ≤ H = C_G(t)`, so `P` extends to a Sylow of `H`, and that Sylow is `S^h` for some
`h ∈ H` (Sylow conjugacy inside `H`).  The conjugate setup `B'` has the same `t` (because
`h ∈ C_G(t)`), hence the same `H` and `U`. -/

/-- `↑(g • S) = conjSub g ↑S` for a Sylow 2-subgroup `S`. -/
theorem coe_smul_sylow_eq_conjSub (g : G) (S : Sylow 2 G) :
    ((g • S : Sylow 2 G) : Subgroup G) = Work.GW2.conjSub g (S : Subgroup G) := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ ((g • S : Sylow 2 G) : Set G) := hx
    rw [Sylow.coe_smul] at hx'
    rw [Set.mem_smul_set] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    exact Subgroup.mem_map.mpr ⟨y, hy, hyx⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hx' : x ∈ ((g • S : Sylow 2 G) : Set G) := by
      rw [Sylow.coe_smul]
      exact Set.mem_smul_set.mpr ⟨y, hy, hyx⟩
    exact hx'

set_option linter.style.haveILetI false in
/-- **Bender's choice of the Sylow 2-subgroup.**  If `2 ∤ |M : M ⊓ C_G(t)|`, then `S` may be
replaced by an `H`-conjugate `B'` (`B'.t = B.t`) whose Sylow meets `M` in a Sylow of `M`. -/
theorem exists_conj_B (B : Work.GW2.BenderSetup G) (M : Subgroup G)
    (hodd : ¬ 2 ∣ (M ⊓ B.H).relIndex M) :
    ∃ B' : Work.GW2.BenderSetup G, B'.t = B.t ∧
      ¬ 2 ∣ (((B'.S : Subgroup G) ⊓ M).relIndex M) ∧
      ((B'.S : Subgroup G) ⊓ M) ≤ M ⊓ B.H ∧
      IsPGroup 2 ↥((B'.S : Subgroup G) ⊓ M) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := M ⊓ B.H with hCdef
  have hCM : C ≤ M := by rw [hCdef]; exact inf_le_left
  have hCH : C ≤ B.H := by rw [hCdef]; exact inf_le_right
  have hCodd : ¬ 2 ∣ C.relIndex M := by rw [hCdef]; exact hodd
  let R : Sylow 2 ↥C := Classical.choice (Sylow.nonempty (p := 2) (G := ↥C))
  let P₀ : Subgroup G := (R : Subgroup ↥C).map C.subtype
  have hP₀C : P₀ ≤ C := Subgroup.map_subtype_le _
  have hP₀M : P₀ ≤ M := le_trans hP₀C hCM
  have hP₀H : P₀ ≤ B.H := le_trans hP₀C hCH
  have hcardP₀ : Nat.card ↥P₀ = 2 ^ (Nat.card ↥M).factorization 2 := by
    have h1 : Nat.card ↥P₀ = Nat.card ↥(R : Subgroup ↥C) :=
      Subgroup.card_map_of_injective (Subtype.val_injective)
    have h2 : Nat.card ↥(R : Subgroup ↥C) = 2 ^ (Nat.card ↥C).factorization 2 :=
      Sylow.card_eq_multiplicity R
    have h3 : (Nat.card ↥C).factorization 2 = (Nat.card ↥M).factorization 2 := by
      have hidx : C.relIndex M * Nat.card ↥C = Nat.card ↥M := by
        have h := Subgroup.relIndex_mul_card C M
        rwa [inf_eq_left.mpr hCM] at h
      have h0 : C.relIndex M ≠ 0 := by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite
      have hC0 : Nat.card ↥C ≠ 0 := Nat.card_pos.ne'
      have h := Nat.factorization_mul h0 hC0
      rw [hidx] at h
      have h2 : (C.relIndex M).factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hCodd
      have h4 := congrArg (fun f : ℕ →₀ ℕ => f 2) h
      simp only [Finsupp.add_apply, h2, zero_add] at h4
      exact h4.symm
    rw [h1, h2, h3]
  have hP₀odd : ¬ 2 ∣ P₀.relIndex M := by
    have hpg : IsPGroup 2 ↥(P₀.subgroupOf M) :=
      (IsPGroup.of_card hcardP₀).of_equiv (Subgroup.subgroupOfEquivOfLe hP₀M).symm
    obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow (p := 2) (G := ↥M) hpg
    have hcardS : Nat.card ↥(S : Subgroup ↥M) = 2 ^ (Nat.card ↥M).factorization 2 :=
      Sylow.card_eq_multiplicity S
    have hcardP : Nat.card ↥(P₀.subgroupOf M) = 2 ^ (Nat.card ↥M).factorization 2 := by
      rw [← hcardP₀]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀M).toEquiv
    have heq : P₀.subgroupOf M = (S : Subgroup ↥M) :=
      Subgroup.eq_of_le_of_card_ge hS (by rw [hcardS, hcardP])
    rw [Subgroup.relIndex, heq]
    exact Sylow.not_dvd_index S
  have hP₀spgH : IsPGroup 2 ↥(P₀.subgroupOf B.H) :=
    (IsPGroup.of_card hcardP₀).of_equiv (Subgroup.subgroupOfEquivOfLe hP₀H).symm
  obtain ⟨T, hP₀T⟩ := IsPGroup.exists_le_sylow (p := 2) (G := ↥B.H) hP₀spgH
  haveI : MulAction.IsPretransitive ↥B.H (Sylow 2 ↥B.H) :=
    Sylow.isPretransitive_of_finite (p := 2) (G := ↥B.H)
  obtain ⟨h, hh⟩ := MulAction.IsPretransitive.exists_smul_eq (M := ↥B.H)
    (α := Sylow 2 ↥B.H) ((B.S).subtype B.S_le_H) T
  have hTs : T = ((h : G) • B.S).subtype (Sylow.smul_le B.S_le_H h) := by
    rw [← hh]
    exact Sylow.smul_subtype B.S_le_H h
  have hP₀le : P₀ ≤ (((h : G) • B.S : Sylow 2 G) : Subgroup G) := by
    intro x hx
    have hxH : x ∈ B.H := hP₀H hx
    have h1 : (⟨x, hxH⟩ : ↥B.H) ∈ (T : Subgroup ↥B.H) :=
      hP₀T (Subgroup.mem_subgroupOf.mpr hx)
    rw [hTs, Sylow.coe_subtype] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hS0le : (B.S0).map (MulAut.conj (h : G)).toMonoidHom ≤
      (((h : G) • B.S : Sylow 2 G) : Subgroup G) := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp hx
    have hxset : x ∈ (((h : G) • B.S : Sylow 2 G) : Set G) := by
      rw [Sylow.coe_smul]
      exact Set.mem_smul_set.mpr ⟨s, B.S0_le hs, hsx⟩
    exact hxset
  have hS0cyc : IsCyclic ↥((B.S0).map (MulAut.conj (h : G)).toMonoidHom) :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective B.S0
      (MulAut.conj (h : G)).toMonoidHom (MulAut.conj (h : G)).injective)).mp B.S0_cyclic
  have hS0idx : ((B.S0).map (MulAut.conj (h : G)).toMonoidHom).relIndex
      (((h : G) • B.S : Sylow 2 G) : Subgroup G) = 2 := by
    have hmap := Subgroup.relIndex_map_map_of_injective (H := B.S0) (K := (B.S : Subgroup G))
      (f := (MulAut.conj (h : G)).toMonoidHom) (MulAut.conj (h : G)).injective
    rw [B.S0_index] at hmap
    rw [coe_smul_sylow_eq_conjSub (h : G) B.S]
    exact hmap
  have htmem : B.t ∈ (B.S0).map (MulAut.conj (h : G)).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨B.t, B.t_mem, ?_⟩
    show (MulAut.conj (h : G)) B.t = B.t
    rw [MulAut.conj_apply]
    have hh' : (h : G) * B.t = B.t * (h : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (show (h : G) ∈ Subgroup.centralizer ({B.t} : Set G) from h.2)
    rw [hh']; group
  let B' : Work.GW2.BenderSetup G :=
    { S := (h : G) • B.S
      S0 := (B.S0).map (MulAut.conj (h : G)).toMonoidHom
      t := B.t
      Hhat := B.Hhat
      S0_le := hS0le
      S0_cyclic := hS0cyc
      S0_index := hS0idx
      t_mem := htmem
      t_order := B.t_order
      Hhat_coatom := B.Hhat_coatom
      H_le_Hhat := B.H_le_Hhat }
  have hsubeq : (B'.S : Subgroup G) ⊓ M = P₀ := by
    have hle1 : P₀ ≤ (B'.S : Subgroup G) ⊓ M :=
      le_inf (show P₀ ≤ (((h : G) • B.S : Sylow 2 G) : Subgroup G) from hP₀le) hP₀M
    have hpg0 : IsPGroup 2 ↥((B'.S : Subgroup G) ⊓ M) :=
      IsPGroup.to_le (B'.S).isPGroup' inf_le_left
    have hpg : IsPGroup 2 ↥(((B'.S : Subgroup G) ⊓ M).subgroupOf M) :=
      hpg0.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    obtain ⟨S', hS'⟩ := IsPGroup.exists_le_sylow (p := 2) (G := ↥M) hpg
    have hcard1 : Nat.card ↥(((B'.S : Subgroup G) ⊓ M).subgroupOf M) =
        Nat.card ↥((B'.S : Subgroup G) ⊓ M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have hcard2 : Nat.card ↥(S' : Subgroup ↥M) = 2 ^ (Nat.card ↥M).factorization 2 :=
      Sylow.card_eq_multiplicity S'
    have hle2 : Nat.card ↥((B'.S : Subgroup G) ⊓ M) ≤ Nat.card ↥P₀ := by
      have h1 : Nat.card ↥(((B'.S : Subgroup G) ⊓ M).subgroupOf M) ≤
          Nat.card ↥(S' : Subgroup ↥M) := Subgroup.card_le_of_le hS'
      rw [hcard1] at h1
      rw [hcard2] at h1
      rw [hcardP₀]
      exact h1
    exact (Subgroup.eq_of_le_of_card_ge hle1 hle2).symm
  refine ⟨B', rfl, ?_, ?_, ?_⟩
  · rw [hsubeq]; exact hP₀odd
  · rw [hsubeq]; exact le_inf hP₀M hP₀H
  · rw [hsubeq]; exact IsPGroup.of_card hcardP₀

end Work.CORE4

namespace Work.CORE4

/-! ## 3. `Case2` only depends on `t` -/

/-- `Case2 B` only depends on `B.t`, so it is preserved when `S`, `S₀` and `Ĥ` are changed. -/
theorem case2_congr_t {G : Type} [Group G] [Finite G] {B B' : Work.GW2.BenderSetup G}
    (h : B'.t = B.t) (h2 : Work.GW2.Case2 B) : Work.GW2.Case2 B' := by
  have hBH : B'.H = B.H := by
    show Subgroup.centralizer ({B'.t} : Set G) = Subgroup.centralizer ({B.t} : Set G)
    rw [h]
  have hBU : B'.U = B.U := by
    show Work.GW2.oddCoreIn B'.H = Work.GW2.oddCoreIn B.H
    rw [hBH]
  obtain ⟨M, hM, ht, X, hX1, hX2, hX3⟩ := h2
  exact ⟨M, hM, h.symm ▸ ht, X, hX1, by rw [hBU]; exact hX2, hX3⟩

/-! Bender 1981, §4 (1)–(5) with Bender's Sylow choice, design-pass-9 layer.

Statement: `Case2SetupImpl9 I`, i.e. for `BenderCtx G` and `B : BenderSetup G` with `Case2 B`,
produce `B' : BenderSetup G` with `B'.t = B.t` (so `B'.H = B.H`, `B'.U = B.U`), `Case2 B'`, and
`D : Case2Data B'` with `Case2Pre B' D` (§4 (1)–(5)) **and** `Case2PrePlus B' D`:

    ¬ 2 ∣ ((B'.S : Subgroup G) ⊓ D.M).relIndex D.M    -- S' ∩ M ∈ Syl₂(M)
    D.K = ⁅(B'.S : Subgroup G) ⊓ layerIn D.M, B'.U ⊓ D.M⁆     -- §4 (1)
    D.B0 = (B'.U ⊓ D.M) ⊓ centralizer ((B'.S ⊓ layerIn D.M : Subgroup G) : Set G)   -- §4 (2)

Route (Bender, p. 224): `M = E E(M)·C_M(t)` (`Submission.Work.CORE4.CountSetup`) and `E(M)` has one
class of involutions (`I.layerOneInvClass`), so `|M : C_M(t)|` is odd; hence a Sylow 2-subgroup of
`C_M(t)`, say `S ∩ M`, is Sylow in `M`, and it lies in `S^h` for some `h ∈ H = C_G(t)`
(`S ≤ H` because `t ∈ Z(S)`).  Replace `B` by `B'` with `S' = S^h`, `S₀' = S₀^h`, same `t` and `Ĥ`
(this fixes `H = C_G(t)` and `U = O(H)`, so `Case2 B ↔ Case2 B'`).  Then (1) `K = I_{U∩M}(s)` for an
involution `s ∈ S' ∩ E` inverting `U ∩ E/Z(E)` (structure of `A₇`/`L₂(q)`: `I.toolkit.lay`,
`I.toolkit.a7`, `I.toolkit.l2…`, `I.toolkit.autL2`), plus `D.K = [S' ∩ E, U ∩ M]` and
`D.B0 = C_{U∩M}(S' ∩ E)`.

This leaf supersedes the old `Case2Setup`: the old statement (any `B`, no Sylow condition, no
(1),(2)) cannot be proved, because `S ∩ M ∈ Syl₂(M)` is Bender's choice of `S` and `Case2Pre` does
not record it.  See `NOTES_CORE4.md` §6 and `NOTES_LEAD_gw_design9.md` §1.

## State of this file

**This file's own proof is complete and compiles.**  It rests on four imported leaves, all of them
the work of colleagues; their files still carry the `sorry` of the leaf statement until their
provers finish:

* `M_eq_layerIn_sup_of` (`M = E(M)·C_M(t)` at the hypothesis list actually needed),
* `case2_congr_t` (`Case2` depends only on `B.t`),
* `coe_smul_sylow_eq_conjSub` and **`exists_conj_B`**: Bender's choice of the Sylow 2-subgroup
  (pass to an `H`-conjugate `S^h` with `S^h ∩ M ∈ Syl₂(M)`) — the design-pass-9 contribution,
  self-contained (Mathlib Sylow conjugacy only),
* `Submission.Work.CORE4.Case2Setup9Odd` (`2 ∤ |M : C_M(t)|`, Bender's oddness — **proved**),
* `Submission.Work.CORE4.Case2Setup9Ecent2` (and `…/Case2Setup9Ecent`, its `Odd (orderOf e)`
  variant): the `E/Z(E)` structure fact behind Bender (4) — `e ∈ E` with `eZ(E)` of odd order and
  `e` centralising a Sylow of `E` implies `e ∈ C_G(E)` — **proved**,
* `Submission.Work.CORE4.Case2SixThreeRaw`: Bender (3) `F(U) ⊓ M = K₁ ⊔ F` for the raw data, with
  no `Case2Pre` available — **proved**.

The §4 (1)–(5) content is decomposed as

1. `Case2Setup9S` / `Case2Setup9S2` (Bender §4 (1),(2)): the involution `s ∈ P ⊓ E` with
   `K = [P ⊓ E, U ⊓ M] = I_{U⊓M}(s)` cyclic, `C_{U⊓M}(s) = C_{U⊓M}(P ⊓ E)` and
   `U ⊓ M = K ⊔ C_{U⊓M}(s)`; the `A₇`/`L₂(q)` structure theory of Bender p. 224.
2. `Case2Setup9Fprops` (Bender §4 (3),(4)): `F ≠ ⊥`, `F ≤ C_G(E(M))`, `N_G(F) = M`, from
   `Case2SixThreeRaw`, `I.toolkit.d110ii`, `Case2Setup9Ecent2` and the `X`-witness of
   Theorem 2.10 (2) — **proved**.
3. `Case2CU_s` (Bender §4 (5), `B = C_U(s)`, i.e. `C_U(s) ≤ M`): **PROVED** by design pass 17
   item A (`Submission/Work/CORE4/Case2CU_s.lean`, sorry-free: `N_G(F) = M` forces
   `F = C_{F(U)}(s)` by normalizer growth in the nilpotent `F(U)`).  The earlier claim that it was
   not derivable from this
   hypothesis budget.  `Case2Pre`'s last conjunct together with `Case2Data.B0_def` *is*
   `C_U(s) ≤ M`; six independent analyses (four reviews of `Case2Setup9F`/`Case2CU_s`, the prover
   of `Case2CU_s`, and the analysis recorded in `NOTES_CASE2SETUP9.md`) agree that the (1),(2) data
   plus the three facts of (2) do not determine it, and the `Case2CU_s` prover *proved* the sharp
   statement: `C_U(s) ≤ M` follows from the extra hypothesis `M ≤ N_G(C_{F(U)}(s))`
   (⟺ `C_{F(U)}(s) = F`, Bender's printed first half of (5)), machine-checked as
   `Work.CORE4.Case2CU_s_of_normal` is nevertheless correct as a reduction: it isolates the input
   `M ≤ N_G(C_{F(U)}(s))`, which design pass 17 obtains from `N_G(F) = M`, so the leaf is closed.
   Equivalences: `C_U(s) = C_H(s) ⊓ U` and
   `C_H(s) = C_U(s)·⟨s,t⟩`, so the goal is `C_H(s) ≤ M`; `F = C_{F(U)}(s) ⊓ M ⊴ M`, and
   `C_{F(U)}(s) ⊴ M` (equivalently `= F`) gives `C_U(s) ≤ N_G(C_{F(U)}(s)) = N_G(F) = M` at once.
   Counting does not obstruct the conclusion: with `|I_U(s)| = |U : C_U(s)|` (Bender 1.5(ii)) and
   `|U ⊓ M| = |K|·|B₀|` one gets `|I_U(s)| = |K|` whenever `C_U(s) ⊄ M`, which is consistent.

Consequences for this file: `Case2Setup9_of_CU` is the whole assembly with (5) taken as the
hypothesis `hCU`, and `Case2Setup9_of_normal` is the same statement with the sharp form of the
missing input; the target `Case2Setup9` is `Case2Setup9_of_CU I (Case2CU_s I)`. -/
/-- The assembly of `Case2SetupImpl9` from the four leaves, with Bender's §4 (5) (`B = C_U(s)`)
supplied as the hypothesis `hCU : Case2CU_s I`.  Everything in the assembly except (5) is proved in
this file or in the imported leaves (`Case2Setup9S` (1),(2); `Case2SixThreeRaw` (3);
`Case2Setup9Ecent2` + `Case2Setup9Fprops` (3),(4)).  `Case2Setup9_of_normal` below is the same
statement with the *sharp* form of the missing input. -/
theorem Case2Setup9_of_CU (I : Work.GW2.C4Inputs)
    (hCU : ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M P : Subgroup G) (s : G),
        IsCoatom M → B.t ∈ Work.GW2.layerIn M → ¬ B.H ≤ M →
        M = Work.GW2.layerIn M ⊔ (M ⊓ B.H) →
        IsPGroup 2 P → P ≤ M ⊓ B.H → ¬ 2 ∣ P.relIndex M →
        s ∈ P ⊓ Work.GW2.layerIn M → orderOf s = 2 →
        (Work.GW2.invSet (B.U ⊓ M) s : Set G) =
            ((⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) : Set G) →
        IsCyclic (⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) →
        ((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) =
            (B.U ⊓ M) ⊓ Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G) →
        B.U ⊓ M = (⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) ⊔
            ((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) →
        (((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ Work.GW2.fittingIn B.U) ≠ ⊥ →
        (((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ Work.GW2.fittingIn B.U) ≤
            Subgroup.centralizer ((Work.GW2.layerIn M : Subgroup G) : Set G) →
        Subgroup.normalizer (((((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓
            Work.GW2.fittingIn B.U) : Subgroup G) : Set G) = M →
        B.U ⊓ Subgroup.centralizer ({s} : Set G) =
            (B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) :
    Work.GW2.Case2SetupImpl9 I := by
  intro G _ _ hbc B hcase2
  classical
  have hcase2c : Work.GW2.Case2 B := hcase2
  obtain ⟨M, hMcoat, hMt, X, hXne, hXle, hXN⟩ := hcase2
  -- §4 (1)–(5) prelude: `E(M)` is one class of involutions, `H ⊄ M`, `M = E(M)·C_M(t)`
  have hone : Work.GW2.OneInvClassIn (Work.GW2.layerIn M) :=
    Case2LayerOneInvClass I G hbc B M hMcoat hMt
  have hnotH : ¬ B.H ≤ M :=
    Case2NotHLeM I G hbc B M hMcoat hMt ⟨X, hXne, hXle, hXN⟩
  have hsup : M = Work.GW2.layerIn M ⊔ (M ⊓ B.H) := M_eq_layerIn_sup_of B M hone hMt
  -- Bender's Sylow choice
  have hodd : ¬ 2 ∣ (M ⊓ B.H).relIndex M := Case2Setup9Odd I G hbc B M hMcoat hMt
  obtain ⟨B', hB't, hB'odd, hB'le, hB'pg⟩ := exists_conj_B B M hodd
  have ht' : B'.t ∈ Work.GW2.layerIn M := hB't.symm ▸ hMt
  -- `B'` has the same `H = C_G(t)` and `U = O(H)`
  have hBH : B'.H = B.H := by
    show Subgroup.centralizer ({B'.t} : Set G) = Subgroup.centralizer ({B.t} : Set G)
    rw [hB't]
  have hBU : B'.U = B.U := by
    show Work.GW2.oddCoreIn B'.H = Work.GW2.oddCoreIn B.H
    rw [hBH]
  have h2' : Work.GW2.Case2 B' := case2_congr_t hB't hcase2c
  have hsup' : M = Work.GW2.layerIn M ⊔ (M ⊓ B'.H) := by rw [hBH]; exact hsup
  have hXle' : X ≤ Work.GW2.fittingIn B'.U := by rw [hBU]; exact hXle
  have hnotH' : ¬ B'.H ≤ M := by rw [hBH]; exact hnotH
  have hB'le' : ((B'.S : Subgroup G) ⊓ M) ≤ M ⊓ B'.H := by rw [hBH]; exact hB'le
  -- §4 (1),(2): Bender's involution `s`
  obtain ⟨s, hsP, hs2, hKdef, hKcyc, hB0eq, hKB0⟩ :=
    Case2Setup9S I G hbc B' M ((B'.S : Subgroup G) ⊓ M) hMcoat ht' hsup' hB'pg hB'le' hB'odd
  have hsP' : s ∈ (B'.S : Subgroup G) ⊓ M := (Subgroup.mem_inf.mp hsP).1
  have hsM : s ∈ M := (Subgroup.mem_inf.mp hsP').2
  have hsH : s ∈ B'.H := (Subgroup.mem_inf.mp (hB'le' hsP')).2
  -- §4 (3): `F(U) ⊓ M = K₀ ⊔ F` (Bender's (3), raw form, no `Case2Pre` needed)
  have hKle : (⁅((B'.S : Subgroup G) ⊓ M) ⊓ Work.GW2.layerIn M, B'.U ⊓ M⁆ : Subgroup G) ≤
      B'.U ⊓ M := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨hg₁P, -⟩ := Subgroup.mem_inf.mp hg₁
    obtain ⟨hg₁S, hg₁M⟩ := Subgroup.mem_inf.mp hg₁P
    obtain ⟨hg₂U, hg₂M⟩ := Subgroup.mem_inf.mp hg₂
    have hg₁H : g₁ ∈ B'.H := (Subgroup.mem_inf.mp (hB'le' (Subgroup.mem_inf.mpr ⟨hg₁S, hg₁M⟩))).2
    rw [commutatorElement_def]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hconj : g₁ * g₂ * g₁⁻¹ ∈ B'.U :=
        (Subgroup.normal_subgroupOf_iff B'.U_le_H).mp B'.U_normal g₂ g₁ hg₂U hg₁H
      exact B'.U.mul_mem hconj (B'.U.inv_mem hg₂U)
    · exact M.mul_mem (M.mul_mem (M.mul_mem hg₁M hg₂M) (M.inv_mem hg₁M)) (M.inv_mem hg₂M)
  have hFU : Work.GW2.fittingIn B'.U ⊓ M =
      (Work.GW2.fittingIn B'.U ⊓
          (⁅((B'.S : Subgroup G) ⊓ M) ⊓ Work.GW2.layerIn M, B'.U ⊓ M⁆ : Subgroup G)) ⊔
        (((B'.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ Work.GW2.fittingIn B'.U) :=
    Case2SixThreeRaw I G hbc B' M s
      (⁅((B'.S : Subgroup G) ⊓ M) ⊓ Work.GW2.layerIn M, B'.U ⊓ M⁆)
      ((B'.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G))
      (((B'.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ Work.GW2.fittingIn B'.U)
      hsH hsM hs2 hKB0 hKle inf_le_left hKdef.symm rfl rfl
  -- the `E/Z(E)` structure input (Bender (4)): odd order modulo `Z(E)` plus a Sylow centraliser
  have hEcent := Case2Setup9Ecent2 I G hbc B' M ((B'.S : Subgroup G) ⊓ M)
    hMcoat ht' hB'pg hB'le' hB'odd
  -- §4 (3),(4): `F ≠ ⊥`, `F ≤ C_G(E)`, `N_G(F) = M`
  obtain ⟨hFne, hFcent, hFnorm⟩ :=
    Case2Setup9Fprops I G hbc B' M X ((B'.S : Subgroup G) ⊓ M) s hMcoat ht' hXne hXle' hXN
      hnotH' hsup' hB'pg hB'le' hB'odd hsP hs2 hKdef hKcyc hB0eq hKB0 hFU hEcent
  -- §4 (5): `B = C_U(s)` (from `hCU`)
  have hB0U : B'.U ⊓ Subgroup.centralizer ({s} : Set G) =
      (B'.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G) :=
    hCU G hbc B' M ((B'.S : Subgroup G) ⊓ M) s hMcoat ht' hnotH' hsup'
      hB'pg hB'le' hB'odd hsP hs2 hKdef hKcyc hB0eq hKB0 hFne hFcent hFnorm  -- the layer sits inside `M`
  have hEM : Work.GW2.layerIn M ≤ M := layerIn_le M
  have hinf : (B'.S : Subgroup G) ⊓ Work.GW2.layerIn M =
      ((B'.S : Subgroup G) ⊓ M) ⊓ Work.GW2.layerIn M := by
    rw [inf_assoc, inf_eq_right.mpr hEM]
  have hsM' : s ∈ (B'.S : Subgroup G) ⊓ Work.GW2.layerIn M := by
    obtain ⟨hs1, hs2'⟩ := Subgroup.mem_inf.mp hsP
    obtain ⟨hsS, -⟩ := Subgroup.mem_inf.mp hs1
    exact Subgroup.mem_inf.mpr ⟨hsS, hs2'⟩
  have hKdef' : ((⁅((B'.S : Subgroup G) ⊓ M) ⊓ Work.GW2.layerIn M, B'.U ⊓ M⁆ :
        Subgroup G) : Set G) = Work.GW2.invSet (B'.U ⊓ M) s := hKdef.symm
  -- the §4 objects
  let D : Work.GW2.Case2Data B' :=
    { M := M
      X := X
      s := s
      K := ⁅((B'.S : Subgroup G) ⊓ M) ⊓ Work.GW2.layerIn M, B'.U ⊓ M⁆
      B0 := (B'.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)
      F := ((B'.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ Work.GW2.fittingIn B'.U
      M_coatom := hMcoat
      t_mem := ht'
      X_ne := hXne
      X_le := hXle'
      NX_le := hXN
      s_mem := hsM'
      s_order := hs2
      K_def := hKdef'
      B0_def := rfl
      F_def := rfl }
  have hpre : Work.GW2.Case2Pre B' D :=
    ⟨hnotH', hone, hKcyc, hKB0, hFne, hFcent, hFnorm, hB0U.symm⟩
  have hpreplus : Work.GW2.Case2PrePlus B' D :=
    ⟨hB'odd, by rw [hinf], hB0eq.trans (by rw [hinf])⟩
  exact ⟨B', hB't, h2', D, hpre, hpreplus⟩

/-- `Case2SetupImpl9` conditional on the *exact* missing input of Bender's §4 (5), in the sharp
form identified by the `Case2CU_s` prover: the coatom `M` normalises `C_{F(U)}(s)`
(equivalently `C_{F(U)}(s) = F`, Bender's printed first half of (5); note `C_{F(U)}(s) = M ⊓ ⋯`
is *not* part of the hypotheses — CORRECTED by design pass 17 item A: `N_G(F) = M` **does** imply
it, via `le_normalizer_CFU_of_normalizer_F` in `Submission/Work/CORE4/Case2CU_s.lean`).

The hypothesis `hY` is exactly the last hypothesis of the machine-checked lemma
`Work.CORE4.Case2CU_s_of_normal` (`Submission/Work/CORE4/Case2CU_s.lean`), whose proof shows that
Bender's (5) follows from it.  So this statement records: *the whole of `Case2SetupImpl9` is
proved modulo that one normaliser statement*, i.e. a design which records `C_{F(U)}(s) ⊴ M`
(or `B = C_U(s)`) as an input of `Case2Pre` (as design pass 10 does) has the setup leaf. -/
theorem Case2Setup9_of_normal (I : Work.GW2.C4Inputs)
    (hY : ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M P : Subgroup G) (s : G),
        IsCoatom M → B.t ∈ Work.GW2.layerIn M →
        M = Work.GW2.layerIn M ⊔ (M ⊓ B.H) →
        IsPGroup 2 P → P ≤ M ⊓ B.H → ¬ 2 ∣ P.relIndex M →
        s ∈ P ⊓ Work.GW2.layerIn M → orderOf s = 2 →
        M ≤ Subgroup.normalizer
          (((Work.GW2.fittingIn B.U ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G)) : Set G)) :
    Work.GW2.Case2SetupImpl9 I :=
  Case2Setup9_of_CU I fun G _ _ hbc B M P s hcoat ht hnotH hsup hPg hPle hPidx hsP hs2
    hKdef hKcyc hB0eq hKB0 hFne hFcent hFnorm =>
    Work.CORE4.Case2CU_s_of_normal I G hbc B M P s hcoat ht hnotH hsup hPg hPle hPidx hsP hs2
      hKdef hKcyc hB0eq hKB0 hFne hFcent hFnorm
      (hY G hbc B M P s hcoat ht hsup hPg hPle hPidx hsP hs2)

/-- Bender 1981, §4 (1)–(5) with Bender's Sylow choice, design-pass-9 layer (the target).

This is `Case2Setup9_of_CU` with the leaf `Case2CU_s` (Bender's (5), `B = C_U(s)`) plugged in.
That leaf is now PROVED (design pass 17 item A, `Case2CU_s.lean`); the only remaining sorry on the
Setup path is `Case2Setup9S` (Bender's (1),(2)).  The rest of the leaf — Bender's Sylow choice
(`exists_conj_B`), and the (1),(2),(3),(4) content (leaves `Case2Setup9S`, `Case2SixThreeRaw`,
`Case2Setup9Ecent2`, `Case2Setup9Fprops`) — is proved, and `Case2Setup9_of_normal` completes the
argument once `C_{F(U)}(s) ⊴ M` is available. -/
theorem Case2Setup9 (I : Work.GW2.C4Inputs) : Work.GW2.Case2SetupImpl9 I :=
  Case2Setup9_of_CU I (Work.CORE4.Case2CU_s I)

end Work.CORE4
