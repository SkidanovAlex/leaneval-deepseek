/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Bender §3.2: the count `|U| = f(k+1)`

`F = C_G(x)` for `x ∉ H^G` inverted by `t`, `M = N_G(F)`, `f = |F|`, `K` the abelian
TI-subgroup of the BSW hypotheses, `k = |K|`.  Bender, *The Brauer–Suzuki–Wall theorem*,
Illinois J. Math. **18** (1974) 229–235, §3.2 (p. 233):

> Hence there are `f(2k−n)` elements outside `M`, among them `fk` involutions, commuting with an
> involution of `M`; …

where `n = |M : F|`.  Adding the `f` involutions of `M` itself, the number of involutions `y`
of `G` that commute with at least one involution of `M` is

`f + f k = f(k+1)`.

This file proves that count:

* `bswS32U_commuting_unique` — the *uniqueness* half of Bender's argument: two involutions
  `u, u' ∈ M` commuting with the same involution `y` coincide.  If `y ∈ M` this is the fact that
  distinct involutions of `M` never commute (`bswS32Setup.commute_involutions_iff`).  If `y ∉ M`
  then `u, u'` both invert `F`, so `u u' ∈ C_G(F) = F`; on the other hand `y` commutes with both,
  so `u u' ∈ M^y`; and `F ⊓ M^y = ⊥` (Bender §3.1(e), `bswS32Hall.tiNormalizer`).  Hence
  `u u' = 1`.
* `bswS32U` — the count itself: every `y ∈ U` has a *unique* commuting involution of `M`, so
  `U ≃ Σ_{u ∈ inv M} {y : y² = 1, uy = yu}`; each fibre has `k+1` elements
  (`ncard_involutions_centralizer_of_involution`) and there are `f` fibres (`bswS32Setup.card_invM`).
-/
import Mathlib
import Submission.Work.BSW.Cases.bswS32Setup
import Submission.Work.BSW.Cases.bswS32Hall
import Submission.Work.BSW.Cases.bswCompletionBase

namespace Work.BSW.Cases

set_option linter.style.haveILetI false

open Subgroup Work.GW2
open Work.BSW.S3

variable {G : Type} [Group G] [Finite G] {t s x : G} {K : Subgroup G}

/-- **Uniqueness of the commuting involution of `M`.**  If `y` is an involution and `u`, `u'` are
involutions of `M = N_G(F)` each commuting with `y`, then `u = u'`. -/
theorem bswS32U_commuting_unique (h : BSWHyps2 G t s K) (hx : x ∉ HG t)
    (hinv : t⁻¹ * x * t = x⁻¹) {y u u' : G}
    (hy2 : orderOf y = 2) (hu2 : orderOf u = 2) (huM : u ∈ NF x)
    (hu'2 : orderOf u' = 2) (hu'M : u' ∈ NF x)
    (huy : y * u = u * y) (hu'y : y * u' = u' * y) : u = u' := by
  by_cases hyM : y ∈ NF x
  · -- `y` and `u`, `u'` are commuting involutions of `M`, hence all equal.
    have key : ∀ v : G, orderOf v = 2 → v ∈ NF x → v * y = y * v → v = y := by
      intro v hv2 hvM hvy
      obtain ⟨c, hc, hcv⟩ := (mem_NF_involution_iff h hx hinv v).mp ⟨hv2, hvM⟩
      obtain ⟨d, hd, hdy⟩ := (mem_NF_involution_iff h hx hinv y).mp ⟨hy2, hyM⟩
      have hcomm : (t * c) * (t * d) = (t * d) * (t * c) := by rw [← hcv, ← hdy]; exact hvy
      have hcd : c = d := (commute_involutions_iff h hx hinv hc hd).mp hcomm
      rw [hcv, hdy, hcd]
    rw [key u hu2 huM huy.symm, key u' hu'2 hu'M hu'y.symm]
  · -- `y ∉ M`: `u` and `u'` invert `F`, and `M^y` meets `F` trivially.
    have hinyu : ∀ c ∈ CF x, u * c * u⁻¹ = c⁻¹ :=
      (involution_mem_normalizer_inverts h hx hinv huM hu2).1
    have hinyu' : ∀ c ∈ CF x, u' * c * u'⁻¹ = c⁻¹ :=
      (involution_mem_normalizer_inverts h hx hinv hu'M hu'2).1
    have hmemF : u * u' ∈ CF x := by
      have hcen : u * u' ∈ Subgroup.centralizer ((CF x : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        have e1 : (u * u') * c * (u * u')⁻¹ = c := by
          rw [mul_inv_rev]
          calc (u * u') * c * (u'⁻¹ * u⁻¹) = u * (u' * c * u'⁻¹) * u⁻¹ := by group
            _ = u * c⁻¹ * u⁻¹ := by rw [hinyu' c hc]
            _ = (u * c * u⁻¹)⁻¹ := by group
            _ = c := by rw [hinyu c hc, inv_inv]
        calc c * (u * u') = ((u * u') * c * (u * u')⁻¹) * (u * u') := by rw [e1]
          _ = (u * u') * c := by group
      have hce : Subgroup.centralizer ((CF x : Subgroup G) : Set G) = CF x :=
        centralizer_centralizer_eq_self h hx hinv
      rwa [hce] at hcen
    have hmemM : u * u' ∈ conjSub y (NF x) := by
      have huN : u ∈ conjSub y (NF x) := by
        rw [conjSub, Subgroup.mem_map]
        refine ⟨u, huM, ?_⟩
        show MulAut.conj y u = u
        rw [MulAut.conj_apply]
        calc y * u * y⁻¹ = (u * y) * y⁻¹ := by rw [huy]
          _ = u := by group
      have hu'N : u' ∈ conjSub y (NF x) := by
        rw [conjSub, Subgroup.mem_map]
        refine ⟨u', hu'M, ?_⟩
        show MulAut.conj y u' = u'
        rw [MulAut.conj_apply]
        calc y * u' * y⁻¹ = (u' * y) * y⁻¹ := by rw [hu'y]
          _ = u' := by group
      exact (conjSub y (NF x)).mul_mem huN hu'N
    have hbot : CF x ⊓ conjSub y (NF x) = ⊥ :=
      tiNormalizer (F := CF x) (centralizer_eq_of_mem_centralizer h hx hinv) y hyM
    have h1 : u * u' = 1 := by
      have hmem : u * u' ∈ CF x ⊓ conjSub y (NF x) := ⟨hmemF, hmemM⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact mul_left_cancel (by rw [h1, Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2])

theorem bswS32U {G : Type} [Group G] [Finite G] {t s x : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hx : x ∉ Work.BSW.HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    Nat.card {y : G // orderOf y = 2 ∧ ∃ u : G, orderOf u = 2 ∧
        u ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) ∧ y * u = u * y} =
      Nat.card ↥(Subgroup.centralizer ({x} : Set G)) * (Nat.card K + 1) := by
  classical
  -- The involutions of `M`, and, for each, the involutions of `G` commuting with it.
  let A := {u : G // orderOf u = 2 ∧ u ∈ NF x}
  haveI hAfintype : Fintype A := Fintype.ofFinite A
  let B : A → Type := fun u => {y : G // orderOf y = 2 ∧ y * (u : G) = (u : G) * y}
  let U := {y : G // orderOf y = 2 ∧ ∃ u : G, orderOf u = 2 ∧ u ∈ NF x ∧ y * u = u * y}
  have hsplit : Nat.card U = Nat.card (Σ u : A, B u) :=
    Nat.card_congr
      { toFun := fun y =>
          ⟨⟨Classical.choose y.2.2, (Classical.choose_spec y.2.2).1,
              (Classical.choose_spec y.2.2).2.1⟩,
            ⟨y.1, y.2.1, (Classical.choose_spec y.2.2).2.2⟩⟩
        invFun := fun p => ⟨p.2.1, p.2.2.1, ⟨p.1.1, p.1.2.1, p.1.2.2, p.2.2.2⟩⟩
        left_inv := fun y => Subtype.ext rfl
        right_inv := fun p => by
          obtain ⟨u, y⟩ := p
          let z : U := ⟨y.1, y.2.1, ⟨u.1, u.2.1, u.2.2, y.2.2⟩⟩
          have hch : ((⟨Classical.choose z.2.2, (Classical.choose_spec z.2.2).1,
              (Classical.choose_spec z.2.2).2.1⟩ : A) : G) = (u : G) :=
            bswS32U_commuting_unique h hx hinv y.2.1 (Classical.choose_spec z.2.2).1
              (Classical.choose_spec z.2.2).2.1 u.2.1 u.2.2
              (Classical.choose_spec z.2.2).2.2 y.2.2
          refine Sigma.ext (Subtype.ext hch) ?_
          refine (Subtype.heq_iff_coe_eq (fun w => ?_)).mpr rfl
          rw [hch] }
  rw [hsplit, Nat.card_sigma]
  have hconst : ∀ u : A, Nat.card (B u) = Nat.card K + 1 := by
    intro u
    have hstep : Nat.card (B u) =
        Nat.card {y : G // orderOf y = 2 ∧ y ∈ Subgroup.centralizer ({(u : G)} : Set G)} :=
      Nat.card_congr (Equiv.subtypeEquivRight
        (fun y => by rw [Subgroup.mem_centralizer_singleton_iff]))
    rw [hstep]
    exact ncard_involutions_centralizer_of_involution h u.2.1
  rw [Finset.sum_congr rfl (fun u _ => hconst u)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_invM h hx hinv]
  rfl

end Work.BSW.Cases
