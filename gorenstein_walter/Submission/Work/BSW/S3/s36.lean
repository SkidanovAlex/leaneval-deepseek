/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, §3 leaves)

# BSW §3, leaf 3.6: `N(X)` for a nontrivial `p`-subgroup `X`

Target: `Work.BSW.S3.s36 : Work.BSW.BSWS36Prop` (Bender 1974, (3.6)): for `X ≠ ⊥` a
`p`-subgroup, the normalizer `N = N_G(X)` has a normal Sylow `p`-subgroup `P`, and a complement
`D` (so `P ⊔ D = N`, `P ⊓ D = ⊥`) that is conjugate into `C_G(x)` or into `K`.
-/
import Mathlib
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.Basic
import Submission.Work.BSW.S3.s36aux
import Submission.Work.BSW.S3.s36d
import Submission.Work.BSW.BSW36.normalizer_inf_normalizer_le_conj_K_or_conj_F
import Submission.Work.BSW.BSW36.normal_sylow_of_forall_sylow_normalizer_le_centralizer
import Submission.Work.BSW.BSW36.exists_normal_pgroup_of_isSolvable
import Submission.OddOrder.FeitThompson

namespace Work.BSW.S3

open Subgroup Work.GW2

theorem s36 : Work.BSW.BSWS36Prop := by
  intro G _ _ t s K x p h X hXne hXp
  haveI : Fact p.Prime := ⟨prime (h := h)⟩
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hNdef
  have hNodd : Odd (Nat.card ↥N) := by
    rw [hNdef]; exact normalizer_odd_order h hXne hXp
  -- Bender (3.6): `N_N(R) ≤ C_N(R)` for every prime `r ≠ p` and Sylow `r`-subgroup `R`
  have hBurn : ∀ (r : ℕ) (hr : r.Prime), r ≠ p → ∀ (R : Sylow r ↥N),
      (Subgroup.normalizer ((R : Subgroup ↥N) : Set ↥N) : Subgroup ↥N) ≤
        Subgroup.centralizer ((R : Subgroup ↥N) : Set ↥N) := by
    intro r hr hrp R
    haveI : Fact r.Prime := ⟨hr⟩
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    by_cases hRbot : (R : Subgroup ↥N) = ⊥
    · rw [hRbot] at hy
      rw [Subgroup.mem_bot.mp hy, mul_one, one_mul]
    · set R' : Subgroup G := (R : Subgroup ↥N).map N.subtype with hR'def
      have hR'le : R' ≤ N := Subgroup.map_subtype_le _
      have hR'p : IsPGroup r R' := R.isPGroup'.map N.subtype
      have hR'ne : R' ≠ ⊥ := by
        intro hb
        apply hRbot
        rw [eq_bot_iff]
        intro z hz
        rw [Subgroup.mem_bot]
        have h1 : (z : G) ∈ (⊥ : Subgroup G) := by
          rw [← hb]
          exact Subgroup.mem_map_of_mem N.subtype hz
        exact Subtype.ext (Subgroup.mem_bot.mp h1)
      have hwR : Work.GW2.conjSub w (R : Subgroup ↥N) = (R : Subgroup ↥N) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hw
      have hwN : (w : G) ∈ Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (R' : Set G) := by
        refine ⟨?_, ?_⟩
        · rw [← hNdef]; exact w.2
        · refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
          change Work.GW2.conjSub (w : G) R' = R'
          rw [hR'def, map_subtype_conjSub, hwR]
      have hyN : (y : G) ∈ Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (R' : Set G) := by
        refine ⟨?_, ?_⟩
        · rw [← hNdef]; exact y.2
        · refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
          change Work.GW2.conjSub (y : G) R' = R'
          have hyy : Work.GW2.conjSub y (R : Subgroup ↥N) = (R : Subgroup ↥N) :=
            Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hy)
          rw [hR'def, map_subtype_conjSub, hyy]
      rcases Work.BSW.BSW36.normalizer_inf_normalizer_le_conj_K_or_conj_F h hXne hXp hr hrp
          hR'le hR'ne hR'p with ⟨g, hg⟩ | ⟨g, hg⟩
      · have h1 : (w : G) ∈ Work.GW2.conjSub g K := hg hwN
        have h2 : (y : G) ∈ Work.GW2.conjSub g K := hg hyN
        have hc : (w : G) * (y : G) = (y : G) * (w : G) :=
          commute_of_mem_conjSub (isMulCommutative_K (hyps (h := h))) h1 h2
        exact Subtype.ext (by simpa using hc.symm)
      · have h1 : (w : G) ∈ Work.GW2.conjSub g (Subgroup.centralizer ({x} : Set G)) := hg hwN
        have h2 : (y : G) ∈ Work.GW2.conjSub g (Subgroup.centralizer ({x} : Set G)) := hg hyN
        have hc : (w : G) * (y : G) = (y : G) * (w : G) :=
          commute_of_mem_conjSub (inverts_centralizer_x h).2 h1 h2
        exact Subtype.ext (by simpa using hc.symm)
  -- Burnside's transfer theorem, applied to `↥N`: the Sylow `p`-subgroup is normal
  obtain ⟨L, hLnorm, hLp, hLuniq⟩ :=
    Work.BSW.BSW36.normal_sylow_of_forall_sylow_normalizer_le_centralizer (prime (h := h)) hBurn
  haveI : L.Normal := hLnorm
  haveI : Nonempty (Sylow p ↥N) := Sylow.nonempty
  let P₀ : Sylow p ↥N := Classical.choice ‹Nonempty (Sylow p ↥N)›
  have hLindex : ¬ p ∣ L.index := by
    rw [← hLuniq P₀]; exact Sylow.not_dvd_index P₀
  have hcop : Nat.Coprime (Nat.card ↥L) L.index := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := p)).mp hLp
    rw [ha]
    exact ((prime (h := h)).coprime_iff_not_dvd.mpr hLindex).pow_left a
  -- Schur–Zassenhaus: a complement of `L` in `↥N`
  obtain ⟨D₀, hD₀⟩ := Subgroup.exists_right_complement'_of_coprime (N := L) hcop
  have hsub : (L.map N.subtype).subgroupOf N = L := by
    ext z
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map_iff_mem (Subgroup.subtype_injective N)
  have hD₀card : Nat.card ↥D₀ = L.index :=
    Nat.mul_left_cancel (Nat.card_pos (α := ↥L))
      (by rw [hD₀.card_mul_card, Subgroup.card_mul_index])
  have hD₀odd : Odd (Nat.card ↥D₀) := by
    rw [hD₀card]
    exact Odd.of_dvd' hNodd ⟨Nat.card ↥L, by rw [mul_comm, Subgroup.card_mul_index]⟩
  refine ⟨L.map N.subtype, D₀.map N.subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le _
  · exact Subgroup.map_subtype_le _
  · exact IsPGroup.map hLp N.subtype
  · rw [hsub]; exact hLindex
  · rw [hsub]; exact hLnorm
  · rw [← Subgroup.map_sup, hD₀.sup_eq_top, Subgroup.map_top, Subgroup.range_subtype]
  · rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_inf] at hz
    obtain ⟨l, hl, hlz⟩ := Subgroup.mem_map.mp hz.1
    obtain ⟨d, hd, hdz⟩ := Subgroup.mem_map.mp hz.2
    have hld : l = d := Subtype.ext (hlz.trans hdz.symm)
    have hmem : l ∈ L ⊓ D₀ := ⟨hl, hld ▸ hd⟩
    rw [disjoint_iff.mp hD₀.disjoint] at hmem
    rw [Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot, ← hlz, hmem]
    rfl
  · by_cases hD₀bot : D₀ = ⊥
    · refine ⟨1, Or.inl ?_⟩
      rw [hD₀bot, Subgroup.map_bot]
      simp
    · haveI : Nontrivial ↥D₀ := (Subgroup.nontrivial_iff_ne_bot D₀).mpr hD₀bot
      -- `D₀ ≠ ⊥` is solvable of odd order, hence has a nontrivial normal `r`-subgroup `R₀`
      obtain ⟨r, R₀, hr, hR₀ne, hR₀norm, hR₀p⟩ :=
        Work.BSW.BSW36.exists_normal_pgroup_of_isSolvable
          (OddOrder.feitThompson hD₀odd : Group.IsSolvable ↥D₀)
      haveI : Fact r.Prime := ⟨hr⟩
      -- `r ∤ |D₀|`, hence `r ≠ p`
      have hrdvd : r ∣ Nat.card ↥R₀ := by
        haveI : Nontrivial ↥R₀ := (Subgroup.nontrivial_iff_ne_bot R₀).mpr hR₀ne
        obtain ⟨z, hz1⟩ := exists_ne (1 : ↥R₀)
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp hR₀p z
        have hz1' : orderOf z ≠ 1 := fun hc => hz1 (orderOf_eq_one_iff.mp hc)
        have hk0 : k ≠ 0 := by
          rintro rfl
          rw [pow_zero] at hk
          exact hz1' hk
        have h2 : orderOf z ∣ Nat.card ↥R₀ := by
          simpa using Subgroup.orderOf_dvd_natCard (⊤ : Subgroup ↥R₀) (Subgroup.mem_top z)
        rw [hk] at h2
        exact (dvd_pow_self r hk0).trans h2
      have hrp : r ≠ p := by
        intro hrp'
        apply hLindex
        rw [← hD₀card, ← hrp']
        exact hrdvd.trans (by
          simpa using Subgroup.card_dvd_of_le (le_top : R₀ ≤ (⊤ : Subgroup ↥D₀)))
      -- the normal `r`-subgroup of `D₀`, transported to `G`
      have hDle : D₀.map N.subtype ≤ N := Subgroup.map_subtype_le _
      have hRD : R₀.map (N.subtype.comp D₀.subtype) ≤ D₀.map N.subtype := by
        rintro z ⟨y, hy, rfl⟩
        exact Subgroup.mem_map_of_mem N.subtype y.2
      have hRne' : R₀.map (N.subtype.comp D₀.subtype) ≠ ⊥ := by
        intro hb
        apply hR₀ne
        rw [eq_bot_iff]
        intro y hy
        rw [Subgroup.mem_bot]
        have h1 : (N.subtype.comp D₀.subtype) y ∈ (⊥ : Subgroup G) := by
          rw [← hb]
          exact Subgroup.mem_map_of_mem _ hy
        exact Subtype.ext (Subtype.ext (by simpa using Subgroup.mem_bot.mp h1))
      have hRn : ∀ d ∈ D₀.map N.subtype, ∀ y ∈ R₀.map (N.subtype.comp D₀.subtype),
          d * y * d⁻¹ ∈ R₀.map (N.subtype.comp D₀.subtype) := by
        intro d hd y hy
        obtain ⟨d', hd', hd'e⟩ := Subgroup.mem_map.mp hd
        obtain ⟨y', hy', hy'e⟩ := Subgroup.mem_map.mp hy
        have h1 : ⟨d', hd'⟩ * y' * ⟨d', hd'⟩⁻¹ ∈ R₀ := hR₀norm.conj_mem y' hy' ⟨d', hd'⟩
        rw [← hd'e, ← hy'e]
        simpa using Subgroup.mem_map_of_mem (N.subtype.comp D₀.subtype) h1
      exact conjSub_le_of_normal_pgroup h hXne hXp hDle hRD hRne' hRn hr hrp
        (IsPGroup.map hR₀p (N.subtype.comp D₀.subtype))

end Work.BSW.S3
