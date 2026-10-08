/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Area BSW, Bender §2: the order of `G`

The assembly of Bender's §2 (`REFS/bender1974_bsw.txt`, pp. 230–232) into
`Work.BSW.BSWOrderProp`: for a finite simple nonabelian group `G` with an involution `t`, an
abelian `K ≤ C_G(t)` with `t ∈ K > 4`, `s` inverting `K` and `C_G(t) = K⟨s⟩`, `K` TI, all
involutions conjugate,

`|G| = (2k−1)(k−1)(2k)` or `|G| = (2k+1)(k+1)(2k)` with `k = |K|`.

The proof follows `Submission/Work/BSW/NOTES_BSW_order.md`: two linear characters `ρ₁, ρ₂` of `K`
give `α* = ind_K^G(1−ρ₁)`, `β* = ind_K^G(ρ₁−ρ₂)` with norms `3, −1, 2`; the decompositions
`α* = 1 + ψ₁ − ψ₂`, `β* = ν₁ − ν₂`; the involution-pair class function `i`
(`Work.BSW.Order.invPairCF`) is paired with `α*, β*` in two ways (Frobenius reciprocity versus the
character formula of Gorenstein 9.4.21); the resulting relations
`R(d+2)² = 2k²d(d+1)` and `R(d−2)² = 2k²d(d−1)` (`R = [G : C_G(t)]`) are solved by the arithmetic
lemmas `orderArithA`, `orderArithB`, using that `C_G(t)` is a Hall subgroup (`hallProp`).
-/
import Submission.Work.BSW.Cases.Order.Main
import Submission.Work.BSW.Char.exists_linear_characters
import Submission.Work.BSW.Cases.Order.hallProp
import Submission.Work.BSW.Cases.Order.orderArithA
import Submission.Work.BSW.Cases.Order.orderArithB
import Submission.Work.BSW.Cases.Order.existsDecompThree
import Submission.Work.BSW.Cases.Order.existsDecompTwo
import Submission.Work.BSW.Cases.Order.shareOfInnerEqNegOne
import Submission.Work.BSW.Cases.Order.arithRelA
import Submission.Work.BSW.Cases.Order.arithRelB
import Submission.Work.BSW.Parity.bswParityProp
import Submission.Work.BSW.Api.card_sup_zpowers
import Submission.Work.BSW.Api.normalizer_K_eq

namespace Work.BSW.Order

open Subgroup Work.GW2 OddOrder.RepresentationTheory

noncomputable section

theorem bswOrderProp_aux : Work.BSW.BSWOrderProp := by
  intro G _ _ hS hnab t s K h hk4
  classical
  letI : Fintype G := Fintype.ofFinite G
  haveI hInvG : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := G)).ne')
  haveI hInvK : Invertible (Nat.card ↥K : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := ↥K)).ne')
  have hk2 : Even (Nat.card ↥K) := Work.BSW.Parity.bswParityProp G t s K h
  have hk6 : 6 ≤ Nat.card ↥K := by
    obtain ⟨m, hm⟩ := hk2
    omega
  obtain ⟨ρ₁, ρ₂, hρ₁t, hρ₂t, hs1, hs2⟩ := Work.BSW.Char.exists_linear_characters h hk6
  have hρ₁ne : ρ₁ ≠ 1 := by
    intro hc
    obtain ⟨y, hy⟩ := hs1
    rw [hc] at hy
    simpa using hy
  have hρ₂ne : ρ₂ ≠ 1 := by
    intro hc
    rw [hc] at hρ₂t
    exact Work.BSW.Char.units_one_ne_neg_one (by simpa using hρ₂t)
  obtain ⟨hn1, hn2, hn3⟩ := Work.BSW.Char.inner_alpha_beta h ρ₁ ρ₂ hρ₁t hρ₂t hs1 hs2
  -- virtual characters, pairings with the trivial character, and the values at `1` and `t`
  have hαZ : Work.BSW.alphaFun K ρ₁ ∈ ZIrr G := alphaFun_mem_ZIrr ρ₁
  have hβZ : Work.BSW.betaFun K ρ₁ ρ₂ ∈ ZIrr G := betaFun_mem_ZIrr ρ₁ ρ₂
  have hα1 : ClassFunction.inner (Work.BSW.alphaFun K ρ₁) (trivialClassFunction G) = 1 :=
    inner_alphaFun_trivial ρ₁ hρ₁ne
  have hβ1 : ClassFunction.inner (Work.BSW.betaFun K ρ₁ ρ₂) (trivialClassFunction G) = 0 :=
    inner_betaFun_trivial ρ₁ ρ₂ hρ₁ne hρ₂ne
  have hα0 : Work.BSW.alphaFun K ρ₁ (1 : G) = 0 := alphaFun_apply_one ρ₁
  have hβ0 : Work.BSW.betaFun K ρ₁ ρ₂ (1 : G) = 0 := betaFun_apply_one ρ₁ ρ₂
  have hαt : Work.BSW.alphaFun K ρ₁ t = 0 := alphaFun_apply_t h ρ₁ hρ₁t
  have hβt : Work.BSW.betaFun K ρ₁ ρ₂ t = 4 := betaFun_apply_t h ρ₁ ρ₂ hρ₁t hρ₂t
  -- the two decompositions
  obtain ⟨ψ₁, ψ₂, hψ₁, hψ₂, hψ12, hdecα, hdegα⟩ :=
    Work.BSW.Cases.Order.existsDecompThree hαZ hn1 hα1 hα0
  obtain ⟨ν₁, ν₂, hν₁, hν₂, hν12, hdecβ, hdegβ⟩ :=
    Work.BSW.Cases.Order.existsDecompTwo hβZ hn3 hβ1 hβ0
  -- `β*(t) = 4` gives `ν₁(t) - ν₂(t) = 4`, and `⟨β*, i⟩ = 0` gives `ν₁(t)² = ν₂(t)²`
  have hνt : ν₁ t - ν₂ t = 4 := by
    have hh := hβt
    rw [hdecβ, ClassFunction.sub_apply] at hh
    exact hh
  have hβi : ClassFunction.inner (Work.BSW.betaFun K ρ₁ ρ₂) (invPairCF G t) = 0 :=
    inner_betaFun_invPairCF h ρ₁ ρ₂ hρ₁ne hρ₂ne
  have hformβ := inner_invPairCF_eq_sub h hν₁ hν₂ hdecβ
  have hcne : ((Nat.card G : ℂ) /
      (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2) ≠ 0 := by
    refine div_ne_zero ?_ (pow_ne_zero 2 ?_)
    · exact_mod_cast (Nat.card_pos (α := G)).ne'
    · exact_mod_cast (Nat.card_pos (α := Subgroup.centralizer ({t} : Set G))).ne'
  have hν1ne0 : ν₁ 1 ≠ 0 := by
    obtain ⟨m, hm0, hm, _⟩ := hν₁.exists_natDegree_charValue_one_dvd_card
    rw [hm]; exact_mod_cast hm0.ne'
  have hνsq : ν₁ t ^ 2 = ν₂ t ^ 2 := by
    have h0 : ((Nat.card G : ℂ) /
        (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2) *
        (ν₁ t ^ 2 / ν₁ 1 - ν₂ t ^ 2 / ν₂ 1) = 0 := by
      rw [← hformβ, hβi]
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact absurd h0 hcne
    · have h2 : (ν₁ t ^ 2 - ν₂ t ^ 2) / ν₁ 1 = 0 := by
        rw [hdegβ] at h0
        rw [← sub_div] at h0
        exact h0
      rw [div_eq_zero_iff] at h2
      rcases h2 with h2 | h2
      · linear_combination h2
      · exact absurd h2 hν1ne0
  have hν₁t : ν₁ t = 2 := by
    have hne : ν₁ t - ν₂ t ≠ 0 := by rw [hνt]; norm_num
    have hfac : (ν₁ t - ν₂ t) * (ν₁ t + ν₂ t) = 0 := by
      linear_combination hνsq
    have hsum0 : ν₁ t + ν₂ t = 0 := by
      rcases mul_eq_zero.mp hfac with h1 | h1
      · exact absurd h1 hne
      · exact h1
    calc ν₁ t = ((ν₁ t - ν₂ t) + (ν₁ t + ν₂ t)) / 2 := by ring
      _ = (4 + 0) / 2 := by rw [hνt, hsum0]
      _ = 2 := by norm_num
  have hν₂t : ν₂ t = -2 := by
    have hsum0 : ν₁ t + ν₂ t = 0 := by
      have hfac : (ν₁ t - ν₂ t) * (ν₁ t + ν₂ t) = 0 := by linear_combination hνsq
      have hne : ν₁ t - ν₂ t ≠ 0 := by rw [hνt]; norm_num
      rcases mul_eq_zero.mp hfac with h1 | h1
      · exact absurd h1 hne
      · exact h1
    rw [hν₁t] at hsum0
    linear_combination hsum0
  -- the sharing of a constituent
  have hshare : ψ₁ = ν₂ ∨ ψ₂ = ν₁ :=
    Work.BSW.Cases.Order.shareOfInnerEqNegOne hψ₁ hψ₂ hν₁ hν₂ hψ12 hν12 hdecα hdecβ hβ1 hn2
  -- `|C_G(t)| = 2k`, `|G| = 2k·R`
  have hCardC : Nat.card (Subgroup.centralizer ({t} : Set G)) = 2 * Nat.card ↥K := by
    rw [Work.BSW.centralizer_t_eq h, Work.BSW.Api.card_sup_zpowers h]
  set R : ℕ := (Subgroup.centralizer ({t} : Set G)).index with hR
  have hCardG : Nat.card G = 2 * Nat.card ↥K * R := by
    rw [hR, ← hCardC, mul_comm]
    exact (Subgroup.index_mul_card _).symm
  have hcop : Nat.Coprime (2 * Nat.card ↥K) R := by
    rw [hR]; exact Work.BSW.Cases.Order.hallProp h
  have hkpos : 0 < Nat.card ↥K := (Nat.card_pos (α := ↥K)).ne'.bot_lt
  rcases hshare with hA | hB
  · -- Case A: `ψ₁ = ν₂`; then `ψ₁(t) = -2`, `ψ₂(t) = -1`
    have hψ₁t : ψ₁ t = -2 := by rw [hA]; exact hν₂t
    have hψ₂t : ψ₂ t = -1 := by
      have hh : (1 : ℂ) + ψ₁ t - ψ₂ t = 0 := by
        have h1 := hαt
        rw [hdecα] at h1
        simpa using h1
      rw [hψ₁t] at hh
      linear_combination -hh
    obtain ⟨d, hdpos, hdcast, hddvd⟩ := hψ₁.exists_natDegree_charValue_one_dvd_card
    have hdne1 : d ≠ 1 := by
      intro hd1
      have h1 : ψ₁ 1 = 1 := by rw [hdcast, hd1]; norm_num
      have hmul := hψ₁.map_mul_of_apply_one_eq_one h1 t t
      rw [Work.BSW.t_mul_self h] at hmul
      have hsq : ψ₁ t ^ 2 = 1 := by rw [sq, ← hmul, h1]
      rw [hψ₁t] at hsq
      norm_num at hsq
    have hd2 : 2 ≤ d := by omega
    have hψ₂1 : ψ₂ 1 = ((d + 1 : ℕ) : ℂ) := by
      rw [hdegα, hdcast]; push_cast; ring
    have hαi : ClassFunction.inner (Work.BSW.alphaFun K ρ₁) (invPairCF G t) =
        (Nat.card ↥K : ℂ) := inner_alphaFun_invPairCF h ρ₁ hρ₁ne
    have hformα := inner_invPairCF_eq h hψ₁ hψ₂ hdecα
    have hkrel : (Nat.card ↥K : ℂ) =
        ((R : ℂ) / (2 * (Nat.card ↥K : ℂ))) *
          (1 + 4 / (d : ℂ) - 1 / ((d : ℂ) + 1)) := by
      have hc : ((Nat.card G : ℂ) /
          (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2) =
          (R : ℂ) / (2 * (Nat.card ↥K : ℂ)) := by
        rw [hCardG, hCardC] <;> push_cast <;> field_simp <;> ring
      have hbracket : (1 + ψ₁ t ^ 2 / ψ₁ 1 - ψ₂ t ^ 2 / ψ₂ 1) =
          (1 + 4 / (d : ℂ) - 1 / ((d : ℂ) + 1)) := by
        rw [hψ₁t, hψ₂t, hdcast, hψ₂1]
        push_cast
        ring
      have h := hαi.symm.trans hformα
      rw [hc, hbracket] at h
      exact h
    have hrel := Work.BSW.Cases.Order.arithRelA hkpos hdpos hkrel
    have hdvd1 : d ∣ 2 * Nat.card ↥K * R := by rw [← hCardG]; exact hddvd
    have hdvd2 : (d + 1) ∣ 2 * Nat.card ↥K * R := by
      rw [← hCardG]
      obtain ⟨e, _, he, hedvd⟩ := hψ₂.exists_natDegree_charValue_one_dvd_card
      have hee : e = d + 1 := by
        have hh : ((e : ℕ) : ℂ) = ((d + 1 : ℕ) : ℂ) := by rw [← he, hψ₂1]
        exact_mod_cast hh
      rw [← hee]; exact hedvd
    have hres := Work.BSW.Cases.Order.orderArithA (Nat.card ↥K) d R hk6 hd2 hcop hrel hdvd1 hdvd2
    refine Or.inl ?_
    rw [hCardG, hres]
    ring
  · -- Case B: `ψ₂ = ν₁`; then `ψ₂(t) = 2`, `ψ₁(t) = 1`
    have hψ₂t : ψ₂ t = 2 := by rw [hB]; exact hν₁t
    have hψ₁t : ψ₁ t = 1 := by
      have hh : (1 : ℂ) + ψ₁ t - ψ₂ t = 0 := by
        have h1 := hαt
        rw [hdecα] at h1
        simpa using h1
      rw [hψ₂t] at hh
      linear_combination hh
    obtain ⟨d, hdpos, hdcast, hddvd⟩ := hψ₂.exists_natDegree_charValue_one_dvd_card
    have hdne1 : d ≠ 1 := by
      intro hd1
      have h1 : ψ₂ 1 = 1 := by rw [hdcast, hd1]; norm_num
      have hmul := hψ₂.map_mul_of_apply_one_eq_one h1 t t
      rw [Work.BSW.t_mul_self h] at hmul
      have hsq : ψ₂ t ^ 2 = 1 := by rw [sq, ← hmul, h1]
      rw [hψ₂t] at hsq
      norm_num at hsq
    have hd2 : 2 ≤ d := by omega
    have hψ₁1 : ψ₁ 1 = ((d - 1 : ℕ) : ℂ) := by
      have hh : ψ₁ 1 = ψ₂ 1 - 1 := by rw [hdegα]; ring
      rw [hh, hdcast, Nat.cast_sub (by omega : 1 ≤ d)]
      push_cast; ring
    have hαi : ClassFunction.inner (Work.BSW.alphaFun K ρ₁) (invPairCF G t) =
        (Nat.card ↥K : ℂ) := inner_alphaFun_invPairCF h ρ₁ hρ₁ne
    have hformα := inner_invPairCF_eq h hψ₁ hψ₂ hdecα
    have hkrel : (Nat.card ↥K : ℂ) =
        ((R : ℂ) / (2 * (Nat.card ↥K : ℂ))) *
          (1 + 1 / ((d : ℂ) - 1) - 4 / (d : ℂ)) := by
      have hc : ((Nat.card G : ℂ) /
          (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2) =
          (R : ℂ) / (2 * (Nat.card ↥K : ℂ)) := by
        rw [hCardG, hCardC] <;> push_cast <;> field_simp <;> ring
      have hbracket : (1 + ψ₁ t ^ 2 / ψ₁ 1 - ψ₂ t ^ 2 / ψ₂ 1) =
          (1 + 1 / ((d : ℂ) - 1) - 4 / (d : ℂ)) := by
        have hcast : ((d - 1 : ℕ) : ℂ) = (d : ℂ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ d)]; push_cast; ring
        rw [hψ₁t, hψ₂t, hψ₁1, hdcast]
        push_cast
        rw [← hcast]
        ring
      have h := hαi.symm.trans hformα
      rw [hc, hbracket] at h
      exact h
    have hrel := Work.BSW.Cases.Order.arithRelB hkpos hd2 hkrel
    have hd3 : 3 ≤ d := by
      rcases Nat.eq_or_lt_of_le hd2 with h2 | h3
      · exfalso
        subst h2
        have hzero : R * (2 - 2) ^ 2 = 0 := by simp
        rw [hzero] at hrel
        have hk0 : 0 < Nat.card ↥K := by omega
        have hpos : (0 : ℕ) < 2 * (Nat.card ↥K) ^ 2 * 2 * (2 - 1) := by
          nlinarith [hk0]
        omega
      · exact h3
    have hdvd1 : d ∣ 2 * Nat.card ↥K * R := by rw [← hCardG]; exact hddvd
    have hdvd2 : (d - 1) ∣ 2 * Nat.card ↥K * R := by
      rw [← hCardG]
      obtain ⟨e, _, he, hedvd⟩ := hψ₁.exists_natDegree_charValue_one_dvd_card
      have hee : e = d - 1 := by
        have hh : ((e : ℕ) : ℂ) = ((d - 1 : ℕ) : ℂ) := by rw [← he, hψ₁1]
        exact_mod_cast hh
      rw [← hee]; exact hedvd
    have hres := Work.BSW.Cases.Order.orderArithB (Nat.card ↥K) d R hk6 hd3 hcop hrel hdvd1 hdvd2
    refine Or.inr ?_
    rw [hCardG, hres]
    ring

end

end Work.BSW.Order
