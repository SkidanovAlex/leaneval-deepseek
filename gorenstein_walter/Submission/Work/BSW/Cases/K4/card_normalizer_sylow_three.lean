import Mathlib

set_option linter.style.haveILetI false

namespace Work.BSW.Cases.K4

/-- The number `n₃` of Sylow `3`-subgroups of a group of order `360` lies in `{1, 4, 10, 40}`.
Indeed `n₃ ∣ 360`, `n₃ ≤ 40` (as `n₃ = [G : N_G(Q)]` and `N_G(Q) ≥ Q` has order `9`), and
`n₃ ≡ 1 (mod 3)`. -/
private lemma sylow_three_number_dichotomy (n : ℕ) (hdvd : n ∣ 360) (hle : n ≤ 40)
    (hm : n ≡ 1 [MOD 3]) : n = 1 ∨ n = 4 ∨ n = 10 ∨ n = 40 := by
  have hn0 : n ≠ 0 := by rintro rfl; norm_num at hdvd
  interval_cases n <;> norm_num at *

/-- In a finite simple group of order `360` the normalizer of a Sylow `3`-subgroup has order
`36` (equivalently: `n₃ = 10`).

Divisor/mod argument: `n₃ ≡ 1 (mod 3)` and `n₃ ∣ 40` give `n₃ ∈ {1, 4, 10, 40}`.  `n₃ ≠ 1` by
simplicity.  `n₃ ≠ 40` because then `N_G(Q) = Q` and Burnside's normal `p`-complement result
(`hasNormalPComplement_of_sylow_normalizer_le_centralizer`) would give a nontrivial proper normal
subgroup.  `n₃ ≠ 4` because the conjugation action of `G` on the four Sylow 3-subgroups is faithful
(its kernel is a normal subgroup, not `⊤` since `n₃ = 4 ≠ 1`), forcing an injection
`G ↪ Equiv.Perm (Sylow 3 G)` with `|Equiv.Perm (Sylow 3 G)| = 4! = 24 < 360`.  The hypothesis
`hburn` is the general consequence of Burnside's result, stated as
`Work.BSW.Cases.K4.exists_not_mem_centralizer_of_isPGroup` (for the Sylow form, apply it to
`Q : Sylow 3 G` coerced to a subgroup). -/
theorem card_normalizer_sylow_three {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 360)
    (hburn : ∀ {p : ℕ} [Fact p.Prime] (Q : Sylow p G), p ∣ Nat.card G →
      ∃ g : G, g ∈ Subgroup.normalizer (Q : Set G) ∧
        g ∉ Subgroup.centralizer ((Q : Subgroup G) : Set G))
    (Q : Sylow 3 G) :
    Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G)) = 36 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite (Sylow 3 G) := inferInstance
  have h3dvd : 3 ∣ Nat.card G := by rw [hG]; norm_num
  have hQcard : Nat.card ↥(Q : Subgroup G) = 9 := by
    rw [Sylow.card_eq_multiplicity, hG]; norm_num [Nat.factorization]
  let N : Subgroup G := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  change Nat.card ↥N = 36
  have hQleN : (Q : Subgroup G) ≤ N := Subgroup.le_normalizer
  have hn_eq : N.index = Nat.card (Sylow 3 G) := (Sylow.card_eq_index_normalizer Q).symm
  -- number-theoretic restriction on the number of Sylow 3-subgroups
  have hcardSyl : Nat.card (Sylow 3 G) ∣ 360 := by
    have h := Subgroup.card_mul_index N
    rw [hn_eq, hG] at h
    exact ⟨Nat.card ↥N, by rw [← h, mul_comm]⟩
  have hle : Nat.card (Sylow 3 G) ≤ 40 := by
    have h9 : 9 ≤ Nat.card ↥N := by
      have := Nat.card_le_card_of_injective (Subgroup.inclusion hQleN)
        (Subgroup.inclusion_injective hQleN)
      rwa [hQcard] at this
    have h := Subgroup.card_mul_index N
    rw [hn_eq, hG] at h
    have : 9 * Nat.card (Sylow 3 G) ≤ 360 :=
      calc 9 * Nat.card (Sylow 3 G) ≤ Nat.card ↥N * Nat.card (Sylow 3 G) :=
            Nat.mul_le_mul_right _ h9
        _ = 360 := h
    omega
  have hmod : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
  have hnum := sylow_three_number_dichotomy _ hcardSyl hle hmod
  -- rule out `n₃ = 1`
  have h1 : Nat.card (Sylow 3 G) ≠ 1 := by
    intro h
    have hNtop : N = ⊤ := Subgroup.index_eq_one.mp (by rw [hn_eq]; exact h)
    have hQnorm : (Q : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    haveI := hQnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q : Subgroup G) with hbot | htop
    · exact Sylow.ne_bot_of_dvd_card Q h3dvd hbot
    · have hc : Nat.card ↥(Q : Subgroup G) = Nat.card G := by rw [htop, Subgroup.card_top]
      omega
  -- rule out `n₃ = 40`
  have h40 : Nat.card (Sylow 3 G) ≠ 40 := by
    intro h
    have hNcard : Nat.card ↥N = 9 := by
      have hh := Subgroup.card_mul_index N
      rw [hn_eq, h, hG] at hh
      omega
    have hNQ : N = (Q : Subgroup G) := by
      have hh := Subgroup.eq_of_le_of_card_ge hQleN (by rw [hNcard, hQcard])
      exact hh.symm
    obtain ⟨g, hgN, hgC⟩ := hburn Q h3dvd
    have hgQ : g ∈ (Q : Subgroup G) := hNQ ▸ hgN
    haveI : IsMulCommutative ↥(Q : Subgroup G) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := ↥(Q : Subgroup G))
        (by rw [hQcard]; norm_num)
    have hQC := Subgroup.le_centralizer (Q : Subgroup G)
    exact hgC (hQC hgQ)
  -- rule out `n₃ = 4`
  have h4 : Nat.card (Sylow 3 G) ≠ 4 := by
    intro h
    set f : G →* Equiv.Perm (Sylow 3 G) := MulAction.toPermHom G (Sylow 3 G) with hf
    have hKle : f.ker ≤ N := by
      intro g hg
      rw [MonoidHom.mem_ker] at hg
      have h2 : g • Q = Q := by
        have h3 := congrArg (fun e : Equiv.Perm (Sylow 3 G) => e Q) hg
        simpa [hf, MulAction.toPermHom_apply] using h3
      exact (Sylow.smul_eq_iff_mem_normalizer).mp h2
    have hNne : N ≠ ⊤ := by
      intro hNtop
      have hh : N.index = 1 := Subgroup.index_eq_one.mpr hNtop
      rw [hn_eq] at hh
      omega
    have hKne : f.ker ≠ ⊤ := by
      intro hKtop
      exact hNne (top_le_iff.mp (hKtop ▸ hKle))
    haveI : f.ker.Normal := MonoidHom.normal_ker f
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with hbot | htop
    · have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hbot
      have hle2 := Nat.card_le_card_of_injective f hinj
      have hperm : Nat.card (Equiv.Perm (Sylow 3 G)) = 24 := by
        rw [Nat.card_perm, h]; norm_num
      rw [hG, hperm] at hle2
      norm_num at hle2
    · exact hKne htop
  have hn10 : Nat.card (Sylow 3 G) = 10 := by
    rcases hnum with h | h | h | h <;> omega
  have hcm := Subgroup.card_mul_index N
  rw [hn_eq, hn10, hG] at hcm
  omega

end Work.BSW.Cases.K4
