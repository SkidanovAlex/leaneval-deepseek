import Mathlib
import Submission.Work.ZassenhausSuzuki.ncard_iUnion_conj
import Submission.Work.ZassenhausTwoGroup.normalizer_Q_eq
import Submission.Work.ZassenhausTwoGroup.normalizer_twoPoint
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.ZassenhausTwoGroup.card_H_eq
import Submission.Work.ZassenhausSuzuki.twoPoint_conj_inf_eq_bot
import Submission.Work.ThmG.rankOne_index
import Submission.Work.ZassenhausSuzuki.arith_card_le
import Submission.Work.ZassenhausSuzuki.ncard_union_three_le
import Submission.Work.ZassenhausSuzuki.isPGroup_two_inf_eq_bot_of_odd
import Submission.Work.ZassenhausSuzuki.card_normalizer_twoPoint

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.card_Q_le_q`

The counting endgame of Suzuki's Theorem 1 (`Q_suzuki_sq`): in the split rank-one Zassenhaus
set-up with `Q ≠ ⊥` a `2`-group, if `V` is a subgroup of order `q + 1` (`q = |Q₀(H)|`) whose
normaliser has order `2(q + 1)`, whose distinct conjugates meet trivially and which meets every
conjugate of `Q` and of `D = twoPoint H t` trivially, then `|Q| ≤ q`.

Write `N = |Q|`, `d = |D| = q - 1`.  The proof is the classical count on the union of the three
families of conjugates:

* `A = ⋃_g Qᵍ`: a union of `[G : N_G(Q)] = [G : H] = N + 1` conjugates of `Q` meeting pairwise
  in `1`, so `|A| = 1 + (N + 1)(N - 1) = N²`;
* `B = ⋃_g Dᵍ`: `[G : N_G(D)]` conjugates of `D` meeting pairwise in `1`, each contributing
  `|D| - 1` further elements;
* `C = ⋃_g Vᵍ`: conjugates of `V` meeting pairwise in `1`, each contributing `|V| - 1 = q`
  further elements.

The three pairwise intersections are exactly `{1}` (`hVQ`, `hVD`, and `2`-group vs. odd order),
so `|G| ≥ |A| + |B| + |C| - 2`; substituting the cardinalities and `|G| = N(N+1)d` gives
`N² + iD·(d-1) + iV·q ≤ N(N+1)d`, and the arithmetic (`arith_card_le`) turns this into `N ≤ q`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.ZassenhausSuzuki

theorem card_Q_le_q {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hQ : Q ≠ ⊥) (V : Subgroup G)
    (hDq : Nat.card ↥(Submission.Blueprint.twoPoint H t) + 1 = Nat.card ↥(Work.ThmF.Q0sub H))
    (hVcard : Nat.card ↥V = Nat.card ↥(Work.ThmF.Q0sub H) + 1)
    (hVnorm : Nat.card ↥(Subgroup.normalizer (V : Set G)) =
      2 * (Nat.card ↥(Work.ThmF.Q0sub H) + 1))
    (hVTI : ∀ g : G, Submission.Blueprint.conj g V ≠ V →
      V ⊓ Submission.Blueprint.conj g V = ⊥)
    (hVQ : ∀ g : G, V ⊓ Submission.Blueprint.conj g Q = ⊥)
    (hVD : ∀ g : G, V ⊓ Submission.Blueprint.conj g (Submission.Blueprint.twoPoint H t) = ⊥) :
    Nat.card ↥Q ≤ Nat.card ↥(Work.ThmF.Q0sub H) := by
  classical
  -- ## Notation
  set D : Subgroup G := twoPoint H t with hDdef
  set d : ℕ := Nat.card ↥D with hddef
  set q : ℕ := Nat.card ↥(Work.ThmF.Q0sub H) with hqdef
  set N : ℕ := Nat.card ↥Q with hNdef
  have hNpos : 0 < N := by rw [hNdef]; exact Nat.card_pos
  have hd1 : 1 ≤ d := by
    have : 0 < d := by rw [hddef]; exact Nat.card_pos
    omega
  have hq : q = d + 1 := hDq.symm
  -- ## The order of `G`
  have hHindex : H.index = N + 1 := by rw [hNdef]; exact Work.ThmG.rankOne_index h
  have hHcard : Nat.card ↥H = N * d := by
    rw [Work.ZassenhausTwoGroup.card_H_eq h, ← hNdef, ← hDdef, ← hddef]
  have hG : Nat.card G = N * (N + 1) * d := by
    rw [← Subgroup.index_mul_card H, hHindex, hHcard]; ring
  -- ## TI hypotheses in the `N_G(·)`-index form
  have hTIQ : ∀ g : G, g ∉ Subgroup.normalizer (Q : Set G) → Q ⊓ conj g Q = ⊥ := by
    intro g hg
    rw [Work.ZassenhausTwoGroup.normalizer_Q_eq h hQ] at hg
    exact Work.ZassenhausTwoGroup.isTI_Q h hZ g hg
  have hTID : ∀ g : G, g ∉ Subgroup.normalizer (D : Set G) → D ⊓ conj g D = ⊥ := by
    intro g hg
    rw [hDdef]
    refine Work.ZassenhausSuzuki.twoPoint_conj_inf_eq_bot h hZ ?_
    intro hc
    refine hg ?_
    rw [hDdef]
    exact Work.Models.mem_normalizer_of_conj_eq hc
  have hTIV : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conj g V = ⊥ := by
    intro g hg
    exact hVTI g (fun hc => hg (Work.Models.mem_normalizer_of_conj_eq hc))
  -- ## The three families of conjugates
  set AQ : Set G := ⋃ g : G, (conj g Q : Set G) with hAQdef
  set AD : Set G := ⋃ g : G, (conj g D : Set G) with hADdef
  set AV : Set G := ⋃ g : G, (conj g V : Set G) with hAVdef
  set iD : ℕ := (Subgroup.normalizer (D : Set G)).index with hiDdef
  set iV : ℕ := (Subgroup.normalizer (V : Set G)).index with hiVdef
  have hAQcard : AQ.ncard = N * N := by
    rw [hAQdef, ncard_iUnion_conj Q hTIQ,
      Work.ZassenhausTwoGroup.normalizer_Q_eq h hQ, hHindex, ← hNdef]
    have hNN : 1 + (N + 1) * (N - 1) = N * N := by
      obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
      rw [hm]
      have hm1 : m + 1 - 1 = m := by omega
      rw [hm1]; ring
    exact hNN
  have hADcard : AD.ncard = 1 + iD * (d - 1) := by
    rw [hADdef, ncard_iUnion_conj D hTID, ← hddef, ← hiDdef]
  have hAVcard : AV.ncard = 1 + iV * q := by
    rw [hAVdef, ncard_iUnion_conj V hTIV, ← hiVdef]
    have : Nat.card ↥V - 1 = q := by rw [hVcard]; omega
    rw [this]
  -- ## A conjugate of `Q` meets a conjugate of `D` trivially (`2`-group vs. odd order)
  have hQinfD : ∀ g : G, Q ⊓ conj g D = ⊥ := by
    intro g
    rw [hDdef]
    exact isPGroup_two_inf_eq_bot_of_odd (A := Q) (B := conj g (twoPoint H t)) h2
      (by rw [Work.Models.card_conj]; exact Work.ThmF.split_odd_card_twoPoint h)
  have hVinfD : ∀ g : G, V ⊓ conj g D = ⊥ := by
    intro g; rw [hDdef]; exact hVD g
  -- ## The pairwise intersections of the three families are `{1}`
  have hIntAQAD : AQ ∩ AD = {1} := by
    rw [hAQdef, hADdef]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨g1, hg1⟩, ⟨g2, hg2⟩⟩
      have hyQ : g1⁻¹ * x * g1 ∈ Q := Work.Models.mem_conj_iff.mp hg1
      have hyD : g1⁻¹ * x * g1 ∈ conj (g1⁻¹ * g2) D := by
        rw [Work.Models.mem_conj_iff]
        have hh : (g1⁻¹ * g2)⁻¹ * (g1⁻¹ * x * g1) * (g1⁻¹ * g2) = g2⁻¹ * x * g2 := by
          group
        rw [hh]
        exact Work.Models.mem_conj_iff.mp hg2
      have hbot := hQinfD (g1⁻¹ * g2)
      have hmem : g1⁻¹ * x * g1 ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact ⟨hyQ, hyD⟩
      have h1 : g1⁻¹ * x * g1 = 1 := Subgroup.mem_bot.mp hmem
      calc x = g1 * (g1⁻¹ * x * g1) * g1⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · intro hx
      rw [hx]
      exact ⟨⟨1, Work.Models.mem_conj_iff.mpr (by simpa using Q.one_mem)⟩,
             ⟨1, Work.Models.mem_conj_iff.mpr (by simpa using D.one_mem)⟩⟩
  have hIntAQAV : AQ ∩ AV = {1} := by
    rw [hAQdef, hAVdef]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨g1, hg1⟩, ⟨g2, hg2⟩⟩
      have hyV : g2⁻¹ * x * g2 ∈ V := Work.Models.mem_conj_iff.mp hg2
      have hyQ : g2⁻¹ * x * g2 ∈ conj (g2⁻¹ * g1) Q := by
        rw [Work.Models.mem_conj_iff]
        have hh : (g2⁻¹ * g1)⁻¹ * (g2⁻¹ * x * g2) * (g2⁻¹ * g1) = g1⁻¹ * x * g1 := by
          group
        rw [hh]
        exact Work.Models.mem_conj_iff.mp hg1
      have hbot := hVQ (g2⁻¹ * g1)
      have hmem : g2⁻¹ * x * g2 ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact ⟨hyV, hyQ⟩
      have h1 : g2⁻¹ * x * g2 = 1 := Subgroup.mem_bot.mp hmem
      calc x = g2 * (g2⁻¹ * x * g2) * g2⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · intro hx
      rw [hx]
      exact ⟨⟨1, Work.Models.mem_conj_iff.mpr (by simpa using Q.one_mem)⟩,
             ⟨1, Work.Models.mem_conj_iff.mpr (by simpa using V.one_mem)⟩⟩
  have hIntADAV : AD ∩ AV = {1} := by
    rw [hADdef, hAVdef]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨g1, hg1⟩, ⟨g2, hg2⟩⟩
      have hyV : g2⁻¹ * x * g2 ∈ V := Work.Models.mem_conj_iff.mp hg2
      have hyD : g2⁻¹ * x * g2 ∈ conj (g2⁻¹ * g1) D := by
        rw [Work.Models.mem_conj_iff]
        have hh : (g2⁻¹ * g1)⁻¹ * (g2⁻¹ * x * g2) * (g2⁻¹ * g1) = g1⁻¹ * x * g1 := by
          group
        rw [hh]
        exact Work.Models.mem_conj_iff.mp hg1
      have hbot := hVinfD (g2⁻¹ * g1)
      have hmem : g2⁻¹ * x * g2 ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact ⟨hyV, hyD⟩
      have h1 : g2⁻¹ * x * g2 = 1 := Subgroup.mem_bot.mp hmem
      calc x = g2 * (g2⁻¹ * x * g2) * g2⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · intro hx
      rw [hx]
      exact ⟨⟨1, Work.Models.mem_conj_iff.mpr (by simpa using D.one_mem)⟩,
             ⟨1, Work.Models.mem_conj_iff.mpr (by simpa using V.one_mem)⟩⟩
  -- ## The count
  have hunion := ncard_union_three_le AQ AD AV 1 hIntAQAD hIntAQAV hIntADAV
  have hleG : (AQ ∪ AD ∪ AV).ncard ≤ Nat.card G := by
    have hh := Set.ncard_le_ncard (s := AQ ∪ AD ∪ AV) (t := Set.univ)
      (Set.subset_univ _) (Set.toFinite _)
    simpa [Set.ncard_univ] using hh
  have hcount : N * N + iD * (d - 1) + iV * q ≤ Nat.card G := by
    have h1 := hunion
    rw [hAQcard, hADcard, hAVcard] at h1
    have h2 : N * N + iD * (d - 1) + iV * q ≤ (AQ ∪ AD ∪ AV).ncard := by omega
    exact le_trans h2 hleG
  -- ## The indices
  have hmult : 2 * (q + 1) * (N * N + iD * (d - 1) + iV * q) ≤
      2 * (q + 1) * (N * (N + 1) * d) := by
    have hh := Nat.mul_le_mul_left (2 * (q + 1)) hcount
    rwa [hG] at hh
  have hDiD : 2 * (q + 1) * (iD * (d - 1)) = (q + 1) * N * (N + 1) * (d - 1) := by
    rcases eq_or_lt_of_le hd1 with h1 | h1
    · rw [← h1]; simp
    · -- `d ≥ 2`, so `D ≠ ⊥` and `N_G(D) = D ⊔ ⟨t⟩` has order `2d`
      have hDne : D ≠ ⊥ := by
        intro hbot
        have hd_eq : d = 1 := by rw [hddef, hbot, Subgroup.card_bot]
        omega
      have hNormCard : Nat.card ↥(Subgroup.normalizer (D : Set G)) = 2 * d := by
        have hh := card_normalizer_twoPoint h hZ (by rw [← hDdef]; exact hDne)
        rwa [← hDdef, ← hddef] at hh
      have h2iD : 2 * iD = N * (N + 1) := by
        have hh : iD * Nat.card ↥(Subgroup.normalizer (D : Set G)) = Nat.card G := by
          rw [hiDdef]; exact Subgroup.index_mul_card (Subgroup.normalizer (D : Set G))
        rw [hNormCard, hG] at hh
        have hh' : (2 * iD) * d = (N * (N + 1)) * d := by linear_combination hh
        exact Nat.mul_right_cancel (by omega : 0 < d) hh'
      calc 2 * (q + 1) * (iD * (d - 1)) = (q + 1) * (2 * iD * (d - 1)) := by ring
        _ = (q + 1) * (N * (N + 1) * (d - 1)) := by rw [h2iD]
        _ = (q + 1) * N * (N + 1) * (d - 1) := by ring
  have hVidx : 2 * (q + 1) * iV = N * (N + 1) * d := by
    have hh : iV * Nat.card ↥(Subgroup.normalizer (V : Set G)) = Nat.card G := by
      rw [hiVdef]; exact Subgroup.index_mul_card (Subgroup.normalizer (V : Set G))
    rw [hVnorm, hG] at hh
    linear_combination hh
  have hViV : 2 * (q + 1) * (iV * q) = N * (N + 1) * d * q := by
    linear_combination (hVidx) * q
  have hmain : 2 * (q + 1) * N * N + (q + 1) * N * (N + 1) * (d - 1) + N * (N + 1) * d * q
      ≤ 2 * (q + 1) * (N * (N + 1) * d) := by
    have h1 := hmult
    have hexp : 2 * (q + 1) * (N * N + iD * (d - 1) + iV * q)
        = 2 * (q + 1) * N * N + 2 * (q + 1) * (iD * (d - 1)) + 2 * (q + 1) * (iV * q) := by
      ring
    rw [hexp, hDiD, hViV] at h1
    exact h1
  -- ## Arithmetic
  exact arith_card_le hNpos hd1 hq hmain

end Work.ZassenhausSuzuki
