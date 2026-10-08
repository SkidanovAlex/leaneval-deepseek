import Mathlib
import Submission.Work.BSW.Char.isTISubset_Kdiff
import Submission.Work.BSW.Api.normalizer_K_eq
import Submission.Work.BSW.Api.card_sup_zpowers
import Submission.Work.BSW.Api.ncard_involutions_eq_index
import Submission.Work.BSW.Char.iFn_eq_card_of_mem_K
import Submission.Work.BSW.Char.coset_sK_involutions
import Submission.Work.BSW.Char.ncard_coset_sK
import Submission.Work.BSW.Cases.bswCompletionBase
import Submission.Work.BSW.Cases.sum_iFn_centralizer
import Submission.Work.BSW.Cases.conjClassSet_K_eq_centralizer
import Submission.Work.BSW.Cases.ncard_conjClassSet_K
import Submission.Work.BSW.Cases.sum_iFn_conjClassSet_K
import Submission.Work.BSW.Cases.exists_conj_inverting_of_notMem

namespace Work.BSW.Cases

open Subgroup Work.GW2

/-! ## Two elementary helpers

* `exists_mul_gt_of_sum_gt`: the pigeonhole step — if `a > 0` and `a · Σ_{Sᶜ} f` exceeds
  `|Sᶜ| · b`, then some element of the complement beats the threshold `b`.
* `arith_key`: Bender's final arithmetic, `(k+1) · I · (I − k² + k − 1) >
  (I(k+1) − 1) · k(k+1+3ε)` for `I = (2k+ε)(k+ε)`, `ε = ±1` and `k ≥ 5`. -/

/-- Pigeonhole: a weighted sum over the complement of `S` that exceeds `|Sᶜ| · b` forces a single
term above `b`. -/
private theorem exists_mul_gt_of_sum_gt {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (f : ι → ℤ) {a b : ℤ} (ha : 0 < a)
    (h : a * ∑ x ∈ Sᶜ, f x > (Sᶜ.card : ℤ) * b) :
    ∃ x ∈ Sᶜ, b < a * f x := by
  by_contra hcon
  have hle : ∀ x ∈ Sᶜ, a * f x ≤ b := by
    intro x hx
    by_contra hlt
    exact hcon ⟨x, hx, not_le.mp hlt⟩
  have h1 : ∑ x ∈ Sᶜ, a * f x ≤ ∑ _x ∈ Sᶜ, b := Finset.sum_le_sum hle
  rw [Finset.mul_sum] at h
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  linarith

/-- Bender's final arithmetic (p. 232): with `I = (2k+ε)(k+ε)`, `ε = ±1` and `k ≥ 5`,
`(k+1)·I·(I − k² + k − 1) > (I(k+1) − 1)·k(k+1+3ε)`.  Both sides have the common factor
`k(k+1+3ε) = I − k² + k − 1 > 0`, the left one multiplied by the extra `(k+1)`. -/
private theorem arith_key {k I ε : ℤ} (hk : 5 ≤ k) (hε : ε = 1 ∨ ε = -1)
    (hI : I = (2 * k + ε) * (k + ε)) :
    (k + 1) * (I * (I - k ^ 2 + k - 1)) >
      (I * (k + 1) - 1) * (k * (k + 1 + 3 * ε)) := by
  have hJeq : I - k ^ 2 + k - 1 = k * (k + 1 + 3 * ε) := by
    rcases hε with h | h
    · rw [h] at hI ⊢
      rw [hI]; ring
    · rw [h] at hI ⊢
      rw [hI]; ring
  have hJpos : 0 < k * (k + 1 + 3 * ε) := by
    rcases hε with h | h
    · rw [h]; nlinarith
    · rw [h]; nlinarith
  have key : (k + 1) * (I * (k * (k + 1 + 3 * ε)))
      - (I * (k + 1) - 1) * (k * (k + 1 + 3 * ε)) = k * (k + 1 + 3 * ε) := by ring
  rw [hJeq]
  linarith [key, hJpos]

/-- Bender 1974 §3, the opening counting (`REFS/vision/bender1974_bsw/p0004.md`, p. 232): there is `x ∉ H^G` (`H^G` = the union of the conjugates of `H = C_G(t)`), inverted by `t`, with `i(x) > k + 3εk/(k+1)`; this is `Core8.BSWExistsXProp`.

Route (all inputs are already proved in this workspace):
* `K^G = H^G` and `|H^G| = |G:H|(k−1) + 1 = I(k−1) + 1`, since `K` is TI with `N_G(K) = H` of
  index `I = invCount G` (`Work.BSW.Char.isTISubset_Kdiff`, `Work.BSW.Api.normalizer_K_eq`,
  `Work.BSW.Api.card_sup_zpowers`, and the TI-saturation cardinality in the odd-order library,
  `OddOrder.BG.Ch4.S14.ncard_conjClassSet_of_isTISubset`, or `TISubsetCounting`).
* `∑_{x ∈ H^G} iFn G x = I(k²−k+2)`: on each conjugate `K^g` one has `iFn = k` off the involution
  and `k+1` on the `K^g s^g` coset (`iFn_eq_card_of_mem_K`, `coset_sK_involutions`,
  `iFn_of_orderOf_eq_two` in `Cases/bswCompletionProp.lean`), there are `I` conjugates, and
  `x = 1` contributes `I`.
* `∑_{x} iFn G x = I² + I` (`Work.BSW.Cases.sum_iFn`), so `∑_{x ∉ H^G} iFn x = I(I−k²+k−1)` over
  `|G| − 1 − I(k−1)` elements; the average exceeds `k + 3εk/(k+1)` because
  `I = (2k+ε)(k+ε)` and `∑/(|G∖H^G|+1) = k + 3εk/(k+1)` exactly.
* `i(x) > 0` gives an involution inverting `x`; conjugating by `g` with `t^g` that involution
  (using `BSWHyps2`(iv)) gives `t⁻¹ x t = x⁻¹` while preserving `x ∉ H^G` and `i(x)`. -/
theorem exists_notMem_HG_iFn_gt {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (ε : ℤ) (h : Work.GW2.BSWHyps2 G t s K) (hk : 4 < Nat.card ↥K) (hε : ε = 1 ∨ ε = -1)
    (hG : (Nat.card G : ℤ) = (2 * Nat.card ↥K + ε) * (Nat.card ↥K + ε) * (2 * Nat.card ↥K)) :
    ∃ x : G, x ∉ {y : G | ∃ g : G, g * y * g⁻¹ ∈ Subgroup.centralizer ({t} : Set G)} ∧
      t⁻¹ * x * t = x⁻¹ ∧
      (Nat.card ↥K : ℤ) * (Nat.card ↥K + 1 + 3 * ε) < (Nat.card ↥K + 1) * (Work.BSW.iFn G x : ℤ) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- Abbreviations: `k = |K|`, `I = invCount G`, `H = C_G(t)`.
  set k : ℤ := (Nat.card ↥K : ℤ) with hk_def
  set I : ℤ := (Work.BSW.invCount G : ℤ) with hI_def
  set H : Subgroup G := Subgroup.centralizer ({t} : Set G) with hH_def
  have hk5nat : 5 ≤ Nat.card ↥K := by omega
  have hk5 : (5 : ℤ) ≤ k := by rw [hk_def]; exact_mod_cast hk5nat
  have hk1pos : (0 : ℤ) < k + 1 := by linarith
  -- `I = |G : H|`
  have hIdx : Work.BSW.invCount G = H.index := by
    rw [hH_def]; exact Work.BSW.Api.ncard_involutions_eq_index h
  have hIdxI : (H.index : ℤ) = I := by rw [← hIdx, ← hI_def]
  -- `|H| = 2k`
  have hcardHnat : Nat.card ↥H = 2 * Nat.card ↥K := by
    rw [hH_def, Work.BSW.centralizer_t_eq h]
    exact Work.BSW.Api.card_sup_zpowers h
  have hcardH : (Nat.card ↥H : ℤ) = 2 * k := by
    rw [hcardHnat]; push_cast; rw [← hk_def]
  -- `|G| = I · 2k`
  have hGcard : (Nat.card G : ℤ) = I * (2 * k) := by
    have h1 := Subgroup.index_mul_card H
    have h2 : (Nat.card G : ℤ) = (H.index : ℤ) * (Nat.card ↥H : ℤ) := by
      rw [← h1]; push_cast; ring
    rw [h2, hcardH, hIdxI]
  -- `I = (2k+ε)(k+ε)`
  have hIeq : I = (2 * k + ε) * (k + ε) := by
    have hG' : (Nat.card G : ℤ) = (2 * k + ε) * (k + ε) * (2 * k) := by
      simpa only [hk_def] using hG
    have h2k : (2 * k : ℤ) ≠ 0 := by linarith
    exact mul_right_cancel₀ h2k (hGcard.symm.trans hG')
  -- The set `S = K^G = H^G` and its finset.
  set S : Set G := OddOrder.GroupTheory.conjClassSet (K : Set G) with hS_def
  set Sf : Finset G := (Set.toFinite S).toFinset with hSf_def
  have hSetc := conjClassSet_K_eq_centralizer h
  have hSeq : S = {z : G | ∃ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({t} : Set G)} := by
    rw [hS_def]; exact hSetc
  -- Cardinality of `S`.
  have hcardS : (S.ncard : ℤ) = I * (k - 1) + 1 := by
    have h1 := ncard_conjClassSet_K h
    rw [← hS_def] at h1
    rw [h1, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ Nat.card ↥K),
      Nat.cast_one, ← hI_def, ← hk_def]
  -- Cardinality of the complement of `S` in `G`: `I(k+1) - 1`.
  have hSfcard : Sf.card = S.ncard := by
    rw [hSf_def]; exact (Set.ncard_eq_toFinset_card S (Set.toFinite S)).symm
  have hcompl_card : (Sfᶜ.card : ℤ) = I * (k + 1) - 1 := by
    have h1 : Sfᶜ.card = Fintype.card G - Sf.card := Finset.card_compl Sf
    have hc : S.ncard ≤ Fintype.card G := by
      rw [← hSfcard]; exact Finset.card_le_univ Sf
    have h3 : (Sfᶜ.card : ℤ) = (Fintype.card G : ℤ) - (S.ncard : ℤ) := by
      rw [h1, hSfcard, Nat.cast_sub hc]
    have h4 : (Fintype.card G : ℤ) = I * (2 * k) := by
      rw [← Nat.card_eq_fintype_card]; exact hGcard
    rw [h3, h4, hcardS]; ring
  -- The sum of `iFn` over `S`, over `G`, and over the complement.
  have hsumS : ∑ x ∈ Sf, (Work.BSW.iFn G x : ℤ) = I * (k ^ 2 - k + 1) + I := by
    have h1 := sum_iFn_conjClassSet_K h
    rw [← hS_def, ← hSf_def] at h1
    rw [h1, ← hI_def, ← hk_def]
  have hsumAll : ∑ x : G, (Work.BSW.iFn G x : ℤ) = I ^ 2 + I := by
    have h1 := sum_iFn G
    have h2 : (∑ x : G, (Work.BSW.iFn G x : ℤ))
        = ((∑ x : G, Work.BSW.iFn G x : ℕ) : ℤ) := by push_cast; rfl
    rw [h2, h1]
    push_cast
    rw [← hI_def]
  have hsum_compl : ∑ x ∈ Sfᶜ, (Work.BSW.iFn G x : ℤ) = I * (I - k ^ 2 + k - 1) := by
    have h1 := Finset.sum_compl_add_sum Sf (fun x => (Work.BSW.iFn G x : ℤ))
    rw [hsumS, hsumAll] at h1
    have h2 : ∑ x ∈ Sfᶜ, (Work.BSW.iFn G x : ℤ) = I ^ 2 + I - (I * (k ^ 2 - k + 1) + I) := by
      linarith
    rw [h2]; ring
  -- The pigeonhole: some `y ∉ S` has `k(k+1+3ε) < (k+1)·i(y)`.
  have hineq : (k + 1) * (∑ x ∈ Sfᶜ, (Work.BSW.iFn G x : ℤ))
      > (Sfᶜ.card : ℤ) * (k * (k + 1 + 3 * ε)) := by
    rw [hsum_compl, hcompl_card]
    exact arith_key hk5 hε hIeq
  obtain ⟨y, hyS, hygt⟩ := exists_mul_gt_of_sum_gt Sf (fun x => (Work.BSW.iFn G x : ℤ)) hk1pos hineq
  have hyS' : y ∉ S := fun hy => (Finset.mem_compl.mp hyS) (by rw [hSf_def]; exact (Set.toFinite S).mem_toFinset.mpr hy)
  have hy_notin : y ∉ {z : G | ∃ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({t} : Set G)} := by
    rw [← hSeq]; exact hyS'
  have hy0 : 0 < Work.BSW.iFn G y := by
    have hb : 0 < k * (k + 1 + 3 * ε) := by
      rcases hε with h1 | h1
      · rw [h1]; nlinarith
      · rw [h1]; nlinarith
    have h1 : 0 < (k + 1) * (Work.BSW.iFn G y : ℤ) := lt_of_lt_of_le hb hygt.le
    have h2 : 0 < (Work.BSW.iFn G y : ℤ) := pos_of_mul_pos_right h1 hk1pos.le
    exact_mod_cast h2
  -- Conjugate so that `t` inverts the witness.
  obtain ⟨x, hx_notin, hxt, hxi⟩ := exists_conj_inverting_of_notMem h hy_notin hy0
  exact ⟨x, hx_notin, hxt, by simpa [hk_def, hxi] using hygt⟩

end Work.BSW.Cases
