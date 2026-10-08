/-
# `Work.PSU3.StageB.Omega.good_shift_of_mem_selfSet` — §2 (20), the self-orbit case

Peterfalvi II Ch. VII §2 (20) compares two *different* `KW`-orbits: if `ω₁, ω₂` are good with a
common shift `α` and `bar ω₁ ∉ orbE (bar ω₂)`, then for `x` in the cross-fibre the sharp relation
`f (ω₁ · zc x) = (ω₂ · zc (x+α))^d` holds (`Omega.cross_orbit_shift_proof`).

This file treats the *self* case: if `ω` is good with shift `α` and `x ∈ F*` is such that
`bar (f (ω · zc x))` lies in the `KW`-orbit of `bar ω` itself, then the `KW`-conjugator can still
be chosen with the sharp shift `fval x + fval α`.

The proof identifies the self-set.  Write `m = orderOf fr.ζ` and let `β` be a root of
`X² + αX + 1` (`exists_beta`), so that `orderOf β = m` (`orderOf_beta_eq`).  The self-set

  `S = {y ∈ Q₀ : toAdd (bar (f (ω y))) ∈ orbE (toAdd (bar ω))}`

has exactly `m - 1` elements (`count_self_eq`, §2 (8)), while §2 (17) (`fcan_zU_eq_vSeq`) puts the
`m - 1` elements `zU i = zc (uSeq β i)`, `1 ≤ i ≤ m - 1`, inside `S` with the sharp shift
`vSeq (fval α) β i = uSeq β i + fval α`.  The `zU i` are pairwise distinct (`uSeq` is injective
below `orderOf β`, the lemma `uSeq_injective_lt_orderOf` proved here), so by counting they
exhaust `S`: there is `i` with `zcQF fr x = zU i`, and §2 (17) at that index is the desired
relation.

Everything here is hole-free; the two counting/positivity inputs are the sibling lemmas
`Omega.card_selfOrbitSet` and `Omega.zU_mem_selfOrbitSet`.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.Seq
import Submission.Work.PSU3.StageB.Omega.fcan_zU_eq_vSeq
import Submission.Work.PSU3.StageB.Omega.fcan_step10_gen
import Submission.Work.PSU3.StageB.Omega.count_self_eq
import Submission.Work.PSU3.StageB.Omega.exists_coset_zeta
import Submission.Work.PSU3.StageB.Omega.exists_beta
import Submission.Work.PSU3.StageB.Omega.orbE_card
import Submission.Work.PSU3.StageB.Omega.orderOf_beta_eq
import Submission.Work.PSU3.StageB.Omega.card_selfOrbitSet
import Submission.Work.PSU3.StageB.Omega.zU_mem_selfOrbitSet
import Submission.Work.PSU3.FineCoords.card_KW_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## Two elementary facts on the sequence `u_i = uSeq β i` -/

/-- `bS β k * β^k = β^(2k) + 1`. -/
lemma bS_mul_pow {β : E n} (hβ : β ≠ 0) (k : ℕ) :
    bS β k * β ^ k = β ^ (2 * k) + 1 := by
  have h2 : β ^ k * β ^ k = β ^ (2 * k) := by
    rw [← pow_two, ← pow_mul, mul_comm k 2]
  rw [bS, add_mul, inv_mul_cancel₀ (pow_ne_zero k hβ), h2]

/-- `u_i = uSeq β i = S_{i-1}/S_i` (`S_k = β^k + β^{-k}`) is injective below `orderOf β`:
`u_i = u_j` forces `(β^2+1)(β^{2(i-1)} + β^{2(j-1)}) = 0`, hence `β^{2(j-i)} = 1`, and the odd
order of `β` (an element of the unit group of a field of characteristic two) forces `i = j`. -/
lemma uSeq_injective_lt_orderOf {β : E n} (hβ : β ≠ 0) (hodd : Odd (orderOf β)) :
    ∀ {i j : ℕ}, 1 ≤ i → i < orderOf β → 1 ≤ j → j < orderOf β →
      uSeq β i = uSeq β j → i = j := by
  intro i j hi hio hj hjo heq
  have hbS : ∀ k, 1 ≤ k → k < orderOf β → bS β k ≠ 0 := by
    intro k hk1 hko
    rw [bS_ne_zero_iff β hβ k]
    intro hk
    have hdvd : orderOf β ∣ k := orderOf_dvd_iff_pow_eq_one.mpr hk
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hpow_ne : ∀ k, 1 ≤ k → k < orderOf β → β ^ k ≠ 1 := by
    intro k hk1 hko
    exact (bS_ne_zero_iff β hβ k).mp (hbS k hk1 hko)
  have hBi : β ^ (2 * i) + 1 ≠ 0 := by
    intro h
    have h1 : β ^ (2 * i) = 1 := by
      have h' := add_eq_zero_iff_eq_neg.mp h
      rwa [CharTwo.neg_eq] at h'
    have h2 : β ^ i * β ^ i = 1 := by
      rw [← pow_two, ← pow_mul, mul_comm i 2]
      exact h1
    exact hpow_ne i hi hio (eq_one_of_mul_self_eq_one h2)
  have hBj : β ^ (2 * j) + 1 ≠ 0 := by
    intro h
    have h1 : β ^ (2 * j) = 1 := by
      have h' := add_eq_zero_iff_eq_neg.mp h
      rwa [CharTwo.neg_eq] at h'
    have h2 : β ^ j * β ^ j = 1 := by
      rw [← pow_two, ← pow_mul, mul_comm j 2]
      exact h1
    exact hpow_ne j hj hjo (eq_one_of_mul_self_eq_one h2)
  -- cross-multiplied form
  have h' : bS β (i - 1) * bS β j = bS β (j - 1) * bS β i := by
    have hc : bS β (i - 1) / bS β i = bS β (j - 1) / bS β j := by
      rw [← uSeq_eq_div' β hβ hi, ← uSeq_eq_div' β hβ hj]
      exact heq
    exact (div_eq_div_iff (hbS i hi hio) (hbS j hj hjo)).mp hc
  -- the cleared form, after multiplying by `β^(i-1) * β^j = β^(j-1) * β^i`
  have hkey_pow : β ^ (i - 1) * β ^ j = β ^ (j - 1) * β ^ i := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h2 : (bS β (i - 1) * β ^ (i - 1)) * (bS β j * β ^ j)
      = (bS β (j - 1) * β ^ (j - 1)) * (bS β i * β ^ i) := by
    have e1 : (bS β (i - 1) * β ^ (i - 1)) * (bS β j * β ^ j)
        = (bS β (i - 1) * bS β j) * (β ^ (i - 1) * β ^ j) := by group
    have e2 : (bS β (j - 1) * β ^ (j - 1)) * (bS β i * β ^ i)
        = (bS β (j - 1) * bS β i) * (β ^ (j - 1) * β ^ i) := by group
    rw [e1, e2, hkey_pow, ← h']
  have hreg : (β ^ (2 * (i - 1)) + 1) * (β ^ (2 * j) + 1)
      = (β ^ (2 * (j - 1)) + 1) * (β ^ (2 * i) + 1) := by
    have e := h2
    rw [bS_mul_pow hβ (i - 1), bS_mul_pow hβ j, bS_mul_pow hβ (j - 1), bS_mul_pow hβ i] at e
    exact e
  have hx : β ^ (2 * i) = β ^ 2 * β ^ (2 * (i - 1)) := by
    rw [show 2 * i = 2 * (i - 1) + 2 by omega, pow_add]
    ring
  have hy : β ^ (2 * j) = β ^ 2 * β ^ (2 * (j - 1)) := by
    rw [show 2 * j = 2 * (j - 1) + 2 by omega, pow_add]
    ring
  have hreg2 : (β ^ (2 * (i - 1)) + 1) * (β ^ 2 * β ^ (2 * (j - 1)) + 1)
      = (β ^ (2 * (j - 1)) + 1) * (β ^ 2 * β ^ (2 * (i - 1)) + 1) := by
    rw [← hy, ← hx]
    exact hreg
  have key1 : (β ^ (2 * (i - 1)) + 1) * (β ^ 2 * β ^ (2 * (j - 1)) + 1)
      + (β ^ (2 * (j - 1)) + 1) * (β ^ 2 * β ^ (2 * (i - 1)) + 1) = 0 := by
    rw [hreg2]
    exact CharTwo.add_self_eq_zero _
  have heq2 : (β ^ (2 * (i - 1)) + 1) * (β ^ 2 * β ^ (2 * (j - 1)) + 1)
      + (β ^ (2 * (j - 1)) + 1) * (β ^ 2 * β ^ (2 * (i - 1)) + 1)
      = (β ^ 2 + 1) * (β ^ (2 * (i - 1)) + β ^ (2 * (j - 1))) := by
    have h2 : (2 : E n) = 0 := CharP.cast_eq_zero (E n) 2
    ring_nf
    simp [h2]
  have hkey : (β ^ 2 + 1) * (β ^ (2 * (i - 1)) + β ^ (2 * (j - 1))) = 0 := by
    rw [← heq2, key1]
  have hx1 : β ^ 2 + 1 ≠ 0 := by
    intro h
    have h1 : β ^ 2 = 1 := by
      have h' := add_eq_zero_iff_eq_neg.mp h
      rwa [CharTwo.neg_eq] at h'
    have h2 : β * β = 1 := by rw [← pow_two]; exact h1
    have h3 : β = 1 := eq_one_of_mul_self_eq_one h2
    have : orderOf β = 1 := by rw [h3]; exact orderOf_one
    omega
  have hAC : β ^ (2 * (i - 1)) = β ^ (2 * (j - 1)) := by
    rcases mul_eq_zero.mp hkey with h0 | h0
    · exact absurd h0 hx1
    · rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h0
      exact h0
  rcases le_total i j with hij | hji
  · have hba : 2 * (j - 1) = 2 * (i - 1) + 2 * (j - i) := by omega
    have h3 : β ^ (2 * (i - 1)) = β ^ (2 * (i - 1)) * β ^ (2 * (j - i)) := by
      rw [← pow_add, ← hba]
      exact hAC
    have h4 : β ^ (2 * (i - 1)) * 1 = β ^ (2 * (i - 1)) * β ^ (2 * (j - i)) := by
      rw [mul_one]; exact h3
    have h2 : β ^ (2 * (j - i)) = 1 := (mul_left_cancel₀ (pow_ne_zero _ hβ) h4).symm
    have hdvd : orderOf β ∣ 2 * (j - i) := orderOf_dvd_iff_pow_eq_one.mpr h2
    have hcop : (orderOf β).Coprime 2 := Nat.coprime_two_right.mpr hodd
    have hdvd2 : orderOf β ∣ (j - i) := hcop.dvd_of_dvd_mul_left hdvd
    have hzi : j - i = 0 := Nat.eq_zero_of_dvd_of_lt hdvd2 (by omega)
    omega
  · have hba : 2 * (i - 1) = 2 * (j - 1) + 2 * (i - j) := by omega
    have h3 : β ^ (2 * (j - 1)) = β ^ (2 * (j - 1)) * β ^ (2 * (i - j)) := by
      rw [← pow_add, ← hba]
      exact hAC.symm
    have h4 : β ^ (2 * (j - 1)) * 1 = β ^ (2 * (j - 1)) * β ^ (2 * (i - j)) := by
      rw [mul_one]; exact h3
    have h2 : β ^ (2 * (i - j)) = 1 := (mul_left_cancel₀ (pow_ne_zero _ hβ) h4).symm
    have hdvd : orderOf β ∣ 2 * (i - j) := orderOf_dvd_iff_pow_eq_one.mpr h2
    have hcop : (orderOf β).Coprime 2 := Nat.coprime_two_right.mpr hodd
    have hdvd2 : orderOf β ∣ (i - j) := hcop.dvd_of_dvd_mul_left hdvd
    have hzi : i - j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd2 (by omega)
    omega

/-! ## The self-orbit crux -/

theorem good_shift_of_mem_selfSet {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hωf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr) (ω * Work.PSU3.StageB.zcQF fr α))
    {x : ↥(Work.PSU3.StageB.FX n)}
    (hx : Multiplicative.toAdd
      (fr.bar (Work.PSU3.StageB.fcan hS.split (ω * Work.PSU3.StageB.zcQF fr x)))
      ∈ Work.PSU3.StageB.orbE fr (Multiplicative.toAdd (fr.bar ω))) :
    ∃ d : fr.KW, Work.PSU3.StageB.fcan hS.split (ω * Work.PSU3.StageB.zcQF fr x) =
      Work.PSU3.StageB.qconj hS.split ⟨(d : G), fr.KW_le d.2⟩
        (ω * Work.PSU3.StageB.zcQ fr
          (Work.PSU3.StageB.fval x + Work.PSU3.StageB.fval α)
          (by rw [map_add, x.2, α.2])) := by
  classical
  have hαfix : σE (fval α) = fval α := α.2
  have hα0 : fval α ≠ 0 := Units.ne_zero α.1
  -- a root `β` of `X² + αX + 1`, of order `orderOf fr.ζ`
  obtain ⟨β, hβ, hβα, hσ'⟩ := exists_beta (frame_one_le_n fr) (fval α) hαfix
  have hσ : σE β = β ∨ σE β = β⁻¹ := hσ'.symm
  have hordβ : orderOf β = orderOf fr.ζ := orderOf_beta_eq hS fr hω hωf hβ hβα
  have hm_dvd : orderOf fr.ζ ∣ Nat.card fr.KW := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_subgroup_dvd_card (Subgroup.zpowers fr.ζ)
  have hodd : Odd (orderOf β) := by
    rw [hordβ]
    exact (Work.PSU3.FineCoords.card_KW_odd fr).of_dvd_nat hm_dvd
  have hm1 : 1 ≤ orderOf fr.ζ := orderOf_pos fr.ζ
  -- the self-orbit set in `Q₀`
  set S : Set ↥Q := {y | (y : G) ∈ fr.Q0 ∧
      Multiplicative.toAdd (fr.bar (fcan hS.split (ω * y))) ∈ orbE fr (Multiplicative.toAdd (fr.bar ω))}
    with hSdef
  have hScard : Nat.card {y : ↥Q // y ∈ S} = orderOf fr.ζ - 1 := by
    rw [hSdef]
    exact card_selfOrbitSet hS fr hω
  have hmem : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 → zU fr β hβ hσ i ∈ S := by
    intro i hi hiN
    rw [hSdef]
    exact ⟨zU_mem_Q0 fr β hβ hσ i, zU_mem_selfOrbitSet hS fr hω hωf hβ hσ hβα i hi hiN⟩
  -- §2 (17) puts `orderOf fr.ζ - 1` *distinct* elements of `S` at our disposal
  set φ : Fin (orderOf fr.ζ - 1) → {y : ↥Q // y ∈ S} := fun k =>
    ⟨zU fr β hβ hσ (k.1 + 1), hmem (k.1 + 1) (by omega) (by omega)⟩ with hφdef
  have hφinj : Function.Injective φ := by
    intro k l hkl
    have h1 : zU fr β hβ hσ (k.1 + 1) = zU fr β hβ hσ (l.1 + 1) := congrArg Subtype.val hkl
    have h2 : fr.zc (uSeq β (k.1 + 1)) = fr.zc (uSeq β (l.1 + 1)) := by
      rw [← zU_coe fr β hβ hσ (k.1 + 1), ← zU_coe fr β hβ hσ (l.1 + 1), h1]
    have h3 : uSeq β (k.1 + 1) = uSeq β (l.1 + 1) :=
      fr.zc_inj _ _ (uSeq_fixed β hβ hσ _) (uSeq_fixed β hβ hσ _) h2
    have h4 : k.1 + 1 = l.1 + 1 :=
      uSeq_injective_lt_orderOf hβ hodd (by omega) (by have := k.2; omega)
        (by omega) (by have := l.2; omega) h3
    exact Fin.ext (by omega)
  have hφsurj : Function.Surjective φ :=
    ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hφinj, by rw [Nat.card_fin, hScard]⟩).2
  -- `zcQF fr x` lies in `S`, hence in the image of `φ`
  have hxS : zcQF fr x ∈ S := ⟨by rw [zcQF_coe]; exact fr.zc_mem _ x.2, hx⟩
  obtain ⟨k, hk⟩ := hφsurj ⟨zcQF fr x, hxS⟩
  have hzU : zU fr β hβ hσ (k.1 + 1) = zcQF fr x := congrArg Subtype.val hk
  have hfv : uSeq β (k.1 + 1) = fval x := by
    have h2 : fr.zc (uSeq β (k.1 + 1)) = fr.zc (fval x) := by
      rw [← zU_coe fr β hβ hσ (k.1 + 1), hzU, zcQF_coe]
    exact fr.zc_inj _ _ (uSeq_fixed β hβ hσ _) x.2 h2
  -- §2 (17) at the index `k`
  have hbS : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 → bS β i ≠ 0 := by
    intro i hi hiN
    rw [bS_ne_zero_iff β hβ i]
    intro hbi
    have hdvd : orderOf fr.ζ ∣ i := by
      rw [← hordβ]
      exact orderOf_dvd_iff_pow_eq_one.mpr hbi
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  set lam : ℕ → ↥(FX n) := lamSeq (fval α) β hαfix hσ with hlamdef
  have hlamm : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 → fval (lam i) = wSeq (fval α) β i := by
    intro i hi hiN
    exact fval_lamSeq (fval α) β hαfix hσ
      (wSeq_ne_zero (fval α) β hα0 i (hbS i hi hiN))
  have hsharp := fcan_zU_eq_vSeq hS fr hω hωf hβ hσ hβα lam hlamm hbS (k.1 + 1)
    (by omega) (by have := k.2; omega)
  refine ⟨dSeq hS fr lam (k.1 + 1), ?_⟩
  have hv1 : σE (vSeq (fval α) β (k.1 + 1)) = vSeq (fval α) β (k.1 + 1) := by
    rw [vSeq, map_add, uSeq_fixed β hβ hσ (k.1 + 1), hαfix]
  have hz : zcQ fr (vSeq (fval α) β (k.1 + 1)) hv1
      = zcQ fr (fval x + fval α) (by rw [map_add, x.2, α.2]) := by
    apply Subtype.ext
    rw [zcQ_coe, zcQ_coe, vSeq, hfv]
  rw [← hzU, hsharp]
  congr 1
  exact congrArg (fun z => ω * z) hz

end Work.PSU3.StageB.Omega
