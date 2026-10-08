import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.mem_AU_iff
import Submission.Work.Tame.inConjAU_iff
import Submission.Work.Tame.punct_subset_conjAU
import Submission.Work.Tame.alphaI2_apply_eq_zero_of_not_inConjAU
import Submission.Work.Tame.mul_mem_conjAU_of_commute
import Submission.Work.Tame.coprime_card_orderOf_projEC
import Submission.Work.GroupTheory.conj_mul_centralizer_of_sup_zpowers

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open Classical
open scoped Pointwise

namespace Work.Tame

universe u

variable {X : Type u}

/-! ## Support of an induced function

An induced function vanishes at `x` when no conjugate of `x` lies in the support of the function
being induced.  This is the only general fact about `Induction.indFun` needed below. -/

/-- **Support of an induced function.**  If no conjugate of `g` lies in the support of the
function `φ` on the subgroup `H`, then `Ind_H^G φ g = 0`. -/
theorem indFun_apply_eq_zero_of_support {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    (φ : ↥H → ℂ) (g : G) (h : ∀ y : ↥H, φ y ≠ 0 → ¬ IsConj g (y : G)) :
    Induction.indFun H φ g = 0 := by
  rw [Induction.indFun_apply_def, mul_eq_zero]
  right
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x * g * x⁻¹ ∈ H
  · rw [dif_pos hx]
    by_contra hne
    exact h ⟨x * g * x⁻¹, hx⟩ hne (isConj_iff.mpr ⟨x, rfl⟩)
  · rw [dif_neg hx]

section Group

variable [Group X] [Fintype X]

/-! ## Wielandt's product theorem inside `𝔑_i`

Feit–Thompson p. 805: "if `N ∈ 𝔑_i` then ... every element of `𝔑_i` is conjugate to an element of
the form `HL = LH` with `L ∈ 𝔏 ∩ 𝔑_i`, `H ∈ 𝔎_i`".  The group-theoretic input is
`Work.GroupTheory.conj_mul_centralizer_of_sup_zpowers` (Wielandt, `[28] p. 162`), applied inside the
subgroup `𝔎_i ⊔ ⟨π(N)⟩ = 𝔎_i⟨N⟩` of `𝔑_i`. -/

/-- **Wielandt's product theorem inside `𝔑_i`.**  For `N ∈ 𝔑_i` with `𝔎_i`-free part
`M = projEC Lhat (Hs i) N`, there are `a' ∈ 𝔎_i` commuting with `M` and `g ∈ X` with
`g * N * g⁻¹ = a' * M`. -/
theorem exists_conj_mul_projEC_aux {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hD : (Dset Lhat).Nonempty) (i : Fin n)
    (N : ↥(Lgrp (Hs i : Set X))) :
    ∃ (a' : X) (g : X),
      a' ∈ Hs i ∧
      a' * ((projEC Lhat (Hs i) N : ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X))) : X) =
        ((projEC Lhat (Hs i) N : ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X))) : X) * a' ∧
      g * (N : X) * g⁻¹ = a' * ((projEC Lhat (Hs i) N :
        ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X))) : X) := by
  set M : ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) := projEC Lhat (Hs i) N with hM
  have hsup : Lgrp (Hs i : Set X) = Hs i ⊔ (Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) :=
    h.supp_prod hD i
  have hHM : (N : X) * ((M : X))⁻¹ ∈ Hs i := by
    have h1 := mul_projEC_inv_mem hsup N
    rwa [← hM] at h1
  -- the subgroup `G₀ = 𝔎_i⟨N⟩ = 𝔎_i ⊔ ⟨M⟩`
  set G0 : Subgroup X := Hs i ⊔ Subgroup.zpowers (M : X) with hG0
  have hHs_le_G0 : Hs i ≤ G0 := by rw [hG0]; exact le_sup_left
  have hzp_le_G0 : Subgroup.zpowers (M : X) ≤ G0 := by rw [hG0]; exact le_sup_right
  have hG0_le_N : G0 ≤ Lgrp (Hs i : Set X) := by
    rw [hG0]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr M.2.2)
  have hM_G0 : (M : X) ∈ G0 := hzp_le_G0 (Subgroup.mem_zpowers (M : X))
  have hH_G0 : (N : X) * ((M : X))⁻¹ ∈ G0 := hHs_le_G0 hHM
  set b : ↥G0 := ⟨(M : X), hM_G0⟩ with hb
  have hbval : (b : X) = (M : X) := rfl
  set a : ↥((Hs i).subgroupOf G0) := ⟨⟨(N : X) * ((M : X))⁻¹, hH_G0⟩, hHM⟩ with ha
  have haval : ((a : ↥G0) : X) = (N : X) * ((M : X))⁻¹ := rfl
  haveI hnorm : ((Hs i).subgroupOf G0).Normal :=
    Subgroup.Normal.mk fun x hx y => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hG0_le_N y.2) (x : X)).mp hx
  have hcard : Nat.card ↥((Hs i).subgroupOf G0) = Nat.card ↥(Hs i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHs_le_G0).toEquiv
  have hcop : (Nat.card ↥((Hs i).subgroupOf G0)).Coprime (orderOf b) := by
    rw [hcard]
    rw [show orderOf b = orderOf ((M : X)) from (Subgroup.orderOf_coe b).symm]
    exact coprime_card_orderOf_projEC h hD i N
  have hztop : Subgroup.zpowers b = (Subgroup.zpowers (M : X)).subgroupOf G0 := by
    ext x
    rw [Subgroup.mem_zpowers_iff, Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg (fun t : ↥G0 => (t : X)) hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have htop : (Hs i).subgroupOf G0 ⊔ Subgroup.zpowers b = ⊤ := by
    rw [hztop, ← Subgroup.subgroupOf_sup hHs_le_G0 hzp_le_G0, ← hG0]
    exact Subgroup.subgroupOf_self G0
  obtain ⟨a', g, hcomm, hconj⟩ :=
    Work.GroupTheory.conj_mul_centralizer_of_sup_zpowers (G := ↥G0)
      (A := (Hs i).subgroupOf G0) (b := b) hcop htop a
  refine ⟨((a' : ↥G0) : X), ((g : ↥G0) : X), Subgroup.mem_subgroupOf.mp a'.2, ?_, ?_⟩
  · have h1 := congrArg (fun t : ↥G0 => (t : X)) hcomm
    simp only [Subgroup.coe_mul] at h1
    rwa [hbval] at h1
  · have h1 := congrArg (fun t : ↥G0 => (t : X)) hconj
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [haval, hbval] at h1
    have h2 : (g : X) * (N : X) * (g : X)⁻¹ = (a' : X) * (M : X) := by
      have h3 : ((N : X) * ((M : X))⁻¹) * (M : X) = (N : X) := by group
      rw [h3] at h1
      exact h1
    exact h2

/-! ## The two summands of (9.4) at an element outside the support -/

/-- **Feit–Thompson Lemma 9.1, first summand.**  For `N ∈ 𝔑_i` not conjugate to any element of
`AU`, the first summand `α_{i1}(N) = α(π(N))` of (9.4) vanishes. -/
theorem alphaI1_eq_zero_of_not_inConjAU {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs) {α : ↥(Lgrp Lhat) → ℂ}
    (hα : α ∈ C0 Lhat) {i : Fin n} {N : ↥(Lgrp (Hs i : Set X))}
    (hN : ¬ inConjAU Lhat n Hs (N : X)) : alphaI1LM Lhat (Hs i) α N = 0 := by
  have hDne : (Dset Lhat).Nonempty := by
    rcases hD with h' | h0
    · exact h'
    · exact absurd h0 (by have := i.isLt; omega)
  set M : ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) := projEC Lhat (Hs i) N with hM
  rw [alphaI1LM_apply, ← hM]
  by_cases hαM : α (Subgroup.inclusion inf_le_left M) = 0
  · exact hαM
  · exfalso
    have hMmem : (M : X) ∈ Lhat := by
      by_contra hc
      exact hαM (hα.2.1 (Subgroup.inclusion inf_le_left M) (by simpa using hc))
    have hMne : (M : X) ≠ 1 := by
      intro hc
      have h1 : (Subgroup.inclusion inf_le_left M : ↥(Lgrp Lhat)) = 1 :=
        Subtype.ext (by simpa using hc)
      exact hαM (by rw [h1]; exact hα.2.2)
    obtain ⟨a', g, ha', hcomm, hconj⟩ := exists_conj_mul_projEC_aux h hDne i N
    rw [← hM] at hcomm hconj
    rcases eq_or_ne a' 1 with ha'1 | ha'ne
    · rw [ha'1, one_mul] at hconj
      obtain ⟨a₀, ha₀, hconj₀⟩ := punct_subset_conjAU h hMmem hMne
      exact hN ((inConjAU_iff h).mpr ⟨a₀, ha₀, (isConj_iff.mpr ⟨g, hconj⟩).trans hconj₀⟩)
    · obtain ⟨a₀, ha₀, hconj₀⟩ :=
        mul_mem_conjAU_of_commute h hDne ha' ha'ne hMmem hMne M.2 hcomm
      exact hN ((inConjAU_iff h).mpr ⟨a₀, ha₀, (isConj_iff.mpr ⟨g, hconj⟩).trans hconj₀⟩)

/-- **Feit–Thompson Lemma 9.1, second summand.**  For `N ∈ 𝔑_i` not conjugate to any element of
`AU`, the second summand `α_{i2}(N) = Ind_{𝔏 ∩ 𝔑_i}^{𝔑_i}(α|_{𝔏 ∩ 𝔑_i})(N)` of (9.4) vanishes. -/
theorem alphaI2_eq_zero_of_not_inConjAU {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) (i : Fin n)
    {N : ↥(Lgrp (Hs i : Set X))} (hN : ¬ inConjAU Lhat n Hs (N : X)) :
    alphaI2LM Lhat (Hs i) α N = 0 :=
  alphaI2_apply_eq_zero_of_not_inConjAU h hα i hN

/-- The difference `(α_{i1} - α_{i2})` of (9.4) vanishes at any element of `𝔑_i` which is not
conjugate to an element of `AU`. -/
theorem beta_eq_zero_of_not_inConjAU {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs) {α : ↥(Lgrp Lhat) → ℂ}
    (hα : α ∈ C0 Lhat) (i : Fin n) {N : ↥(Lgrp (Hs i : Set X))}
    (hN : ¬ inConjAU Lhat n Hs (N : X)) :
    alphaI1LM Lhat (Hs i) α N - alphaI2LM Lhat (Hs i) α N = 0 := by
  rw [alphaI1_eq_zero_of_not_inConjAU h hD hα hN,
    alphaI2_eq_zero_of_not_inConjAU h hα i hN, sub_zero]

/-- **Feit–Thompson Lemma 9.1, vanishing part** (p. 805).  If `x ∈ X` is not conjugate to any
element of `𝔄_L` for any `L ∈ ⋃_{i=0}^n 𝔏_i` — i.e. `¬ inConjAU Lhat n Hs x` — then
`α^τ(x) = 0` for every `α ∈ 𝓒₀(L̂)`.

The hypothesis `HasTameData Lhat n Hs` is the normalisation of Definition 9.1 explained in
`Submission/Work/Tame/NOTES.md` §1: either `𝔇 ≠ ∅`, so that the supporting subgroups and the
properties (ii)(a)–(e) exist and Feit–Thompson's argument via the decomposition of elements of
`𝔑_i` as `HL` and the T. I. set property of `Ñ_i` applies, or `n = 0`, in which case `τ` is just
induction from `𝔏` and the claim is the Brauer–Suzuki statement that `Ind_𝔏^X α` vanishes off the
conjugates of `L̂` (a T. I. set by `isTISet_of_Dset_eq_empty`). -/
theorem tau_eq_zero_of_not_isConj {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) {x : X} (hx : ¬ inConjAU Lhat n Hs x) :
    tau Lhat n Hs α x = 0 := by
  classical
  rw [tau_apply]
  -- the term `α^* = Ind_𝔏^X α`
  have hL : Induction.indFun (Lgrp Lhat) α x = 0 := by
    apply indFun_apply_eq_zero_of_support
    intro y hy hconj
    have hyL : (y : X) ∈ Lhat := by
      by_contra hc
      exact hy (hα.2.1 y hc)
    have hy1 : (y : X) ≠ 1 := by
      intro hc
      exact hy (by
        rw [show y = (1 : ↥(Lgrp Lhat)) from Subtype.ext (by simpa using hc)]
        exact hα.2.2)
    obtain ⟨a, ha, hconj'⟩ := punct_subset_conjAU h hyL hy1
    exact hx ((inConjAU_iff h).mpr ⟨a, ha, hconj.trans hconj'⟩)
  -- the terms `(α_{i1} - α_{i2})^*`
  have hN : ∀ i : Fin n, Induction.indFun (Lgrp (Hs i : Set X))
      (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α) x = 0 := by
    intro i
    apply indFun_apply_eq_zero_of_support
    intro y hy hconj
    have hy_not : ¬ inConjAU Lhat n Hs (y : X) := by
      intro hc
      obtain ⟨a, ha, hconja⟩ := (inConjAU_iff h).mp hc
      exact hx ((inConjAU_iff h).mpr ⟨a, ha, hconj.trans hconja⟩)
    exact hy (beta_eq_zero_of_not_inConjAU h hD hα i hy_not)
  rw [hL, zero_add]
  exact Finset.sum_eq_zero fun i _ => hN i

end Group

end Work.Tame
