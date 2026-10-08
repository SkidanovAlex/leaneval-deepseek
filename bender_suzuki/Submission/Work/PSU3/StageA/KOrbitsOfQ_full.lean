import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.GoodRepsDef
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.prop1c
import Submission.Work.ThmF.ChV12.L6basic
import Submission.Work.ZassenhausSuzuki.szA_of_isSuzukiTwoGroup
import Submission.Work.PSU3.StageA.caseC_not_suzuki_card_q2_b
import Submission.Work.PSU3.StageA.caseB_canon_data_rrk
import Submission.Work.PSU3.StageA.caseB_Ksub_action_coords
import Submission.Work.PSU3.StageA.Ksub_cyclic_caseB
import Submission.Work.PSU3.StageA.false_of_commuting_involutions
import Submission.Work.PSU3.StageA.caseB_GoodReps_ncard
import Submission.Work.PSU3.StageA.caseB_GoodReps_mem_Q0sub_iff
import Submission.Work.PSU3.StageA.caseB_orbits_conj_core_clean

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.KOrbitsOfQ_full`

Peterfalvi II, Ch. VI §2 (`H = Q ⋊ D` split rank-one data with `t` an involution outside
`H`, `s ∈ Q` an involution, `r ∈ Q` with the structure identity `t s t = r⁻¹ t r`, `K = J(D,t)`):
in case b) of Ch. VI §1 (`Q` non-abelian of order `|Q₀|²`, `orderOf (s*t) = 5`, `W = C_V(K) = ⊥`,
`K = J(D,t)` a subgroup) every `x ∈ Q#` is `K`-conjugate to one of the representatives

`s, r, r⁻¹, r·r^{-k} = r·(k⁻¹ r⁻¹ k)` (`1 ≠ k ∈ Kset`).

## Structure of the proof

The representatives above form the set `GoodReps H t s r`.  Two external ingredients give the
statement (both are Ch. VI §2 of the source, p. 261–262):

* **`caseB_GoodReps_ncard`**: `|GoodReps| = |Q₀sub H| + 1` (the source's count `q + 1 = |K#| + 3`);
* **`caseB_GoodReps_separated`**: no two distinct elements of `GoodReps` are `K`-conjugate
  (the source's computation (5)–(7), using `caseB_canon_data_rrk` for the canonical form of
  `r r^{-k}`, `caseB_Ksub_action_coords` for the `𝔽_q`-coordinates of `K = J(D,t)`, and
  `false_of_commuting_involutions` for the exceptional case).

Given them, the argument is the counting of the source:

* `Kset H t` acts **freely** on `Q#` (Ch. V §2, `Work.ThmF.ChV12.prop1a`), so every `K`-orbit on
  `Q#` has `|Kset| = |Q₀| - 1` elements;
* the map `(g,k) ↦ k⁻¹ g k : GoodReps × Kset → Q#` is **injective**: `k₁⁻¹g₁k₁ = k₂⁻¹g₂k₂`
  makes `g₁` and `g₂` `K`-conjugate, so `g₁ = g₂` (separatedness), and then `k₁ = k₂` by freeness;
* both sides have `(q+1)(q-1) = q² - 1 = |Q#|` elements, so the map is surjective — which is the
  statement.

This file proves the counting core `KOrbitsOfQ_of_sep` and the elementary facts it rests on.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}

/-! ## Elementary facts about `Q₀sub` and `Kset` -/

/-- `Q₀sub H = ⟨Inv H⟩` consists of `1` and the involutions of `H` (Ch. V §1 Prop. 1 (c)). -/
theorem Q0sub_eq_involutions_union (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    (Work.ThmF.Q0sub H : Set G) = Submission.Blueprint.involutions (H : Set G) ∪ {1} := by
  classical
  have hcomm := Work.ThmF.L5.involutions_commute hS.situation hC4 hS.split
  obtain ⟨-, -, -, h4⟩ := Work.ThmF.ChV12.Q0sub_elementary H hcomm
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · by_cases h1 : x = 1
    · exact Or.inr (Set.mem_singleton_iff.mpr h1)
    · exact Or.inl (h4 x hx h1)
  · rcases hx with hx | hx
    · exact Work.ThmF.Q0_le_Q0sub H (Work.ThmF.mem_Q0_iff.mpr (Or.inl hx))
    · rw [Set.mem_singleton_iff.mp hx]; exact (Work.ThmF.Q0sub H).one_mem

/-- `|Kset H t| = |Q₀sub H| - 1`. -/
theorem ncard_Kset_eq (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    (Work.ThmF.Kset H t).ncard = Nat.card (Work.ThmF.Q0sub H) - 1 := by
  classical
  have hcard := Work.ThmF.Bender.cardKsetEqInv hS.split.stronglyEmbedded hS.split.invol
    hS.split.not_mem
  have hset := Q0sub_eq_involutions_union hS hC4
  have h1notin : (1 : G) ∉ Submission.Blueprint.involutions (H : Set G) := by
    rintro ⟨-, h⟩
    exact absurd h (by norm_num)
  have hncard : ((Work.ThmF.Q0sub H : Set G)).ncard
      = (Submission.Blueprint.involutions (H : Set G)).ncard + 1 := by
    rw [hset, Set.union_singleton, Set.ncard_insert_of_notMem h1notin (Set.toFinite _)]
  have hcoe : ((Work.ThmF.Q0sub H : Set G)).ncard = Nat.card (Work.ThmF.Q0sub H) :=
    (Nat.card_coe_set_eq (Work.ThmF.Q0sub H : Set G)).symm
  rw [hcard]
  omega

/-- `Kset H t` is closed under inverses (its carrier is the subgroup `Ksub`, via `hKsub`). -/
theorem Kset_inv_mem (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    {k : G} (hk : k ∈ Work.ThmF.Kset H t) : k⁻¹ ∈ Work.ThmF.Kset H t := by
  have h : k ∈ (Work.ThmF.Ksub H t : Set G) := by rw [hKsub]; exact hk
  have h' : k⁻¹ ∈ (Work.ThmF.Ksub H t : Set G) := (Work.ThmF.Ksub H t).inv_mem h
  rwa [hKsub] at h'

/-- `Kset H t` is closed under multiplication (via `hKsub`). -/
theorem Kset_mul_mem (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    {k j : G} (hk : k ∈ Work.ThmF.Kset H t) (hj : j ∈ Work.ThmF.Kset H t) :
    k * j ∈ Work.ThmF.Kset H t := by
  have h1 : k ∈ (Work.ThmF.Ksub H t : Set G) := by rw [hKsub]; exact hk
  have h2 : j ∈ (Work.ThmF.Ksub H t : Set G) := by rw [hKsub]; exact hj
  have h3 : k * j ∈ (Work.ThmF.Ksub H t : Set G) := (Work.ThmF.Ksub H t).mul_mem h1 h2
  rwa [hKsub] at h3

/-- Every element of `Kset H t` normalises `Q`. -/
theorem Kset_normalizes_Q (hS : Work.PSU3.PSU3Hyp H Q t) {k : G}
    (hk : k ∈ Work.ThmF.Kset H t) : k ∈ Subgroup.normalizer (Q : Set G) :=
  hS.split.normal (Work.RankOneUniqueness.twoPoint_le_left H t
    (Work.ThmF.Kset_subset H t hk))

/-- The conjugate of `x ∈ Q` by `k ∈ Kset` lies in `Q`. -/
theorem Kset_conj_mem_Q (hS : Work.PSU3.PSU3Hyp H Q t) {k : G}
    (hk : k ∈ Work.ThmF.Kset H t) {x : G} (hx : x ∈ Q) : k⁻¹ * x * k ∈ Q := by
  have h := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q : Set G)).inv_mem
    (Kset_normalizes_Q hS hk)) x).mp hx
  simpa using h

/-- `Kset H t` acts freely on `Q#`: an element of `Kset` commuting with `1 ≠ x ∈ Q` is `1`
(Ch. V §2). -/
theorem Kset_free_on_Q (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) {k : G} (hk : k ∈ Work.ThmF.Kset H t)
    (hk1 : k ≠ 1) {x : G} (hx : x ∈ Q) (hconj : k⁻¹ * x * k = x) : x = 1 := by
  refine Work.ThmF.ChV12.prop1a hS.situation hC4 H Q t hS.split k hk hk1 x hx ?_
  have h := congrArg (fun z : G => k * z) hconj
  simpa [mul_assoc] using h

/-- `r ≠ 1`: if `r = 1` the structure identity gives `s * t = 1`, whence `s = t ∉ H`. -/
theorem r_ne_one_of_hsr (hS : Work.PSU3.PSU3Hyp H Q t) (hs : s ∈ Q)
    (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r) : r ≠ 1 := by
  rintro rfl
  have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hS.split
  have h1 : t * s * t = t := by simpa using hsr
  have h2 : s * t = 1 := by
    have h1' : t * (t * s * t) = 1 := by rw [h1, ht2]
    have key : t * (t * s * t) = s * t := by
      rw [show t * (t * s * t) = (t * t) * (s * t) from by group, ht2, one_mul]
    rwa [key] at h1'
  have hs_eq_t : s = t := by
    calc s = s * t * t := by rw [mul_assoc, ht2, mul_one]
      _ = 1 * t := by rw [h2]
      _ = t := one_mul t
  exact hS.split.not_mem (hs_eq_t ▸ hS.split.le hs)

/-! ## The counting argument -/

/-- **The counting core.**  If the representatives `GoodReps H t s r` are pairwise non-`K`-conjugate
and there are `|Q₀sub H| + 1` of them, then every `x ∈ Q#` is `K`-conjugate to one of them. -/
theorem KOrbitsOfQ_of_sep (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (h5 : orderOf (s * t) = 5)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 2)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    (hsep : ∀ g₁ ∈ GoodReps H t s r, ∀ g₂ ∈ GoodReps H t s r, g₁ ≠ g₂ →
      ¬ ∃ k ∈ Work.ThmF.Kset H t, k⁻¹ * g₁ * k = g₂)
    (hGood : (GoodReps H t s r).ncard = Nat.card (Work.ThmF.Q0sub H) + 1) :
    ∀ x ∈ Q, x ≠ 1 → ∃ k ∈ Work.ThmF.Kset H t, k⁻¹ * x * k ∈ GoodReps H t s r := by
  classical
  set q : ℕ := Nat.card (Work.ThmF.Q0sub H) with hq
  have hr1 : r ≠ 1 := r_ne_one_of_hsr hS hs hr hsr
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  -- ## GoodReps lies in `Q#`
  have hGRQ : ∀ g ∈ GoodReps H t s r, g ∈ Q := by
    intro g hg
    rcases hg with hg | ⟨k, hk, hk1, rfl⟩
    · rcases Set.mem_insert_iff.mp hg with h1 | h1
      · rw [Set.mem_singleton_iff.mp h1]; exact hs
      · rcases Set.mem_insert_iff.mp h1 with h2 | h2
        · rw [Set.mem_singleton_iff.mp h2]; exact hr
        · rw [Set.mem_singleton_iff.mp h2]; exact Q.inv_mem hr
    · exact Q.mul_mem hr (Kset_conj_mem_Q hS hk (Q.inv_mem hr))
  have hGR1 : ∀ g ∈ GoodReps H t s r, g ≠ 1 := by
    intro g hg
    rcases hg with hg | ⟨k, hk, hk1, rfl⟩
    · rcases Set.mem_insert_iff.mp hg with h1 | h1
      · rw [Set.mem_singleton_iff.mp h1]; exact hs1
      · rcases Set.mem_insert_iff.mp h1 with h2 | h2
        · rw [Set.mem_singleton_iff.mp h2]; exact hr1
        · rw [Set.mem_singleton_iff.mp h2]
          exact fun h => hr1 (inv_eq_one.mp (by simpa using h.symm))
    · intro hcon
      -- `r * (k⁻¹ r⁻¹ k) = 1` gives `k⁻¹ r k = r`, so `k` commutes with `r`
      have h2 : k⁻¹ * r⁻¹ * k = r⁻¹ := by
        have h := congrArg (fun z : G => r⁻¹ * z) hcon
        rw [mul_one] at h
        rwa [show r⁻¹ * (r * (k⁻¹ * r⁻¹ * k)) = k⁻¹ * r⁻¹ * k from by group] at h
      have hrk : k⁻¹ * r * k = r := by
        have h3 : (k⁻¹ * r⁻¹ * k)⁻¹ = r := by rw [h2, inv_inv]
        have h4 : (k⁻¹ * r⁻¹ * k)⁻¹ = k⁻¹ * r * k := by group
        rw [h4] at h3
        exact h3
      exact hr1 (Kset_free_on_Q hS hC4 hk hk1 hr hrk)
  -- ## injectivity of `(g,k) ↦ k⁻¹ g k`
  have hinj : ∀ g₁ ∈ GoodReps H t s r, ∀ g₂ ∈ GoodReps H t s r,
      ∀ k₁ ∈ Work.ThmF.Kset H t, ∀ k₂ ∈ Work.ThmF.Kset H t,
      k₁⁻¹ * g₁ * k₁ = k₂⁻¹ * g₂ * k₂ → g₁ = g₂ ∧ k₁ = k₂ := by
    intro g₁ hg₁ g₂ hg₂ k₁ hk₁ k₂ hk₂ heq
    have hk : k₁ * k₂⁻¹ ∈ Work.ThmF.Kset H t :=
      Kset_mul_mem hKsub hk₁ (Kset_inv_mem hKsub hk₂)
    have hconj : (k₁ * k₂⁻¹)⁻¹ * g₁ * (k₁ * k₂⁻¹) = g₂ := by
      have h := congrArg (fun z : G => k₂ * z * k₂⁻¹) heq
      have h2 : k₂ * (k₁⁻¹ * g₁ * k₁) * k₂⁻¹ = g₂ := by simpa [mul_assoc] using h
      calc (k₁ * k₂⁻¹)⁻¹ * g₁ * (k₁ * k₂⁻¹)
          = k₂ * (k₁⁻¹ * g₁ * k₁) * k₂⁻¹ := by group
        _ = g₂ := h2
    have hg12 : g₁ = g₂ := by
      by_contra hne
      exact hsep g₁ hg₁ g₂ hg₂ hne ⟨k₁ * k₂⁻¹, hk, hconj⟩
    subst hg12
    have hk21 : k₂ * k₁⁻¹ ∈ Work.ThmF.Kset H t :=
      Kset_mul_mem hKsub hk₂ (Kset_inv_mem hKsub hk₁)
    have hcomm : g₁ * (k₁ * k₂⁻¹) = (k₁ * k₂⁻¹) * g₁ := by
      have h := congrArg (fun z : G => k₁ * z) heq
      have h1 : g₁ * k₁ = k₁ * k₂⁻¹ * g₁ * k₂ := by
        simpa [mul_assoc] using h
      calc g₁ * (k₁ * k₂⁻¹) = (g₁ * k₁) * k₂⁻¹ := by group
        _ = (k₁ * k₂⁻¹ * g₁ * k₂) * k₂⁻¹ := by rw [h1]
        _ = (k₁ * k₂⁻¹) * g₁ := by group
    have hfix : (k₂ * k₁⁻¹)⁻¹ * g₁ * (k₂ * k₁⁻¹) = g₁ := by
      calc (k₂ * k₁⁻¹)⁻¹ * g₁ * (k₂ * k₁⁻¹)
          = (k₁ * k₂⁻¹) * g₁ * (k₂ * k₁⁻¹) := by
            rw [show (k₂ * k₁⁻¹)⁻¹ = k₁ * k₂⁻¹ from by group]
        _ = ((k₁ * k₂⁻¹) * g₁) * (k₂ * k₁⁻¹) := by group
        _ = ((g₁ * (k₁ * k₂⁻¹))) * (k₂ * k₁⁻¹) := by rw [hcomm]
        _ = g₁ := by group
    have h1 : k₂ * k₁⁻¹ = 1 := by
      by_contra hne
      exact hGR1 g₁ hg₁ (Kset_free_on_Q hS hC4 hk21 hne (hGRQ g₁ hg₁) hfix)
    have hk12 : k₁ = k₂ := by
      have h2 : k₂ = k₁ := by
        calc k₂ = (k₂ * k₁⁻¹) * k₁ := by group
          _ = 1 * k₁ := by rw [h1]
          _ = k₁ := one_mul k₁
      exact h2.symm
    exact ⟨rfl, hk12⟩
  -- ## cardinalities
  have hKcard : (Work.ThmF.Kset H t).ncard = q - 1 := by
    rw [ncard_Kset_eq hS hC4, hq]
  have h1q : 1 ≤ q := by
    haveI : Nonempty ↥(Work.ThmF.Q0sub H) := ⟨⟨1, (Work.ThmF.Q0sub H).one_mem⟩⟩
    have hpos : 0 < Nat.card ↥(Work.ThmF.Q0sub H) := Nat.card_pos
    rw [hq]; omega
  have hdom : Nat.card (↥(GoodReps H t s r) × ↥(Work.ThmF.Kset H t)) = q ^ 2 - 1 := by
    rw [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_coe_set_eq, hGood, hKcard]
    have h2 : (1 : ℕ) ≤ q ^ 2 := by have := pow_pos (by omega : 0 < q) 2; omega
    have h1 : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
    have h3 : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := by
      rw [Nat.cast_sub h2, Nat.cast_pow]
      norm_num
    have hcast : ((q + 1) * (q - 1) : ℤ) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      rw [h3]
      push_cast [h1]
      ring
    exact_mod_cast hcast
  have hcod : Nat.card ↥{y : G | y ∈ Q ∧ y ≠ 1} = q ^ 2 - 1 := by
    have hset : ({y : G | y ∈ Q ∧ y ≠ 1} : Set G) = (Q : Set G) \ {1} := by
      ext y; simp
    have h1 : ((Q : Set G) \ {1}).ncard = (Q : Set G).ncard - 1 :=
      Set.ncard_sdiff_singleton_of_mem Q.one_mem
    have h2 : (Q : Set G).ncard = Nat.card ↥Q := Nat.card_coe_set_eq _
    rw [Nat.card_coe_set_eq, hset, h1, h2, hcard]
  have hcard_eq : Nat.card (↥(GoodReps H t s r) × ↥(Work.ThmF.Kset H t))
      = Nat.card ↥{y : G | y ∈ Q ∧ y ≠ 1} := by rw [hdom, hcod]
  -- ## conclusion
  intro x hx hx1
  by_contra hcon
  push_neg at hcon
  have hmaps : ∀ p : ↥(GoodReps H t s r) × ↥(Work.ThmF.Kset H t),
      ((p.2 : G))⁻¹ * (p.1 : G) * (p.2 : G) ∈ ({z : G | z ∈ Q ∧ z ≠ 1} : Set G) := by
    intro p
    refine ⟨Kset_conj_mem_Q hS p.2.2 (hGRQ p.1 p.1.2), ?_⟩
    intro h1
    exact hGR1 p.1 p.1.2 (by
      have h := congrArg (fun z : G => (p.2 : G) * z * (p.2 : G)⁻¹) h1
      simpa [mul_assoc] using h)
  let F : ↥(GoodReps H t s r) × ↥(Work.ThmF.Kset H t) → ↥{z : G | z ∈ Q ∧ z ≠ 1} :=
    fun p => ⟨(p.2 : G)⁻¹ * (p.1 : G) * (p.2 : G), hmaps p⟩
  have hfinj : Function.Injective F := by
    rintro ⟨g₁, k₁⟩ ⟨g₂, k₂⟩ hEq
    have hval : (k₁ : G)⁻¹ * (g₁ : G) * (k₁ : G) = (k₂ : G)⁻¹ * (g₂ : G) * (k₂ : G) :=
      congrArg Subtype.val hEq
    obtain ⟨h1, h2⟩ := hinj g₁ g₁.2 g₂ g₂.2 k₁ k₁.2 k₂ k₂.2 hval
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hxnot : (⟨x, hx, hx1⟩ : ↥{z : G | z ∈ Q ∧ z ≠ 1}) ∉ Set.range F := by
    rintro ⟨p, hp⟩
    have hval : (p.2 : G)⁻¹ * (p.1 : G) * (p.2 : G) = x := congrArg Subtype.val hp
    have hmem : ((p.2 : G)⁻¹)⁻¹ * x * (p.2 : G)⁻¹ ∈ GoodReps H t s r := by
      have hred : ((p.2 : G)⁻¹)⁻¹ * ((p.2 : G)⁻¹ * (p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹
          = (p.1 : G) := by group
      rw [← hval, hred]
      exact p.1.2
    exact hcon ((p.2 : G)⁻¹) (Kset_inv_mem hKsub p.2.2) hmem
  have hproper : (Set.range F).ncard < (Set.univ : Set ↥{z : G | z ∈ Q ∧ z ≠ 1}).ncard := by
    have hssub : Set.range F ⊂ (Set.univ : Set ↥{z : G | z ∈ Q ∧ z ≠ 1}) := by
      refine ⟨Set.subset_univ _, ?_⟩
      intro hsub
      exact hxnot (hsub (Set.mem_univ _))
    exact Set.ncard_lt_ncard hssub (Set.toFinite _)
  have hrange : (Set.range F).ncard = Nat.card (↥(GoodReps H t s r) × ↥(Work.ThmF.Kset H t)) :=
    Set.ncard_range_of_injective hfinj
  rw [Set.ncard_univ, hcard_eq.symm, hrange] at hproper
  exact absurd hproper (lt_irrefl _)

theorem KOrbitsOfQ_full {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (h5 : orderOf (s * t) = 5) (hW : Work.ThmF.W H t = ⊥)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 2)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) :
    ∀ x ∈ Q, x ≠ 1 → ∃ k ∈ Work.ThmF.Kset H t, k⁻¹ * x * k ∈ Work.PSU3.StageA.GoodReps H t s r := by
  refine KOrbitsOfQ_of_sep hS hC4 hs hs2 hr hsr h5 hcard hKsub ?_ ?_
  · -- Ch. VI §2 of the source: the representatives are pairwise non-`K`-conjugate.
    -- `Q₀sub H` is normal in `H` (`Q0sub_elementary`), so `Kset` normalises it.
    have hQ0norm : ∀ {a x : G}, a ∈ Work.ThmF.Kset H t → x ∈ Work.ThmF.Q0sub H →
        a⁻¹ * x * a ∈ Work.ThmF.Q0sub H := by
      intro a x ha hx
      have hcomm := Work.ThmF.L5.involutions_commute hS.situation hC4 hS.split
      obtain ⟨-, -, hnorm, -⟩ := Work.ThmF.ChV12.Q0sub_elementary H hcomm
      have haH : a ∈ H :=
        Work.RankOneUniqueness.twoPoint_le_left H t (Work.ThmF.Kset_subset H t ha)
      simpa only [inv_inv] using hnorm a⁻¹ (H.inv_mem haH) x hx
    intro g₁ hg₁ g₂ hg₂ hne ⟨k, hkK, hkconj⟩
    have hiff₁ : g₁ ∈ Work.ThmF.Q0sub H ↔ g₁ = s :=
      caseB_GoodReps_mem_Q0sub_iff hS hC4 hHig hs hs2 hr hsr h5 hW hnab hcard hKsub hg₁
    have hiff₂ : g₂ ∈ Work.ThmF.Q0sub H ↔ g₂ = s :=
      caseB_GoodReps_mem_Q0sub_iff hS hC4 hHig hs hs2 hr hsr h5 hW hnab hcard hKsub hg₂
    by_cases h1 : g₁ ∈ Work.ThmF.Q0sub H
    · have h2 : g₂ ∈ Work.ThmF.Q0sub H := hkconj ▸ hQ0norm hkK h1
      exact hne ((hiff₁.mp h1).trans (hiff₂.mp h2).symm)
    · by_cases h2 : g₂ ∈ Work.ThmF.Q0sub H
      · have hkInv : k⁻¹ ∈ Work.ThmF.Kset H t := Kset_inv_mem hKsub hkK
        have h1' : g₁ ∈ Work.ThmF.Q0sub H := by
          have hmem : k * g₂ * k⁻¹ ∈ Work.ThmF.Q0sub H := by
            simpa only [inv_inv] using hQ0norm hkInv h2
          rwa [show k * g₂ * k⁻¹ = g₁ from by rw [← hkconj]; group] at hmem
        exact hne ((hiff₁.mp h1').trans (hiff₂.mp h2).symm)
      · exact hne (caseB_orbits_conj_core_K hS hC4 hHig hs hs2 hr hsr h5 hW hnab hcard hKsub
          hg₁ hg₂ h1 h2 hkK hkconj)
  · -- the count `|GoodReps| = |Q₀sub H| + 1`
    exact caseB_GoodReps_ncard hS hC4 hs hs2 hr hsr h5 hKsub

end Work.PSU3.StageA
