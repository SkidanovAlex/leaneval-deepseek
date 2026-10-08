import Mathlib
import Submission.Work.BSW.Cases.DataZass.Setup
import Submission.Work.BSW.Cases.DataZass.Dfree
import Submission.Work.BSW.Cases.DataZass.QsMulFree
import Submission.OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup

/-!
# `zass_fix`: no nonidentity element fixes three points of `G ⧸ N_G(Q)`

This file proves the "at most two fixed points" clause of the Zassenhaus conversion: for a
Bender configuration `IsBSWConf q Q D` (Bender's conclusion (1)–(4) together with 3.7) with
`q = p ^ k ≥ 5`, every `g ≠ 1` fixes at most two points of the coset space `G ⧸ N_G(Q)`.

## Structure of the proof

Write `H := N_G(Q)`, so that `Ω := G ⧸ H` is the set of Sylow `p`-subgroups of `G` (via
`xH ↦ xQx⁻¹`) and `|Ω| = q + 1`.

* `QsMulTransitive` (with `QsMulFree`, proved in the companion files): `Q` acts freely on the
  `q` points different from the base point, hence transitively on them (both sets have `q`
  elements).
* `pElemConj`: a `p`-element normalizing a conjugate of `Q` lies in it (so a nonidentity element
  of `Q` fixes only the base point, since `Q` is disjoint from its conjugates).
* `isFrobeniusGroup_normalizer`: `Q ⋊ D` is a Frobenius group with kernel `Q` and complement `D`
  (Bender's (4) says precisely that each `d ∈ D#` acts fixed-point-freely on `Q`), so by
  Isaacs Thm 6.4 (4) — `IsFrobeniusGroup.centralizer_kernel_le`, from the formalised
  Isaacs Chapter 6 — the centralizer of every `n ∈ Q#` lies in `Q`:
  `centralizer_le_of_mem_normalizer`.  Consequently every `h ∈ H \ Q` acts fixed-point-freely on
  `Q`.
* `ncard_fix_ne_base_le_one`: an `h ∈ H \ Q` fixes at most one point off the base point.  Indeed
  if `x₁ ≠ x₂` are such points, then `x₂ = c • x₁` for some `c ∈ Q` (transitivity), and from
  `h • x₂ = x₂` we get `(c⁻¹ h c h⁻¹) • x₁ = x₁`; as `c⁻¹ h c h⁻¹ ∈ Q` and `x₁` is not the base
  point, freeness gives `h c h⁻¹ = c`, so `c = 1` by the fixed-point-freeness of `h` on `Q`, i.e.
  `x₂ = x₁`, a contradiction.
* `ncard_fix_le_two_of_mem_normalizer` assembles the two cases `h ∈ Q#` and `h ∈ H \ Q`.
* `zass_fix` conjugates a general `g ≠ 1` fixing a point into `H` (the number of fixed points is
  invariant under conjugation) and applies the previous step.
-/

open scoped MatrixGroups Pointwise

namespace Work.BSW.Cases.DataZass

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G]

/-! ## `Q` is transitive on the non-base points -/

/-- `Q` acts transitively on the points of `G ⧸ N_G(Q)` different from the base point. -/
theorem QsMulTransitive {q : ℕ} {Q : Subgroup G} (hQcard : Nat.card Q = q)
    (hcard : Nat.card (G ⧸ Subgroup.normalizer (Q : Set G)) = q + 1)
    (hfree : ∀ c ∈ Q, ∀ x : G ⧸ Subgroup.normalizer (Q : Set G), c • x = x →
      x ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) → c = 1)
    {x y : G ⧸ Subgroup.normalizer (Q : Set G)}
    (hx : x ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)))
    (hy : y ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G))) :
    ∃ c ∈ Q, c • x = y := by
  have hinj : Function.Injective (fun c : Q => c • x) := by
    intro c1 c2 h12
    have hmem : ((c1 : G)⁻¹ * (c2 : G)) ∈ Q := Q.mul_mem (Q.inv_mem c1.2) c2.2
    have h12' : (c2 : G) • x = (c1 : G) • x := h12.symm
    have hfix : ((c1 : G)⁻¹ * (c2 : G)) • x = x := by
      rw [mul_smul, h12', inv_smul_smul]
    have hone : (c1 : G)⁻¹ * (c2 : G) = 1 := hfree _ hmem x hfix hx
    exact Subtype.ext (inv_mul_eq_one.mp hone)
  have hsub : (fun c : Q => c • x) '' (Set.univ : Set Q) ⊆
      {z : G ⧸ Subgroup.normalizer (Q : Set G) |
        z ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G))} := by
    rintro z ⟨c, -, rfl⟩
    intro hc
    have hc' : (c : G) • x = ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) := hc
    have h3 : ((c : G)⁻¹) • ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) =
        ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) := by
      change ((((c : G)⁻¹) * 1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) =
        ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G))
      rw [QuotientGroup.eq]
      simpa using le_normalizer c.2
    exact hx (by
      calc x = ((c : G)⁻¹) • ((c : G) • x) := (inv_smul_smul _ _).symm
        _ = ((c : G)⁻¹) • ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) := by rw [hc']
        _ = ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) := h3)
  have hcardimg : ((fun c : Q => c • x) '' (Set.univ : Set Q)).ncard = q := by
    rw [Set.ncard_image_of_injective _ hinj, Set.ncard_univ, hQcard]
  have hcard' : ({z : G ⧸ Subgroup.normalizer (Q : Set G) |
      z ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G))} : Set _).ncard = q := by
    rw [← Set.compl_singleton_eq ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G))]
    rw [Set.ncard_compl, Set.ncard_singleton, hcard]
    omega
  have himg := Set.eq_of_subset_of_ncard_le hsub (by rw [hcardimg, hcard'])
  have hy' : y ∈ (fun c : Q => c • x) '' (Set.univ : Set Q) := by
    rw [himg]; exact hy
  obtain ⟨c, -, hc⟩ := hy'
  exact ⟨c, c.2, hc⟩

/-! ## A `p`-element normalizing a conjugate of `Q` lies in it -/

/-- A `p`-element of the normalizer of a conjugate `P = aQa⁻¹` of `Q` lies in `P` (so a
nonidentity element of `Q` normalizes only the Sylow subgroup containing it). -/
theorem pElemConj {q p k : ℕ} (hp : p.Prime) (hq : q = p ^ k) (h5 : 5 ≤ q) (hodd : Odd q)
    {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D) {P : Subgroup G}
    (hP : ∃ a : G, P = Work.GW2.conjSub a Q) {y : G} (hy : y ∈ Subgroup.normalizer (P : Set G))
    (hord : ∃ j : ℕ, orderOf y = p ^ j) : y ∈ P := by
  obtain ⟨a, rfl⟩ := hP
  have hk : k ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hq
    omega
  have hQk : Nat.card Q = p ^ k := by rw [h.card_Q, hq]
  have hDle : D ≤ Subgroup.normalizer (Q : Set G) := by
    rw [h.normalizer_Q]; exact le_sup_right
  have hH : Nat.card ↥(Subgroup.normalizer (Q : Set G)) = p ^ k * ((q - 1) / 2) := by
    rw [h.normalizer_Q, card_sup_of_inf_bot_of_le_normalizer h.inf_bot hDle, h.card_Q,
      h.card_D, hq]
  have hm2 : 2 * ((q - 1) / 2) = q - 1 := by
    obtain ⟨t, ht⟩ := hodd
    rw [ht, show (2 * t + 1 - 1) = 2 * t by omega,
      Nat.mul_div_right t (by norm_num : 0 < 2)]
  have hpnd : ¬ p ∣ (q - 1) / 2 := by
    intro hdiv
    have h1 : p ∣ q := by rw [hq]; exact dvd_pow_self p hk
    have h2 : p ∣ q - 1 := by
      have h3 : p ∣ 2 * ((q - 1) / 2) := dvd_mul_of_dvd_right hdiv 2
      rwa [hm2] at h3
    have h4 := Nat.dvd_sub h1 h2
    rw [show q - (q - 1) = 1 by omega] at h4
    exact hp.not_dvd_one h4
  have hy' : a⁻¹ * y * a ∈ Subgroup.normalizer (Q : Set G) := by
    rw [normalizer_conjSub_H] at hy
    exact (mem_conjSub_iff_H (a := a) (x := y)
      (Q := Subgroup.normalizer (Q : Set G))).mp hy
  have hord' : ∃ j : ℕ, orderOf (a⁻¹ * y * a) = p ^ j := by
    obtain ⟨j, hj⟩ := hord
    refine ⟨j, ?_⟩
    have h1 : a⁻¹ * y * a = (MulAut.conj a⁻¹) y := by rw [MulAut.conj_apply, inv_inv]
    rw [h1, (MulAut.conj a⁻¹).orderOf_eq y, hj]
  have hmem := mem_of_pElement_of_mem_normalizer hp hpnd hQk hH hy' hord'
  rw [mem_conjSub_iff_H]
  exact hmem

/-! ## The Frobenius structure of `N_G(Q) = Q ⋊ D` -/

/-- `Q ⋊ D` is a Frobenius group with kernel `Q` and complement `D`: this is exactly Bender's
clause (4) (`N_G(X) = N_G(D)` for every `1 ≠ X ≤ D` plus `N_G(D) = D⟨u⟩` with `u ∉ D` of
order `2` inverting `D`), which says that every nonidentity element of `D` acts
fixed-point-freely on `Q`. -/
theorem isFrobeniusGroup_normalizer {q : ℕ} (hodd : Odd q) (h5 : 5 ≤ q)
    {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(Subgroup.normalizer (Q : Set G))
      (Q.subgroupOf (Subgroup.normalizer (Q : Set G)))
      (D.subgroupOf (Subgroup.normalizer (Q : Set G))) := by
  have hQH : Q ≤ Subgroup.normalizer (Q : Set G) := le_normalizer
  have hDH : D ≤ Subgroup.normalizer (Q : Set G) := by
    rw [h.normalizer_Q]; exact le_sup_right
  have hcardH : Nat.card ↥(Subgroup.normalizer (Q : Set G)) = q * ((q - 1) / 2) := by
    rw [h.normalizer_Q, card_sup_of_inf_bot_of_le_normalizer h.inf_bot hDH, h.card_Q,
      h.card_D]
  have hcardQ' : Nat.card ↥(Q.subgroupOf (Subgroup.normalizer (Q : Set G))) = q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv, h.card_Q]
  have hcardD' : Nat.card ↥(D.subgroupOf (Subgroup.normalizer (Q : Set G))) = (q - 1) / 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv, h.card_D]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr le_rfl
  · rw [Subgroup.isComplement'_iff_card_mul_and_disjoint]
    refine ⟨by rw [hcardQ', hcardD', hcardH], ?_⟩
    rw [disjoint_iff, Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxQ, hxD⟩
    have h1 : (x : G) ∈ Q ⊓ D := ⟨hxQ, hxD⟩
    rw [h.inf_bot] at h1
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  · intro hbot
    have h1 : Nat.card ↥(Q.subgroupOf (Subgroup.normalizer (Q : Set G))) = 1 := by
      rw [hbot]; exact Subgroup.card_bot
    rw [hcardQ'] at h1
    omega
  · intro hbot
    have h1 : Nat.card ↥(D.subgroupOf (Subgroup.normalizer (Q : Set G))) = 1 := by
      rw [hbot]; exact Subgroup.card_bot
    rw [hcardD'] at h1
    omega
  · intro a ha ha1 n hn hn1 hconj
    rw [Subgroup.mem_subgroupOf] at ha hn
    have ha1' : (a : G) ≠ 1 := fun h1 => ha1 (Subtype.ext (by simpa using h1))
    have hn1' : (n : G) ≠ 1 := fun h1 => hn1 (Subtype.ext (by simpa using h1))
    have hconj' : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
      have h2 := congrArg (fun z : ↥(Subgroup.normalizer (Q : Set G)) => (z : G)) hconj
      simpa using h2
    exact Dfree hodd h ha ha1' hn hn1' hconj'

/-- **Isaacs Thm 6.4 (1) ⇒ (4)** for the Frobenius group `Q ⋊ D`: any element of `N_G(Q)`
commuting with a nonidentity element of `Q` already lies in `Q`. -/
theorem centralizer_le_of_mem_normalizer {q : ℕ} (hodd : Odd q) (h5 : 5 ≤ q)
    {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D) :
    ∀ n ∈ Q, n ≠ 1 → ∀ c ∈ Subgroup.normalizer (Q : Set G), c * n * c⁻¹ = n → c ∈ Q := by
  have hF := isFrobeniusGroup_normalizer (G := G) (Q := Q) (D := D) hodd h5 h
  have hker := OddOrder.Isaacs.Ch06.IsFrobeniusGroup.centralizer_kernel_le
    (N := Q.subgroupOf (Subgroup.normalizer (Q : Set G)))
    (A := D.subgroupOf (Subgroup.normalizer (Q : Set G))) hF
  intro n hn hn1 c hc hcn
  have hQH : Q ≤ Subgroup.normalizer (Q : Set G) := le_normalizer
  let nB : ↥(Subgroup.normalizer (Q : Set G)) := ⟨n, hQH hn⟩
  have hnB : nB ∈ Q.subgroupOf (Subgroup.normalizer (Q : Set G)) := hn
  have hnB1 : nB ≠ 1 := by
    intro h1
    refine hn1 ?_
    have h2 := congrArg (fun z : ↥(Subgroup.normalizer (Q : Set G)) => (z : G)) h1
    simpa [nB] using h2
  have hcent : (⟨c, hc⟩ : ↥(Subgroup.normalizer (Q : Set G))) ∈
      Subgroup.centralizer ({nB} : Set ↥(Subgroup.normalizer (Q : Set G))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change c * n = n * c
    have h2 := congrArg (fun z => z * c) hcn
    simpa [mul_assoc] using h2
  have hres := (hker nB hnB hnB1) hcent
  exact Subgroup.mem_subgroupOf.mp hres

/-! ## Fixed points of elements of `N_G(Q)` -/

/-- A nonidentity element of `Q` fixes only the base point (its own Sylow subgroup). -/
theorem fix_subset_base_of_mem_Q {q p k : ℕ} (hp : p.Prime) (hq : q = p ^ k) (h5 : 5 ≤ q)
    (hodd : Odd q) {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D) {h' : G} (hh' : h' ∈ Q)
    (hne : h' ≠ 1) :
    ({x : G ⧸ Subgroup.normalizer (Q : Set G) | h' • x = x} : Set _)
      ⊆ {((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G))} := by
  intro x hx
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  have hmem : a⁻¹ * h' * a ∈ Subgroup.normalizer (Q : Set G) := by
    have h1 : (h' * a)⁻¹ * a ∈ Subgroup.normalizer (Q : Set G) := (QuotientGroup.eq).mp hx
    have h2 := Subgroup.inv_mem _ h1
    rwa [show ((h' * a)⁻¹ * a)⁻¹ = a⁻¹ * h' * a by group] at h2
  have hmem' : h' ∈ Subgroup.normalizer (Work.GW2.conjSub a Q : Set G) := by
    rw [normalizer_conjSub_H]
    exact (mem_conjSub_iff_H (a := a) (x := h')
      (Q := Subgroup.normalizer (Q : Set G))).mpr hmem
  have hk : k ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hq
    omega
  have hQk : Nat.card Q = p ^ k := by rw [h.card_Q, hq]
  have hord : ∃ j : ℕ, orderOf h' = p ^ j := exists_orderOf_eq_pow_of_mem hp hQk hh'
  have hyP : h' ∈ Work.GW2.conjSub a Q :=
    pElemConj hp hq h5 hodd h (P := Work.GW2.conjSub a Q) ⟨a, rfl⟩ hmem' hord
  have hbot : h' ∈ Q ⊓ Work.GW2.conjSub a Q := ⟨hh', hyP⟩
  by_cases haH : a ∈ Subgroup.normalizer (Q : Set G)
  · have ha' : ((a : G) : G ⧸ Subgroup.normalizer (Q : Set G)) =
        ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) :=
      QuotientGroup.eq.mpr (by simpa using Subgroup.inv_mem _ haH)
    simpa using ha'
  · rw [IsBSWConf.disjoint h a haH] at hbot
    exact absurd (Subgroup.mem_bot.mp hbot) hne

/-- An element of `N_G(Q)` outside `Q` fixes at most one point other than the base point. -/
theorem ncard_fix_ne_base_le_one {q : ℕ} (hodd : Odd q) (h5 : 5 ≤ q)
    {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D)
    (htrans : ∀ x y : G ⧸ Subgroup.normalizer (Q : Set G),
      x ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) →
      y ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) → ∃ c ∈ Q, c • x = y)
    (hfree : ∀ c ∈ Q, ∀ x : G ⧸ Subgroup.normalizer (Q : Set G), c • x = x →
      x ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) → c = 1)
    {h' : G} (hh : h' ∈ Subgroup.normalizer (Q : Set G)) (hQ : h' ∉ Q) :
    ({x : G ⧸ Subgroup.normalizer (Q : Set G) |
        x ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) ∧ h' • x = x}).ncard ≤ 1 := by
  rw [Set.ncard_le_one]
  intro x1 hx1 x2 hx2
  have hx1' : x1 ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) ∧ h' • x1 = x1 := hx1
  have hx2' : x2 ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) ∧ h' • x2 = x2 := hx2
  obtain ⟨hx1n, hx1f⟩ := hx1'
  obtain ⟨hx2n, hx2f⟩ := hx2'
  obtain ⟨c, hc, hcx⟩ := htrans x1 x2 hx1n hx2n
  have hn1 : h' * c * h'⁻¹ ∈ Q := by
    have hh' := hh
    rw [Subgroup.mem_normalizer_iff] at hh'
    exact (hh' c).mp hc
  have hmemQ : c⁻¹ * h' * c * h'⁻¹ ∈ Q := by
    have h1 : c⁻¹ * (h' * c * h'⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem hc) hn1
    simpa [mul_assoc] using h1
  have hfix1 : (c⁻¹ * h' * c * h'⁻¹) • x1 = x1 := by
    have he1 : h'⁻¹ • x1 = x1 := by
      have h2 : x1 = h'⁻¹ • x1 := by
        have h3 := congrArg (fun z => h'⁻¹ • z) hx1f
        rwa [inv_smul_smul] at h3
      exact h2.symm
    have h2 : (h' * c * h'⁻¹) • x1 = x2 := by
      calc (h' * c * h'⁻¹) • x1 = h' • (c • (h'⁻¹ • x1)) := by rw [mul_smul, mul_smul]
        _ = h' • (c • x1) := by rw [he1]
        _ = h' • x2 := by rw [hcx]
        _ = x2 := hx2f
    rw [show c⁻¹ * h' * c * h'⁻¹ = c⁻¹ * (h' * c * h'⁻¹) by group, mul_smul, h2,
      ← hcx, inv_smul_smul]
  have hone : c⁻¹ * h' * c * h'⁻¹ = 1 := hfree _ hmemQ x1 hfix1 hx1n
  have hconj : h' * c * h'⁻¹ = c := by
    have h2 := congrArg (fun z => c * z) hone
    simpa [mul_assoc] using h2
  by_cases hc1 : c = 1
  · rw [hc1, one_smul] at hcx
    exact hcx
  · exact absurd (centralizer_le_of_mem_normalizer hodd h5 h c hc hc1 h' hh hconj) hQ

/-! ## Assembly -/

/-- No nonidentity element of `N_G(Q)` fixes more than two points of `G ⧸ N_G(Q)`. -/
theorem ncard_fix_le_two_of_mem_normalizer {q p k : ℕ} (hp : p.Prime) (hq : q = p ^ k)
    (h5 : 5 ≤ q) (hodd : Odd q) {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D)
    (htrans : ∀ x y : G ⧸ Subgroup.normalizer (Q : Set G),
      x ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) →
      y ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) → ∃ c ∈ Q, c • x = y)
    (hfree : ∀ c ∈ Q, ∀ x : G ⧸ Subgroup.normalizer (Q : Set G), c • x = x →
      x ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) → c = 1)
    {h' : G} (hh : h' ∈ Subgroup.normalizer (Q : Set G)) (hne : h' ≠ 1) :
    ({x : G ⧸ Subgroup.normalizer (Q : Set G) | h' • x = x}).ncard ≤ 2 := by
  by_cases hQ : h' ∈ Q
  · have hsub := fix_subset_base_of_mem_Q hp hq h5 hodd h hQ hne
    have h1 := Set.ncard_le_ncard hsub
    rw [Set.ncard_singleton] at h1
    omega
  · have hbase : h' • ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) =
        ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) := by
      change (((h' * 1 : G)) : G ⧸ Subgroup.normalizer (Q : Set G)) =
        ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G))
      rw [QuotientGroup.eq]
      simpa using hh
    have hsub : ({x : G ⧸ Subgroup.normalizer (Q : Set G) | h' • x = x} : Set _) ⊆
        ({((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G))} : Set _) ∪
          {x : G ⧸ Subgroup.normalizer (Q : Set G) |
            x ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) ∧ h' • x = x} := by
      intro x hx
      by_cases hxb : x = ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G))
      · rw [hxb]
        exact Or.inl (by simp)
      · exact Or.inr ⟨hxb, hx⟩
    have h1 := Set.ncard_le_ncard hsub
    have h2 := Set.ncard_union_le ({((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G))} : Set _)
      {x : G ⧸ Subgroup.normalizer (Q : Set G) |
        x ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) ∧ h' • x = x}
    have h3 := ncard_fix_ne_base_le_one hodd h5 h htrans hfree hh hQ
    rw [Set.ncard_singleton] at h2
    omega

/-- **The "at most two fixed points" clause**: every `g ≠ 1` fixes at most two points of
`G ⧸ N_G(Q)`. -/
theorem zass_fix {G : Type} [Group G] [Finite G] {q p k : ℕ} {Q D : Subgroup G}
    (hp : p.Prime) (hq : q = p ^ k) (h5 : 5 ≤ q) (hodd : Odd q)
    (h : Work.BSW.Cases.IsBSWConf (G := G) q Q D) {g : G} (hg : g ≠ 1) :
    {x : G ⧸ Subgroup.normalizer (Q : Set G) | g • x = x}.ncard ≤ 2 := by
  have hfree : ∀ c ∈ Q, ∀ x : G ⧸ Subgroup.normalizer (Q : Set G), c • x = x →
      x ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) → c = 1 :=
    fun c hc x hfix hx => QsMulFree hp hq h5 hodd h hc hx hfix
  have htrans : ∀ x y : G ⧸ Subgroup.normalizer (Q : Set G),
      x ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) →
      y ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) → ∃ c ∈ Q, c • x = y :=
    fun x y hx hy => QsMulTransitive h.card_Q (zass_card h5 hodd h) hfree hx hy
  by_cases hne : ({x : G ⧸ Subgroup.normalizer (Q : Set G) | g • x = x} : Set _).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x0
    have hmem : a⁻¹ * g * a ∈ Subgroup.normalizer (Q : Set G) := by
      have h1 : (g * a)⁻¹ * a ∈ Subgroup.normalizer (Q : Set G) := (QuotientGroup.eq).mp hx0
      have h2 := Subgroup.inv_mem _ h1
      rwa [show ((g * a)⁻¹ * a)⁻¹ = a⁻¹ * g * a by group] at h2
    have hne' : a⁻¹ * g * a ≠ 1 := by
      intro h1
      refine hg ?_
      calc g = a * (a⁻¹ * g * a) * a⁻¹ := by group
        _ = a * 1 * a⁻¹ := by rw [h1]
        _ = 1 := by group
    have hcardeq : ({x : G ⧸ Subgroup.normalizer (Q : Set G) | g • x = x} : Set _).ncard =
        ({x : G ⧸ Subgroup.normalizer (Q : Set G) | (a⁻¹ * g * a) • x = x} : Set _).ncard := by
      refine Set.ncard_congr (fun x _ => a⁻¹ • x) ?_ ?_ ?_
      · intro x hx
        show (a⁻¹ * g * a) • (a⁻¹ • x) = a⁻¹ • x
        rw [mul_smul, mul_smul, smul_inv_smul, hx]
      · intro x y hx hy hxy
        have h2 := congrArg (fun z => a • z) hxy
        simpa using h2
      · intro y hy
        exact ⟨a • y, by
          show g • (a • y) = a • y
          rw [← mul_smul, show g * a = a * (a⁻¹ * g * a) by group, mul_smul, hy], by
          show a⁻¹ • (a • y) = y
          rw [inv_smul_smul]⟩
    rw [hcardeq]
    exact ncard_fix_le_two_of_mem_normalizer hp hq h5 hodd h htrans hfree hmem hne'
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.ncard_empty]
    omega

end Work.BSW.Cases.DataZass
