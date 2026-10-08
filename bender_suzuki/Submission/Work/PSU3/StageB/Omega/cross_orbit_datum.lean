import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.count_le
import Submission.Work.PSU3.StageB.Omega.count_le_self
import Submission.Work.PSU3.StageB.Omega.count_self_eq
import Submission.Work.PSU3.StageB.Omega.orbE_card
import Submission.Work.PSU3.StageB.Omega.exists_coset_zeta
import Submission.Work.PSU3.StageB.Omega.exists_zcQF_eq_of_mem_Q0

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageB.Omega.cross_orbit_datum` — the cross-orbit connecting pair

Peterfalvi II, Ch. VII §2, items (7)+(8), used in (19)/(20): for two elements `ω₁, ω₂ ∉ Q₀`
whose `KW`-orbits on `Q/Q₀` differ (`bar ω₁ ∉ bar ω₂ · KW`), the "cross-orbit fibre"
`{x ∈ Q₀ : f(ω₁ x) ∈ (ω₂ Q₀)^{KW}}` has *exactly* `m = |KW : K|` elements; since distinct
solutions give distinct cosets of `K` in `KW` (item (7)) and there are exactly `m` cosets, the
trivial coset is attained: `f(ω₁ x₁) = (ω₂ y₂)^k` with `k ∈ K = KW ∩ Ksub`.

The pigeonhole is the one of `count_self_eq`: the `KW`-orbits on `E n^×` number `r` with
`r · m = 2ⁿ + 1`, the fibres of `x ↦ orbE (bar (f (ω₁ x)))` partition `Q₀` (`|Q₀| = 2ⁿ`),
the self-orbit fibre is `≤ m - 1` (`count_le_self`) and every other fibre is `≤ m` (`count_le`).
Hence every fibre off the self-orbit has exactly `m` elements.

The hypothesis `hf₁` (`bar (f ω₁) ∉ bar ω₂ · KW`) is what excludes `x₁ = 1`, so that `x₁` can be
parametrised as `zcQF fr X₁` with `X₁ ∈ F*`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open Submission.Blueprint
open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB
open Classical

namespace Work.PSU3.StageB.Omega

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## Abstract counting: a fibre off the distinguished point has exactly `m` elements -/

/-- **Abstract counting, off-point version.**  If a finite type `β` with a distinguished `O₀`
carries `N : β → ℕ` with total `q`, all values `≤ m`, the value at `O₀` `≤ m - 1`, and
`#β · m = q + 1`, then the value at any *other* `O₁` is exactly `m`. -/
lemma card_fiber_eq_of_sum_bound_ne {β : Type} [Fintype β] (O₀ O₁ : β) (N : β → ℕ) (m q : ℕ)
    (hm : 1 ≤ m) (hcard : Fintype.card β * m = q + 1)
    (hN₀ : N O₀ ≤ m - 1) (hN : ∀ b, b ≠ O₀ → N b ≤ m)
    (hsum : (∑ b : β, N b) = q) (hne : O₁ ≠ O₀) :
    N O₁ = m := by
  classical
  have hle : ∀ b : β, N b ≤ (if b = O₀ then m - 1 else m) := by
    intro b
    by_cases h : b = O₀
    · subst h; simp only [if_pos rfl]; exact hN₀
    · simp only [if_neg h]; exact hN b h
  have hsumg : (∑ b : β, (if b = O₀ then m - 1 else m)) = q := by
    have h1 : (∑ b : β, (if b = O₀ then m - 1 else m))
        = ∑ b : β, (m - (if b = O₀ then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : b = O₀
      · subst h; simp
      · simp [h]
    rw [h1]
    rw [Finset.sum_tsub_distrib (Finset.univ)
        (f := fun _ : β => m) (g := fun b : β => if b = O₀ then 1 else 0)
        (fun b _ => by by_cases h : b = O₀ <;> simp [h, hm])]
    have hdelta : (∑ b : β, (if b = O₀ then 1 else 0)) = 1 := by
      rw [Finset.sum_ite_eq' Finset.univ O₀ (fun _ => (1 : ℕ))]
      simp
    rw [hdelta, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    omega
  have h2 := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := fun b : β => N b) (g := fun b : β => if b = O₀ then m - 1 else m)
      (fun b _ => hle b)).mp (by rw [hsum, hsumg])
  have h3 := h2 O₁ (Finset.mem_univ O₁)
  rwa [if_neg hne] at h3

/-! ## The cross-orbit fibre has exactly `m` elements -/

/-- **§2 (8), cross-orbit.**  For `ω, ω' ∉ Q₀` whose `KW`-orbits differ, the number of `x ∈ Q₀`
with `f(ω x) = (ω' y)^d` (`d ∈ KW`, `y ∈ Q₀`) is exactly `|KW : K| = orderOf ζ`. -/
theorem cross_orbit_card {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω ω' : ↥Q} (hω : (ω : G) ∉ fr.Q0) (hω' : (ω' : G) ∉ fr.Q0)
    (horb : Multiplicative.toAdd (fr.bar ω) ∉
      orbE fr (Multiplicative.toAdd (fr.bar ω'))) :
    Nat.card (ConjSet hS fr ω ω') = Nat.card fr.KW / Nat.card ↥(Ksub H t) := by
  classical
  obtain ⟨_hn, hQ0, _hKW, _hKsub, hdiv⟩ := omega_card_facts hS fr
  haveI : Fintype (OrbSet fr) := Fintype.ofFinite (OrbSet fr)
  let O0 : OrbSet fr :=
    ⟨orbE fr (Multiplicative.toAdd (fr.bar ω)), ⟨_, toAdd_bar_ne_zero fr hω, rfl⟩⟩
  let O2 : OrbSet fr :=
    ⟨orbE fr (Multiplicative.toAdd (fr.bar ω')), ⟨_, toAdd_bar_ne_zero fr hω', rfl⟩⟩
  let N : OrbSet fr → ℕ := fun O => Nat.card {x : Q0Dom fr // orbPhi hS fr ω hω x = O}
  have hcard_dom : Nat.card (Q0Dom fr) = 2 ^ n := by
    rw [show Nat.card (Q0Dom fr) = Nat.card ↥fr.Q0 from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe fr.Q0_le).toEquiv, hQ0]
  have hsum : ∑ O : OrbSet fr, N O = 2 ^ n := by
    rw [← hcard_dom]
    exact (natCard_eq_sum_card_fiber (orbPhi hS fr ω hω)).symm
  have hcard_orbit : Fintype.card (OrbSet fr) * orderOf fr.ζ = 2 ^ n + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact (orbE_card hS fr).2
  have hm : 1 ≤ orderOf fr.ζ := by have := orderOf_pos fr.ζ; omega
  -- every fibre but the one of `ω` has at most `m` points
  have hN : ∀ O : OrbSet fr, O ≠ O0 → N O ≤ orderOf fr.ζ := by
    intro O _
    obtain ⟨ν, hν, hrep⟩ := orbSet_exists_rep fr O
    have hwit : ∀ x : {x : Q0Dom fr // orbPhi hS fr ω hω x = O},
        Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x.1.1))) ∈
          orbE fr (Multiplicative.toAdd (fr.bar ν)) := by
      intro x
      have hval : orbE fr (Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x.1.1)))) =
          (O : Set (E n)) := congrArg Subtype.val x.2
      rw [← hrep, ← hval]
      exact orbE_refl fr _
    have hinj : Function.Injective (fun x : {x : Q0Dom fr // orbPhi hS fr ω hω x = O} =>
        (⟨x.1.1, x.1.2, orbit_mem_to_witness hS fr (hwit x)⟩ : ConjSet hS fr ω ν)) := by
      intro x y hxy
      have h1 : (x.1.1 : ↥Q) = (y.1.1 : ↥Q) := congrArg (fun z => (z.1 : ↥Q)) hxy
      exact Subtype.ext (Subtype.ext h1)
    refine (Nat.card_le_card_of_injective _ hinj).trans ?_
    have h := count_le hS fr hω hν
    rw [hdiv] at h
    exact h
  -- the fibre of `ω` is at most `m - 1`
  have hN0 : N O0 ≤ orderOf fr.ζ - 1 := by
    have hge : N O0 ≤ Nat.card (SelfSet hS fr ω) := by
      have hwit : ∀ x : {x : Q0Dom fr // orbPhi hS fr ω hω x = O0},
          Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x.1.1))) ∈
            orbE fr (Multiplicative.toAdd (fr.bar ω)) := by
        intro x
        have hval : orbE fr (Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x.1.1)))) =
            (O0 : Set (E n)) := congrArg Subtype.val x.2
        have hO0val : (O0 : Set (E n)) = orbE fr (Multiplicative.toAdd (fr.bar ω)) := rfl
        rw [← hO0val, ← hval]
        exact orbE_refl fr _
      have hinj : Function.Injective (fun x : {x : Q0Dom fr // orbPhi hS fr ω hω x = O0} =>
          (⟨x.1.1, x.1.2, orbit_mem_to_witness hS fr (hwit x)⟩ : SelfSet hS fr ω)) := by
        intro x y hxy
        have h1 : (x.1.1 : ↥Q) = (y.1.1 : ↥Q) := congrArg (fun z => (z.1 : ↥Q)) hxy
        exact Subtype.ext (Subtype.ext h1)
      exact Nat.card_le_card_of_injective _ hinj
    have hCS : Nat.card (SelfSet hS fr ω) ≤ orderOf fr.ζ - 1 := by
      have h := count_le_self hS fr hω
      rw [hdiv] at h
      exact h
    exact hge.trans hCS
  have hne : O2 ≠ O0 := by
    intro h
    apply horb
    have hmem0 : Multiplicative.toAdd (fr.bar ω) ∈ (O0 : Set (E n)) := orbE_refl fr _
    rw [← h] at hmem0
    simpa [O2] using hmem0
  have hN2 : N O2 = orderOf fr.ζ :=
    card_fiber_eq_of_sum_bound_ne O0 O2 N (orderOf fr.ζ) (2 ^ n) hm hcard_orbit hN0 hN hsum hne
  have hfib : N O2 ≤ Nat.card (ConjSet hS fr ω ω') := by
    have hwit : ∀ x : {x : Q0Dom fr // orbPhi hS fr ω hω x = O2},
        Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x.1.1))) ∈
          orbE fr (Multiplicative.toAdd (fr.bar ω')) := by
      intro x
      have hval : orbE fr (Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x.1.1)))) =
          (O2 : Set (E n)) := congrArg Subtype.val x.2
      have hO2val : (O2 : Set (E n)) = orbE fr (Multiplicative.toAdd (fr.bar ω')) := rfl
      rw [← hO2val, ← hval]
      exact orbE_refl fr _
    have hinj : Function.Injective (fun x : {x : Q0Dom fr // orbPhi hS fr ω hω x = O2} =>
        (⟨x.1.1, x.1.2, orbit_mem_to_witness hS fr (hwit x)⟩ : ConjSet hS fr ω ω')) := by
      intro x y hxy
      have h1 : (x.1.1 : ↥Q) = (y.1.1 : ↥Q) := congrArg (fun z => (z.1 : ↥Q)) hxy
      exact Subtype.ext (Subtype.ext h1)
    exact Nat.card_le_card_of_injective _ hinj
  have hCS_le : Nat.card (ConjSet hS fr ω ω') ≤ orderOf fr.ζ := by
    have h := count_le hS fr hω hω'
    rw [hdiv] at h
    exact h
  rw [hdiv]
  exact le_antisymm hCS_le (hN2 ▸ hfib)

/-! ## The trivial coset of `K` in `KW` is attained -/

/-- **§2 (7)+(8), conclusion.**  If the cross-orbit fibre has `|KW : K|` elements, then, among
its solutions, one has its `KW`-witness in `K = KW ∩ Ksub`: there are `x, y ∈ Q₀` and
`k ∈ Ksub` with `f(ω x) = (ω' y)^k`. -/
theorem exists_Ksub_witness_of_card {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω ω' : ↥Q} (hω : (ω : G) ∉ fr.Q0) (hω' : (ω' : G) ∉ fr.Q0)
    (hcard : Nat.card (ConjSet hS fr ω ω') = Nat.card fr.KW / Nat.card ↥(Ksub H t)) :
    ∃ x y : ↥Q, (x : G) ∈ fr.Q0 ∧ (y : G) ∈ fr.Q0 ∧ ∃ k : fr.KW, ((k : G) ∈ Ksub H t) ∧
      fcan hS.split (ω * x) = qconj hS.split
        (⟨(k : G), fr.KW_le k.2⟩ : ↥(twoPoint H t)) (ω' * y) := by
  classical
  let S := ConjSet hS fr ω ω'
  let W : S → fr.KW := fun s => Classical.choose s.2.2
  let Y : S → ↥Q := fun s => Classical.choose (Classical.choose_spec s.2.2)
  have hY : ∀ s : S, (Y s : G) ∈ fr.Q0 :=
    fun s => (Classical.choose_spec (Classical.choose_spec s.2.2)).1
  have hWeq : ∀ s : S, fcan hS.split (ω * s.1) =
      qconj hS.split (⟨(W s : G), fr.KW_le (W s).2⟩ : ↥(twoPoint H t)) (ω' * Y s) :=
    fun s => (Classical.choose_spec (Classical.choose_spec s.2.2)).2
  let K0 : Subgroup fr.KW := (Ksub H t).comap fr.KW.subtype
  have hKm : ∀ d : fr.KW, d ∈ K0 ↔ (d : G) ∈ Ksub H t := fun d => Subgroup.mem_comap
  have hK0card : Nat.card ↥K0 = Nat.card ↥(Ksub H t) := by
    rw [show K0 = (Ksub H t).comap fr.KW.subtype from rfl, Subgroup.comap_subtype]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := Ksub H t) (K := fr.KW) (fr.K_le)).toEquiv
  have hquot : Nat.card (fr.KW ⧸ K0) = Nat.card fr.KW / Nat.card ↥(Ksub H t) := by
    rw [← Subgroup.index_eq_card K0, Subgroup.index_eq_card_div K0, hK0card]
  have hcardS : Nat.card S = Nat.card (fr.KW ⧸ K0) := by
    rw [show S = ConjSet hS fr ω ω' from rfl, hcard, hquot]
  have hinj : Function.Injective (fun s : S => (QuotientGroup.mk (W s) : fr.KW ⧸ K0)) := by
    intro s1 s2 h
    by_contra hne
    have hne1 : (s1 : ↥Q) ≠ (s2 : ↥Q) := fun hh => hne (Subtype.ext hh)
    have hmem : (W s1)⁻¹ * (W s2) ∈ K0 := QuotientGroup.eq.mp h
    have hmemK : ((W s1 : fr.KW) : G)⁻¹ * ((W s2 : fr.KW) : G) ∈ Ksub H t := by
      have hh := (hKm ((W s1)⁻¹ * (W s2))).mp hmem
      simpa using hh
    exact coset_sep_KW hS fr hω hω' s1.2.1 s2.2.1 hne1 (hY s1) (hY s2)
      (hWeq s1) (hWeq s2) hmemK
  haveI : Finite (fr.KW ⧸ K0) :=
    Finite.of_surjective (QuotientGroup.mk (s := K0)) (QuotientGroup.mk_surjective (s := K0))
  have hsurj : Function.Surjective (fun s : S => (QuotientGroup.mk (W s) : fr.KW ⧸ K0)) :=
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, hcardS⟩).2
  obtain ⟨s, hs⟩ := hsurj (QuotientGroup.mk (1 : fr.KW))
  have hmem1 : (W s)⁻¹ ∈ K0 := by simpa using QuotientGroup.eq.mp hs
  have hWmem : (W s : fr.KW) ∈ K0 := by simpa using K0.inv_mem hmem1
  refine ⟨s.1, Y s, s.2.1, hY s, W s, (hKm (W s)).mp hWmem, ?_⟩
  exact hWeq s

/-! ## The cross-orbit datum -/

theorem cross_orbit_datum {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω₁ ω₂ : ↥Q} (h₁ : (ω₁ : G) ∉ fr.Q0) (h₂ : (ω₂ : G) ∉ fr.Q0)
    (horb : Multiplicative.toAdd (fr.bar ω₁) ∉
      Work.PSU3.StageB.orbE fr (Multiplicative.toAdd (fr.bar ω₂)))
    (hf₁ : Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split ω₁)) ∉
      Work.PSU3.StageB.orbE fr (Multiplicative.toAdd (fr.bar ω₂))) :
    ∃ X₁ : ↥(Work.PSU3.StageB.FX n), ∃ y₂ : ↥Q, ((y₂ : G) ∈ fr.Q0) ∧ ∃ k : fr.KW,
      ((k : G) ∈ Work.ThmF.Ksub H t) ∧
      Work.PSU3.StageB.fcan hS.split (ω₁ * Work.PSU3.StageB.zcQF fr X₁) =
        Work.PSU3.StageB.qconj hS.split
          (⟨(k : G), fr.KW_le k.2⟩ : ↥(Submission.Blueprint.twoPoint H t)) (ω₂ * y₂) := by
  classical
  have hcard := cross_orbit_card hS fr h₁ h₂ horb
  obtain ⟨x, y, hxQ0, hyQ0, k, hkKsub, heq⟩ :=
    exists_Ksub_witness_of_card hS fr h₁ h₂ hcard
  have hx1 : x ≠ 1 := by
    intro hxeq
    apply hf₁
    have hmem := orbE_of_cntSet hS fr (ω := ω₁) (ω' := ω₂) (x := x) (d := k) (y := y)
      hxQ0 hyQ0 heq
    simpa [hxeq] using hmem
  obtain ⟨X₁, hX₁⟩ := exists_zcQF_eq_of_mem_Q0 fr hxQ0 hx1
  refine ⟨X₁, y, hyQ0, k, hkKsub, ?_⟩
  rw [hX₁]
  exact heq

end Work.PSU3.StageB.Omega
