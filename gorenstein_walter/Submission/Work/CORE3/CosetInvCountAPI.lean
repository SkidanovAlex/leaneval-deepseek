import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.SumMulBCount

/-!
# CORE3: the elementary API of `cosetInvCount` (Bender 1981 §3)

`cosetInvCount Hh g` is the number of involutions in the left coset `g Hh`
(`Submission/Work/BSW/Defs.lean`), and `bCount Hh n` counts the nontrivial cosets containing
exactly `n` involutions.  This file collects the elementary facts about `cosetInvCount` that the
§3 leaves `Work.CORE3.Case1bOne` and `Work.CORE3.Case1bEightNine` need:

* `mk_eq_iff_leftRel`, `mk_eq_one_iff` : membership in a coset, and the trivial coset, read off
  from `Quotient.out`;
* `cosetInvCount_congr` : `cosetInvCount` only depends on the coset (translation invariance);
* `cosetInvCount_conj` : invariance under conjugation by an element of `N_G(Hh)` (the cosets of
  `Hh` are permuted by `N_G(Hh)`);
* `exists_forall_of_cosetInvCount_eq_one`, `cosetInvCount_eq_one_of` : `cosetInvCount Hh g = 1`
  as a `∃!` statement about the involutions of the coset;
* `two_le_cosetInvCount_of` : two distinct involutions in a coset give `2 ≤ cosetInvCount`;
* `exists_mem_zpowers_orderOf_eq_two` : a nontrivial element of even order has a power of order
  `2` inside its cyclic subgroup (the group-theoretic input of the fixed-point-freeness
  argument: `s ∈ S` nontrivial has an involution `w ∈ ⟨s⟩ ≤ S`).
-/

namespace Work.CORE3

open Subgroup
open Work.GW2

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

section Basic

variable {G : Type*} [Group G]

/-- Membership in the left coset `c` of `Hh`, read through the chosen representative
`Quotient.out c`: `x ∈ c` iff `(Quotient.out c)⁻¹ * x ∈ Hh`. -/
theorem mk_eq_iff_leftRel (Hh : Subgroup G) (c : G ⧸ Hh) (x : G) :
    QuotientGroup.mk x = c ↔ (Quotient.out c)⁻¹ * x ∈ Hh := by
  conv_lhs => rw [← Quotient.out_eq c]
  rw [eq_comm, QuotientGroup.eq]

/-- The trivial coset of `Hh` is `Hh` itself. -/
theorem mk_eq_one_iff (Hh : Subgroup G) (x : G) :
    QuotientGroup.mk x = ((1 : G) : G ⧸ Hh) ↔ x ∈ Hh := by
  rw [QuotientGroup.eq]
  simp

/-- **Translation invariance.**  `cosetInvCount` only depends on the coset: if `h` is in the
coset `g Hh` (i.e. `g⁻¹ * h ∈ Hh`) then the two cosets contain the same involutions. -/
theorem cosetInvCount_congr (Hh : Subgroup G) {g h : G} (hgh : g⁻¹ * h ∈ Hh) :
    cosetInvCount Hh g = cosetInvCount Hh h := by
  have hset : {x : G | orderOf x = 2 ∧ g⁻¹ * x ∈ Hh}
      = {x : G | orderOf x = 2 ∧ h⁻¹ * x ∈ Hh} := by
    ext x
    constructor
    · rintro ⟨hx2, hx⟩
      refine ⟨hx2, ?_⟩
      rw [show h⁻¹ * x = (g⁻¹ * h)⁻¹ * (g⁻¹ * x) from by group]
      exact Hh.mul_mem (Hh.inv_mem hgh) hx
    · rintro ⟨hx2, hx⟩
      refine ⟨hx2, ?_⟩
      rw [show g⁻¹ * x = (g⁻¹ * h) * (h⁻¹ * x) from by group]
      exact Hh.mul_mem hgh hx
  show ({x : G | orderOf x = 2 ∧ g⁻¹ * x ∈ Hh} : Set G).ncard
      = ({x : G | orderOf x = 2 ∧ h⁻¹ * x ∈ Hh} : Set G).ncard
  rw [hset]

/-- **Conjugation invariance.**  Conjugation by an element of the normalizer of `Hh` permutes
the cosets of `Hh` and preserves the number of involutions in each. -/
theorem cosetInvCount_conj (Hh : Subgroup G) {s : G}
    (hs : s ∈ Subgroup.normalizer (Hh : Set G)) (g : G) :
    cosetInvCount Hh (s * g * s⁻¹) = cosetInvCount Hh g := by
  -- conjugation by `s⁻¹` moves the coset of `s * g * s⁻¹` back to the coset of `g`
  have hiff : ∀ z : G, s⁻¹ * z * s ∈ Hh ↔ z ∈ Hh := by
    intro z
    rw [Subgroup.mem_normalizer_iff.mp hs (s⁻¹ * z * s)]
    rw [show s * (s⁻¹ * z * s) * s⁻¹ = z from by group]
  have hset : (fun x : G => s * x * s⁻¹) '' {x : G | orderOf x = 2 ∧ g⁻¹ * x ∈ Hh}
      = {y : G | orderOf y = 2 ∧ (s * g * s⁻¹)⁻¹ * y ∈ Hh} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx2, hx⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · change orderOf (s * x * s⁻¹) = 2
        rw [← MulAut.conj_apply s x, MulEquiv.orderOf_eq]
        exact hx2
      · rw [show (s * g * s⁻¹)⁻¹ * (s * x * s⁻¹) = s * (g⁻¹ * x) * s⁻¹ from by group]
        exact (Subgroup.mem_normalizer_iff.mp hs (g⁻¹ * x)).mp hx
    · rintro ⟨hy2, hy⟩
      refine ⟨s⁻¹ * y * s, ⟨?_, ?_⟩, by group⟩
      · have hconj : s⁻¹ * y * s = MulAut.conj s⁻¹ y := by
          rw [MulAut.conj_apply]; group
        rw [hconj, MulEquiv.orderOf_eq]
        exact hy2
      · have h1 : s⁻¹ * ((s * g * s⁻¹)⁻¹ * y) * s ∈ Hh :=
          (hiff ((s * g * s⁻¹)⁻¹ * y)).mpr hy
        rwa [show s⁻¹ * ((s * g * s⁻¹)⁻¹ * y) * s = g⁻¹ * (s⁻¹ * y * s) from by group] at h1
  show ({y : G | orderOf y = 2 ∧ (s * g * s⁻¹)⁻¹ * y ∈ Hh} : Set G).ncard
      = ({x : G | orderOf x = 2 ∧ g⁻¹ * x ∈ Hh} : Set G).ncard
  rw [← hset, Set.ncard_image_of_injective _ (fun a b hab => by
    have h := congrArg (fun z : G => s⁻¹ * z * s) hab
    simpa [mul_assoc] using h)]

/-- If the coset of `g` contains exactly one involution, that involution is unique. -/
theorem exists_forall_of_cosetInvCount_eq_one (Hh : Subgroup G) {g : G}
    (h : cosetInvCount Hh g = 1) :
    ∃ x : G, orderOf x = 2 ∧ g⁻¹ * x ∈ Hh ∧
      ∀ y : G, orderOf y = 2 → g⁻¹ * y ∈ Hh → y = x := by
  have h1 : ({x : G | orderOf x = 2 ∧ g⁻¹ * x ∈ Hh} : Set G).ncard = 1 := h
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp h1
  have hxmem : x ∈ ({x : G | orderOf x = 2 ∧ g⁻¹ * x ∈ Hh} : Set G) := by
    rw [hx]; exact Set.mem_singleton_iff.mpr rfl
  refine ⟨x, hxmem.1, hxmem.2, ?_⟩
  intro y hy2 hyg
  have hymem : y ∈ ({x : G | orderOf x = 2 ∧ g⁻¹ * x ∈ Hh} : Set G) := ⟨hy2, hyg⟩
  rw [hx] at hymem
  exact Set.mem_singleton_iff.mp hymem

/-- Conversely: a unique involution in the coset of `g` gives `cosetInvCount Hh g = 1`. -/
theorem cosetInvCount_eq_one_of (Hh : Subgroup G) {g x : G} (hx2 : orderOf x = 2)
    (hxg : g⁻¹ * x ∈ Hh) (huniq : ∀ y : G, orderOf y = 2 → g⁻¹ * y ∈ Hh → y = x) :
    cosetInvCount Hh g = 1 := by
  have hset : {y : G | orderOf y = 2 ∧ g⁻¹ * y ∈ Hh} = ({x} : Set G) := by
    ext y
    constructor
    · rintro ⟨hy2, hyg⟩
      exact Set.mem_singleton_iff.mpr (huniq y hy2 hyg)
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨hx2, hxg⟩
  show ({y : G | orderOf y = 2 ∧ g⁻¹ * y ∈ Hh} : Set G).ncard = 1
  rw [hset, Set.ncard_singleton]

/-- Two distinct involutions in the coset of `g` force `cosetInvCount Hh g ≥ 2`. -/
theorem two_le_cosetInvCount_of {G : Type*} [Group G] [Finite G] (Hh : Subgroup G) {g x y : G}
    (hx2 : orderOf x = 2) (hxg : g⁻¹ * x ∈ Hh) (hy2 : orderOf y = 2) (hyg : g⁻¹ * y ∈ Hh)
    (hxy : x ≠ y) : 2 ≤ cosetInvCount Hh g := by
  have hsub : ({x, y} : Set G) ⊆ {z : G | orderOf z = 2 ∧ g⁻¹ * z ∈ Hh} := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with h | h
    · subst h; exact ⟨hx2, hxg⟩
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact ⟨hy2, hyg⟩
  have hle : ({x, y} : Set G).ncard ≤
      ({z : G | orderOf z = 2 ∧ g⁻¹ * z ∈ Hh} : Set G).ncard := Set.ncard_le_ncard hsub
  rw [Set.ncard_pair hxy] at hle
  exact hle

end Basic

/-- A nontrivial element of even order has a power of order `2` inside its cyclic subgroup:
if `orderOf s = 2 * n` then `s ^ n` has order `2`.  (In particular every nontrivial element of a
`2`-group has an involution in the cyclic subgroup it generates.) -/
theorem exists_mem_zpowers_orderOf_eq_two {H : Type*} [Group H] [Finite H] {s : H}
    (hs : s ≠ 1) (heven : 2 ∣ orderOf s) :
    ∃ w : H, w ∈ Subgroup.zpowers s ∧ orderOf w = 2 := by
  obtain ⟨n, hn⟩ := heven
  have hnpos : 0 < n := by
    have h := orderOf_pos s
    omega
  refine ⟨s ^ n, ?_, ?_⟩
  · rw [Subgroup.mem_zpowers_iff]
    exact ⟨(n : ℤ), by rw [zpow_natCast]⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← pow_mul, show n * 2 = 2 * n from by ring, ← hn, pow_orderOf_eq_one]
    · intro h1
      have hdvd : orderOf s ∣ n := orderOf_dvd_iff_pow_eq_one.mpr h1
      have hle : orderOf s ≤ n := Nat.le_of_dvd hnpos hdvd
      omega

end Work.CORE3
