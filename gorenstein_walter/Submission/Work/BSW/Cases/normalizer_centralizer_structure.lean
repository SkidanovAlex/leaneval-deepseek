import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Api.card_centralizer_of_card_K_two
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Cases.bswK2Involution
import Submission.Work.BSW.Cases.K2NCS.Setup
import Submission.Work.BSW.Cases.K2NCS.mul_conj_dichotomy

set_option autoImplicit false

open scoped Pointwise

namespace Work.BSW.Cases.K2NCS

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}

/-- The classification of the elements of `N_G(C_G(t))` outside `C_G(t)`: they lie in the coset
`C_G(t) · g` or in `C_G(t) · g²`, where `g` is any element of `N_G(C_G(t)) \ C_G(t)` of order `3`.

Indeed `x` and `g` both act on the Klein four-group `C_G(t) = {1,t,s,ts}` by 3-cycles
(`Work.BSW.Cases.K2NCS.mul_conj_dichotomy`), and the two possible 3-cycles correspond to the two
cosets. -/
theorem exists_mul_of_mem_normalizer {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    (hdich : ActionDichotomy G t s) {g x : G}
    (hgN : g ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G))
    (hgC : g ∉ Subgroup.centralizer ({t} : Set G)) (hg3 : orderOf g = 3)
    (hxN : x ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G))
    (hxC : x ∉ Subgroup.centralizer ({t} : Set G)) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set G), x = c * g ∨ x = c * (g * g) := by
  have hg3m : g * g * g = 1 := by
    have h1 : g ^ 3 = 1 := by rw [← hg3]; exact pow_orderOf_eq_one g
    rwa [show g ^ 3 = g * g * g from by rw [pow_succ, pow_two]] at h1
  have hgg : g * (g * g) = 1 := by rw [← mul_assoc, hg3m]
  have hs := Work.BSW.s_mul_t_eq_t_mul_s h
  have hs2 := Work.BSW.s_mul_self h
  have ht2 := Work.BSW.t_mul_self h
  -- a helper: commutation with `t` is membership in `C_G(t)`
  have hxcomm : ∀ y : G, y * t * y⁻¹ = t → y ∈ Subgroup.centralizer ({t} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    calc t * y = (y * t * y⁻¹) * y := by rw [hy]
      _ = y * t := by group
  rcases hdich x hxN hxC with ⟨e1x, e2x⟩ | ⟨e1x, e2x⟩ <;>
    rcases hdich g hgN hgC with ⟨e1g, e2g⟩ | ⟨e1g, e2g⟩
  · -- `x` and `g` both act by `(t s ts)`
    refine ⟨x * g * g, hxcomm _ ?_, Or.inl ?_⟩
    · calc (x * g * g) * t * (x * g * g)⁻¹ = x * (g * g * t * (g * g)⁻¹) * x⁻¹ := by group
        _ = x * (t * s) * x⁻¹ := by
            rw [show g * g * t * (g * g)⁻¹ = t * s from by
              calc g * g * t * (g * g)⁻¹ = g * (g * t * g⁻¹) * g⁻¹ := by group
                _ = g * s * g⁻¹ := by rw [e1g]
                _ = t * s := e2g]
        _ = (x * t * x⁻¹) * (x * s * x⁻¹) := by group
        _ = s * (t * s) := by rw [e1x, e2x]
        _ = t := by rw [← mul_assoc, hs, mul_assoc, hs2, mul_one]
    · rw [show x * g * g * g = x from by rw [mul_assoc, mul_assoc, hgg, mul_one]]
  · -- `x` acts by `(t s ts)` and `g` by `(t ts s)`
    refine ⟨x * g, hxcomm _ ?_, Or.inr ?_⟩
    · calc (x * g) * t * (x * g)⁻¹ = x * (g * t * g⁻¹) * x⁻¹ := by group
        _ = x * (t * s) * x⁻¹ := by rw [e1g]
        _ = (x * t * x⁻¹) * (x * s * x⁻¹) := by group
        _ = s * (t * s) := by rw [e1x, e2x]
        _ = t := by rw [← mul_assoc, hs, mul_assoc, hs2, mul_one]
    · rw [show x * g * (g * g) = x from by rw [mul_assoc, hgg, mul_one]]
  · -- `x` acts by `(t ts s)` and `g` by `(t s ts)`
    refine ⟨x * g, hxcomm _ ?_, Or.inr ?_⟩
    · calc (x * g) * t * (x * g)⁻¹ = x * (g * t * g⁻¹) * x⁻¹ := by group
        _ = x * s * x⁻¹ := by rw [e1g]
        _ = t := e2x
    · rw [show x * g * (g * g) = x from by rw [mul_assoc, hgg, mul_one]]
  · -- `x` and `g` both act by `(t ts s)`
    refine ⟨x * g * g, hxcomm _ ?_, Or.inl ?_⟩
    · calc (x * g * g) * t * (x * g * g)⁻¹ = x * (g * g * t * (g * g)⁻¹) * x⁻¹ := by group
        _ = x * s * x⁻¹ := by
            rw [show g * g * t * (g * g)⁻¹ = s from by
              calc g * g * t * (g * g)⁻¹ = g * (g * t * g⁻¹) * g⁻¹ := by group
                _ = g * (t * s) * g⁻¹ := by rw [e1g]
                _ = (g * t * g⁻¹) * (g * s * g⁻¹) := by group
                _ = (t * s) * t := by rw [e1g, e2g]
                _ = s := by rw [mul_assoc, hs, ← mul_assoc, ht2, one_mul]]
        _ = t := e2x
    · rw [show x * g * g * g = x from by rw [mul_assoc, mul_assoc, hgg, mul_one]]

/-- Every element of the coset `C · g` (or `C · g²`) generates the same cyclic subgroup as a
conjugate `c g c⁻¹` of `g`, when `g` acts fixed-point-freely on the Klein four-group `C` of
order `4`.

Indeed the map `d ↦ d · (g d g⁻¹)⁻¹` is an injective (hence bijective) self-map of the four-element
set `C`, which shows that `C · g = {c g c⁻¹ : c ∈ C}`; and `x ∈ C · g²` gives
`x⁻¹ ∈ C · g`. -/
theorem exists_conj_zpowers_eq_mul {G : Type} [Group G] [Finite G] {C : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (C : Set G)) (hcard : Nat.card ↥C = 4)
    (hg3 : orderOf g = 3)
    (hfree : ∀ c ∈ C, g * c * g⁻¹ = c → c = 1)
    (hx : (∃ c ∈ C, x = c * g) ∨ (∃ c ∈ C, x = c * (g * g))) :
    ∃ c ∈ C, Subgroup.zpowers (c * g * c⁻¹) = Subgroup.zpowers x := by
  have hgmem : ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro c hc
    have h := hg
    rw [Subgroup.mem_normalizer_iff] at h
    exact (h c).mp hc
  have hinj : Function.Injective (fun d : ↥C => (⟨(d : G) * (g * (d : G) * g⁻¹)⁻¹,
      C.mul_mem d.2 (C.inv_mem (hgmem d d.2))⟩ : ↥C)) := by
    intro d e hde
    have h1 : (d : G) * (g * (d : G) * g⁻¹)⁻¹ = (e : G) * (g * (e : G) * g⁻¹)⁻¹ := by
      simpa using congrArg Subtype.val hde
    rw [show (g * (d : G) * g⁻¹)⁻¹ = g * (d : G)⁻¹ * g⁻¹ from by group,
        show (g * (e : G) * g⁻¹)⁻¹ = g * (e : G)⁻¹ * g⁻¹ from by group] at h1
    -- multiply `h1` on the left by `e⁻¹` and on the right by `g`
    have h2 : g * ((e : G)⁻¹ * (d : G)) * g⁻¹ = (e : G)⁻¹ * (d : G) := by
      have h := congrArg (fun w => (e : G)⁻¹ * w * g) h1
      have hA : (e : G)⁻¹ * ((d : G) * (g * (d : G)⁻¹ * g⁻¹)) * g =
          (e : G)⁻¹ * (d : G) * g * (d : G)⁻¹ := by group
      have hB : (e : G)⁻¹ * ((e : G) * (g * (e : G)⁻¹ * g⁻¹)) * g = g * (e : G)⁻¹ := by group
      rw [hA, hB] at h
      have h3 : (e : G)⁻¹ * (d : G) = g * ((e : G)⁻¹ * (d : G)) * g⁻¹ := by
        calc (e : G)⁻¹ * (d : G)
            = ((e : G)⁻¹ * (d : G) * g * (d : G)⁻¹) * (d : G) * g⁻¹ := by group
          _ = (g * (e : G)⁻¹) * (d : G) * g⁻¹ := by rw [h]
          _ = g * ((e : G)⁻¹ * (d : G)) * g⁻¹ := by group
      exact h3.symm
    have h3 : (e : G)⁻¹ * (d : G) ∈ C := C.mul_mem (C.inv_mem e.2) d.2
    have h4 : (e : G)⁻¹ * (d : G) = 1 := hfree _ h3 h2
    have h5 : (d : G) = (e : G) := by
      have h := congrArg (fun w => (e : G) * w) h4
      rw [mul_one] at h
      rw [show (e : G) * ((e : G)⁻¹ * (d : G)) = (d : G) from by group] at h
      exact h
    exact Subtype.ext h5
  have hsurj : Function.Surjective (fun d : ↥C => (⟨(d : G) * (g * (d : G) * g⁻¹)⁻¹,
      C.mul_mem d.2 (C.inv_mem (hgmem d d.2))⟩ : ↥C)) :=
    Finite.injective_iff_surjective.mp hinj
  have hcov : ∀ u ∈ C, ∃ d ∈ C, (d : G) * g * (d : G)⁻¹ = (u : G) * g := by
    intro u hu
    obtain ⟨d, hd⟩ := hsurj ⟨u, hu⟩
    refine ⟨d, d.2, ?_⟩
    have h : (d : G) * (g * (d : G) * g⁻¹)⁻¹ = (u : G) := by
      simpa using congrArg Subtype.val hd
    calc (d : G) * g * (d : G)⁻¹ = ((d : G) * (g * (d : G) * g⁻¹)⁻¹) * g := by group
      _ = (u : G) * g := by rw [h]
  have hinv : ∀ y : G, Subgroup.zpowers y⁻¹ = Subgroup.zpowers y := by
    intro y
    refine le_antisymm ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_zpowers_iff]
      exact ⟨-1, zpow_neg_one y⟩
    · rw [Subgroup.zpowers_le, Subgroup.mem_zpowers_iff]
      exact ⟨-1, by rw [zpow_neg_one, inv_inv]⟩
  have hgginv : (g * g)⁻¹ = g := by
    have h : g * g * g = 1 := by
      have h1 : g ^ 3 = 1 := by rw [← hg3]; exact pow_orderOf_eq_one g
      rwa [show g ^ 3 = g * g * g from by rw [pow_succ, pow_two]] at h1
    exact (eq_inv_of_mul_eq_one_right h).symm
  rcases hx with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
  · obtain ⟨d, hdC, hdle⟩ := hcov u hu
    refine ⟨d, hdC, ?_⟩
    show Subgroup.zpowers ((d : G) * g * (d : G)⁻¹) = Subgroup.zpowers ((u : G) * g)
    rw [hdle]
  · have hxu : (u * (g * g))⁻¹ = (g * u⁻¹ * g⁻¹) * g := by
      calc (u * (g * g))⁻¹ = (g * g)⁻¹ * u⁻¹ := by rw [mul_inv_rev]
        _ = g * u⁻¹ := by rw [hgginv]
        _ = g * u⁻¹ * g⁻¹ * g := by group
    obtain ⟨d, hdC, hdle⟩ := hcov (g * u⁻¹ * g⁻¹) (hgmem u⁻¹ (C.inv_mem hu))
    refine ⟨d, hdC, ?_⟩
    show Subgroup.zpowers ((d : G) * g * (d : G)⁻¹) = Subgroup.zpowers (u * (g * g))
    rw [hdle, ← hxu]
    exact hinv _

/-- `N_G(C_G(t))` has order `12`: it is the union of the three cosets `C`, `C g`, `C g²`. -/
theorem card_eq_twelve_of_cover {G : Type} [Group G] [Finite G] {N C : Subgroup G} {g : G}
    (hCN : C ≤ N) (hgN : g ∈ N)
    (hgnorm : Subgroup.zpowers g ≤ Subgroup.normalizer (C : Set G))
    (hgC : g ∉ C) (hg3 : orderOf g = 3)
    (hcardC : Nat.card ↥C = 4)
    (hcov : ∀ x ∈ N, x ∉ C → ∃ c ∈ C, x = c * g ∨ x = c * (g * g)) :
    Nat.card ↥N = 12 := by
  have hgg : g * g ∈ Subgroup.zpowers g :=
    Subgroup.mul_mem _ (Subgroup.mem_zpowers g) (Subgroup.mem_zpowers g)
  have hsup : N = C ⊔ Subgroup.zpowers g := by
    refine le_antisymm ?_ (sup_le hCN (Subgroup.zpowers_le.mpr hgN))
    intro x hx
    by_cases hxC : x ∈ C
    · exact Subgroup.mem_sup_left hxC
    · obtain ⟨c, hcC, hcase⟩ := hcov x hx hxC
      rcases hcase with hcase | hcase
      · exact hcase ▸ Subgroup.mul_mem_sup hcC (Subgroup.mem_zpowers g)
      · exact hcase ▸ Subgroup.mul_mem_sup hcC hgg
  have hinf : C ⊓ Subgroup.zpowers g = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h4 : Nat.card ↥(C ⊓ Subgroup.zpowers g) ∣ 4 := by
      rw [← hcardC]; exact Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card ↥(C ⊓ Subgroup.zpowers g) ∣ 3 := by
      rw [show (3 : ℕ) = Nat.card ↥(Subgroup.zpowers g) by rw [Nat.card_zpowers, hg3]]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hgd := Nat.dvd_gcd h4 h3
    rw [show Nat.gcd 4 3 = 1 by norm_num] at hgd
    exact Nat.dvd_one.mp hgd
  calc Nat.card ↥N = Nat.card ↥(C ⊔ Subgroup.zpowers g) := by rw [hsup]
    _ = Nat.card ↥C * Nat.card ↥(Subgroup.zpowers g) :=
        Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot hgnorm hinf
    _ = 4 * 3 := by rw [hcardC, Nat.card_zpowers, hg3]
    _ = 12 := by norm_num

end Work.BSW.Cases.K2NCS

namespace Work.BSW.Cases

open Subgroup Work.GW2
open scoped Pointwise

/-- `C_G(t)` in the `|K| = 2` case. -/
def K2C (G : Type) [Group G] (t : G) : Subgroup G := Subgroup.centralizer ({t} : Set G)

/-- `N_G(C_G(t))` in the `|K| = 2` case. -/
def K2N (G : Type) [Group G] (t : G) : Subgroup G :=
  Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}

/-- An element of `N_G(C_G(t))` outside `C_G(t)` has no fixed point among the nonidentity elements
of `C_G(t)`: its permutation of the three involutions `t`, `s`, `t * s` is a 3-cycle. -/
theorem mul_conj_ne_self (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    (hdich : Work.BSW.Cases.K2NCS.ActionDichotomy G t s) {x : G} (hxN : x ∈ K2N G t)
    (hxC : x ∉ K2C G t) {z : G} (hz : z ∈ K2C G t) (hz1 : z ≠ 1) :
    x * z * x⁻¹ ≠ z := by
  have hmem : z ∈ Subgroup.centralizer ({t} : Set G) := hz
  rcases (Work.BSW.Cases.K2NCS.mem_centralizer_iff_one_or h hk z).mp hmem with h1 | h1 | h1 | h1
  · exact absurd h1 hz1
  · rw [h1]
    intro hcon
    rcases hdich x hxN hxC with ⟨e1, _⟩ | ⟨e1, _⟩
    · simp only [e1] at hcon
      exact Work.BSW.s_notMem_K h (hcon ▸ Work.BSW.t_mem_K h)
    · simp only [e1] at hcon
      have h2 : t * s = t * 1 := by rw [mul_one]; exact hcon
      exact Work.BSW.s_ne_one h (mul_left_cancel h2)
  · rw [h1]
    intro hcon
    rcases hdich x hxN hxC with ⟨_, e2⟩ | ⟨_, e2⟩
    · simp only [e2] at hcon
      have h2 : t * s = 1 * s := by rw [one_mul]; exact hcon
      exact Work.BSW.t_ne_one h (mul_right_cancel h2)
    · simp only [e2] at hcon
      exact Work.BSW.s_notMem_K h (hcon ▸ Work.BSW.t_mem_K h)
  · rw [h1]
    intro hcon
    rcases hdich x hxN hxC with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have e3 : x * (t * s) * x⁻¹ = t := by
        calc x * (t * s) * x⁻¹ = (x * t * x⁻¹) * (x * s * x⁻¹) := by group
          _ = s * (t * s) := by rw [e1, e2]
          _ = t := by rw [← mul_assoc, Work.BSW.s_mul_t_eq_t_mul_s h, mul_assoc,
              Work.BSW.s_mul_self h, mul_one]
      simp only [e3] at hcon
      have h2 : t * 1 = t * s := by rw [mul_one]; exact hcon
      exact Work.BSW.s_ne_one h (mul_left_cancel h2).symm
    · have e3 : x * (t * s) * x⁻¹ = s := by
        calc x * (t * s) * x⁻¹ = (x * t * x⁻¹) * (x * s * x⁻¹) := by group
          _ = (t * s) * t := by rw [e1, e2]
          _ = s := by rw [mul_assoc, Work.BSW.s_mul_t_eq_t_mul_s h, ← mul_assoc,
              Work.BSW.t_mul_self h, one_mul]
      simp only [e3] at hcon
      have h2 : t * s = 1 * s := by rw [one_mul]; exact hcon.symm
      exact Work.BSW.t_ne_one h (mul_right_cancel h2)

/-- The map `c ↦ ⟨c g c⁻¹⟩` from `C` to the set of subgroups of order `3` of `N`. -/
def K2Phi {G : Type} [Group G] (N C : Subgroup G) (g : G) (hgN : g ∈ N) (hCN : C ≤ N)
    (hg3 : orderOf g = 3) : ↥C → {T : Subgroup G // T ≤ N ∧ Nat.card T = 3} :=
  fun c =>
    ⟨Subgroup.zpowers ((c : G) * g * (c : G)⁻¹),
      Subgroup.zpowers_le.mpr (N.mul_mem (N.mul_mem (hCN c.2) hgN) (N.inv_mem (hCN c.2))),
      by
        rw [Nat.card_zpowers]
        rw [show ((c : G) * g * (c : G)⁻¹) = (MulAut.conj (c : G)) g from by
          simp only [MulAut.conj_apply]]
        exact (MulEquiv.orderOf_eq (MulAut.conj (c : G)) g).trans hg3⟩

/-- No nonidentity element of `C_G(t)` normalizes `⟨g⟩`, for `g ∈ N_G(C_G(t)) \ C_G(t)` of
order `3`: if `c g c⁻¹ ∈ ⟨g⟩` then `c · (g c g⁻¹)⁻¹ ∈ C_G(t) ⊓ ⟨g⟩ = 1`, so that `g` centralizes
`c`, contradicting `Work.BSW.Cases.mul_conj_ne_self`. -/
theorem not_mem_normalizer_zpowers (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    (hdich : Work.BSW.Cases.K2NCS.ActionDichotomy G t s) {g : G} (hgN : g ∈ K2N G t)
    (hgC : g ∉ K2C G t) (hg3 : orderOf g = 3) {c : G} (hc : c ∈ K2C G t) (hc1 : c ≠ 1) :
    c ∉ Subgroup.normalizer ((Subgroup.zpowers g : Set G)) := by
  intro hcN
  have hC4 : Nat.card ↥(K2C G t) = 4 := by
    simpa [K2C] using Work.BSW.Api.card_centralizer_of_card_K_two h hk
  -- `g c g⁻¹ ∈ C`
  have hgcC : g * c * g⁻¹ ∈ K2C G t := by
    have h' : g ∈ Subgroup.normalizer ((K2C G t) : Set G) := hgN
    rw [Subgroup.mem_normalizer_iff] at h'
    exact (h' c).mp hc
  -- `c g c⁻¹ ∈ ⟨g⟩`
  have hmem : c * g * c⁻¹ ∈ Subgroup.zpowers g := by
    have h' := hcN
    rw [Subgroup.mem_normalizer_iff] at h'
    exact (h' g).mp (Subgroup.mem_zpowers g)
  have hginv : g⁻¹ ∈ Subgroup.zpowers g :=
    Subgroup.mem_zpowers_iff.mpr ⟨-1, zpow_neg_one g⟩
  -- `c * (g c g⁻¹)⁻¹ ∈ ⟨g⟩`
  have hA : c * (g * c * g⁻¹)⁻¹ ∈ Subgroup.zpowers g := by
    have h := (Subgroup.zpowers g).mul_mem hmem hginv
    rwa [show (c * g * c⁻¹) * g⁻¹ = c * (g * c * g⁻¹)⁻¹ from by group] at h
  have hAc : c * (g * c * g⁻¹)⁻¹ ∈ K2C G t :=
    (K2C G t).mul_mem hc ((K2C G t).inv_mem hgcC)
  have hdis : K2C G t ⊓ Subgroup.zpowers g = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h4 : Nat.card ↥(K2C G t ⊓ Subgroup.zpowers g) ∣ 4 := by
      rw [← hC4]; exact Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card ↥(K2C G t ⊓ Subgroup.zpowers g) ∣ 3 := by
      rw [show (3 : ℕ) = Nat.card ↥(Subgroup.zpowers g) by rw [Nat.card_zpowers, hg3]]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hgd := Nat.dvd_gcd h4 h3
    rw [show Nat.gcd 4 3 = 1 by norm_num] at hgd
    exact Nat.dvd_one.mp hgd
  have hA1 : c * (g * c * g⁻¹)⁻¹ = 1 := by
    have hmem' : c * (g * c * g⁻¹)⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hdis]
      exact ⟨hAc, hA⟩
    exact Subgroup.mem_bot.mp hmem'
  have hcomm : g * c * g⁻¹ = c := by
    have h := congrArg (fun w => w * (g * c * g⁻¹)) hA1
    rw [mul_assoc, inv_mul_cancel, mul_one, one_mul] at h
    exact h.symm
  exact mul_conj_ne_self h hk hdich hgN hgC hc hc1 hcomm

theorem normalizer_centralizer_structure {G : Type} [Group G] [Finite G] (t s : G) (K : Subgroup G)
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    (∀ x : G, x ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G) →
        x ∉ Subgroup.centralizer ({t} : Set G) → orderOf x = 3) ∧
    (∀ T : Subgroup G, T ≤ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G) →
        Nat.card T = 3 →
        Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G) ⊓
          Subgroup.normalizer (T : Set G) = T) ∧
    (Nat.card {T : Subgroup G // T ≤ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G) ∧
        Nat.card T = 3} = 4) := by
  change (∀ x : G, x ∈ K2N G t → x ∉ K2C G t → orderOf x = 3) ∧
    (∀ T : Subgroup G, T ≤ K2N G t → Nat.card T = 3 →
      K2N G t ⊓ Subgroup.normalizer (T : Set G) = T) ∧
    (Nat.card {T : Subgroup G // T ≤ K2N G t ∧ Nat.card T = 3} = 4)
  have hC4 : Nat.card ↥(K2C G t) = 4 := by
    simpa [K2C] using Work.BSW.Api.card_centralizer_of_card_K_two h hk
  have hmemC : ∀ x : G, x ∈ K2C G t ↔ x = 1 ∨ x = t ∨ x = s ∨ x = t * s := fun x => by
    simpa [K2C] using Work.BSW.Cases.K2NCS.mem_centralizer_iff_one_or h hk x
  have hcomm : ∀ a b : G, a ∈ K2C G t → b ∈ K2C G t → a * b = b * a := fun a b ha hb =>
    Work.BSW.Cases.K2NCS.mul_comm_of_mem_centralizer h hk ha hb
  have hdich : Work.BSW.Cases.K2NCS.ActionDichotomy G t s :=
    fun x hxN hxC => Work.BSW.Cases.K2NCS.mul_conj_dichotomy h hk hxN hxC
  have hC_le_N : K2C G t ≤ K2N G t := fun x hx => Subgroup.le_normalizer hx
  -- choose `g` with `g * s * g⁻¹ = t`; then `g⁻¹ ∈ N \ C`
  obtain ⟨g, hg⟩ := isConj_iff.mp (Work.BSW.involutions_conj h s (Work.BSW.orderOf_s h))
  have hgconj : g⁻¹ * t * g = s := by
    calc g⁻¹ * t * g = g⁻¹ * (g * s * g⁻¹) * g := by rw [hg]
      _ = s := by group
  have hCs : Nat.card ↥(Subgroup.centralizer ({s} : Set G)) = 4 :=
    (Work.BSW.Cases.bswK2Involution h hk (Work.BSW.orderOf_s h)).1
  have hCseq : K2C G t = Subgroup.centralizer ({s} : Set G) := by
    have hle : K2C G t ≤ Subgroup.centralizer ({s} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm x s hx ((hmemC s).mpr (Or.inr (Or.inr (Or.inl rfl))))
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hC4, hCs])
  have hmap2 : Subgroup.centralizer ({s} : Set G) = Subgroup.centralizer ({t} : Set G) := by
    simp only [← hCseq, K2C]
  have hg₀N : g⁻¹ ∈ K2N G t := by
    show g⁻¹ ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Subgroup.map (MulAut.conj g⁻¹).toMonoidHom (Subgroup.centralizer ({t} : Set G)) =
      Subgroup.centralizer ({t} : Set G)
    rw [Work.BSW.Cases.map_conj_centralizer (g⁻¹) t]
    rw [show g⁻¹ * t * (g⁻¹)⁻¹ = s from by rw [inv_inv]; exact hgconj]
    exact hmap2
  have hg₀C : g⁻¹ ∉ K2C G t := by
    intro hmem
    have h1 : g⁻¹ * t = t * g⁻¹ := Subgroup.mem_centralizer_singleton_iff.mp hmem
    have h2 : s = t := by
      rw [← hgconj]
      calc g⁻¹ * t * g = (t * g⁻¹) * g := by rw [h1]
        _ = t := by rw [mul_assoc, inv_mul_cancel, mul_one]
    exact Work.BSW.s_notMem_K h (h2 ▸ Work.BSW.t_mem_K h)
  -- the free action of `N \ C` on `C \ {1}`
  have hfree : ∀ v : G, v ∈ K2N G t → v ∉ K2C G t →
      ∀ c ∈ K2C G t, v * c * v⁻¹ = c → c = 1 := by
    intro v hvN hvC c hc' hcc
    by_contra hc1
    exact mul_conj_ne_self h hk hdich hvN hvC hc' hc1 hcc
  -- conjunct 1: every element of `N \ C` has order 3
  have horder3 : ∀ x : G, x ∈ K2N G t → x ∉ K2C G t → orderOf x = 3 := by
    intro x hxN hxC
    have hconj3 : x * (x * (x * t * x⁻¹) * x⁻¹) * x⁻¹ = t := by
      rcases hdich x hxN hxC with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have e3 : x * (x * t * x⁻¹) * x⁻¹ = t * s := by
          calc x * (x * t * x⁻¹) * x⁻¹ = x * s * x⁻¹ := by rw [e1]
            _ = t * s := e2
        calc x * (x * (x * t * x⁻¹) * x⁻¹) * x⁻¹ = x * (t * s) * x⁻¹ := by rw [e3]
          _ = (x * t * x⁻¹) * (x * s * x⁻¹) := by group
          _ = s * (t * s) := by rw [e1, e2]
          _ = t := by rw [← mul_assoc, Work.BSW.s_mul_t_eq_t_mul_s h, mul_assoc,
              Work.BSW.s_mul_self h, mul_one]
      · have e3 : x * (x * t * x⁻¹) * x⁻¹ = s := by
          calc x * (x * t * x⁻¹) * x⁻¹ = x * (t * s) * x⁻¹ := by rw [e1]
            _ = (x * t * x⁻¹) * (x * s * x⁻¹) := by group
            _ = (t * s) * t := by rw [e1, e2]
            _ = s := by rw [mul_assoc, Work.BSW.s_mul_t_eq_t_mul_s h, ← mul_assoc,
                Work.BSW.t_mul_self h, one_mul]
        calc x * (x * (x * t * x⁻¹) * x⁻¹) * x⁻¹ = x * s * x⁻¹ := by rw [e3]
          _ = t := e2
    have hpoweq : x * x * x * t * (x * x * x)⁻¹ = t :=
      (show x * (x * (x * t * x⁻¹) * x⁻¹) * x⁻¹ = x * x * x * t * (x * x * x)⁻¹ from by
        group).symm.trans hconj3
    have ht_comm : t * (x * x * x) = x * x * x * t := by
      have h1 : x * x * x * t * (x * x * x)⁻¹ = t * (x * x * x) * (x * x * x)⁻¹ := by
        rw [hpoweq]
        group
      exact (mul_right_cancel h1).symm
    have hmem3 : x * x * x ∈ K2C G t := by
      show x * x * x ∈ Subgroup.centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact ht_comm
    have h3eq : x * x * x = 1 := by
      by_contra hne
      rcases (hmemC (x * x * x)).mp hmem3 with h1 | h1 | h1 | h1
      · exact hne h1
      · have hcomm' : x * t * x⁻¹ = t := by
          calc x * t * x⁻¹ = x * (x * x * x) * x⁻¹ := by rw [← h1]
            _ = x * x * x := by group
            _ = t := h1
        exact (mul_conj_ne_self h hk hdich hxN hxC ((hmemC t).mpr (Or.inr (Or.inl rfl)))
          (Work.BSW.t_ne_one h)) hcomm'
      · have hcomm' : x * s * x⁻¹ = s := by
          calc x * s * x⁻¹ = x * (x * x * x) * x⁻¹ := by rw [← h1]
            _ = x * x * x := by group
            _ = s := h1
        exact (mul_conj_ne_self h hk hdich hxN hxC ((hmemC s).mpr (Or.inr (Or.inr (Or.inl rfl))))
          (Work.BSW.s_ne_one h)) hcomm'
      · have hts1 : t * s ≠ 1 := by
          intro hts
          have hst : s = t := by
            have h2 := congrArg (fun w => t * w) hts
            rw [← mul_assoc, Work.BSW.t_mul_self h, one_mul, mul_one] at h2
            exact h2
          exact Work.BSW.s_notMem_K h (hst ▸ Work.BSW.t_mem_K h)
        have hcomm' : x * (t * s) * x⁻¹ = t * s := by
          calc x * (t * s) * x⁻¹ = x * (x * x * x) * x⁻¹ := by rw [← h1]
            _ = x * x * x := by group
            _ = t * s := h1
        exact (mul_conj_ne_self h hk hdich hxN hxC
          ((hmemC (t * s)).mpr (Or.inr (Or.inr (Or.inr rfl)))) hts1) hcomm'
    have hx3eq1 : x ^ 3 = 1 := by
      calc x ^ 3 = x ^ 2 * x := pow_succ x 2
        _ = x * x * x := by rw [pow_two]
        _ = 1 := h3eq
    have hxne1 : x ≠ 1 := by
      intro hx1
      exact hxC (by rw [hx1]; exact (K2C G t).one_mem)
    have hdvd : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hx3eq1
    have hne1 : orderOf x ≠ 1 := fun h1 => hxne1 (orderOf_eq_one_iff.mp h1)
    have hne2 : orderOf x ≠ 2 := by intro h2; rw [h2] at hdvd; norm_num at hdvd
    have hle : orderOf x ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < orderOf x := orderOf_pos x
    omega
  -- the cover of `N` and `|N| = 12`
  have hcov : ∀ x : G, x ∈ K2N G t → x ∉ K2C G t →
      ∃ d ∈ K2C G t, x = d * g⁻¹ ∨ x = d * (g⁻¹ * g⁻¹) :=
    fun x hxN hxC => Work.BSW.Cases.K2NCS.exists_mul_of_mem_normalizer h hk hdich hg₀N hg₀C
      (horder3 g⁻¹ hg₀N hg₀C) hxN hxC
  have hg₀3 : orderOf g⁻¹ = 3 := horder3 g⁻¹ hg₀N hg₀C
  have hN12 : Nat.card ↥(K2N G t) = 12 :=
    Work.BSW.Cases.K2NCS.card_eq_twelve_of_cover hC_le_N hg₀N
      (Subgroup.zpowers_le.mpr hg₀N) hg₀C hg₀3 hC4 hcov
  -- the bijection `C ≃ {T ≤ N : |T| = 3}`
  have hΦsurj : Function.Surjective (K2Phi (K2N G t) (K2C G t) g⁻¹ hg₀N hC_le_N hg₀3) := by
    rintro ⟨T, hTN, hT3⟩
    have hne : T ≠ ⊥ := by
      intro hbot
      rw [hbot] at hT3
      have h1 : Nat.card ↥(⊥ : Subgroup G) = 1 := Subgroup.card_eq_one.mpr rfl
      rw [h1] at hT3
      norm_num at hT3
    obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hyT : (y : G) ∈ T := y.2
    have hyne : (y : G) ≠ 1 := fun hc => hy1 (Subtype.ext hc)
    have hy3 : orderOf (y : G) = 3 := by
      have hdvd : orderOf (y : G) ∣ Nat.card ↥T := by
        rw [← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hyT)
      rw [hT3] at hdvd
      have hne1 : orderOf (y : G) ≠ 1 := fun h1 => hyne (orderOf_eq_one_iff.mp h1)
      have hne2 : orderOf (y : G) ≠ 2 := by intro h2; rw [h2] at hdvd; norm_num at hdvd
      have hle : orderOf (y : G) ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < orderOf (y : G) := orderOf_pos _
      omega
    have hTeq : T = Subgroup.zpowers (y : G) :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyT)
        (by rw [Nat.card_zpowers, hy3, hT3])).symm
    have hyN : (y : G) ∈ K2N G t := hTN hyT
    have hyC : (y : G) ∉ K2C G t := by
      intro hmem
      have hCT : K2C G t ⊓ T = ⊥ := by
        rw [← Subgroup.card_eq_one]
        have h4 : Nat.card ↥(K2C G t ⊓ T) ∣ 4 := by
          rw [← hC4]; exact Subgroup.card_dvd_of_le inf_le_left
        have h3 : Nat.card ↥(K2C G t ⊓ T) ∣ 3 := by
          rw [← hT3]; exact Subgroup.card_dvd_of_le inf_le_right
        have hgd := Nat.dvd_gcd h4 h3
        rw [show Nat.gcd 4 3 = 1 by norm_num] at hgd
        exact Nat.dvd_one.mp hgd
      have hmem' : (y : G) ∈ (⊥ : Subgroup G) := by
        rw [← hCT]
        exact ⟨hmem, hyT⟩
      exact hyne (Subgroup.mem_bot.mp hmem')
    obtain ⟨c', hc'C, hcase⟩ :=
      Work.BSW.Cases.K2NCS.exists_mul_of_mem_normalizer h hk hdich hg₀N hg₀C hg₀3 hyN hyC
    obtain ⟨d, hdC, hsub⟩ := Work.BSW.Cases.K2NCS.exists_conj_zpowers_eq_mul hg₀N hC4 hg₀3
      (hfree g⁻¹ hg₀N hg₀C)
      (by
        rcases hcase with hcase | hcase
        · exact Or.inl ⟨c', hc'C, hcase⟩
        · exact Or.inr ⟨c', hc'C, hcase⟩)
    refine ⟨⟨d, hdC⟩, ?_⟩
    apply Subtype.ext
    show Subgroup.zpowers (d * g⁻¹ * d⁻¹) = T
    rw [hsub]
    simp only [hTeq]
  have hΦinj : Function.Injective (K2Phi (K2N G t) (K2C G t) g⁻¹ hg₀N hC_le_N hg₀3) := by
    rintro ⟨a, haC⟩ ⟨b, hbC⟩ hab
    have hsub : Subgroup.zpowers ((a : G) * g⁻¹ * (a : G)⁻¹) =
        Subgroup.zpowers ((b : G) * g⁻¹ * (b : G)⁻¹) := by
      have h := congrArg Subtype.val hab
      simpa only [K2Phi] using h
    have huC : b⁻¹ * a ∈ K2C G t := (K2C G t).mul_mem ((K2C G t).inv_mem hbC) haC
    have huN : b⁻¹ * a ∈ Subgroup.normalizer ((Subgroup.zpowers g⁻¹ : Set G)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change Subgroup.map (MulAut.conj (b⁻¹ * (a : G))).toMonoidHom (Subgroup.zpowers g⁻¹) =
        Subgroup.zpowers g⁻¹
      -- conjugate the equality `hsub` by `b⁻¹`
      have hmap := congrArg (fun H : Subgroup G => H.map (MulAut.conj (b : G)⁻¹).toMonoidHom)
        hsub
      rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
      have e1 : (MulAut.conj (b : G)⁻¹).toMonoidHom ((a : G) * g⁻¹ * (a : G)⁻¹) =
          (b⁻¹ * (a : G)) * g⁻¹ * (b⁻¹ * (a : G))⁻¹ := by
        show (MulAut.conj (b : G)⁻¹) ((a : G) * g⁻¹ * (a : G)⁻¹) = _
        rw [MulAut.conj_apply]
        group
      have e2 : (MulAut.conj (b : G)⁻¹).toMonoidHom ((b : G) * g⁻¹ * (b : G)⁻¹) = g⁻¹ := by
        show (MulAut.conj (b : G)⁻¹) ((b : G) * g⁻¹ * (b : G)⁻¹) = _
        rw [MulAut.conj_apply]
        group
      rw [e1, e2] at hmap
      rw [MonoidHom.map_zpowers]
      have e3 : (MulAut.conj (b⁻¹ * (a : G))).toMonoidHom g⁻¹ =
          (b⁻¹ * (a : G)) * g⁻¹ * (b⁻¹ * (a : G))⁻¹ := by
        show (MulAut.conj (b⁻¹ * (a : G))) g⁻¹ = _
        rw [MulAut.conj_apply]
      rw [e3]
      exact hmap
    have hu1 : b⁻¹ * a = 1 := by
      by_contra hne
      exact
        (Work.BSW.Cases.not_mem_normalizer_zpowers h hk hdich hg₀N hg₀C hg₀3 huC hne) huN
    have hba : (a : G) = (b : G) := by
      have h := congrArg (fun w => (b : G) * w) hu1
      rw [mul_one] at h
      rw [show (b : G) * (b⁻¹ * (a : G)) = (a : G) from by group] at h
      exact h
    exact Subtype.ext hba
  have hcard := Nat.card_congr
    (Equiv.ofBijective (K2Phi (K2N G t) (K2C G t) g⁻¹ hg₀N hC_le_N hg₀3) ⟨hΦinj, hΦsurj⟩)
  rw [hC4] at hcard
  -- conjunct 2: order-`3` subgroups of `N` are self-normalizing
  have hnormT : ∀ T : Subgroup G, T ≤ K2N G t → Nat.card T = 3 →
      K2N G t ⊓ Subgroup.normalizer (T : Set G) = T := by
    intro T hTN hT3
    have hstab : K2C G t ⊓ Subgroup.normalizer (T : Set G) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      rintro z ⟨hzC, hzT⟩
      by_contra hz1
      -- `T` is a conjugate of `⟨g⁻¹⟩`, and that conjugate also generates an order-`3` subgroup
      obtain ⟨c, hc⟩ := hΦsurj ⟨T, hTN, hT3⟩
      have hcval : T = Subgroup.zpowers ((c : G) * g⁻¹ * (c : G)⁻¹) := by
        simpa only [K2Phi] using (congrArg Subtype.val hc).symm
      have hcN : (c : G) * g⁻¹ * (c : G)⁻¹ ∈ K2N G t :=
        (K2N G t).mul_mem ((K2N G t).mul_mem (hC_le_N c.2) hg₀N)
          ((K2N G t).inv_mem (hC_le_N c.2))
      have hcC : (c : G) * g⁻¹ * (c : G)⁻¹ ∉ K2C G t := by
        intro hmem
        refine hg₀C ?_
        have h : (c : G)⁻¹ * ((c : G) * g⁻¹ * (c : G)⁻¹) * (c : G) = g⁻¹ := by group
        rw [← h]
        exact (K2C G t).mul_mem ((K2C G t).mul_mem ((K2C G t).inv_mem c.2) hmem) c.2
      have hc3 : orderOf ((c : G) * g⁻¹ * (c : G)⁻¹) = 3 := by
        rw [show (c : G) * g⁻¹ * (c : G)⁻¹ = (MulAut.conj (c : G)) g⁻¹ from by
          simp only [MulAut.conj_apply]]
        exact (MulEquiv.orderOf_eq (MulAut.conj (c : G)) g⁻¹).trans hg₀3
      rw [hcval] at hzT
      exact (Work.BSW.Cases.not_mem_normalizer_zpowers h hk hdich hcN hcC hc3 hzC hz1) hzT
    have hbound : Nat.card ↥(K2N G t ⊓ Subgroup.normalizer (T : Set G)) ≤ 3 := by
      have hinj : Function.Injective
          (fun p : ↥(K2C G t) × ↥(K2N G t ⊓ Subgroup.normalizer (T : Set G)) =>
            (⟨(p.1 : G) * (p.2 : G),
              (K2N G t).mul_mem (hC_le_N p.1.2) p.2.2.1⟩ : ↥(K2N G t))) := by
        rintro ⟨a, b⟩ ⟨a', b'⟩ hab
        have hab' : (a : G) * (b : G) = (a' : G) * (b' : G) := by
          simpa using congrArg Subtype.val hab
        have key : (a' : G)⁻¹ * (a : G) = (b' : G) * (b : G)⁻¹ := by
          calc (a' : G)⁻¹ * (a : G)
              = (a' : G)⁻¹ * ((a : G) * (b : G)) * (b : G)⁻¹ := by group
            _ = (a' : G)⁻¹ * ((a' : G) * (b' : G)) * (b : G)⁻¹ := by rw [hab']
            _ = (b' : G) * (b : G)⁻¹ := by group
        have hmem : (a' : G)⁻¹ * (a : G) ∈ K2C G t ⊓ Subgroup.normalizer (T : Set G) := by
          refine ⟨(K2C G t).mul_mem ((K2C G t).inv_mem a'.2) a.2, ?_⟩
          rw [key]
          exact (Subgroup.normalizer (T : Set G)).mul_mem b'.2.2
            ((Subgroup.normalizer (T : Set G)).inv_mem b.2.2)
        have h1 : (a' : G)⁻¹ * (a : G) = 1 := by
          have h := hmem
          rw [hstab] at h
          exact Subgroup.mem_bot.mp h
        have haeq : (a : G) = (a' : G) := by
          have h : (a' : G) * ((a' : G)⁻¹ * (a : G)) = (a' : G) * 1 := by rw [h1]
          rw [show (a' : G) * ((a' : G)⁻¹ * (a : G)) = (a : G) from by group, mul_one] at h
          exact h
        have hbeq : (b : G) = (b' : G) := by
          have h2 : (b' : G) * (b : G)⁻¹ = 1 := by rw [← key]; exact h1
          have h : ((b' : G) * (b : G)⁻¹) * (b : G) = 1 * (b : G) := by rw [h2]
          rw [one_mul, show ((b' : G) * (b : G)⁻¹) * (b : G) = (b' : G) from by group] at h
          exact h.symm
        exact Prod.ext (Subtype.ext haeq) (Subtype.ext hbeq)
      have hcard' := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_prod, hC4, hN12] at hcard'
      omega
    have hle : T ≤ K2N G t ⊓ Subgroup.normalizer (T : Set G) :=
      fun x hx => ⟨hTN hx, Subgroup.le_normalizer hx⟩
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hT3]; exact hbound)).symm
  exact ⟨horder3, hnormT, hcard.symm⟩

end Work.BSW.Cases
