/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Bender 1974 §3.1: the core of the centralizer of an element with odd centralizer

Bender, *The Brauer–Suzuki–Wall theorem*, Illinois J. Math. **18** (1974) 229–235, §3.1(i),(iv)
(`REFS/vision/bender1974_bsw/p0004.md`–`p0005.md`).

`Work.BSW.Cases.S31core` states: for `x` whose centralizer `F = C_G(x)` has odd order and an
involution `u` inverting `x`, the centralizer `F` is abelian, has order `i(x) = Work.BSW.iFn G x`,
and every non-identity element of `F` has centralizer `F`.

The proof follows the sketch in the statement of `S31core`:

1. `x` commutes with no involution (`Work.BSW.Cases.not_mem_centralizer_of_involution_of_odd`).
2. Hence `C_F(u) = 1`: if `1 ≠ c ∈ F` commutes with `u`, then `c ∈ C_G(u)` and the interface lemma
   `Work.BSW.Cases.isInvolution_or_centralizer_le_of_mem_centralizer` gives either `orderOf c = 2`
   (then `c` is an involution commuting with `x`) or `C_G(c) ≤ C_G(u) ∋ x` — both contradict 1.
3. The general fixed-point-free-involution theorem
   `Work.BSW.Cases.K4.inverts_of_fixedPointFree_involution` (already proved in the workspace)
   applied to `F` and `u` gives that `u` inverts every element of `F`, and that `F` is abelian.
4. The involutions inverting `x` are exactly the coset `uF`, whence `i(x) = |F|`.
5. For `a ∈ F^#`: any involution `v` commuting with `a` gives, again by the interface lemma (as
   `a ≠ 1`), either `orderOf a = 2` or `C_G(a) ≤ C_G(v) ∋ x` — both contradict 1.  So the
   hypotheses `hnin` hold with `F` replaced by `C_G(a)` (which is normalised by `u`, since `u`
   inverts `a`), and step 3 with `F` replaced by `C_G(a)` shows that `C_G(a)` is abelian; as
   `x ∈ C_G(a)`, this gives `C_G(a) ≤ C_G(x) = F`, whence `C_G(a) = F`.
-/
import Mathlib
import Submission.Work.BSW.Cases.bswCompletionBase
import Submission.Work.BSW.Cases.K4.inverts_of_fixedPointFree_involution
import Submission.Work.BSW.Char.iFn_t
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Api.ncard_involutions_eq_index

namespace Work.BSW.Cases

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}

section Conjugation

/-- If `w` is an involution with `w * y * w = y⁻¹`, then `w * y = y⁻¹ * w`. -/
theorem mul_left_conj_eq {G : Type} [Group G] {y w : G} (hww : w * w = 1)
    (hwinv : w * y * w = y⁻¹) : w * y = y⁻¹ * w := by
  calc w * y = w * y * (w * w) := by rw [hww, mul_one]
    _ = (w * y * w) * w := by group
    _ = y⁻¹ * w := by rw [hwinv]

/-- If `w` is an involution with `w * y * w = y⁻¹`, then `y * w = w * y⁻¹`. -/
theorem mul_right_conj_eq {G : Type} [Group G] {y w : G} (hww : w * w = 1)
    (hwinv : w * y * w = y⁻¹) : y * w = w * y⁻¹ := by
  calc y * w = (w * w) * y * w := by rw [hww, one_mul]
    _ = w * (w * y * w) := by group
    _ = w * y⁻¹ := by rw [hwinv]

/-- If `w` is an involution with `w * y * w = y⁻¹`, then `w * y⁻¹ = y * w`. -/
theorem mul_inv_conj_eq {G : Type} [Group G] {y w : G} (hww : w * w = 1)
    (hwinv : w * y * w = y⁻¹) : w * y⁻¹ = y * w := by
  have hwyiw : w * y⁻¹ * w = y := by
    calc w * y⁻¹ * w = (w * y * w)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_left hww]
          group
      _ = (y⁻¹)⁻¹ := by rw [hwinv]
      _ = y := inv_inv y
  calc w * y⁻¹ = w * y⁻¹ * (w * w) := by rw [hww, mul_one]
    _ = (w * y⁻¹ * w) * w := by group
    _ = y * w := by rw [hwyiw]

end Conjugation

/-- **Bender §3.1(i) engine.**  Let `y` be an element of a finite group `G` satisfying Bender's
hypotheses `BSWHyps2`, let `w` be an involution inverting `y`, and suppose that no involution of
`G` commutes with `y`.  Then `C_G(y)` has no non-trivial element commuting with `w`, `w` inverts
every element of `C_G(y)`, and `C_G(y)` is abelian. -/
theorem centralizer_of_inverting_involution (h : BSWHyps2 G t s K) {y w : G}
    (hw : orderOf w = 2) (hwinv : w⁻¹ * y * w = y⁻¹)
    (hnin : ∀ v : G, orderOf v = 2 → y ∉ Subgroup.centralizer ({v} : Set G)) :
    (∀ c ∈ Subgroup.centralizer ({y} : Set G), c * w = w * c → c = 1) ∧
      (∀ c ∈ Subgroup.centralizer ({y} : Set G), w * c * w = c⁻¹) ∧
        IsMulCommutative ↥(Subgroup.centralizer ({y} : Set G)) := by
  have hww : w * w = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two hw
  have hwinv' : w * y * w = y⁻¹ := by rw [← hwinv, inv_eq_of_mul_eq_one_left hww]
  have hwy : w * y = y⁻¹ * w := mul_left_conj_eq hww hwinv'
  have hyw : y * w = w * y⁻¹ := mul_right_conj_eq hww hwinv'
  have hwyi : w * y⁻¹ = y * w := mul_inv_conj_eq hww hwinv'
  -- step 2: `C_F(w) = 1`
  have hker : ∀ c ∈ Subgroup.centralizer ({y} : Set G), c * w = w * c → c = 1 := by
    intro c hc hcw
    by_contra hc1
    have hcw' : c ∈ Subgroup.centralizer ({w} : Set G) := by
      rwa [Subgroup.mem_centralizer_singleton_iff]
    have hyc : y ∈ Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      exact hc.symm
    rcases isInvolution_or_centralizer_le_of_mem_centralizer h hw hcw' hc1 with h2 | hle
    · exact (hnin c h2) hyc
    · exact (hnin w hw) (hle hyc)
  -- `w` normalises `F = C_G(y)`
  have hmem : ∀ c ∈ Subgroup.centralizer ({y} : Set G),
      w * c * w⁻¹ ∈ Subgroup.centralizer ({y} : Set G) := by
    intro c hc
    rw [inv_eq_of_mul_eq_one_left hww]
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have hcyi : c * y⁻¹ = y⁻¹ * c := (Commute.inv_right (show Commute c y from hc)).eq
    calc w * c * w * y = w * c * (w * y) := by group
      _ = w * c * (y⁻¹ * w) := by rw [hwy]
      _ = w * (c * y⁻¹) * w := by group
      _ = w * (y⁻¹ * c) * w := by rw [hcyi]
      _ = w * y⁻¹ * c * w := by group
      _ = y * w * c * w := by rw [hwyi]
      _ = y * (w * c * w) := by group
  have hnorm : w ∈ Subgroup.normalizer
      (Subgroup.centralizer ({y} : Set G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hmem x
    · intro hx
      have h2 : w * (w * x * w⁻¹) * w⁻¹ ∈ Subgroup.centralizer ({y} : Set G) := hmem _ hx
      have he : w * (w * x * w⁻¹) * w⁻¹ = x := by
        rw [inv_eq_of_mul_eq_one_left hww]
        calc w * (w * x * w) * w = (w * w) * x * (w * w) := by group
          _ = x := by rw [hww, one_mul, mul_one]
      rwa [he] at h2
  have hfix : ∀ a ∈ Subgroup.centralizer ({y} : Set G), w * a * w⁻¹ = a → a = 1 := by
    intro a ha hconj
    have hwa : w * a = a * w := by
      calc w * a = w * a * (w⁻¹ * w) := by rw [inv_mul_cancel, mul_one]
        _ = (w * a * w⁻¹) * w := by group
        _ = a * w := by rw [hconj]
    exact hker a ha hwa.symm
  obtain ⟨hab, hinv⟩ :=
    Work.BSW.Cases.K4.inverts_of_fixedPointFree_involution
      (Subgroup.centralizer ({y} : Set G)) w hww hnorm hfix
  exact ⟨hker, fun c hc => by rw [← hinv c hc, inv_eq_of_mul_eq_one_left hww],
    IsMulCommutative.of_comm (fun a b => Subtype.ext (hab a.1 a.2 b.1 b.2))⟩

omit [Finite G] in
/-- **Bender §3.1(iv).**  If an involution `w` inverts `y`, does not commute with `y`, and inverts
every element of `F = C_G(y)`, then the involutions inverting `y` are exactly the coset `w F`;
in particular there are `|F|` of them, i.e. `Work.BSW.iFn G y = |C_G(y)|`. -/
theorem iFn_eq_card_centralizer_of_inverting_involution {y w : G}
    (hw : orderOf w = 2) (hwinv : w⁻¹ * y * w = y⁻¹)
    (hwF : w ∉ Subgroup.centralizer ({y} : Set G))
    (hinvF : ∀ c ∈ Subgroup.centralizer ({y} : Set G), w * c * w = c⁻¹) :
    Work.BSW.iFn G y = Nat.card ↥(Subgroup.centralizer ({y} : Set G)) := by
  have hww : w * w = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two hw
  have hwinv' : w * y * w = y⁻¹ := by rw [← hwinv, inv_eq_of_mul_eq_one_left hww]
  have hwyi : w * y⁻¹ = y * w := mul_inv_conj_eq hww hwinv'
  rw [Work.BSW.iFn]
  have hcard := Set.ncard_congr
    (s := (Set.univ : Set ↥(Subgroup.centralizer ({y} : Set G))))
    (t := {u : G | orderOf u = 2 ∧ u⁻¹ * y * u = y⁻¹})
    (fun c _ => w * (c : G)) ?_ ?_ ?_
  · rw [Set.ncard_univ] at hcard
    exact hcard.symm
  · -- the coset `w F` consists of involutions inverting `y`
    intro c _
    constructor
    · have hsq : (w * (c : G)) * (w * (c : G)) = 1 := by
        calc (w * (c : G)) * (w * (c : G)) = (w * (c : G) * w) * (c : G) := by group
          _ = (c : G)⁻¹ * (c : G) := by rw [hinvF c c.2]
          _ = 1 := inv_mul_cancel _
      have hne : w * (c : G) ≠ 1 := by
        intro h1
        refine hwF ?_
        have hw_eq : w = (c : G)⁻¹ := by
          calc w = w * (c : G) * (c : G)⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
            _ = 1 * (c : G)⁻¹ := by rw [h1]
            _ = (c : G)⁻¹ := one_mul _
        rw [hw_eq]
        exact (Subgroup.centralizer ({y} : Set G)).inv_mem c.2
      have hdvd : orderOf (w * (c : G)) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsq)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hne
      · exact h1
    · have hc_comm : Commute (c : G) y :=
        Subgroup.mem_centralizer_singleton_iff.mp c.2
      have hci : (c : G)⁻¹ * y⁻¹ * (c : G) = y⁻¹ := by
        rw [(hc_comm.inv_left.inv_right).eq, mul_assoc, inv_mul_cancel, mul_one]
      calc (w * (c : G))⁻¹ * y * (w * (c : G))
          = (c : G)⁻¹ * w⁻¹ * y * w * (c : G) := by group
        _ = (c : G)⁻¹ * (w * y * w) * (c : G) := by
              rw [inv_eq_of_mul_eq_one_left hww]; group
        _ = (c : G)⁻¹ * y⁻¹ * (c : G) := by rw [hwinv']
        _ = y⁻¹ := hci
  · -- injectivity
    intro a b _ _ hab
    exact Subtype.ext (mul_left_cancel hab)
  · -- surjectivity
    intro u hu
    obtain ⟨hu2, huconj⟩ := hu
    have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_left
      (Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2)
    have huc : w * u ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have huyu : u * y * u = y⁻¹ := by simpa [hu_inv] using huconj
      have huy : u * y = y⁻¹ * u := by
        calc u * y = u * y * (u * u) := by
              rw [Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2, mul_one]
          _ = (u * y * u) * u := by group
          _ = y⁻¹ * u := by rw [huyu]
      calc (w * u) * y = w * (u * y) := by group
        _ = w * (y⁻¹ * u) := by rw [huy]
        _ = (w * y⁻¹) * u := by group
        _ = (y * w) * u := by rw [hwyi]
        _ = y * (w * u) := by group
    exact ⟨⟨w * u, huc⟩, Set.mem_univ _, by show w * (w * u) = u; rw [← mul_assoc, hww, one_mul]⟩

/-- **Bender 1974 §3.1(i),(iv)** (see `REFS/vision/bender1974_bsw/p0004.md`–`p0005.md`): for `x`
whose centralizer `F = C_G(x)` has odd order and an involution `u` inverting `x`, the centralizer
is abelian of size `i(x)`, and every non-identity element of `F` has centralizer `F`. -/
theorem S31core {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) {x u : G}
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer ({x} : Set G))))
    (hu : orderOf u = 2) (huinv : u⁻¹ * x * u = x⁻¹) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = Work.BSW.iFn G x ∧
      IsMulCommutative ↥(Subgroup.centralizer ({x} : Set G)) ∧
      (∀ a ∈ Subgroup.centralizer ({x} : Set G), a ≠ 1 →
        Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({x} : Set G)) := by
  have hnin_x : ∀ v : G, orderOf v = 2 → x ∉ Subgroup.centralizer ({v} : Set G) :=
    fun v hv => not_mem_centralizer_of_involution_of_odd hodd hv
  obtain ⟨hker, hinv, hab⟩ := centralizer_of_inverting_involution h hu huinv hnin_x
  have hu_inv : u⁻¹ = u :=
    inv_eq_of_mul_eq_one_left (Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu)
  have hwF : u ∉ Subgroup.centralizer ({x} : Set G) := by
    intro hmem
    refine hnin_x u hu ?_
    rw [Subgroup.mem_centralizer_singleton_iff] at hmem ⊢
    exact hmem.symm
  refine ⟨?_, hab, ?_⟩
  · exact (iFn_eq_card_centralizer_of_inverting_involution hu huinv hwF hinv).symm
  · intro a ha ha1
    have hxa : x ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [Subgroup.mem_centralizer_singleton_iff] at ha
      exact ha.symm
    have hFa : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({a} : Set G) := by
      intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val (hab.is_comm.comm
          (⟨a, ha⟩ : ↥(Subgroup.centralizer ({x} : Set G)))
          (⟨c, hc⟩ : ↥(Subgroup.centralizer ({x} : Set G))))).symm
    have hnin_a : ∀ v : G, orderOf v = 2 → a ∉ Subgroup.centralizer ({v} : Set G) := by
      intro v hv hmem
      rcases isInvolution_or_centralizer_le_of_mem_centralizer h hv hmem ha1 with h2 | hle
      · exact (not_mem_centralizer_of_involution_of_odd hodd h2) hxa
      · exact (not_mem_centralizer_of_involution_of_odd hodd hv) (hle hxa)
    have huinv_a : u⁻¹ * a * u = a⁻¹ := by
      rw [hu_inv]
      exact hinv a ha
    obtain ⟨-, -, hab_a⟩ := centralizer_of_inverting_involution h hu huinv_a hnin_a
    have hle : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
      intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val (hab_a.is_comm.comm
          (⟨x, hxa⟩ : ↥(Subgroup.centralizer ({a} : Set G)))
          (⟨c, hc⟩ : ↥(Subgroup.centralizer ({a} : Set G))))).symm
    exact le_antisymm hle hFa

end Work.BSW.Cases
