import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.OddCore
import Submission.Work.ZassenhausSuzuki.Odd.q_structure
import Submission.Work.ZassenhausSuzuki.Odd.exists_sylow_of_powTwoOrder
import Submission.Work.ZassenhausSuzuki.Odd.sylow_eq_of_mem
import Submission.Work.ZassenhausSuzuki.Odd.card_powTwoOrder_eq_sylow_mul
import Submission.Work.ZassenhausSuzuki.Odd.card_sylow_two_eq
import Submission.Work.ZassenhausTwoGroup.normalizer_Q_eq
import Submission.Work.ZassenhausTwoGroup.isTI_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.Odd.card_twoElements_ne_one`

The number of non-identity elements of `2`-power order in the Suzuki rank-one configuration
`H = Q ⋊ D` (with `q = |Z(Q)|`, `|Q| = q²`) is `q⁴ - 1`, i.e.

`Nat.card {x // x ≠ 1 ∧ PowTwoOrder x} + 1 = q⁴`.

The count is the classical one.  Since `|G| = q²(q-1)(q²+1)` with `q - 1` and `q² + 1` odd
(`Work.ZassenhausSuzuki.Odd.card_G_eq`), the root group `Q` is a Sylow `2`-subgroup of `G`
with `N_G(Q) = H` (`Work.ZassenhausTwoGroup.normalizer_Q_eq`), so the number of Sylow
`2`-subgroups is `[G : H] = q² + 1`.  Distinct Sylow `2`-subgroups of `G` meet trivially
(`Q` is T.I.: `Work.ZassenhausTwoGroup.isTI_Q`), hence every non-identity element of
`2`-power order lies in exactly one Sylow `2`-subgroup and

`#{x ≠ 1 : 2-power order} = (q² + 1) · (|Q| - 1) = (q² + 1)(q² - 1) = q⁴ - 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki.Odd

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

theorem card_twoElements_ne_one (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t) :
    Nat.card {x : G // x ≠ 1 ∧ Work.ZassenhausSuzuki.Odd.PowTwoOrder x} + 1
      = (Work.ZassenhausSuzuki.Odd.q H) ^ 4 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQ2, hDcard, hfour, hpow, hnot3, hidx⟩ := q_structure h
  -- ## `Q` is a Sylow `2`-subgroup: its index `[G : Q] = (q-1)(q²+1)` is odd
  have hIdx : ¬ 2 ∣ Q.index := by
    have hcardG : Nat.card G = q H ^ 2 * (q H - 1) * (q H ^ 2 + 1) := card_G_eq h
    have h1 := Subgroup.card_mul_index Q
    rw [hcardG, hQ2] at h1
    rw [mul_assoc] at h1
    have hIdx : Q.index = (q H - 1) * (q H ^ 2 + 1) :=
      Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [hIdx]
    obtain ⟨l, hl⟩ := hpow
    have hl2 : 2 ≤ l := by
      by_contra hc
      interval_cases l <;> omega
    have h2q : 2 ∣ q H := by
      rw [hl]
      exact dvd_pow_self 2 (by omega)
    have hq1 : 1 ≤ q H := by omega
    intro hd
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 2)).mp hd with hc | hc
    · have h2 : 2 ∣ q H - (q H - 1) := Nat.dvd_sub h2q hc
      rw [Nat.sub_sub_self hq1] at h2
      omega
    · have h2q2 : 2 ∣ q H ^ 2 := by
        obtain ⟨a, ha⟩ := h2q
        exact ⟨2 * a * a, by rw [ha]; ring⟩
      have h2 : 2 ∣ q H ^ 2 + 1 - q H ^ 2 := Nat.dvd_sub hc h2q2
      rw [Nat.add_sub_cancel_left] at h2
      omega
  let P₀ : Sylow 2 G := h.h2.toSylow hIdx
  have hP0 : (P₀ : Subgroup G) = Q := IsPGroup.toSylow_coe h.h2 hIdx
  have hcardP0 : Nat.card ↥P₀ = q H ^ 2 := hQ2
  -- ## distinct Sylow `2`-subgroups meet trivially, so each `2`-element has a unique Sylow
  have huniq : ∀ (P P' : Sylow 2 G) (x : G), x ∈ P → x ∈ P' → x ≠ 1 → P = P' :=
    fun P P' x hxP hxP' hx1 =>
      sylow_eq_of_mem (Work.ZassenhausTwoGroup.isTI_Q h.hsplit h.hzass)
        h.hsplit.normal P₀ hP0 hx1 hxP hxP'
  have hex : ∀ x : G, x ≠ 1 → PowTwoOrder x → ∃ P : Sylow 2 G, x ∈ P :=
    fun x _ hpx => exists_sylow_of_powTwoOrder hpx
  -- ## counting
  have hcount := card_powTwoOrder_eq_sylow_mul huniq hex P₀
  rw [hcount, hcardP0, card_sylow_two_eq h]
  have hcast : ((q H ^ 2 - 1 : ℕ) : ℤ) = ((q H : ℤ)) ^ 2 - 1 := by
    rw [Nat.cast_sub (by nlinarith : 1 ≤ q H ^ 2), Nat.cast_pow, Nat.cast_one]
  have harith : ((((q H ^ 2 + 1) * (q H ^ 2 - 1) + 1 : ℕ)) : ℤ) = ((q H ^ 4 : ℕ) : ℤ) := by
    push_cast
    rw [hcast]
    ring
  exact_mod_cast harith

end Work.ZassenhausSuzuki.Odd
