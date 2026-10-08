import Mathlib
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.CharBridge
import Submission.Work.BG.S02
import Submission.Work.BG.modTwoIndep

/-!
# Area BG: the parity step `l34ne_chi_even`

If `χ ∈ ±Irr(G)` has degree divisible by `4`, and `u ∈ G` is an element whose centralizer
contains a subgroup `L` of index at most `2` in a Sylow 2-subgroup `S` of `G`, then
`χ(u) ≡ 0 (mod 2)` in the sense of `Work.BG.AlgIntModTwo`.

The mathematics is the standard `2`-adic argument around Gorenstein 4.2.10
(`Work.BG.centralIntegral`): with `d = |G : C_G(u)|`, the number `d · χ(u) / χ(1)` is an
algebraic integer.  Because `C_G(u)` contains an index-`≤ 2` subgroup of `S`, the index `d`
is not divisible by `4`:

* `d` divides `|G : L|`, and `|G : L| = L.relIndex S · |G : S|` with `|G : S|` odd and
  `L.relIndex S ≤ 2`, so `|G : L|` is odd or twice an odd number;
* if `d` is odd, multiplying `d · χ(u)/χ(1)` by the integer `χ(1)/2` exhibits `d · χ(u)/2` as
  an algebraic integer, and `χ(u)/2 = d · χ(u)/2 - ((d-1)/2) · χ(u)`;
* if `d = 2m` with `m` odd, multiplying by the integer `χ(1)/4` exhibits `m · χ(u)/2` as an
  algebraic integer, and `χ(u)/2 = m · χ(u)/2 - ((m-1)/2) · χ(u)`.

The same argument with `χ` replaced by `-χ` handles the signed case, since
`(-χ)(1) = -χ(1)` is again divisible by `4`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **Arithmetic core.**  If `χ ∈ Irr(G)` has degree divisible by `4` and
`4 ∤ |G : C_G(u)|`, then `χ(u) ≡ 0 (mod 2)`.

Gorenstein 4.2.10 (`Work.BG.centralIntegral`) gives `d · χ(u)/χ(1)` algebraic integral for
`d = |G : C_G(u)|`.  Since `4 ∤ d`, either `d` is odd or `d = 2m` with `m` odd; in the first
case multiplying by the integral number `χ(1)/2`, in the second by the integral number
`χ(1)/4`, produces `d' · χ(u)/2` for an odd `d'`, and `χ(u)/2` is then
`d' · χ(u)/2 - ((d'-1)/2) · χ(u)`, a difference of two algebraic integers. -/
theorem algIntModTwo_of_isIrreducibleCharacter_of_four_dvd_degree
    {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ)
    (h4 : ∃ k : ℤ, χ 1 = (4 : ℂ) * (k : ℂ)) (u : G)
    (hnd : ¬ 4 ∣ (Subgroup.centralizer ({u} : Set G)).index) :
    AlgIntModTwo (χ u) 0 := by
  have hdeg : χ 1 ≠ 0 := by
    obtain ⟨d, hd, h1⟩ := hχ.exists_apply_one_eq_pos_natCast
    rw [h1]; exact_mod_cast hd.ne'
  -- the degree `χ 1 = 4k` makes `χ 1 / 4 = k` and `χ 1 / 2 = 2k` algebraic integers
  have h4int : IsIntegral ℤ (χ 1 / 4) := by
    obtain ⟨k, hk⟩ := h4
    have : χ 1 / 4 = (k : ℂ) := by rw [hk]; field_simp
    rw [this]; exact isIntegral_intCast k
  have h2int : IsIntegral ℤ (χ 1 / 2) := by
    obtain ⟨k, hk⟩ := h4
    have : χ 1 / 2 = ((2 * k : ℤ) : ℂ) := by rw [hk]; push_cast; ring
    rw [this]; exact isIntegral_intCast (2 * k)
  have hci := centralIntegral χ hχ u
  have hu : IsIntegral ℤ (χ u) := isIntegral_apply_of_isIrreducibleCharacter hχ u
  have hprod4 : IsIntegral ℤ (((Subgroup.centralizer ({u} : Set G)).index : ℂ) * χ u / 4) := by
    have heq : ((Subgroup.centralizer ({u} : Set G)).index : ℂ) * χ u / 4
        = (((Subgroup.centralizer ({u} : Set G)).index : ℂ) * χ u / χ 1) * (χ 1 / 4) := by
      field_simp
    rw [heq]; exact hci.mul h4int
  have hprod2 : IsIntegral ℤ (((Subgroup.centralizer ({u} : Set G)).index : ℂ) * χ u / 2) := by
    have heq : ((Subgroup.centralizer ({u} : Set G)).index : ℂ) * χ u / 2
        = (((Subgroup.centralizer ({u} : Set G)).index : ℂ) * χ u / χ 1) * (χ 1 / 2) := by
      field_simp
    rw [heq]; exact hci.mul h2int
  by_cases h2 : 2 ∣ (Subgroup.centralizer ({u} : Set G)).index
  · -- `d = 2m` with `m` odd
    obtain ⟨m, hm⟩ := h2
    have hmnot : ¬ 2 ∣ m := by
      intro h
      obtain ⟨j, hj⟩ := h
      exact hnd ⟨j, by rw [hm, hj]; ring⟩
    have hoddm : Odd m := Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
    obtain ⟨j, hj⟩ := hoddm
    have hm2 : IsIntegral ℤ ((m : ℂ) * χ u / 2) := by
      have heq : (m : ℂ) * χ u / 2
          = ((Subgroup.centralizer ({u} : Set G)).index : ℂ) * χ u / 4 := by
        rw [hm]; push_cast; ring
      rw [heq]; exact hprod4
    refine ⟨χ u / 2, ?_, by ring⟩
    have heq2 : χ u / 2 = (m : ℂ) * χ u / 2 - (j : ℂ) * χ u := by
      rw [hj]; push_cast; ring
    rw [heq2]
    exact hm2.sub ((isIntegral_natCast j).mul hu)
  · -- `d` odd
    have hodd : Odd (Subgroup.centralizer ({u} : Set G)).index :=
      Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
    obtain ⟨j, hj⟩ := hodd
    refine ⟨χ u / 2, ?_, by ring⟩
    have heq2 : χ u / 2
        = ((Subgroup.centralizer ({u} : Set G)).index : ℂ) * χ u / 2 - (j : ℂ) * χ u := by
      rw [hj]; push_cast; ring
    rw [heq2]
    exact hprod2.sub ((isIntegral_natCast j).mul hu)

/-- **Index bound.**  If `u ∈ G` and `L` is a subgroup centralized by `u` with `L ≤ S` and
`L.relIndex S ≤ 2`, where `S` is a Sylow 2-subgroup of `G`, then `4 ∤ |G : C_G(u)|`.

Indeed `d := |G : C_G(u)|` divides `|G : L|`, and `|G : L| = L.relIndex S · |G : S|` with
`|G : S|` odd and `L.relIndex S ∈ {1,2}`; so `|G : L|` is odd or twice an odd number and hence
not divisible by `4`. -/
theorem not_four_dvd_centralizer_index_of_relIndex_le_two
    {G : Type} [Group G] [Finite G] [Fintype G]
    (S : Sylow 2 G) {u : G}
    (hL : ∃ L : Subgroup G, L ≤ (S : Subgroup G) ∧ L.relIndex (S : Subgroup G) ≤ 2 ∧
      (∀ l ∈ L, l * u = u * l)) :
    ¬ 4 ∣ (Subgroup.centralizer ({u} : Set G)).index := by
  obtain ⟨L, hLS, hrel, hcomm⟩ := hL
  -- `u` centralizes `L`
  have hLc : L ≤ Subgroup.centralizer ({u} : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (hcomm l hl).symm
  have hdiv : (Subgroup.centralizer ({u} : Set G)).index ∣ L.index :=
    Subgroup.index_dvd_of_le hLc
  -- the index of a Sylow 2-subgroup is odd
  have hSodd : Odd (S : Subgroup G).index := by
    have h : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
    exact Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact h)
  -- the relative index is positive because `S` is finite
  have hrelpos : 0 < L.relIndex (S : Subgroup G) :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := L.subgroupOf (S : Subgroup G)))
  -- `|G : L| = L.relIndex S · |G : S|`
  have hLidx : L.index = L.relIndex (S : Subgroup G) * (S : Subgroup G).index :=
    (Subgroup.relIndex_mul_index hLS).symm
  have h4L : ¬ 4 ∣ L.index := by
    have hr : L.relIndex (S : Subgroup G) = 1 ∨ L.relIndex (S : Subgroup G) = 2 := by omega
    rintro ⟨c, hc⟩
    rw [hLidx] at hc
    rcases hr with h1 | h2
    · rw [h1, one_mul] at hc
      obtain ⟨j, hj⟩ := hSodd
      omega
    · rw [h2] at hc
      obtain ⟨j, hj⟩ := hSodd
      omega
  intro h4d
  exact h4L (h4d.trans hdiv)

open OddOrder.RepresentationTheory Work.BG in
theorem l34ne_chi_even {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (S : Sylow 2 G) {χ : ClassFunction G ℂ} (hχ : Work.BG.IsPmIrr χ)
    (h4 : ∃ k : ℤ, χ 1 = (4 : ℂ) * (k : ℂ)) {u : G}
    (hL : ∃ L : Subgroup G, L ≤ (S : Subgroup G) ∧ L.relIndex (S : Subgroup G) ≤ 2 ∧
      (∀ l ∈ L, l * u = u * l)) :
    Work.BG.AlgIntModTwo (χ u) 0 := by
  have hnd := not_four_dvd_centralizer_index_of_relIndex_le_two S hL
  rcases hχ with hχ | hχ
  · exact algIntModTwo_of_isIrreducibleCharacter_of_four_dvd_degree hχ h4 u hnd
  · have h4' : ∃ k : ℤ, (-χ) 1 = (4 : ℂ) * (k : ℂ) := by
      obtain ⟨k, hk⟩ := h4
      exact ⟨-k, by rw [ClassFunction.neg_apply, hk]; push_cast; ring⟩
    have hres := algIntModTwo_of_isIrreducibleCharacter_of_four_dvd_degree hχ h4' u hnd
    have h2 : AlgIntModTwo (-(χ u)) 0 := by simpa using hres
    simpa using h2.neg

end Work.BG
