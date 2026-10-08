import Mathlib

/-!
# `Work.BG.cardDvdOfFree`: the order of a group acting freely off a fixed point divides `|X| - 1`

Let a finite group `G` act on a finite set `X` with a globally fixed point `x₀` and no other
fixed points of any non-identity element:

`hfree : ∀ g ≠ 1, ∀ x ≠ x₀, g • x ≠ x`.

Every point `x ≠ x₀` then has trivial stabiliser, so by orbit–stabiliser each orbit in `X`
is either `{x₀}` (a singleton) or has cardinality `|G|`.  Hence `|X| = |G| * (number of orbits
other than `{x₀}`) + 1`, and therefore `|G| ∣ |X| - 1`.

This is proved via the class formula
`MulAction.card_eq_sum_card_group_div_card_stabilizer'`, applied to a section `φ` of the
orbit-quotient map that sends the orbit of `x₀` to `x₀` itself and every other orbit `ω` to
`ω.out` (a representative, which is automatically `≠ x₀`).
-/

namespace Work.BG

open MulAction

set_option linter.style.haveILetI false

theorem cardDvdOfFree {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (x₀ : X) (hfix : ∀ g : G, g • x₀ = x₀)
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : X, x ≠ x₀ → g • x ≠ x) :
    Nat.card G ∣ Nat.card X - 1 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fintype (Quotient (MulAction.orbitRel G X)) := Fintype.ofFinite _
  -- the orbit of `x₀` in the orbit quotient
  let ω₀ : Quotient (MulAction.orbitRel G X) := Quotient.mk'' x₀
  -- a section of the quotient map, avoiding `x₀` outside the orbit of `x₀`
  let φ : Quotient (MulAction.orbitRel G X) → X := fun ω => if ω = ω₀ then x₀ else ω.out
  have hφ : Function.LeftInverse (Quotient.mk'' : X → Quotient (MulAction.orbitRel G X)) φ := by
    intro ω
    by_cases h : ω = ω₀
    · rw [h, show φ ω₀ = x₀ from by simp [φ]]
    · rw [show φ ω = ω.out from by simp [φ, h]]
      exact Quotient.out_eq' ω
  -- each term of the class formula is `1` on the orbit of `x₀` and `|G|` elsewhere
  have hterm : ∀ ω : Quotient (MulAction.orbitRel G X),
      Fintype.card G / Fintype.card ↥(MulAction.stabilizer G (φ ω))
        = (if ω = ω₀ then (1:ℕ) else Fintype.card G) := by
    intro ω
    by_cases h : ω = ω₀
    · -- the stabiliser of `x₀` is everything, so the index is `1`
      rw [ite_eq_left h, show φ ω = x₀ from by simp [φ, h]]
      have hcard : Fintype.card ↥(MulAction.stabilizer G x₀) = Fintype.card G :=
        Fintype.card_congr
          { toFun := fun y => (y : G)
            invFun := fun g => ⟨g, by rw [MulAction.mem_stabilizer_iff]; exact hfix g⟩
            left_inv := fun y => Subtype.ext rfl
            right_inv := fun g => rfl }
      rw [hcard, Nat.div_self (Fintype.card_pos_iff.mpr ⟨1⟩)]
    · -- other orbits: the representative is `≠ x₀`, so its stabiliser is trivial
      rw [ite_eq_right h, show φ ω = ω.out from by simp [φ, h]]
      have houtne : (ω.out : X) ≠ x₀ := by
        intro hh
        exact h (by rw [← Quotient.out_eq' ω, hh])
      have hle : Fintype.card ↥(MulAction.stabilizer G (ω.out : X)) ≤ 1 :=
        Fintype.card_le_one_iff.mpr (fun u v => Subtype.ext (by
          have hu : (u : G) = 1 := by
            by_contra hg
            exact hfree u.1 hg (ω.out : X) houtne (MulAction.mem_stabilizer_iff.mp u.2)
          have hv : (v : G) = 1 := by
            by_contra hg
            exact hfree v.1 hg (ω.out : X) houtne (MulAction.mem_stabilizer_iff.mp v.2)
          rw [hu, hv]))
      have hpos : 0 < Fintype.card ↥(MulAction.stabilizer G (ω.out : X)) :=
        Fintype.card_pos_iff.mpr ⟨1⟩
      have hcard : Fintype.card ↥(MulAction.stabilizer G (ω.out : X)) = 1 := by omega
      rw [hcard, Nat.div_one]
  -- the resulting sum is `(|orbit space| - 1) * |G| + 1`
  have hsum : (∑ ω : Quotient (MulAction.orbitRel G X),
      (if ω = ω₀ then (1:ℕ) else Fintype.card G))
      = (Fintype.card (Quotient (MulAction.orbitRel G X)) - 1) * Fintype.card G + 1 := by
    rw [(Finset.sum_erase_add (Finset.univ : Finset (Quotient (MulAction.orbitRel G X)))
        (fun ω => if ω = ω₀ then (1:ℕ) else Fintype.card G) (Finset.mem_univ ω₀)).symm]
    rw [show (if ω₀ = ω₀ then (1:ℕ) else Fintype.card G) = 1 from by simp]
    have hcongr : (∑ x ∈ Finset.univ.erase ω₀,
          (if x = ω₀ then (1:ℕ) else Fintype.card G))
        = (∑ _x ∈ Finset.univ.erase ω₀, Fintype.card G) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_erase] at hx
      exact ite_eq_right hx.1
    rw [hcongr, Finset.sum_const, smul_eq_mul,
      Finset.card_erase_of_mem (Finset.mem_univ ω₀), Finset.card_univ]
  -- class formula
  have hX : Fintype.card X
      = (Fintype.card (Quotient (MulAction.orbitRel G X)) - 1) * Fintype.card G + 1 := by
    rw [MulAction.card_eq_sum_card_group_div_card_stabilizer' G X (φ := φ) hφ]
    simp only [hterm]
    exact hsum
  rw [Nat.card_eq_fintype_card (α := G), Nat.card_eq_fintype_card (α := X), hX,
    Nat.add_sub_cancel]
  exact dvd_mul_left _ _

end Work.BG
