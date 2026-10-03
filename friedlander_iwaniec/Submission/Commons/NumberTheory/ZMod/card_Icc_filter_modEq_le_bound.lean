import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.ZMod

/-- Numerical bound: `(2 * A) / d ≤ 2 * (A / d) + 1` for `d > 0`. -/
private lemma two_mul_div_add_one (A d : ℕ) (hd : 0 < d) :
    (2 * A) / d ≤ 2 * (A / d) + 1 := by
  have hr : A % d ≤ d - 1 := Nat.le_sub_one_of_lt (Nat.mod_lt A hd)
  have hA : A ≤ (A / d) * d + (d - 1) := by
    calc A = d * (A / d) + A % d := (Nat.div_add_mod A d).symm
      _ = (A / d) * d + A % d := by rw [Nat.mul_comm d (A / d)]
      _ ≤ (A / d) * d + (d - 1) := Nat.add_le_add_left hr _
  have hbound : 2 * A ≤ d * (2 * (A / d)) + 2 * (d - 1) := by
    calc 2 * A ≤ 2 * ((A / d) * d + (d - 1)) := Nat.mul_le_mul_left 2 hA
      _ = d * (2 * (A / d)) + 2 * (d - 1) := by ring
  calc (2 * A) / d ≤ (d * (2 * (A / d)) + 2 * (d - 1)) / d := Nat.div_le_div_right hbound
    _ = 2 * (A / d) + (2 * (d - 1)) / d :=
        Nat.mul_add_div hd (2 * (A / d)) (2 * (d - 1))
    _ ≤ 2 * (A / d) + 1 := by
        have h1 : (2 * (d - 1)) / d < 2 := by
          rw [Nat.div_lt_iff_lt_mul hd]
          omega
        omega

/-- **Counting integers in a residue class in a symmetric interval.**

The number of integers `a` with `-A ≤ a ≤ A` and `a ≡ a₀ (mod d)` is at most
`2 * (A / d) + 2`. -/
theorem card_Icc_filter_modEq_le_bound {d : ℕ} (hd : 0 < d) (A : ℕ) (a₀ : ℤ) :
    ((Finset.Icc (-(A : ℤ)) (A : ℤ)).filter (fun a : ℤ => a ≡ a₀ [ZMOD d])).card
      ≤ 2 * (A / d) + 2 := by
  classical
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  set S : Finset ℤ :=
    (Finset.Icc (-(A : ℤ)) (A : ℤ)).filter (fun a : ℤ => a ≡ a₀ [ZMOD d]) with hS
  set T : Finset ℤ := Finset.Icc (0 : ℤ) (((2 * A) / d : ℕ) : ℤ) with hT
  -- the shift-and-divide map sends `S` into the small interval `T`
  have hmaps : ∀ x ∈ S, (x + (A : ℤ)) / (d : ℤ) ∈ T := by
    intro x hx
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨hxl, hxu⟩, -⟩ := hx
    rw [hT, Finset.mem_Icc]
    constructor
    · exact Int.ediv_nonneg (by linarith) (le_of_lt hdZ)
    · have hle : x + (A : ℤ) ≤ ((2 * A : ℕ) : ℤ) := by
        push_cast
        linarith
      calc (x + (A : ℤ)) / (d : ℤ)
          ≤ (((2 * A : ℕ) : ℤ)) / (d : ℤ) := Int.ediv_le_ediv hdZ hle
        _ = (((2 * A) / d : ℕ) : ℤ) := by rw [← Int.natCast_ediv]
  -- on a fixed residue class the map is strictly increasing
  have hmono : ∀ x ∈ S, ∀ y ∈ S, x < y →
      (x + (A : ℤ)) / (d : ℤ) < (y + (A : ℤ)) / (d : ℤ) := by
    intro x hx y hy hxy
    rw [hS, Finset.mem_filter] at hx hy
    obtain ⟨-, hxmod⟩ := hx
    obtain ⟨-, hymod⟩ := hy
    have hmod : (d : ℤ) ∣ y - x := by
      have h1 : x ≡ y [ZMOD (d : ℤ)] := hxmod.trans hymod.symm
      rwa [Int.modEq_iff_dvd] at h1
    have hpos : 0 < y - x := by linarith
    have hdle : (d : ℤ) ≤ y - x := Int.le_of_dvd hpos hmod
    have hstep : x + (A : ℤ) + d ≤ y + (A : ℤ) := by linarith
    have h1 : (x + (A : ℤ) + d) / (d : ℤ) = (x + (A : ℤ)) / (d : ℤ) + 1 := by
      have h := Int.add_ediv_of_dvd_left (a := (d : ℤ)) (b := x + (A : ℤ))
        (c := (d : ℤ)) (dvd_refl (d : ℤ))
      rw [Int.ediv_self (ne_of_gt hdZ)] at h
      rw [show x + (A : ℤ) + d = (d : ℤ) + (x + (A : ℤ)) by ring, h]
      ring
    have h2 : (x + (A : ℤ) + d) / (d : ℤ) ≤ (y + (A : ℤ)) / (d : ℤ) :=
      Int.ediv_le_ediv hdZ hstep
    linarith
  have hcard : S.card ≤ T.card := by
    refine Finset.card_le_card_of_injOn (fun x => (x + (A : ℤ)) / (d : ℤ)) ?_ ?_
    · intro x hx
      exact hmaps x hx
    · intro x hx y hy hxy
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact absurd hxy (ne_of_lt (hmono x hx y hy hlt))
      · exact absurd hxy.symm (ne_of_lt (hmono y hy x hx hlt))
  have hTcard : T.card = 2 * A / d + 1 := by
    rw [hT, Int.card_Icc, sub_zero]
    have hcast : ((((2 * A) / d : ℕ) : ℤ) + 1) = ((((2 * A) / d + 1 : ℕ)) : ℤ) := by
      push_cast; ring
    rw [hcast, Int.toNat_natCast]
  calc S.card ≤ T.card := hcard
    _ = 2 * A / d + 1 := hTcard
    _ ≤ 2 * (A / d) + 2 := by
        have := two_mul_div_add_one A d hd
        omega

end Commons.NumberTheory.ZMod
