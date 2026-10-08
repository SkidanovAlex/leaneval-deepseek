import Mathlib

namespace Work.CORE3.MData

/-- If `A` is normal, `X ≤ A ⊔ C`, and `|X|` is coprime to `|C|`, then `X ≤ A`.

The image of `X` under the quotient map `G → G ⧸ A` is contained in the image of
`C` (since the image of `A` is trivial and `X ≤ A ⊔ C`). Its order therefore
divides both `|X|` and `|C|`; by coprimality it is `1`, so the image is trivial,
i.e. `X` lies in the kernel `A`. -/
theorem le_left_of_le_sup_of_coprime {G : Type} [Group G] [Finite G]
    {A C X : Subgroup G} (hA : A.Normal) (hX : X ≤ A ⊔ C)
    (hcop : Nat.Coprime (Nat.card X) (Nat.card C)) : X ≤ A := by
  let f : G →* G ⧸ A := QuotientGroup.mk' A
  -- The image of `A` in `G ⧸ A` is trivial.
  have hmapA : A.map f = ⊥ :=
    (Subgroup.map_eq_bot_iff A (f := f)).mpr (le_of_eq (QuotientGroup.ker_mk' A).symm)
  -- Hence the image of `X` is contained in the image of `C`.
  have hXC : X.map f ≤ C.map f := by
    calc X.map f ≤ (A ⊔ C).map f := Subgroup.map_mono hX
      _ = A.map f ⊔ C.map f := Subgroup.map_sup A C f
      _ = ⊥ ⊔ C.map f := by rw [hmapA]
      _ = C.map f := bot_sup_eq _
  -- The order of the image of `X` divides `|X|` and `|C|`.
  have h1 : Nat.card ↥(X.map f) ∣ Nat.card ↥X := Subgroup.card_map_dvd X f
  have h2 : Nat.card ↥(X.map f) ∣ Nat.card ↥(C.map f) := Subgroup.card_dvd_of_le hXC
  have h3 : Nat.card ↥(C.map f) ∣ Nat.card ↥C := Subgroup.card_map_dvd C f
  have h4 : Nat.card ↥(X.map f) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 (h2.trans h3)
  -- So the image is trivial and `X` lies in the kernel `A`.
  have h5 : X.map f = ⊥ := Subgroup.card_eq_one.mp h4
  rw [Subgroup.map_eq_bot_iff] at h5
  rw [show f.ker = A from QuotientGroup.ker_mk' A] at h5
  exact h5

end Work.CORE3.MData
