/-
Copyright (c) 2025. All rights reserved.

# Surjectivity of the localisation map on square classes

The arithmetic content of Grünwald's theorem in degree `2`
(`Work.QuadraticLocalGlobal.grunwald_degree_two`) is that for finitely many **distinct** primes
`q i` and prescribed local square classes `c i` there is a global rational square class `x`
whose localisations are the `c i`.  This file restates that in the vocabulary of
`Work.AbsoluteKummer.SqClass`:

`sqClassLocalize_surjective`: the product of the localisation maps
`SqClass ℚ → ∏ i, SqClass ℚ_[q i]` is surjective.

The only point to check is that the definition of `sqClassLocalize` — a map induced on the
quotient `ℚˣ/(ℚˣ)²` by the localisation homomorphism `ℚˣ → ℚ_[p]ˣ` — computes the local square
class of the image, and that `SameSquare` is exactly the statement that two units of `ℚ_[p]`
have the same class in `SqClass ℚ_[p]`.
-/
import Mathlib
import Submission.Work.AbsoluteKummer.SqClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.Grunwald

open scoped Classical

/-- Two units of `ℚ_[p]` whose values have the same square class (`SameSquare`) represent the same
element of `SqClass ℚ_[p] = ℚ_[p]ˣ/(ℚ_[p]ˣ)²`. -/
theorem mk'_eq_of_sameSquare {p : ℕ} [Fact p.Prime] {a b : (ℚ_[p])ˣ}
    (h : Work.QuadraticLocalGlobal.SameSquare (a : ℚ_[p]) (b : ℚ_[p])) :
    QuotientGroup.mk' (Work.Kummer.nthPowerSubgroup 2 (ℚ_[p])ˣ) a =
      QuotientGroup.mk' (Work.Kummer.nthPowerSubgroup 2 (ℚ_[p])ˣ) b := by
  obtain ⟨z, hz⟩ := h
  have hz0 : z ≠ 0 := by
    rintro rfl
    refine Units.ne_zero b ?_
    rw [← hz]; ring
  refine (QuotientGroup.mk'_eq_mk' _).mpr ⟨(Units.mk0 z hz0) ^ 2, ?_, ?_⟩
  · exact ⟨Units.mk0 z hz0, rfl⟩
  · ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [mul_comm]; exact hz

/-- **Surjectivity of the localisation map on square classes**, i.e. Grünwald's theorem in
degree `2` in the language of `SqClass`: for finitely many distinct primes `q i` and prescribed
local square classes there is a global rational square class with those localisations. -/
theorem sqClassLocalize_surjective {ι : Type*} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime] (hq : Function.Injective q) : Function.Surjective (fun x : Work.AbsoluteKummer.SqClass ℚ => fun i : ι => Work.AbsoluteKummer.sqClassLocalize (q i) x) := by
  intro y
  -- lift the prescribed local square classes to `p`-adic units
  choose c hc using fun i =>
    QuotientGroup.mk'_surjective (Work.Kummer.nthPowerSubgroup 2 (ℚ_[q i])ˣ) (y i)
  -- Grünwald: some rational unit has the prescribed local square classes
  obtain ⟨d, hd⟩ := Work.QuadraticLocalGlobal.grunwald_degree_two q hq c
  refine ⟨QuotientGroup.mk' _ d, funext fun i => ?_⟩
  show Work.AbsoluteKummer.sqClassLocalize (q i) (QuotientGroup.mk' _ d) = y i
  rw [Work.AbsoluteKummer.sqClassLocalize_mk]
  rw [mk'_eq_of_sameSquare (hd i), hc i]

end Work.AbsoluteKummer.Grunwald
