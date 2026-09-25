import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.isCyclotomicExtension_Wfield
import Submission.Work.Tower.CyclotomicBase.isCyclotomicExtension_Zfield
import Submission.Work.Tower.CyclotomicBase.inertia_eq_inertiaSub
import Submission.Work.Tower.CyclotomicBase.inertia_le_fixingSubgroup_of_ramificationIdxIn_eq_one
import Submission.Work.Tower.CyclotomicBase.exists_unitsMap_eq_one_and
import Submission.Work.Tower.CyclotomicBase.ramificationIdxIn_cyc
import Submission.Work.Tower.CyclotomicBase.ramificationIdxIn_Zfield_eq_one
import Submission.Work.Tower.CyclotomicBase.disc_Ffield
import Submission.Work.Tower.CyclotomicBase.finrank_Mfield_over_FMfield
import Submission.Work.Tower.CyclotomicBase.disc_Mfield
import Submission.Work.Tower.CyclotomicBase.isUnramifiedExtension_of_absNorm_differentIdeal_eq_one

/-!
# Ramification of the cyclotomic base

This file collects the ramification-theoretic facts about the fields `Wᵢ = ℚ(ζ_{rᵢ})`,
`Zᵢ = ℚ(ζ_{D/rᵢ})`, `Lᵢ`, `M` and `F` inside `ℚ(ζ_D)`.
-/

set_option linter.style.haveILetI false
set_option autoImplicit false

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.Tower.CyclotomicBase

variable {ℓ : ℕ}

/-- The prime `rᵢ` is totally ramified in `Wᵢ = ℚ(ζ_{rᵢ})`: its ramification index is `rᵢ - 1`. -/
theorem ramificationIdxIn_Wfield (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    [NeZero (D r)] (i : Fin ℓ) :
    (Ideal.span {(r i : ℤ)}).ramificationIdxIn (NumberField.RingOfIntegers ↥(Wfield r i)) =
      r i - 1 := by
  haveI : Fact (Nat.Prime (r i)) := ⟨hr i⟩
  haveI := isCyclotomicExtension_Wfield r hr i
  exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime (r i) ↥(Wfield r i)

/-- **`M/F` is unramified at every finite prime.**  Since `M` and `F` have discriminants
`|disc M| = (∏ rᵢ²)^{3^{ℓ-1}}` and `|disc F| = (∏ rᵢ)² = |disc M|^{1/3^{ℓ-1}}`, the tower formula
for the discriminant shows that the norm of the relative different is `1`, so the different is
trivial and the extension is unramified. -/
theorem isUnramifiedExtension_FMfield {ℓ : ℕ} (hℓ : 0 < ℓ) (r : Fin ℓ → ℕ)
    (hr : ∀ i, Nat.Prime (r i)) (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r)
    [NeZero (D r)] :
    Work.Tower.IsUnramifiedExtension ↥(FMfield r hr hr3) ↥(Mfield r hr hr3) := by
  haveI : IsGalois ↥(FMfield r hr hr3) ↥(Mfield r hr hr3) :=
    isGalois_tower_Ffield_Mfield r hr hr3
  refine isUnramifiedExtension_of_absNorm_differentIdeal_eq_one ?_
  have htower := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    ↥(FMfield r hr hr3) (NumberField.RingOfIntegers ↥(FMfield r hr hr3))
    ↥(Mfield r hr hr3) (NumberField.RingOfIntegers ↥(Mfield r hr hr3))
  rw [finrank_Mfield_over_FMfield hℓ r hr hr3 hrinj] at htower
  have hdiscF : (NumberField.discr ↥(FMfield r hr hr3)).natAbs = (∏ i, r i) ^ 2 := by
    simp only [FMfield]
    rw [← NumberField.discr_eq_discr_of_algEquiv (↥(Ffield r hr hr3))
      (IntermediateField.restrictAlgEquiv (Ffield_le_Mfield r hr hr3))]
    have h := congrArg Int.natAbs (disc_Ffield hℓ r hr hr3 hrinj)
    rw [Int.natAbs_abs, Int.natAbs_pow, Int.natAbs_natCast] at h
    exact h
  have hdiscM : (NumberField.discr ↥(Mfield r hr hr3)).natAbs =
      ((∏ i, r i) ^ 2) ^ (3 ^ (ℓ - 1)) := by
    have h := congrArg Int.natAbs (disc_Mfield r hr hr3 hrinj)
    rw [Int.natAbs_abs, Int.natAbs_pow, Int.natAbs_natCast] at h
    rw [Finset.prod_pow] at h
    exact h
  rw [hdiscF, hdiscM] at htower
  have hgoal : 1 * ((∏ i, r i) ^ 2) ^ (3 ^ (ℓ - 1)) =
      Ideal.absNorm (differentIdeal (𝓞 ↥(FMfield r hr hr3)) (𝓞 ↥(Mfield r hr hr3))) *
        ((∏ i, r i) ^ 2) ^ (3 ^ (ℓ - 1)) := by
    rw [one_mul]; exact htower
  have hpos : 0 < ((∏ i, r i) ^ 2) ^ (3 ^ (ℓ - 1)) :=
    pow_pos (pow_pos (Finset.prod_pos fun i _ => (hr i).pos) 2) _
  exact (Nat.eq_of_mul_eq_mul_right hpos hgoal).symm

end Work.Tower.CyclotomicBase
