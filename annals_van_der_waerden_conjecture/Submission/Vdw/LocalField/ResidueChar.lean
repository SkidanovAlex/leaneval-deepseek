import Mathlib
import Submission.Vdw.LocalField.Completion
import Submission.Vdw.LocalField.Unramified

open scoped NumberField
open IsDedekindDomain

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Local-field chapter (stone 3, groundwork): characteristic of the residue field

The residue field `κ = 𝓞 K ⧸ P` of a maximal ideal `P` over the rational
prime `p` has characteristic `p`.  This module supplies that fact, plus the
membership lemmas it rests on (`P` lies over `(p)`, so the ideal-comap of
`P` in `ℤ` is exactly `(p)`).

These are the characteristic inputs for the Teichmüller-lift step of stone 3
(`Perfection.teichmuller` requires `[CharP (R ⧸ I) p]` at the valuation ring
`R = kpInt p P` of the completion `K_P`; the residue ring is identified with
`𝓞 K ⧸ P` by `Unramified.completion_residueField_equiv`, and `CharP` is
invariant under ring equivalences).
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- A maximal ideal `P` over `(p)` contains an integer `z` iff `p ∣ z`
(`P.LiesOver (p)` means the ideal-comap of `P` in `ℤ` is exactly `(p)`). -/
lemma int_mem_iff_dvd (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (z : ℤ) :
    (algebraMap ℤ (𝓞 K)) z ∈ P ↔ (p : ℤ) ∣ z := by
  classical
  have hunder : (Ideal.span ({(p : ℤ)} : Set ℤ) : Ideal ℤ) = Ideal.under ℤ P :=
    Ideal.over_def P (Ideal.span ({(p : ℤ)} : Set ℤ))
  constructor
  · intro hz
    have hc : z ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) P := Ideal.mem_comap.mpr hz
    rw [← Ideal.under_def] at hc
    rw [← hunder] at hc
    rwa [Ideal.mem_span_singleton] at hc
  · intro hz
    have hc : z ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) P := by
      rw [← Ideal.under_def]
      rw [← hunder]
      exact Ideal.mem_span_singleton.mpr hz
    exact Ideal.mem_comap.mp hc

/-- The natural `p : 𝓞 K` lies in `P` (instance of `int_mem_iff_dvd` at
`z = p`). -/
lemma intCast_mem_of_liesOver (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (algebraMap ℤ (𝓞 K)) (p : ℤ) ∈ P := by
  exact (int_mem_iff_dvd (K := K) p P (p : ℤ)).2 dvd_rfl

/-- A natural number `x` lies in `P` (as an element of `𝓞 K`) iff `p ∣ x`. -/
lemma natCast_mem_iff_dvd (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (x : ℕ) :
    (x : 𝓞 K) ∈ P ↔ p ∣ x := by
  classical
  have hcast : (x : 𝓞 K) = algebraMap ℤ (𝓞 K) (x : ℤ) := by norm_num
  rw [hcast]
  rw [int_mem_iff_dvd (K := K) p P (x : ℤ)]
  exact Int.ofNat_dvd

/-- **The residue field has characteristic `p`.**  (The quotient map
`ℕ → 𝓞K → 𝓞K ⧸ P` has kernel exactly the multiples of `p`.) -/
theorem charP_quotient_of_liesOver (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    CharP (𝓞 K ⧸ P) p := by
  refine CharP.mk ?_
  intro x
  rw [← map_natCast (Ideal.Quotient.mk P) x]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact natCast_mem_iff_dvd (K := K) p P x

/-- The residue field `κ = kResidue P` of a prime over `p` is a field of
characteristic `p`. -/
theorem residue_charP (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    letI : Field (kResidue P) := Ideal.Quotient.field P
    CharP (kResidue P) p := by
  classical
  letI : Field (kResidue P) := Ideal.Quotient.field P
  dsimp [kResidue]
  exact charP_quotient_of_liesOver (K := K) p P

end
end Submission.Vdw.LocalField
