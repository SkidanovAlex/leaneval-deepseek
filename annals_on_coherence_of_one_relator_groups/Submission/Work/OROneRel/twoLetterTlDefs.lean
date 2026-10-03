/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The two-letter relator `a ^ p * b ^ q`: definitions and elementary properties

This file fixes the basic data of the two-letter case of the Magnus--Moldavanskii step (the target
`Work.OROneRel.twoLetter_hnnData`): the relator `tlU p q = a ^ p * b ^ q` in the free group on
`Fin 2` and the weight `tlW p q` (`a ↦ q`, `b ↦ -p`) that kills it.  It is a leaf so that the
delegated inputs of the target (the Freiheitssatz and the splitting of the `Z`-domain) can import it
without importing the target's own file.
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.wordOfDefs
import Submission.Work.OROneRel.letterPow_mul_letterPow_hypotheses

namespace Work.OROneRel

/-- The weight of the two-letter case: `a = 0 ↦ q`, `b = 1 ↦ -p`.  It kills `a ^ p * b ^ q`. -/
def tlW (p q : ℕ) : Fin 2 → ℤ := fun i => if i = 0 then (q : ℤ) else -(p : ℤ)

/-- The two-letter relator `a ^ p * b ^ q`. -/
def tlU (p q : ℕ) : FreeGroup (Fin 2) := FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q

theorem tlU_not_isProperPower (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ¬ IsProperPower (tlU p q) := by
  simpa only [tlU] using
    not_isProperPower_letterPow_mul_letterPow (a := (0 : Fin 2)) (b := 1) (by decide) hp hq

theorem tlU_isCyclicallyReduced (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    IsCyclicallyReducedRelator (tlU p q) := by
  simpa only [tlU] using
    isCyclicallyReducedRelator_letterPow_mul_letterPow (a := (0 : Fin 2)) (b := 1) (by decide) hp hq

theorem tlU_relatorNorm (p q : ℕ) : relatorNorm (tlU p q) = p + q := by
  simpa only [tlU] using
    relatorNorm_letterPow_mul_letterPow (a := (0 : Fin 2)) (b := 1) (by decide) p q

theorem tlU_relatorLetters {p q : ℕ} {x : Fin 2} (hx : x ∈ relatorLetters (tlU p q)) :
    x = 0 ∨ x = 1 := by
  have h := relatorLetters_letterPow_mul_letterPow (a := (0 : Fin 2)) (b := 1) (by decide) p q
    (by simpa only [tlU] using hx)
  simpa using h

theorem tlU_eps_zero (p q : ℕ) : eps (0 : Fin 2) (tlU p q) = (p : ℤ) := by
  simpa only [tlU] using
    (eps_letterPow_mul_letterPow (a := (0 : Fin 2)) (b := 1) (by decide) p q).1

theorem tlU_eps_one (p q : ℕ) : eps (1 : Fin 2) (tlU p q) = (q : ℤ) := by
  simpa only [tlU] using
    (eps_letterPow_mul_letterPow (a := (0 : Fin 2)) (b := 1) (by decide) p q).2

theorem tlU_hbad (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∀ x : Fin 2, x ∈ relatorLetters (tlU p q) → eps x (tlU p q) ≠ 0 := by
  intro x hx
  rcases tlU_relatorLetters hx with rfl | rfl
  · rw [tlU_eps_zero]; exact_mod_cast (by omega : p ≠ 0)
  · rw [tlU_eps_one]; exact_mod_cast (by omega : q ≠ 0)

end Work.OROneRel
