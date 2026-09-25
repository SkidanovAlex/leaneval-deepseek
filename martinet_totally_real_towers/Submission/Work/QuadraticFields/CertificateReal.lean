import Mathlib
import Submission.Work.QuadraticFields.Certificate
import Submission.Work.QuadraticFields.MultiquadraticInside
import Submission.Work.QuadraticFields.QuadField

/-!
# A second numerical certificate: a totally real quadratic base field

The unramified-`2`-tower route can also be run over a *totally real* quadratic base field with a
large `2`-class group rank.  This file fixes the base field used by the team for that variant,

  `F = ℚ(√(5·13·17·29·37·41·53))`,

a real quadratic field with `disc F = 5·13·17·29·37·41·53` and `ω(disc F) = 7`, hence
`rank₂ Cl F ≥ 6` (genus theory; here `2` is inert in `F`, i.e. `disc F ≡ 5 (mod 8)`).

The multiquadratic field `M = ℚ(√5, √13, √17, √29, √37, √41, √53)` is an unramified extension of
`F` of degree `2 ^ 6 = 64`, exhibiting six independent unramified quadratic extensions of `F`.

## Main definitions

* `Work.QuadraticFields.gsPrimes`: the seven prime discriminants `5, 13, 17, 29, 37, 41, 53`.
* `Work.QuadraticFields.gsM`, `gsRoot`, `gsF`: `M`, the chosen square roots, and `F ⊆ M`.
-/

namespace Work.QuadraticFields

set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000 in
/-- The seven prime discriminants of the totally real certificate. -/
def gsPrimes : Finset ℤ := {5, 13, 17, 29, 37, 41, 53}

/-- The same seven numbers as rationals. -/
def gsPrimesQ : Finset ℚ := gsPrimes.image (fun d : ℤ => (d : ℚ))

/-- The six independent generators of the unramified extension. -/
def gsPrimes6 : Finset ℤ := {5, 13, 17, 29, 37, 41}

theorem gsPrimes_card : gsPrimes.card = 7 := by
  norm_num [gsPrimes]

theorem gsPrimesQ_card : gsPrimesQ.card = 7 := by
  rw [gsPrimesQ, Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h)]
  exact gsPrimes_card

/-- The discriminant of the totally real base field. -/
theorem gsPrimes_prod : (∏ a ∈ gsPrimes, (a : ℚ)) = 2576450045 := by
  norm_num [gsPrimes]

theorem gsPrimes_odd : ∀ a ∈ gsPrimes, Odd a := by
  intro a ha
  rw [gsPrimes] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [Odd]

theorem gsPrimes_isPrimeDiscriminant (a : ℤ) (ha : a ∈ gsPrimes) :
    IsPrimeDiscriminant a := by
  rw [gsPrimes] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inr ⟨5, by norm_num, by norm_num, by norm_num⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨13, by norm_num, by norm_num, by norm_num⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨17, by norm_num, by norm_num, by norm_num⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨29, by norm_num, by norm_num, by norm_num⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨37, by norm_num, by norm_num, by norm_num⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨41, by norm_num, by norm_num, by norm_num⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨53, by norm_num, by norm_num, by norm_num⟩))

theorem gsPrimes_coprime (a b : ℤ) (ha : a ∈ gsPrimes) (hb : b ∈ gsPrimes) (hne : a ≠ b) :
    Nat.Coprime a.natAbs b.natAbs := by
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [gsPrimes] at ha hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | (exfalso; exact hne rfl)
      | (norm_num)

/-- The multiquadratic field `M = ℚ(√5, √13, √17, √29, √37, √41, √53)` of the certificate. -/
abbrev gsM : Type := ↥(multiQuad gsPrimesQ)

/-- The chosen square roots of the certificate primes inside `M`. -/
def gsRoot (a : ℤ) : gsM :=
  if h : a ∈ gsPrimes then
    (⟨sqrtVal (a : ℚ), sqrtVal_mem_multiQuad (s := gsPrimesQ)
      (Finset.mem_image.mpr ⟨a, h, rfl⟩)⟩ : gsM)
  else 1

theorem gsRoot_of_mem {a : ℤ} (ha : a ∈ gsPrimes) :
    gsRoot a = (⟨sqrtVal (a : ℚ), sqrtVal_mem_multiQuad (s := gsPrimesQ)
      (Finset.mem_image.mpr ⟨a, ha, rfl⟩)⟩ : gsM) :=
  dif_pos ha

theorem gsRoot_sq (a : ℤ) (ha : a ∈ gsPrimes) :
    gsRoot a ^ 2 = algebraMap ℚ gsM (a : ℚ) := by
  rw [gsRoot_of_mem ha]
  apply Subtype.ext
  change sqrtVal (a : ℚ) ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ)
  rw [sqrtVal_sq]

/-- The totally real base field `F = ℚ(√(5·13·17·29·37·41·53)) ⊆ M`. -/
def gsF : IntermediateField ℚ gsM := prodSubfield gsPrimes gsRoot

end

end Work.QuadraticFields
