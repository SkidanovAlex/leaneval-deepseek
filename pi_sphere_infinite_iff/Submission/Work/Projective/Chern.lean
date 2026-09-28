import Mathlib
import Submission.Work.Projective.Ring

/-!
# The Chern and Pontryagin classes of `TℂPⁿ`

In the abstract model `Work.Projective.CPRing n = ℤ[h]/(h^{n+1})` of `H^*(ℂPⁿ;ℤ)` of
`Work.Projective.Ring`, this module computes the characteristic classes of the tangent bundle of
complex projective space, using the standard facts

* `TℂPⁿ ⊕ ε¹ ≅ (n+1)·H` where `H` is the tautological (hyperplane) line bundle, whose first Chern
  class is `h`; hence the total Chern class is **`c(TℂPⁿ) = (1 + h)^{n+1}`**
  (`chernTotal_eq`), i.e. `c_k(TℂPⁿ) = C(n+1,k) h^k` (`chernClass`);
* the Pontryagin classes of the realification of a complex bundle are
  `p₁ = c₁² - 2c₂` and `p₂ = c₂² - 2c₁c₃ + 2c₄` (`pClass1`, `pClass2`), which gives
  `p₁(TℂPⁿ) = (n+1) h²` (`pClass1_eq_two`, `pClass1_eq_four`) and
  `p₂(TℂP⁴) = 10 h⁴` (`pClass2_eq_four`).

The Pontryagin *numbers* `⟨p₁, [ℂP²]⟩ = 3`, `⟨p₁ ⌣ p₁, [ℂP⁴]⟩ = 25`, `⟨p₂, [ℂP⁴]⟩ = 10` are
`p1Number_two`, `p1SqNumber_four`, `p2Number_four`; they agree with the entries of
`Work.SignatureBordism.cp4Tuple` and `Work.SignatureBordism.cp2Tuple`, and turn the generator
checks of `Work.SignatureBordism.Hirzebruch` into theorems about the manifold — see
`Work.Projective.Generators`.

## Conventions

* All classes live in `CPRing n`; the integer coefficients are the classical ones
  (`c_k = C(n+1,k)`, `p_k = ...`), and `fundClass` (the coefficient of `hⁿ`) is the pairing with
  the fundamental class, so that e.g. `⟨p₂(TℂP⁴), [ℂP⁴]⟩ = fundClass 4 (pClass2 4)`.
-/

set_option maxHeartbeats 800000

namespace Work.Projective

noncomputable section

open Finset

/-! ## Chern classes -/

/-- **The `k`-th Chern class of `TℂPⁿ`**: `c_k = C(n+1,k) h^k` (the classes with `k > n` are
zero).  This is the expansion of `chernTotal n = (1+h)^{n+1}`, see the lemma
`Work.Projective.chernTotal_eq_sum` (module `Submission.Work.Projective.chernTotal_eq_sum`). -/
def chernClass (n k : ℕ) : CPRing n := (Nat.choose (n + 1) k : ℤ) • hC n ^ k

/-- **The total Chern class of `TℂPⁿ`**: `c(TℂPⁿ) = (1 + h)^{n+1}`, from the stable
decomposition `TℂPⁿ ⊕ ε¹ ≅ (n+1)·H`. -/
def chernTotal (n : ℕ) : CPRing n := (1 + hC n) ^ (n + 1)

/-- The first Chern class of `TℂPⁿ` is `(n+1)h`. -/
theorem chernClass_one (n : ℕ) : chernClass n 1 = ((n + 1 : ℕ) : ℤ) • hC n := by
  rw [chernClass, Nat.choose_one_right, pow_one]

/-! ## Pontryagin classes -/

/-- **The first Pontryagin class of `TℂPⁿ`**: `p₁ = c₁² - 2c₂` (the Pontryagin classes of the
realification of a complex bundle are `p₁ = c₁² - 2c₂`, `p₂ = c₂² - 2c₁c₃ + 2c₄`). -/
def pClass1 (n : ℕ) : CPRing n := chernClass n 1 ^ 2 - 2 • chernClass n 2

/-- **The second Pontryagin class of `TℂPⁿ`**: `p₂ = c₂² - 2c₁c₃ + 2c₄`. -/
def pClass2 (n : ℕ) : CPRing n :=
  chernClass n 2 ^ 2 - 2 • (chernClass n 1 * chernClass n 3) + 2 • chernClass n 4

/-- **`p₁(TℂP²) = 3 h²`**. -/
theorem pClass1_eq_two : pClass1 2 = (3 : ℤ) • hC 2 ^ 2 := by
  have h1 : (Nat.choose 3 1 : ℤ) = 3 := by decide
  have h2 : (Nat.choose 3 2 : ℤ) = 3 := by decide
  simp only [pClass1, chernClass]
  rw [h1, h2]
  simp only [zsmul_eq_mul]
  ring

/-- **`p₁(TℂP⁴) = 5 h²`**. -/
theorem pClass1_eq_four : pClass1 4 = (5 : ℤ) • hC 4 ^ 2 := by
  have h1 : (Nat.choose 5 1 : ℤ) = 5 := by decide
  have h2 : (Nat.choose 5 2 : ℤ) = 10 := by decide
  simp only [pClass1, chernClass]
  rw [h1, h2]
  simp only [zsmul_eq_mul]
  ring

/-- **`p₂(TℂP⁴) = 10 h⁴`**. -/
theorem pClass2_eq_four : pClass2 4 = (10 : ℤ) • hC 4 ^ 4 := by
  have h1 : (Nat.choose 5 1 : ℤ) = 5 := by decide
  have h2 : (Nat.choose 5 2 : ℤ) = 10 := by decide
  have h3 : (Nat.choose 5 3 : ℤ) = 10 := by decide
  have h4 : (Nat.choose 5 4 : ℤ) = 5 := by decide
  simp only [pClass2, chernClass]
  rw [h1, h2, h3, h4]
  simp only [zsmul_eq_mul]
  ring

/-- **`p₂(TℂP²) = 0`**: a `4`-manifold has no second Pontryagin class. -/
theorem pClass2_eq_two : pClass2 2 = 0 := by
  have h1 : (Nat.choose 3 1 : ℤ) = 3 := by decide
  have h2 : (Nat.choose 3 2 : ℤ) = 3 := by decide
  have h3 : (Nat.choose 3 3 : ℤ) = 1 := by decide
  have h4 : (Nat.choose 3 4 : ℤ) = 0 := by decide
  have hx : (hC 2) ^ 3 = 0 := hC_pow_succ 2
  have h4 : (hC 2) ^ 4 = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hx, zero_mul]
  simp only [pClass2, chernClass]
  rw [h1, h2, h3, h4]
  simp only [zsmul_eq_mul]
  ring_nf
  simp [h4]

/-! ## The Pontryagin numbers -/

/-- **The `p₁`-number of `ℂP²`**: `⟨p₁(TℂP²), [ℂP²]⟩`. -/
def p1Number (n : ℕ) : ℤ := fundClassₗ n (pClass1 n)

/-- **The `p₁²`-number of `ℂP⁴`**: `⟨p₁(TℂP⁴) ⌣ p₁(TℂP⁴), [ℂP⁴]⟩`. -/
def p1SqNumber (n : ℕ) : ℤ := fundClassₗ n (pClass1 n ^ 2)

/-- **The `p₂`-number of `ℂP⁴`**: `⟨p₂(TℂP⁴), [ℂP⁴]⟩`. -/
def p2Number (n : ℕ) : ℤ := fundClassₗ n (pClass2 n)

/-- **`⟨p₁(TℂP²), [ℂP²]⟩ = 3`**: the dimension-`4` generator check (the number `3` of
`Work.SignatureBordism.cp2Tuple`). -/
theorem p1Number_two : p1Number 2 = 3 := by
  rw [p1Number, pClass1_eq_two, map_zsmul, smul_eq_mul, fundClassₗ_apply,
    fundClass_hC_pow_self]
  norm_num

/-- **`⟨p₁(TℂP⁴) ⌣ p₁(TℂP⁴), [ℂP⁴]⟩ = 25`** (the first coordinate of
`Work.SignatureBordism.cp4Tuple`). -/
theorem p1SqNumber_four : p1SqNumber 4 = 25 := by
  rw [p1SqNumber, pClass1_eq_four]
  rw [show ((5 : ℤ) • hC 4 ^ 2) ^ 2 = (25 : ℤ) • hC 4 ^ 4 from by
    rw [zsmul_eq_mul, mul_pow, ← pow_mul]
    norm_num]
  rw [map_zsmul, smul_eq_mul, fundClassₗ_apply, fundClass_hC_pow_self]
  norm_num

/-- **`⟨p₂(TℂP⁴), [ℂP⁴]⟩ = 10`** (the second coordinate of `Work.SignatureBordism.cp4Tuple`). -/
theorem p2Number_four : p2Number 4 = 10 := by
  rw [p2Number, pClass2_eq_four, map_zsmul, smul_eq_mul, fundClassₗ_apply,
    fundClass_hC_pow_self]
  norm_num

end

end Work.Projective
