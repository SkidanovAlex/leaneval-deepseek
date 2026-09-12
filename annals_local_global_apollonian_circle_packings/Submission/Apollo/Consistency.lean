/-
Per-quadruple χ₂ consistency: the first ingredient is the mod-p quadratic
residue lemma: reducing the Descartes equation modulo an odd prime p forces
pairwise products of the remaining coordinates to be squares mod p.
-/
import Submission.Apollo.KR
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false

namespace Apollo

/-- The mod-p bridge lemma: if x, y, z solve the reduced Descartes equation
(x+y+z)² = 2(x²+y²+z²) over ZMod p with p odd, then xy is a square.  (No
nonzero hypotheses needed: a zero product is `0 = 0²`.) -/
lemma descartes_pair_square_zmod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {x y z : ZMod p}
    (h : (x + y + z) ^ 2 = 2 * (x ^ 2 + y ^ 2 + z ^ 2)) :
    IsSquare (x * y) := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hz
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) Nat.prime_two).1 hd
    exact hp hp2
  have h4ne : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2ne h2ne
  have hD : x ^ 2 + y ^ 2 + z ^ 2 - 2 * x * y - 2 * x * z - 2 * y * z = 0 := by
    calc
      x ^ 2 + y ^ 2 + z ^ 2 - 2 * x * y - 2 * x * z - 2 * y * z
          = 2 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2 := by ring
      _ = 0 := by rw [h]; ring
  have hsq : (z - x - y) ^ 2 = 4 * x * y := by
    calc
      (z - x - y) ^ 2 = 4 * x * y + (x ^ 2 + y ^ 2 + z ^ 2 - 2 * x * y - 2 * x * z - 2 * y * z) := by ring
      _ = 4 * x * y := by rw [hD]; ring
  refine ⟨(z - x - y) / 2, ?_⟩
  field_simp [hsq]
  rw [show x * y * 2 ^ 2 = 4 * x * y by ring]
  exact hsq.symm

/-- The cyclic variants: xz and yz are squares too. -/
lemma descartes_pair_square_zmod' {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {x y z : ZMod p}
    (h : (x + y + z) ^ 2 = 2 * (x ^ 2 + y ^ 2 + z ^ 2)) :
    IsSquare (x * z) ∧ IsSquare (y * z) := by
  constructor
  · -- xz: apply the main lemma to the triple (x, z, y)
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      descartes_pair_square_zmod (p := p) hp (x := x) (y := z) (z := y) (by simpa [add_assoc, add_comm, add_left_comm] using h)
  · -- yz: apply to (y, z, x)
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      descartes_pair_square_zmod (p := p) hp (x := y) (y := z) (z := x) (by simpa [add_assoc, add_comm, add_left_comm] using h)


/-- A nonzero square mod the prime p has Jacobi symbol 1. -/
lemma jacobiSym_eq_one_of_zmod_square {a : ℤ} {p : ℕ} [Fact p.Prime]
    (hsq : IsSquare (a : ZMod p)) (hne : (a : ZMod p) ≠ 0) : jacobiSym a p = 1 := by
  have hleg : legendreSym p a = 1 := (legendreSym.eq_one_iff p hne).mpr hsq
  simpa [jacobiSym.legendreSym.to_jacobiSym] using hleg

end Apollo
