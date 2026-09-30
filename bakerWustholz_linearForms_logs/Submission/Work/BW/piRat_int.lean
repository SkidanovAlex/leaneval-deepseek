import Mathlib
import Submission.Work.BW.est15defs
import Submission.Work.BW.tijdeman_int

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Integrality of the `Π`-factor `piRat`

`piRat` (see `Submission.Work.BW.est15defs`) is the product of the values
`Δ(γ_m(λ); t_m) = C(γ_m(λ) + t_m, t_m)` of the Baker–Wüstholz `Δ`-polynomials at the
integral arguments `γ_m(λ)` of §13.  Each such value is an integer, so `piRat` is an integer.

The only input is the classical fact that `k!` divides the product of any `k` consecutive
integers (`Nat.factorial_coe_dvd_prod`), which applied to `x + 1, x + 2, …, x + k` gives the
integrality of `Δ(x;k)` for every integer `x`.
-/

namespace Work.BW

open Polynomial Finset

/-- Evaluation form of `deltaRat`: `Δ(x;k) = (x+1)(x+2)⋯(x+k)/k!`. -/
lemma deltaRat_eq_inv_mul_prod (x : ℤ) (k : ℕ) :
    deltaRat x k
      = ((k.factorial : ℚ))⁻¹ * ∏ i ∈ Finset.range k, ((x : ℚ) + (i : ℚ) + 1) := by
  rw [deltaRat, deltaPoly, Polynomial.smul_eq_C_mul, map_mul, Polynomial.aeval_C]
  congr 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C]
  push_cast
  ring

/-- `Δ(x;k)` is an integer for every integer `x`. -/
theorem deltaRat_exists_int (x : ℤ) (k : ℕ) : ∃ N : ℤ, deltaRat x k = (N : ℚ) := by
  obtain ⟨N, hN⟩ := Nat.factorial_coe_dvd_prod k (x + 1)
  refine ⟨N, ?_⟩
  rw [deltaRat_eq_inv_mul_prod]
  have hcast : (∏ i ∈ Finset.range k, ((x : ℚ) + (i : ℚ) + 1))
      = (k.factorial : ℚ) * (N : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) hN
    simp only [Int.cast_prod, Int.cast_add, Int.cast_natCast] at h
    push_cast at h
    have hp1 : (∏ i ∈ Finset.range k, ((x : ℚ) + (i : ℚ) + 1))
        = ∏ i ∈ Finset.range k, ((x : ℚ) + 1 + (i : ℚ)) :=
      Finset.prod_congr rfl fun i _ => by ring
    rw [hp1, h]
  rw [hcast, inv_mul_cancel_left₀]
  exact_mod_cast Nat.factorial_ne_zero k

/-- A finite product of rationals, each of which is an integer, is an integer. -/
lemma exists_int_prod_of_exists_int {ι : Type*} [Fintype ι] (f : ι → ℚ)
    (hf : ∀ i, ∃ N : ℤ, f i = (N : ℚ)) : ∃ N : ℤ, ∏ i, f i = (N : ℚ) := by
  classical
  choose N hN using hf
  refine ⟨∏ i, N i, ?_⟩
  rw [show (∏ i, f i) = ∏ i, ((N i : ℤ) : ℚ) from Finset.prod_congr rfl (fun i _ => hN i)]
  push_cast
  rfl

theorem piRat_int {n r : ℕ} (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ)
    (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ) (t : Fin (r - 1) → ℕ)
    (lm : AuxIdx r h D0 Dj) : ∃ N : ℤ, piRat b k L ι h D0 Dj t lm = (N : ℚ) := by
  rw [piRat]
  exact exists_int_prod_of_exists_int _
    (fun m => deltaRat_exists_int (gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))

end Work.BW
