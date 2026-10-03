import Mathlib
import Submission.Work.Peluse.SwapC.pboxSum_asym_eq

/-!
# The core vocabulary of `Work.Peluse.SwapC.concatStep`

This module freezes the objects that the concatenation step (KKL Lemma 6.1) manipulates:

* `Rest v f` — the product over the *nonzero* sign patterns of the asymmetric cube term, so that
  `asymCube v f = f * Rest v f` (the `ω = 0` corner is factored out, which is where the
  Cauchy–Schwarz inequality in the base variable is applied);
* `cFun` — the corner family of the concatenation identification: after the Cauchy–Schwarz step
  the object is a box inner product over the `2s` doubled slots, whose corner functions are
  `\bar f(·+δ_{H₀}) f(·+δ_{H₁})` (the zero corner), `f · \bar f(·+δ_{H₀})` (the corners of the first
  half), `\bar f · f(·+δ_{H₁})` (the corners of the second half) and the constant `1` (the mixed
  corners).

See `NOTES_concatStep_SESSION.md` at the workspace root for the full route.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse

/-- The "tail" of the asymmetric cube term of order `d`: the product over the nonzero sign
patterns.  `asymCube v f x = f x * Rest v f x`. -/
def Rest {d : ℕ} (v : Fin d → ℤ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∏ ω ∈ Finset.univ.erase (0 : Fin d → Bool),
    (star^[weight ω]) (f (x + cornerShift v (fun _ => 0) ω))

/-- `asymCube` splits off its `ω = 0` corner. -/
lemma asymCube_eq_mul_Rest {d : ℕ} (v : Fin d → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    asymCube v f x = f x * Rest v f x :=
  asymCube_eq_mul d v f x

/-- The first half of the sign patterns of a `2s`-fold cube (the slots of the first index). -/
def cL (s : ℕ) (ω : Fin (2 * s) → Bool) : Fin s → Bool := fun j => ω ⟨j.val, by omega⟩

/-- The second half of the sign patterns of a `2s`-fold cube (the slots of the second index). -/
def cR (s : ℕ) (ω : Fin (2 * s) → Bool) : Fin s → Bool := fun j => ω ⟨s + j.val, by omega⟩

/-- The corner family of the concatenation identification (KKL Lemma 6.1), as a function of the
`2s`-fold sign pattern.  All the entries are `1`-bounded whenever `f` is. -/
def cFun (s : ℕ) (f : ℤ → ℂ) (dH0 dH1 : ℤ) (ω : Fin (2 * s) → Bool) : ℤ → ℂ :=
  if (∀ j : Fin s, cL s ω j = false) ∧ (∀ j : Fin s, cR s ω j = false) then
    fun z => star (f (z + dH0)) * f (z + dH1)
  else if (∀ j : Fin s, cR s ω j = false) then fun z => f z * star (f (z + dH0))
  else if (∀ j : Fin s, cL s ω j = false) then fun z => star (f z) * f (z + dH1)
  else fun _ => 1

/-- The corner family of the concatenation identification (KKL Lemma 6.1), indexed by the two
halves of the sign pattern. -/
def cUB (s : ℕ) (f : ℤ → ℂ) (dH0 dH1 : ℤ) (ε ε' : Fin s → Bool) : ℤ → ℂ :=
  if (∀ j : Fin s, ε j = false) ∧ (∀ j : Fin s, ε' j = false) then
    fun z => star (f (z + dH0)) * f (z + dH1)
  else if (∀ j : Fin s, ε' j = false) then fun z => f z * star (f (z + dH0))
  else if (∀ j : Fin s, ε j = false) then fun z => star (f z) * f (z + dH1)
  else fun _ => 1

/-- `cFun` is `cUB` read through the splitting of the sign pattern. -/
lemma cFun_eq_cUB (s : ℕ) (f : ℤ → ℂ) (dH0 dH1 : ℤ) (ω : Fin (2 * s) → Bool) :
    cFun s f dH0 dH1 ω = cUB s f dH0 dH1 (cL s ω) (cR s ω) := by
  unfold cFun cUB
  rfl

/-- The corner family is `1`-bounded. -/
lemma cFun_bound (s : ℕ) (f : ℤ → ℂ) (dH0 dH1 : ℤ) (hf : ∀ x : ℤ, ‖f x‖ ≤ 1)
    (ω : Fin (2 * s) → Bool) (z : ℤ) : ‖cFun s f dH0 dH1 ω z‖ ≤ 1 := by
  unfold cFun
  split_ifs with h1 h2 h3
  · rw [norm_mul, norm_star]
    exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
  · rw [norm_mul, norm_star]
    exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
  · rw [norm_mul, norm_star]
    exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
  · simp

end

end Work.Peluse.SwapC
