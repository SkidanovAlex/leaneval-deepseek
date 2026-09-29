import Mathlib
import Submission.HvdH.Interfaces

/-!
# Definitions for the Transform area (paper §3, Theorem 3.1)

This file contains the mathematical objects used to state the correctness of the power-of-two
complex transform `F_{t₁,…,t_d}` (paper Theorem 3.1):

* `zeta r c` = `ζ^c` with `ζ = e^{πi/r}` (paper Prop 3.5);
* `chirp ts j` = `a_j = e^{πi Σ_i j_i²/t_i}` (paper (3.1));
* `phiArr`, `psiFlat`: the maps `T̃` and `Ũ = T̃⁻¹` of paper Prop 3.5, written as the
  pointwise scalings of the coefficient vector by `ζ^c` resp. `ζ^{-c}`.

Nothing here depends on the program layer; the program lemmas are stated in terms of
`cvecVal`, `rarrVal`, `fxVec`, `fxArr`, `Approx`, `ApproxR`, `convC`, `convR`, `dftMulti`
from `Submission.HvdH.Interfaces`.
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-- `ζ ^ c` where `ζ = e^{πi/r}` (paper Prop 3.5). -/
noncomputable def zeta (r c : ℕ) : ℂ := Complex.exp (Real.pi * Complex.I * (c : ℂ) / (r : ℂ))

/-- `ζ ^ (-c)`; since `‖ζ‖ = 1` this is the conjugate of `ζ^c`. -/
noncomputable def zetaInv (r c : ℕ) : ℂ := (zeta r c)⁻¹

/-- The Bluestein chirp vector: `a_j = e^{πi Σ_i j_i²/t_i}` for a flat lexicographic index
`j` (paper (3.1)); `j_i = (digits ts j)_i`. -/
noncomputable def chirp (ts : List ℕ) (j : ℕ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (phase ts (digits ts j) (digits ts j) : ℂ))

/-- The map `T̃` of paper Prop 3.5: apply `S` (multiply the coefficient of `y^c` by `ζ^c`) to every
last-axis block.  Indexed by the flat type `Fin ((ts' ++ [r]).prod)` so that it composes with
`convC (ts' ++ [r])` without casts. -/
noncomputable def phiArrL (r : ℕ) (ts' : List ℕ) (w : Fin ((ts' ++ [r]).prod) → ℂ) :
    Fin ts'.prod → Fin r → ℂ :=
  fun a c => zeta r c * w ⟨(a : ℕ) * r + c, by
    have h1 := a.isLt; have h2 := c.isLt
    rw [List.prod_append]
    have h3 : (a : ℕ) * r + (c : ℕ) < (a : ℕ) * r + r := Nat.add_lt_add_left h2 _
    have h4 : (a : ℕ) * r + r = ((a : ℕ) + 1) * r := by rw [Nat.succ_mul]
    simpa using lt_of_lt_of_le (h4 ▸ h3) (Nat.mul_le_mul_right r (Nat.succ_le_of_lt h1))⟩

/-- The inverse `Ũ = T̃⁻¹` of paper Prop 3.5: flatten `(a,c) ↦ a*r+c` and multiply the `i`-th
entry by `ζ^{-(i mod r)}`. -/
noncomputable def psiFlatL (r : ℕ) (ts' : List ℕ) (v : Fin ts'.prod → Fin r → ℂ) :
    Fin ((ts' ++ [r]).prod) → ℂ :=
  fun i => (zeta r ((i : ℕ) % r))⁻¹ * v ⟨(i : ℕ) / r, by
    have hi : (i : ℕ) < ts'.prod * r := by simpa [List.prod_append] using i.isLt
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; exact absurd hi (by simp)
    · exact (Nat.div_lt_iff_lt_mul h).2 hi⟩ ⟨(i : ℕ) % r, by
    have hi : (i : ℕ) < ts'.prod * r := by simpa [List.prod_append] using i.isLt
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; exact absurd hi (by simp)
    · exact Nat.mod_lt _ h⟩

/-- The pointwise scaling of a flat vector by the stretched table `i ↦ ζ^{i mod r}` (the map
`T̃` in "flat" form). -/
noncomputable def phiFlat (r : ℕ) (M : ℕ) (w : Fin (M * r) → ℂ) : Fin (M * r) → ℂ :=
  fun i => zeta r ((i : ℕ) % r) * w i

/-- The pointwise scaling of a flat vector by the stretched table `i ↦ ζ^{-(i mod r)}`. -/
noncomputable def psiFlat' (r : ℕ) (M : ℕ) (w : Fin (M * r) → ℂ) : Fin (M * r) → ℂ :=
  fun i => (zeta r ((i : ℕ) % r))⁻¹ * w i

@[simp] lemma zeta_zero (r : ℕ) : zeta r 0 = 1 := by simp [zeta]

lemma zeta_eq_pow (r c : ℕ) : zeta r c = zeta r 1 ^ c := by
  rw [zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma zeta_add (r a b : ℕ) : zeta r (a + b) = zeta r a * zeta r b := by
  rw [zeta, zeta, zeta, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `ζ^r = -1` (paper Prop 3.5). -/
lemma zeta_one (r : ℕ) : zeta r 1 = Complex.exp (Real.pi * Complex.I / (r : ℂ)) := by
  rw [zeta]; congr 1; ring

lemma zeta_self (r : ℕ) (hr : 0 < r) : zeta r r = -1 := by
  rw [zeta_eq_pow, zeta_one, ← Complex.exp_nat_mul]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h : (r : ℂ) * (Real.pi * Complex.I / (r : ℂ)) = Real.pi * Complex.I := by
    field_simp
  rw [h, Complex.exp_pi_mul_I]

lemma zeta_ne_zero (r : ℕ) (c : ℕ) : zeta r c ≠ 0 := by
  rw [zeta_eq_pow]; exact pow_ne_zero _ (Complex.exp_ne_zero _)

lemma phase_zero_left (ts : List ℕ) : phase ts (digits ts 0) (digits ts 0) = 0 := by
  induction ts with
  | nil => simp [HvdH.phase]
  | cons t ts ih => simp only [HvdH.digits, HvdH.phase, Nat.zero_mod]; rw [ih]; simp

@[simp] lemma chirp_zero (ts : List ℕ) : chirp ts 0 = 1 := by
  rw [chirp, phase_zero_left]
  simp [Complex.ofReal_zero]

end Work.Transform
