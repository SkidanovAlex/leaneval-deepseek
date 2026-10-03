import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.Defs

/-!
# The `σ = 1` case of the sharp dual--difference interchange (`ddiSharp_one`)

This module holds the definitions and elementary rewrites shared by the proof of
`Work.Peluse.Ulower.StepLe.SharpMassDDI 1` (`Submission/Work/Peluse/Ulower/StepLe/ddiSharp/
ddiSharp_one.lean`, namespace `Work.Peluse.Ulower.StepLe.ddiSharp`) and the lemmas it delegates.

The level-`1` mass inequality is the Gram/energy argument in the Hilbert space `ℓ²(Z × ℤ)`:
with the averaged family `f = avgFn G = |Z|⁻¹ ∑_z G z`, the "row" correlations
`rowC G φ a u = ∑'_x e(φ a u x) conj (f (x + a 0)) f (x + u 0)` (the summands of `hypoMass`)
satisfy `(∑_u ‖rowC u‖²)² ≤ (∑_{u,v} ‖gramD (u,v)‖²) (∑'_x ‖f (x+a 0)‖²)²` for each row `a`
(the abstract energy lemma, with the test vector absorbing the decorations), and the conclusion
mass `concMass` is the sum of the `‖gramD‖²` over the cube set `□_1(H) = Θ_1(H)`.

* `avgFn`, `rowC`, `gramD` are the three objects (the `z`-average, the row correlation and the
  Gram entry);
* `cubeTerm_fin1` and `mixedPhase_fin1` are the one-dimensional identifications of the cube term
  and of the mixed phase, which is what makes `hypoMass`/`concMass` computable;
* `normSq_inv_natCast_mul` factors a `B⁻¹` normalisation out of a squared norm;
* `sum_gramD_swap` swaps the two indices of a double `‖gramD‖²`-sum (a `Finset.sum_comm`);
* `cubeTerm_zero` handles the empty-decoration case.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe.ddiSharp.one

noncomputable section

open Work.Peluse

/-- The averaged family `f y = |Z|⁻¹ ∑_z G z y` (the `z`-average of the decorations). -/
def avgFn {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ) : ℤ → ℂ :=
  fun y => ((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z y

/-- The level-`1` hypothesis correlation of the row `a` at the column shift `u`:
`∑'_x e(2πi φ a u x) · conj (f (x + a 0)) · f (x + u 0)`, the summand of `hypoMass`. -/
def rowC {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ)
    (φ : (Fin 1 → ℤ) → (Fin 1 → ℤ) → ℝ) (a u : Fin 1 → ℤ) : ℂ :=
  ∑' x : ℤ, Complex.exp (2 * Real.pi * Complex.I * (φ a u : ℂ) * (x : ℂ)) *
    star (avgFn G (x + a 0)) * avgFn G (x + u 0)

/-- The level-`1` conclusion correlation at the triple `(a,u,v)`:
`∑'_x e(2πi (φ a v - φ a u) x) · |Z|⁻¹ ∑_z G z (x + v 0) · conj (G z (x + u 0))`,
the summand of `concMass`. -/
def gramD {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ)
    (φ : (Fin 1 → ℤ) → (Fin 1 → ℤ) → ℝ) (a u v : Fin 1 → ℤ) : ℂ :=
  ∑' x : ℤ, Complex.exp (2 * Real.pi * Complex.I * ((φ a v : ℂ) - (φ a u : ℂ)) * (x : ℂ)) *
    (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + v 0) * star (G z (x + u 0)))

private lemma weight_const_fin1 (b : Bool) :
    Work.Peluse.weight (fun _ : Fin 1 => b) = if b then 1 else 0 := by
  cases b <;> simp [Work.Peluse.weight]

private lemma cornerShift_const_fin1 (b : Bool) (u v : Fin 1 → ℤ) :
    Work.Peluse.cornerShift u v (fun _ : Fin 1 => b) = if b then u 0 else v 0 := by
  cases b <;> simp [Work.Peluse.cornerShift]

/-- The one-dimensional cube term: `cubeTerm u v f x = f (x + v 0) · conj (f (x + u 0))`. -/
theorem cubeTerm_fin1 (u v : Fin 1 → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.cubeTerm u v f x = f (x + v 0) * star (f (x + u 0)) := by
  rw [Work.Peluse.cubeTerm]
  rw [Fintype.prod_equiv (Equiv.funUnique (Fin 1) Bool)
    (fun ω : Fin 1 → Bool => (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift u v ω)))
    (fun b : Bool => if b then star (f (x + u 0)) else f (x + v 0))]
  · rw [Fintype.prod_bool]; simp only [if_true, if_false, Bool.false_eq_true]; ring
  · intro ω
    rw [show (Equiv.funUnique (Fin 1) Bool) ω = ω 0 from rfl]
    have hω : ω = fun _ => ω 0 := by
      funext i
      exact congrArg ω (Subsingleton.elim i 0)
    rw [hω, weight_const_fin1 (ω 0), cornerShift_const_fin1 (ω 0) u v]
    cases h : ω 0 <;> simp

/-- The mixed phase at level `1` is the difference `φ a v - φ a u`. -/
theorem mixedPhase_fin1 (φ : (Fin 1 → ℤ) → (Fin 1 → ℤ) → ℝ) (a u v : Fin 1 → ℤ) :
    Work.Peluse.Ulower.StepLe.mixedPhase φ (a, u, v) = φ a v - φ a u := by
  rw [Work.Peluse.Ulower.StepLe.mixedPhase]
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool)
    (fun ω : Fin 1 → Bool => (-1 : ℝ) ^ Work.Peluse.weight ω *
        φ a (fun i => if ω i = true then u i else v i))
    (fun b : Bool => if b then -φ a u else φ a v)]
  · rw [Fintype.sum_bool]; simp only [Bool.false_eq_true, if_true, if_false]; ring
  · intro ω
    rw [show (Equiv.funUnique (Fin 1) Bool) ω = ω 0 from rfl]
    have hω : ω = fun _ => ω 0 := by funext i; exact congrArg ω (Subsingleton.elim i 0)
    rw [hω, weight_const_fin1 (ω 0)]
    have hmix : (fun i : Fin 1 => if (fun _ : Fin 1 => ω 0) i = true then u i else v i)
        = (if ω 0 then u else v) := by
      cases h : ω 0 <;> simp
    rw [hmix]
    cases h : ω 0 <;> simp

/-- Factoring a natural-number normaliser out of a squared norm. -/
lemma normSq_inv_natCast_mul (B : ℕ) (z : ℂ) :
    ‖((B : ℂ))⁻¹ * z‖ ^ 2 = (((B : ℝ))⁻¹) ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, norm_inv, Complex.norm_natCast, mul_pow, inv_pow]

/-- Swapping the two indices of a double sum of `‖gramD‖²`. -/
lemma sum_gramD_swap {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ)
    (φ : (Fin 1 → ℤ) → (Fin 1 → ℤ) → ℝ) (a : Fin 1 → ℤ) (N : Finset (Fin 1 → ℤ)) :
    (∑ u ∈ N, ∑ v ∈ N, ‖gramD G φ a v u‖ ^ 2)
      = ∑ u ∈ N, ∑ v ∈ N, ‖gramD G φ a u v‖ ^ 2 := by
  rw [Finset.sum_comm]

/-- The cube term of the zero function vanishes. -/
lemma cubeTerm_zero (u v : Fin 1 → ℤ) (x : ℤ) :
    Work.Peluse.cubeTerm u v (0 : ℤ → ℂ) x = 0 := by
  rw [Work.Peluse.cubeTerm]
  have h0 : ∀ n : ℕ, (star^[n]) (0 : ℂ) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, star_zero]
  have hfac : ∀ ω : Fin 1 → Bool,
      (star^[Work.Peluse.weight ω]) ((0 : ℤ → ℂ) (x + Work.Peluse.cornerShift u v ω)) = 0 := by
    intro ω
    simp
  rw [Finset.prod_congr rfl (fun ω _ => hfac ω)]
  simp

end

end Work.Peluse.Ulower.StepLe.ddiSharp.one
