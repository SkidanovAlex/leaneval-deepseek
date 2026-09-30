import Mathlib
import Submission.Work.BMF.H6_imports

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Twisting the pretentious distance by a Dirichlet character and an `n^{it}` phase

For `f : ℕ → ℂ`, a Dirichlet character `χ` modulo `r`, and reals `T₀, u`,
the pretentious distance satisfies, for every `X`,

`𝔻 (f · χ · n^{-iT₀}) (n^{iu}) X = 𝔻 f (χ⁻¹ · n^{i(T₀+u)}) X`.

The two sums defining the distance have the same index set (the primes `≤ X`), and the
summands agree pointwise because for a prime `p`

`f(p) χ(p) p^{-iT₀} conj(p^{iu}) = f(p) conj(χ⁻¹(p) p^{i(T₀+u)})`,

using `conj(χ⁻¹(p)) = χ(p)` (values of a Dirichlet character are `0` or on the unit circle)
and `conj(p^{iw}) = p^{-iw} = p^{conj(iw)}` for a real base `p > 0`.
-/

namespace Work.BMF

open BoundedMultiplicativeFunctions

/-- Conjugation commutes with an exponentiation of a natural (in particular, real
nonnegative) base. -/
lemma star_natCast_cpow (n : ℕ) (w : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ w) = (n : ℂ) ^ (starRingEnd ℂ) w := by
  have h := Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg (y := (n : ℝ))
    (Nat.cast_nonneg n) w
  simpa using h

/-- For a complex Dirichlet character, conjugation of the value of the inverse character
at `a` is the value of the character at `a`. -/
lemma star_inv_apply_char (r : ℕ) (χ : DirichletCharacter ℂ r) (a : ZMod r) :
    (starRingEnd ℂ) ((χ⁻¹ : DirichletCharacter ℂ r) a) = χ a := by
  have h := congrArg (starRingEnd ℂ) (MulChar.star_apply' χ a)
  simpa using h.symm

/-- The pointwise identity underlying `D_twist_char`, at a prime `p`. -/
lemma twist_pointwise (r : ℕ) (χ : DirichletCharacter ℂ r) (f : ℕ → ℂ) (T₀ u : ℝ)
    {p : ℕ} (hp : p.Prime) :
    f p * χ p * (p : ℂ) ^ (-(Complex.I * T₀)) * (starRingEnd ℂ) ((p : ℂ) ^ (Complex.I * u))
      = f p *
        (starRingEnd ℂ) ((χ⁻¹ : DirichletCharacter ℂ r) p * (p : ℂ) ^ (Complex.I * (T₀ + u))) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h₁ : (starRingEnd ℂ) ((p : ℂ) ^ (Complex.I * u)) = (p : ℂ) ^ (-(Complex.I * u)) := by
    have h := star_natCast_cpow p (Complex.I * (u : ℂ))
    simpa using h
  have h₂ : (starRingEnd ℂ) ((p : ℂ) ^ (Complex.I * (T₀ + u))) =
      (p : ℂ) ^ (-(Complex.I * (T₀ + u))) := by
    have h := star_natCast_cpow p (Complex.I * ((T₀ : ℂ) + (u : ℂ)))
    simpa using h
  have hχ : (starRingEnd ℂ) ((χ⁻¹ : DirichletCharacter ℂ r) p) = χ p :=
    star_inv_apply_char r χ (p : ZMod r)
  rw [RingHom.map_mul, hχ, h₁, h₂]
  rw [show f p * χ ↑p * ↑p ^ (-(Complex.I * ↑T₀)) * ↑p ^ (-(Complex.I * ↑u))
        = f p * (χ ↑p * (↑p ^ (-(Complex.I * ↑T₀)) * ↑p ^ (-(Complex.I * ↑u)))) by ring]
  rw [← Complex.cpow_add (-(Complex.I * ↑T₀)) (-(Complex.I * ↑u)) hp0]
  rw [show -(Complex.I * (T₀ : ℂ)) + -(Complex.I * (u : ℂ))
        = -(Complex.I * ((T₀ : ℂ) + (u : ℂ))) by ring]

theorem D_twist_char (r : ℕ) (χ : DirichletCharacter ℂ r) (f : ℕ → ℂ) (T₀ u X : ℝ) :
    BoundedMultiplicativeFunctions.𝔻 (fun n ↦ f n * (χ n) * ((n : ℂ) ^ (-(Complex.I * T₀))))
        (fun n ↦ (n : ℂ) ^ (Complex.I * u)) X
      = BoundedMultiplicativeFunctions.𝔻 f
        (fun n ↦ (χ⁻¹ : DirichletCharacter ℂ r) n * ((n : ℂ) ^ (Complex.I * (T₀ + u)))) X := by
  unfold BoundedMultiplicativeFunctions.𝔻
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  show (1 - (f p * χ p * (p : ℂ) ^ (-(Complex.I * T₀)) *
        (starRingEnd ℂ) ((p : ℂ) ^ (Complex.I * u))).re) / (p : ℝ)
      = (1 - (f p * (starRingEnd ℂ) ((χ⁻¹ : DirichletCharacter ℂ r) p *
        (p : ℂ) ^ (Complex.I * (T₀ + u)))).re) / (p : ℝ)
  rw [twist_pointwise r χ f T₀ u (Nat.prime_of_mem_primesLE hp)]

end Work.BMF
