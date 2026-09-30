import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The monomial character `x ↦ ∏ j, (x j : ℂ) ^ (w j)` of the torus `(ℂˣ)^m`, as a monoid
homomorphism into the multiplicative monoid `ℂ`.  (Here the target is the underlying
multiplicative monoid of `ℂ`; the values are always nonzero.) -/
noncomputable def monoChar (m : ℕ) (w : Fin m → ℤ) : (Fin m → ℂˣ) →* ℂ where
  toFun x := ∏ j, (x j : ℂ) ^ (w j)
  map_one' := by simp
  map_mul' := by
    intro x y
    simp only [Pi.mul_apply, Units.val_mul]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => by rw [mul_zpow])

@[simp]
lemma monoChar_apply {m : ℕ} (w : Fin m → ℤ) (x : Fin m → ℂˣ) :
    monoChar m w x = ∏ j, (x j : ℂ) ^ (w j) := rfl

/-- `2 : ℂ` is not a root of unity, so the map `n ↦ 2 ^ n` on `ℤ` is injective. -/
lemma two_cpow_inj {a b : ℤ} (h : (2 : ℂ) ^ a = (2 : ℂ) ^ b) : a = b := by
  have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [hcast] at h
  rw [← Complex.ofReal_zpow, ← Complex.ofReal_zpow] at h
  exact (zpow_right_strictMono₀ (show (1 : ℝ) < 2 by norm_num)).injective
    (Complex.ofReal_injective h)

/-- The character index `w` is determined by the character: distinct `w` give distinct monomial
characters.  Evaluate at the torus point with `j`-th coordinate `2` and all others `1`. -/
lemma monoChar_injective (m : ℕ) : Function.Injective (monoChar m) := by
  intro w w' h
  funext i
  have hx : ∏ j, (((Function.update (1 : Fin m → ℂˣ) i (Units.mk0 (2 : ℂ) (by norm_num))) j : ℂ)
        ^ (w j))
      = ∏ j, (((Function.update (1 : Fin m → ℂˣ) i (Units.mk0 (2 : ℂ) (by norm_num))) j : ℂ)
        ^ (w' j)) := by
    simpa using DFunLike.congr_fun h
      (Function.update (1 : Fin m → ℂˣ) i (Units.mk0 (2 : ℂ) (by norm_num)))
  have e1 : ∏ j, (((Function.update (1 : Fin m → ℂˣ) i (Units.mk0 (2 : ℂ) (by norm_num))) j : ℂ)
        ^ (w j)) = (2 : ℂ) ^ (w i) := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      rw [Function.update_of_ne hj]
      simp
    · intro hj
      exact absurd (Finset.mem_univ i) hj
  have e2 : ∏ j, (((Function.update (1 : Fin m → ℂˣ) i (Units.mk0 (2 : ℂ) (by norm_num))) j : ℂ)
        ^ (w' j)) = (2 : ℂ) ^ (w' i) := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      rw [Function.update_of_ne hj]
      simp
    · intro hj
      exact absurd (Finset.mem_univ i) hj
  rw [e1, e2] at hx
  exact two_cpow_inj hx

/-- Linear independence of the monomial characters `x ↦ ∏ j, (x j : ℂ) ^ (w j)` on the
torus `(ℂˣ)^m` (indexed by `w : Fin m → ℤ`, with `zpow` exponents): a finite linear combination
of distinct such characters that vanishes at every torus point has all coefficients zero.
This is Dedekind's linear independence of characters applied to the monoid homs
`(Fin m → ℂˣ) →* ℂ`, `x ↦ ∏ j, (x j : ℂ) ^ (w j)`, together with the fact that distinct `w`
give distinct characters (e.g. evaluate at `x` with `x j = 2` and the other coordinates `1`). -/
lemma mono_char_linearIndependent {m : ℕ} (s : Finset (Fin m → ℤ)) (c : (Fin m → ℤ) → ℂ)
    (h : ∀ x : Fin m → ℂˣ, ∑ w ∈ s, c w * ∏ j, (x j : ℂ) ^ (w j) = 0) :
    ∀ w ∈ s, c w = 0 := by
  have hLI : LinearIndependent ℂ (fun w : Fin m → ℤ => ⇑(monoChar m w)) :=
    (linearIndependent_monoidHom (Fin m → ℂˣ) ℂ).comp (monoChar m) (monoChar_injective m)
  rw [linearIndependent_iff'] at hLI
  refine hLI s c ?_
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, monoChar_apply]
  exact h x

end Work.BW
