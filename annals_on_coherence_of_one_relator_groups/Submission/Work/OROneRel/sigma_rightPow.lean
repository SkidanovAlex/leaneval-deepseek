/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

The exponent sum of the right-multiplication substitution `y ↦ y * t ^ (-(q y))`:

  `σ_t (rightPow t q u) = σ_t u * ∏_z (σ_z u) ^ (-(q z))`

(where the finite product is over any `s : Finset α` containing the support of `q`).  In particular
`σ_t (rightPow t q u) = 0` whenever `Σ_z q z · σ_z u = σ_t u`, which is the point of the
substitution: it makes a chosen exponent sum vanish at the cost of no extra non-`t` letters
(`nonTLetters_rightPow_le`).
-/
import Mathlib
import Submission.Work.OROneRel.rightPowDefs
import Submission.Work.OROneRel.FreiheitssatzDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The pointwise product of monoid homomorphisms into a commutative monoid, evaluated at a point,
is the product of the individual evaluations.  (Mathlib has this for `AddChar` but not for
`MonoidHom`; the instances are pointwise, so a `Finset` induction suffices.) -/
lemma prod_apply_monoidHom {M : Type*} {N : Type*} [MulOneClass M] [CommMonoid N]
    {ι : Type*} (s : Finset ι) (g : ι → (M →* N)) (x : M) :
    (∏ z ∈ s, g z) x = ∏ z ∈ s, g z x := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => simp [Finset.prod_cons, ih]

theorem sigma_rightPow {α : Type u} (t : α) (q : α → ℤ) (s : Finset α)
    (hs : ∀ z : α, z ∉ s → q z = 0) (u : FreeGroup α) :
    Work.OROneRel.sigma t (Work.OROneRel.rightPow t q u) =
      Work.OROneRel.sigma t u * ∏ z ∈ s, (Work.OROneRel.sigma z u) ^ (-(q z)) := by
  classical
  -- In `Multiplicative ℤ`, the generator `ofAdd 1` powers as `(ofAdd 1) ^ n = ofAdd n`.
  have hp : ∀ n : ℤ, (Multiplicative.ofAdd (1 : ℤ)) ^ n = Multiplicative.ofAdd n := by
    intro n
    rw [← Int.ofAdd_mul]; simp
  -- `sigma x` is `1` on every generator different from `x`, and `ofAdd 1` on `of x`.
  have hsig : ∀ x : α, sigma x (FreeGroup.of x) = Multiplicative.ofAdd (1 : ℤ) := by
    intro x
    simp only [sigma, FreeGroup.lift_apply_of]
    simp
  -- Both sides are homomorphisms `F α →* Multiplicative ℤ` in `u`; it suffices to compare them
  -- on the generators.  The right-hand side is the product of `sigma t` with the homs
  -- `u ↦ (sigma z u) ^ (-(q z))`.
  have key : (sigma t).comp (rightPow t q)
      = sigma t * ∏ z ∈ s, (zpowGroupHom (-(q z))).comp (sigma z) := by
    apply FreeGroup.ext_hom
    intro y
    -- Value of a single factor on the generator `of y`.
    have hF : ∀ z, ((zpowGroupHom (-(q z))).comp (sigma z)) (FreeGroup.of y)
        = if z = y then Multiplicative.ofAdd (-(q y)) else 1 := by
      intro z
      by_cases hzy : z = y
      · subst hzy
        have hz : (sigma z) (FreeGroup.of z) = Multiplicative.ofAdd (1 : ℤ) := hsig z
        rw [MonoidHom.comp_apply, hz, zpowGroupHom_apply, hp]
        simp
      · have hyz : y ≠ z := fun h => hzy h.symm
        have h1 : sigma z (FreeGroup.of y) = 1 := by
          simp only [sigma, FreeGroup.lift_apply_of]
          rw [if_neg hyz]
        rw [MonoidHom.comp_apply, h1, zpowGroupHom_apply, one_zpow, if_neg hzy]
    rw [MonoidHom.comp_apply, MonoidHom.mul_apply, prod_apply_monoidHom, rightPow_of]
    rw [map_mul, map_zpow]
    rw [hsig t]
    rw [hp]
    -- The product over `s` picks out the single `z = y` term, which is `ofAdd (-(q y))`; if
    -- `y ∉ s` then that term is trivial because `q y = 0`.
    have hprod : ∏ z ∈ s, ((zpowGroupHom (-(q z))).comp (sigma z)) (FreeGroup.of y)
        = Multiplicative.ofAdd (-(q y)) := by
      simp_rw [hF]
      rw [Finset.prod_ite_eq']
      by_cases hy : y ∈ s
      · simp [hy]
      · rw [if_neg hy]
        have hq : q y = 0 := hs y hy
        simp [hq]
    rw [hprod]
  have h2 : ((sigma t).comp (rightPow t q)) u
      = (sigma t * ∏ z ∈ s, (zpowGroupHom (-(q z))).comp (sigma z)) u :=
    congrArg (fun f : FreeGroup α →* Multiplicative ℤ => f u) key
  simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, prod_apply_monoidHom,
    zpowGroupHom_apply] at h2
  exact h2

end Work.OROneRel
