/-
Copyright: subproject `Submission/Work/FSeed/` of `mandelbar_not_path_connected`.

# `Work.FSeed.Portrait.alpha_orbit` — the period-`5` orbit of the root portrait angles

The two root angles of the parabolic seed parameter

  `α₁ = 371/1023`, `α₂ = 404/1023`

of `Submission/Work/FSeed/Defs.lean` sit over the common denominator `1023 = 3·11·31 = 2^10 - 1`,
which is exactly what makes them a period-`5` (and hence period-`10`) cycle of the tricorn angle
map `T θ = Int.fract (-2 θ) = -2θ mod 1`:

* `α₁ ↦ α₂` under `T^[5]`, `α₂ ↦ α₁` under `T^[5]`, hence `T^[10]` fixes both;
* the first ten iterates of `α₁` are pairwise distinct, so `α₁` has exact period `10` and the
  two rays `α₁`, `α₂` form a genuine period-`5` cycle of `T` (the halves of the cycle are
  exchanged by `T^[5]`);
* consequently the portrait angles have period `5`:
  `pairRay₁ (j+5) = pairRay₂ j` and `pairRay₂ (j+5) = pairRay₁ j`.

## The proof

All of this is arithmetic on the rationals of denominator `1023`.  The single analytic input is
the elementary reduction of a `T`-step on such a rational to a residue mod `1023`:

  `T (m/1023) = ((-2·m) mod 1023)/1023`   (`T_rat_mod`),

which is `Int.fract_div_intCast_eq_div_intCast_mod` (`Int.fract (a/N) = (a mod N)/N`) together
with `T θ = Int.fract (-2θ)`.  Iterating it gives, for `0 ≤ p < 1023`,

  `T^[n] (p/1023) = (((-2)^n · p) mod 1023)/1023`   (`iterate_mod`),

using `(-2)·(M mod 1023) ≡ -2M (mod 1023)` (`mul_emod_1023`).  The two instances
`p = 371` (`T_iter_alpha1`) and `p = 404` (`T_iter_alpha2`) turn the whole statement into the
finite residue computations

  `371 ↦ 281 ↦ 461 ↦ 101 ↦ 821 ↦ 404 ↦ 215 ↦ 593 ↦ 860 ↦ 326 ↦ 371`,

which are discharged by `norm_num`; the pairwise distinctness of the ten residues (equivalently,
`orbit_inj`: an equality of two iterates forces an equality of two distinct residues) is a
`interval_cases` case check on `i, j < 10`.
-/
import Mathlib
import Submission.Work.FSeed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Function
open scoped Topology

noncomputable section

namespace Work.FSeed.Portrait

open Work.FSeed

/-! ## One step of `T` on a rational with denominator `1023` -/

/-- The angle map `T` sends the rational `m/1023` to the residue `(-2m) mod 1023` over `1023`:
this is `T θ = Int.fract (-2θ)` together with `Int.fract (a/N) = (a mod N)/N`. -/
lemma T_rat_mod (m : ℤ) :
    T ((m : ℝ)/1023) = ((((-2 : ℤ) * m) % 1023 : ℤ) : ℝ)/1023 := by
  have key := Int.fract_div_intCast_eq_div_intCast_mod (k := ℝ) (m := (-2:ℤ)*m) (n := 1023)
  rw [T_apply]
  have h : -2 * ((m : ℝ)/1023) = (((-2 : ℤ) * m : ℤ) : ℝ)/1023 := by push_cast; ring
  rw [h]
  simpa using key

/-- Reducing `(-2)·(M mod 1023)` is the same as reducing `(-2)·M`. -/
lemma mul_emod_1023 (a M : ℤ) : (a * (M % 1023)) % 1023 = (a * M) % 1023 := by
  rw [Int.mul_emod, Int.mul_emod a M]; congr 1; rw [Int.emod_emod]

/-! ## The iterates of `T` on a rational with denominator `1023` -/

/-- Iterating `T_rat_mod`: for `0 ≤ p < 1023` the `n`-th iterate of `T` at `p/1023` is
`((-2)^n p) mod 1023` over `1023`. -/
lemma iterate_mod (p : ℤ) (hp0 : 0 ≤ p) (hp1 : p < 1023) (n : ℕ) :
    (T^[n]) ((p : ℝ)/1023) = ((((-2 : ℤ)^n * p) % 1023 : ℤ) : ℝ)/1023 := by
  induction n with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul, Int.emod_eq_of_lt hp0 hp1]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, T_rat_mod]
    congr 1
    rw [mul_emod_1023]
    congr 1
    rw [pow_succ]; ring_nf

/-- The iterates of `T` at the first root angle `α₁ = 371/1023`. -/
lemma T_iter_alpha1 (n : ℕ) :
    (T^[n]) α₁ = ((((-2 : ℤ)^n * 371) % 1023 : ℤ) : ℝ)/1023 := by
  have h : α₁ = ((371 : ℤ) : ℝ)/1023 := by norm_num [α₁]
  rw [h]
  exact iterate_mod 371 (by norm_num) (by norm_num) n

/-- The iterates of `T` at the second root angle `α₂ = 404/1023`. -/
lemma T_iter_alpha2 (n : ℕ) :
    (T^[n]) α₂ = ((((-2 : ℤ)^n * 404) % 1023 : ℤ) : ℝ)/1023 := by
  have h : α₂ = ((404 : ℤ) : ℝ)/1023 := by norm_num [α₂]
  rw [h]
  exact iterate_mod 404 (by norm_num) (by norm_num) n

/-! ## The period-`5` cycle of the root angles -/

/-- `T^[5] α₁ = α₂`: half of the period-`5` cycle. -/
lemma alpha1_five : (T^[5]) α₁ = α₂ := by
  rw [T_iter_alpha1 5]; norm_num [α₂]

/-- `T^[5] α₂ = α₁`: the other half of the period-`5` cycle. -/
lemma alpha2_five : (T^[5]) α₂ = α₁ := by
  rw [T_iter_alpha2 5]; norm_num [α₁]

/-- `T^[10] α₁ = α₁`: the root angle is fixed by the tenth iterate. -/
lemma alpha1_ten : (T^[10]) α₁ = α₁ := by
  rw [T_iter_alpha1 10]; norm_num [α₁]

/-! ## Exactness of the period -/

/-- The first ten iterates of `α₁` are pairwise distinct: two equal iterates would force two of
the ten residues `((-2)^n · 371) mod 1023` (all distinct) to be equal. -/
lemma orbit_inj : ∀ i j : ℕ, i < 10 → j < 10 → (T^[i]) α₁ = (T^[j]) α₁ → i = j := by
  intro i j hi hj h
  have hR : (((-2 : ℤ)^i * 371) % 1023 : ℤ) = (((-2 : ℤ)^j * 371) % 1023 : ℤ) := by
    have h2 : ((((-2 : ℤ)^i * 371) % 1023 : ℤ) : ℝ)
        = ((((-2 : ℤ)^j * 371) % 1023 : ℤ) : ℝ) := by
      have hh : ((((-2 : ℤ)^i * 371) % 1023 : ℤ) : ℝ)/1023
          = ((((-2 : ℤ)^j * 371) % 1023 : ℤ) : ℝ)/1023 := by
        rw [← T_iter_alpha1 i, ← T_iter_alpha1 j]; exact h
      linarith [hh]
    exact_mod_cast h2
  interval_cases i <;> interval_cases j <;> first | rfl | (norm_num at hR)

/-! ## The orbit portrait of the root angles -/

theorem alpha_orbit :
    (Work.FSeed.T^[10]) Work.FSeed.α₁ = Work.FSeed.α₁ ∧
      (Work.FSeed.T^[5]) Work.FSeed.α₁ = Work.FSeed.α₂ ∧
      (Work.FSeed.T^[5]) Work.FSeed.α₂ = Work.FSeed.α₁ ∧
      Work.FSeed.α₁ ≠ Work.FSeed.α₂ ∧
      (∀ i j : ℕ, i < 10 → j < 10 → i ≠ j →
        (Work.FSeed.T^[i]) Work.FSeed.α₁ ≠ (Work.FSeed.T^[j]) Work.FSeed.α₁) ∧
      (∀ j : ℕ, Work.FSeed.pairRay₁ (j + 5) = Work.FSeed.pairRay₂ j ∧
        Work.FSeed.pairRay₂ (j + 5) = Work.FSeed.pairRay₁ j) := by
  refine ⟨alpha1_ten, alpha1_five, alpha2_five, ?_, ?_, ?_⟩
  · norm_num [α₁, α₂]
  · intro i j hi hj hij h
    exact hij (orbit_inj i j hi hj h)
  · intro j
    constructor
    · simp only [pairRay₁, pairRay₂, Function.iterate_add_apply, alpha1_five]
    · simp only [pairRay₁, pairRay₂, Function.iterate_add_apply, alpha2_five]

end Work.FSeed.Portrait
