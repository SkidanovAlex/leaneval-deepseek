import Mathlib
import Submission.Work.ORLyndon.twoSidedShear
import Submission.Work.ORLyndon.Fox
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.eps_rightPow

/-!
# The five properties of the two-sided shear `x ↦ t ^ (-m) * x * t ^ (-m')`

`Work.ORLyndon.shear t x m m'` is the Nielsen transformation of the free group `F α` which fixes
every generator except `x` and sends `x ↦ t ^ (-m) * x * t ^ (-m')`.  This file collects the five
properties of it that are consumed by the residual argument of `Work.ORLyndon.EpsNeZeroDescent`
(and, through it, by the Lyndon-independence machinery of the `ORLyndon` subproject):

* `Function.Injective` / `Function.Surjective` — the shear is an automorphism of `F α`, since
  `shear t x (-m) (-m')` is a two-sided inverse of `shear t x m m'`;
* it is *clean off `t`*: `∂ (ψ (of q)) / ∂ y = 0` for `y ≠ t`, `q ≠ y` (the only letters occurring
  in the image of a generator are `t` and that generator itself);
* its exponent-sum shift: `σ_t (ψ w) = σ_t w - (m + m') · σ_x w`; choosing `m + m' = σ_t u / σ_x u`
  makes the image of the relator have vanishing `t`-exponent sum;
* it preserves `¬ IsProperPower`.

The proof follows the same route as `Work.ORLyndon.transvectionLeftProps`: the shear is exhibited
as a composite of the left transvection `x ↦ t ^ (-m) * x` with the right shear `x ↦ x * t^ (-m')`,
so bijectivity is by exhibit of an explicit two-sided inverse on the generators, the exponent-sum
formula is an induction on the word, cleanliness is a direct Fox computation, and the preservation
of `¬ IsProperPower` is transported along the inverse.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

/-! ## Fox derivatives of powers of a generator

Powering and inverting a single generator keeps the Fox derivative with respect to a *different*
letter equal to zero.  These are the only Fox computations needed for cleanliness off `t`. -/

/-- The Fox derivative of a natural power of `of t`, with respect to a different letter, vanishes. -/
private lemma foxD_pow_of_ne {X : Type*} [DecidableEq X] {K : Type*} [Ring K] {y t : X}
    (h : y ≠ t) (n : ℕ) : foxD (K := K) y ((FreeGroup.of t) ^ n) = 0 := by
  induction n with
  | zero => rw [pow_zero, foxD_one]
  | succ n ih =>
    rw [pow_succ, foxD_mul, ih, foxD_of, if_neg (Ne.symm h), mul_zero, add_zero]

/-- The Fox derivative of an integral power of `of t`, with respect to a different letter,
vanishes. -/
private lemma foxD_zpow_of_ne {X : Type*} [DecidableEq X] {K : Type*} [Ring K] {y t : X}
    (h : y ≠ t) (k : ℤ) : foxD (K := K) y ((FreeGroup.of t) ^ k) = 0 := by
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg k
  · rw [hn, zpow_natCast, foxD_pow_of_ne h n]
  · rw [hn, zpow_neg, zpow_natCast, foxD_inv, foxD_pow_of_ne h n, mul_zero, neg_zero]

/-! ## Cleanliness off `t` -/

/-- **The two-sided shear is clean off `t`.**  For `y ≠ t` the Fox derivative of the image of a
generator `of q` with respect to `y` vanishes as soon as `q ≠ y`: the image in question is either
`of q` itself (`q ≠ x`) or `t ^ (-m) * of x * t ^ (-m')` (`q = x`), and in both cases the only
letters occurring with a nonzero `y`-derivative would be `y` itself. -/
private lemma shear_foxD_clean {α : Type*} [DecidableEq α] {K : Type*} [Ring K] {t x : α}
    (hxt : t ≠ x) (m m' : ℤ) :
    ∀ y : α, y ≠ t → ∀ q : α, q ≠ y →
      foxD (K := K) y (shear t x m m' (FreeGroup.of q)) = 0 := by
  intro y hyt q hqy
  by_cases hqx : q = x
  · rw [hqx, shear_of]
    simp only [foxD_mul, foxD_zpow_of_ne hyt, foxD_of,
      if_neg (fun h : x = y => hqy (hqx.trans h)), mul_zero, add_zero]
  · rw [shear_of_ne hqx m m', foxD_of, if_neg hqy]

/-! ## The exponent-sum shift -/

/-- **The exponent-sum shift of the two-sided shear**: `σ_t (ψ w) = σ_t w - (m + m') · σ_x w`.
Every occurrence of `x ^ s` in `w` is replaced by `t ^ (-m * s) * x ^ s * t ^ (-m' * s)`, so the
`t`-exponent sum changes by `-(m + m')` times the `x`-exponent sum, while the exponent sum of every
other letter is untouched. -/
private theorem shear_eps {α : Type*} [DecidableEq α] {t x : α} (hxt : t ≠ x) (m m' : ℤ)
    (w : FreeGroup α) :
    Work.OROneRel.eps t (shear t x m m' w)
      = Work.OROneRel.eps t w - (m + m') * Work.OROneRel.eps x w := by
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · simp only [map_one, Work.OROneRel.epsc_one, mul_zero, sub_zero]
  · intro z
    by_cases hz : z = x
    · rw [hz, shear_of]
      simp only [Work.OROneRel.epsc_mul, Work.OROneRel.epsc_zpow, Work.OROneRel.epsc_of_eq]
      ring
    · rw [shear_of_ne hz m m', Work.OROneRel.epsc_of_ne (Ne.symm hz)]
      ring
  · intro z ih
    rw [map_inv, Work.OROneRel.epsc_inv, ih, Work.OROneRel.epsc_inv, Work.OROneRel.epsc_inv]
    ring
  · intro a b iha ihb
    rw [map_mul, Work.OROneRel.epsc_mul, iha, ihb, Work.OROneRel.epsc_mul, Work.OROneRel.epsc_mul]
    ring

/-! ## Bijectivity -/

/-- The shears attached to opposite pairs of integers are mutually inverse: this is the explicit
two-sided inverse of `shear t x m m'`.  Both composites fix every generator outside `x`, and on
`x` the two `t`-frames cancel. -/
private theorem shear_comp {α : Type*} [DecidableEq α] {t x : α} (hxt : t ≠ x) (m m' : ℤ) :
    (shear t x (-m) (-m')).comp (shear t x m m') = MonoidHom.id (FreeGroup α) := by
  refine FreeGroup.ext_hom _ _ ?_
  intro z
  show shear t x (-m) (-m') (shear t x m m' (FreeGroup.of z)) = FreeGroup.of z
  by_cases hz : z = x
  · rw [hz, shear_of, map_mul, map_mul, map_zpow, map_zpow,
      shear_of_ne (t := t) (x := x) (z := t) hxt, shear_of]
    group
  · rw [shear_of_ne hz m m', shear_of_ne hz (-m) (-m')]

/-! ## The main statement -/

/-- **The five properties of the two-sided shear `x ↦ t ^ (-m) * x * t ^ (-m')`.** -/
theorem shearProps {α : Type*} [DecidableEq α] {K : Type*} [Field K] (t x : α) (hxt : t ≠ x) (m m' : ℤ) :
    Function.Injective (Work.ORLyndon.shear (α := α) t x m m') ∧
    Function.Surjective (Work.ORLyndon.shear (α := α) t x m m') ∧
    (∀ y : α, y ≠ t → ∀ q : α, q ≠ y →
      foxD (K := K) y (Work.ORLyndon.shear t x m m' (FreeGroup.of q)) = 0) ∧
    (∀ w : FreeGroup α, Work.OROneRel.eps t (Work.ORLyndon.shear t x m m' w)
      = Work.OROneRel.eps t w - (m + m') * Work.OROneRel.eps x w) ∧
    (∀ w : FreeGroup α, ¬ Work.OROneRel.IsProperPower w →
      ¬ Work.OROneRel.IsProperPower (Work.ORLyndon.shear t x m m' w)) := by
  have hleft : Function.LeftInverse (shear t x (-m) (-m')) (shear t x m m') := fun u => by
    rw [← MonoidHom.comp_apply, shear_comp hxt m m']
    rfl
  -- the inverse composite: `shear t x m m'` is a left inverse of `shear t x (-m) (-m')`
  have hcomp' : (shear t x m m').comp (shear t x (-m) (-m')) = MonoidHom.id (FreeGroup α) := by
    simpa only [neg_neg] using shear_comp hxt (-m) (-m')
  have hright : Function.LeftInverse (shear t x m m') (shear t x (-m) (-m')) := fun u => by
    rw [← MonoidHom.comp_apply, hcomp']
    rfl
  exact ⟨hleft.injective, hright.surjective,
    fun y hy q hq => shear_foxD_clean (K := K) hxt m m' y hy q hq,
    fun w => shear_eps hxt m m' w,
    fun w hw hpp => by
      obtain ⟨v, k, hk, hv⟩ := hpp
      obtain ⟨u, rfl⟩ := hright.surjective v
      exact hw ⟨u, k, hk, hleft.injective (by rw [map_pow]; exact hv)⟩⟩

end Work.ORLyndon
