import Mathlib
import Submission.Work.ORLyndon.transvectionLeft
import Submission.Work.ORLyndon.Fox
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.eps_rightPow

/-!
# Properties of the left transvection

`Work.ORLyndon.transvectionLeft t y m` is the elementary Nielsen transformation of `F α` with
`y ↦ t ^ (-m) * y` and every other generator fixed.  This file proves the five properties used by
the transvection route of `Work.ORLyndon.EpsNeZeroDescent`:

* it is bijective (its inverse is `transvectionLeft t y (-m)`);
* it is *clean off `t`*: `∂ (ψ (of q)) / ∂ x = 0` for `x ≠ t`, `q ≠ x`;
* its exponent-sum shift: `eps t (ψ w) = eps t w - m * eps y w`;
* it preserves `¬ IsProperPower`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

/-! ## Fox derivatives of powers of a letter

Powering and inverting a single generator keeps the Fox derivative with respect to a *different*
letter equal to zero.  These are the only Fox computations needed for cleanliness off `t`. -/

/-- The Fox derivative of a natural power of `of t`, with respect to a different letter, vanishes. -/
private lemma foxD_pow_of_ne {X : Type*} [DecidableEq X] {K : Type*} [Ring K] {x t : X} (h : x ≠ t)
    (n : ℕ) : foxD (K := K) x ((FreeGroup.of t) ^ n) = 0 := by
  induction n with
  | zero => rw [pow_zero, foxD_one]
  | succ n ih => rw [pow_succ, foxD_mul, ih, foxD_of, if_neg (Ne.symm h), mul_zero, add_zero]

/-- The Fox derivative of an integral power of `of t`, with respect to a different letter,
vanishes. -/
private lemma foxD_zpow_of_ne {X : Type*} [DecidableEq X] {K : Type*} [Ring K] {x t : X}
    (h : x ≠ t) (k : ℤ) : foxD (K := K) x ((FreeGroup.of t) ^ k) = 0 := by
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg k
  · rw [hn, zpow_natCast, foxD_pow_of_ne (K := K) h n]
  · rw [hn, zpow_neg, zpow_natCast, foxD_inv, foxD_pow_of_ne (K := K) h n, mul_zero, neg_zero]

/-! ## Cleanliness off `t` -/

/-- **The left transvection is clean off `t`.**  For `x ≠ t` the Fox derivative of the image of a
generator `of q` with respect to `x` vanishes as soon as `q ≠ x`.  (`x = t` is excluded on purpose:
the image of `of y` does contain `t`.) -/
private lemma foxD_transvectionLeft_clean {α : Type*} [DecidableEq α] {K : Type*} [Ring K]
    {t y : α} (hyt : t ≠ y) (m : ℤ) :
    ∀ x : α, x ≠ t → ∀ q : α, q ≠ x →
      foxD (K := K) x (transvectionLeft t y m (FreeGroup.of q)) = 0 := by
  intro x hxt q hqx
  by_cases hqy : q = y
  · subst hqy
    rw [transvectionLeft_of, foxD_mul, foxD_zpow_of_ne (K := K) hxt, foxD_of, if_neg hqx,
      mul_zero, add_zero]
  · rw [transvectionLeft_of_ne hqy m, foxD_of, if_neg hqx]

/-! ## The exponent-sum shift -/

/-- **The exponent-sum shift of the left transvection**: `σ_t (ψ w) = σ_t w - m · σ_y w`.  With
`m · eps y u = eps t u` this makes the `t`-exponent sum of `u` vanish. -/
private theorem transvectionLeft_eps {α : Type*} [DecidableEq α] {t y : α} (hyt : t ≠ y) (m : ℤ)
    (w : FreeGroup α) :
    Work.OROneRel.eps t (transvectionLeft t y m w)
      = Work.OROneRel.eps t w - m * Work.OROneRel.eps y w := by
  refine FreeGroup.induction_on w ?h1 ?h2 ?h3 ?h4
  · simp only [map_one, Work.OROneRel.epsc_one, mul_zero, sub_zero]
  · intro z
    by_cases hz : z = y
    · subst hz
      simp only [transvectionLeft_of, Work.OROneRel.epsc_mul, Work.OROneRel.epsc_zpow,
        Work.OROneRel.epsc_of_eq, Work.OROneRel.epsc_of_ne hyt]
      ring
    · rw [transvectionLeft_of_ne hz m, Work.OROneRel.epsc_of_ne (Ne.symm hz)]
      ring
  · intro z ih
    rw [map_inv, Work.OROneRel.epsc_inv, ih, Work.OROneRel.epsc_inv, Work.OROneRel.epsc_inv]
    ring
  · intro a b iha ihb
    rw [map_mul, Work.OROneRel.epsc_mul, iha, ihb, Work.OROneRel.epsc_mul, Work.OROneRel.epsc_mul]
    ring

/-! ## Bijectivity -/

/-- The transvections attached to opposite integers are mutually inverse: this is the explicit
two-sided inverse of `transvectionLeft t y m`. -/
theorem transvectionLeft_comp {α : Type*} [DecidableEq α] {t y : α} (hyt : t ≠ y) (m m' : ℤ)
    (h : m + m' = 0) :
    (transvectionLeft t y m').comp (transvectionLeft t y m) = MonoidHom.id (FreeGroup α) := by
  refine FreeGroup.ext_hom _ _ ?_
  intro z
  show transvectionLeft t y m' (transvectionLeft t y m (FreeGroup.of z)) = FreeGroup.of z
  by_cases hz : z = y
  · rw [hz, transvectionLeft_of, map_mul, map_zpow,
      transvectionLeft_of_ne (t := t) (y := y) (z := t) hyt m', transvectionLeft_of]
    rw [← mul_assoc, ← zpow_add, ← neg_add, h, neg_zero, zpow_zero, one_mul]
  · rw [transvectionLeft_of_ne (t := t) (y := y) (z := z) hz m,
      transvectionLeft_of_ne (t := t) (y := y) (z := z) hz m']

/-! ## The main statement -/

/-- The five properties of the left transvection. -/
theorem transvectionLeftProps {α : Type*} [DecidableEq α] {K : Type*} [Field K] {t y : α}
    (hyt : t ≠ y) (m : ℤ) :
    Function.Injective (Work.ORLyndon.transvectionLeft t y m) ∧
    Function.Surjective (Work.ORLyndon.transvectionLeft t y m) ∧
    (∀ x : α, x ≠ t → ∀ q : α, q ≠ x →
      foxD (K := K) x (Work.ORLyndon.transvectionLeft t y m (FreeGroup.of q)) = 0) ∧
    (∀ w : FreeGroup α, Work.OROneRel.eps t (Work.ORLyndon.transvectionLeft t y m w)
      = Work.OROneRel.eps t w - m * Work.OROneRel.eps y w) ∧
    (∀ w : FreeGroup α, ¬ Work.OROneRel.IsProperPower w →
      ¬ Work.OROneRel.IsProperPower (Work.ORLyndon.transvectionLeft t y m w)) := by
  have hleft : Function.LeftInverse (transvectionLeft t y (-m)) (transvectionLeft t y m) :=
    fun u => by
      rw [← MonoidHom.comp_apply, transvectionLeft_comp hyt m (-m) (add_neg_cancel m)]
      rfl
  have hright : Function.LeftInverse (transvectionLeft t y m) (transvectionLeft t y (-m)) :=
    fun u => by
      rw [← MonoidHom.comp_apply, transvectionLeft_comp hyt (-m) m (neg_add_cancel m)]
      rfl
  exact ⟨hleft.injective, hright.surjective,
    fun x hx q hq => foxD_transvectionLeft_clean (K := K) hyt m x hx q hq,
    fun w => transvectionLeft_eps hyt m w, fun w hw hpp => by
      obtain ⟨v, k, hk, hv⟩ := hpp
      obtain ⟨u, rfl⟩ := hright.surjective v
      exact hw ⟨u, k, hk, hleft.injective (by rw [map_pow]; exact hv)⟩⟩

end Work.ORLyndon
